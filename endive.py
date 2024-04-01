import random
import logging
import sys
import os
import time
import subprocess
import re
import json
import argparse
import platform
from datetime import datetime
import tempfile
import uuid
import pickle
import itertools
import datetime
from itertools import chain, combinations

import graphviz

import pyeda
import pyeda.inter

import mc
import tlaparse
from proofs import *
from mc import CTI,Trace,State

DEBUG = False
MAC_FAST_JAVA_EXE = "/usr/local/zulu15.32.15-ca-jdk15.0.3-macosx_aarch64/bin/java"
JAVA_EXE="java"
GEN_TLA_DIR="gen_tla"
STATECACHE_DIR="statecache"
LATEST_TLC_JAR = "tla2tools_2.18.jar"

# Use local custom built TLC for now.
# TLC_JAR = "../../tlaplus/tlatools/org.lamport.tlatools/dist/tla2tools.jar"
TLC_JAR = "tla2tools-checkall.jar"

def powerset(iterable, min_size=0):
    "powerset([1,2,3]) --> () (1,) (2,) (3,) (1,2) (1,3) (2,3) (1,2,3)"
    s = list(iterable)
    subsets = list(chain.from_iterable(combinations(s, r) for r in range(len(s)+1)))
    return [subset for subset in subsets if len(subset) >= min_size]


def chunks(seq, n_chunks):
    """ Splits a given iterable into n evenly (as possible) sized chunks."""
    N = len(seq)
    chunk_size = max(N // n_chunks, 1)
    # print("chunk size:", chunk_size)
    return (seq[i:i+chunk_size] for i in range(0, N, chunk_size))

def dict_product(inp):
    """ Produce Cartesian product of dicts with list valued fields. """
    for k in inp:
        inp[k] = [(i,v) for i,v in enumerate(inp[k])]
    # print(inp[k])
    prod = list(itertools.product(*inp.values()))
    # print(list(prod))

    # Prefer instances with all smaller params before looking at instances
    # with larger params.
    elems = [dict(zip(inp, x)) for x in prod]
    sorted_elems = sorted(elems, key = lambda d : max([v[0] for v in d.values()]))
    
    # Remove sort indices.
    for d in sorted_elems:
        for k in d:
            d[k] = d[k][1]
    return sorted_elems

class InductiveInvGen():
    """ 
    Encapsulates the algorithm for inferring an inductive invariant given a
    protocol specification, safety property, and various other parameters.
    """

    def __init__(self, specdir, specname, safety, constants, state_constraint, quant_inv, model_consts, preds,
                    symmetry=False, simulate=False, simulate_depth=6, typeok="TypeOK", tlc_specific_spec=False, seed=0, num_invs=1000, num_rounds=3, num_iters=3, 
                    num_simulate_traces=10000, tlc_workers=6, quant_vars=[],java_exe="java",cached_invs=None, cached_invs_gen_time_secs=None, use_cpp_invgen=False,
                    pregen_inv_cmd=None, opt_quant_minimize=False, try_final_minimize=False, 
                    proof_tree_mode=False,
                    proof_tree_mode_persistent=False, 
                    interactive_mode=False, max_num_conjuncts_per_round=10000,
                    max_num_ctis_per_round=10000, override_num_cti_workers=None, use_apalache_ctigen=False,all_args={},spec_config=None,
                    auto_lemma_action_decomposition=False, 
                    enable_partitioned_state_caching=False,
                    enable_cti_slice_projection=False,
                    action_filter=None):
        self.java_exe = java_exe
        self.java_version_info = None
        
        self.specdir = specdir
        self.results_dirname = "results"
        self.specname = specname
        self.safety = safety
        self.cached_invs=cached_invs
        self.cached_invs_gen_time_secs=cached_invs_gen_time_secs
        self.use_cpp_invgen = use_cpp_invgen
        self.pregen_inv_cmd = pregen_inv_cmd

        self.spec_config = spec_config
        self.all_args = all_args

        self.seed = seed
        self.num_rounds = num_rounds
        self.num_iters = num_iters
        self.num_invs = num_invs
        self.tlc_workers = tlc_workers
        self.n_cti_elimination_workers = all_args["cti_elimination_workers"]
        self.use_apalache_ctigen = use_apalache_ctigen
        self.do_apalache_final_induction_check = all_args["do_apalache_final_induction_check"]
        self.auto_lemma_action_decomposition = auto_lemma_action_decomposition
        self.action_filter = action_filter
        # Actions specified in comma-separated list.
        if self.action_filter is not None:
            self.action_filter = self.action_filter.split(",")

        # Ensure a reasonable default timeout on these checks for now.
        # See https://apalache.informal.systems/docs/apalache/tuning.html#timeouts for more details.
        self.apalache_smt_timeout_secs = all_args["apalache_smt_timeout_secs"]

        self.max_proof_node_ctis = all_args["max_proof_node_ctis"]
        self.proof_tree_mode = proof_tree_mode

        # In persistent mode we will save the generated proof graph on completion and also load 
        # from a previously saved proof graph by default if one exists.
        self.persistent_proof_tree_mode = proof_tree_mode_persistent

        self.proof_tree_cmd = all_args["proof_tree_cmd"]
        self.proof_struct_tag = all_args["proof_struct_tag"]
        self.interactive_mode = interactive_mode
        self.max_num_conjuncts_per_round = max_num_conjuncts_per_round
        self.max_duration_secs_per_round = all_args["max_duration_secs_per_round"]
        self.override_num_cti_workers = override_num_cti_workers
        self.k_cti_induction_depth = all_args["k_cti_induction_depth"]

        self.target_sample_states = all_args["target_sample_states"]
        self.target_sample_time_limit_ms = all_args["target_sample_time_limit_ms"]
        self.save_dot = all_args["save_dot"]
        self.enable_partitioned_state_caching = enable_partitioned_state_caching
        self.enable_cti_slice_projection = enable_cti_slice_projection
        self.disable_state_cache_slicing = all_args["disable_state_cache_slicing"]
        self.disable_grammar_slicing = all_args["disable_grammar_slicing"]


        # Set an upper limit on CTIs per round to avoid TLC getting overwhelmend. Hope is that 
        # this will be enough to provide reasonably even sampling of the CTI space.
        self.MAX_NUM_CTIS_PER_ROUND = max_num_ctis_per_round

        # Adjust the number of traces generated by each worker so that the overall
        # amount is roughly equal to the specified number of traces.
        self.num_simulate_traces = num_simulate_traces
        self.num_simulate_traces_per_worker = num_simulate_traces // self.tlc_workers

        self.quant_inv = quant_inv
        self.quant_vars = quant_vars
        self.preds = preds
        self.opt_quant_minimize = opt_quant_minimize
        self.try_final_minimize = try_final_minimize

        # Whether or not we re-run an iteration after finding some conjuncts
        # that eliminate CTIs.
        self.rerun_iterations = True

        self.initialize_quant_inv()

        #
        # TLC model config.
        #

        # Accept constants as either list of lines or string.
        # if type(constants)==list:
            # constants = "\n".join(constants)
        self.constants = constants

        self.state_constraint = state_constraint
        self.model_consts = model_consts
        self.symmetry = symmetry
        self.simulate = simulate
        self.simulate_depth = simulate_depth
        self.typeok = typeok
        self.tlc_specific_spec = tlc_specific_spec

        self.strengthening_conjuncts = []

        # The set of all generated invariants discovered so far.
        self.all_sat_invs = set()
        self.all_checked_invs = set()

        # Is the conjunction of the safety property and the current set of
        # strengthening conjuncts believed to be inductive.
        self.is_inductive = False

        # Set randomness based on given seed.
        random.seed(self.seed)

        # General statistics.
        self.state_cache_start = 0
        self.ctigen_start = 0
        self.invcheck_start = 0
        self.ctielimcheck_start = 0

        self.ctigen_duration_secs = 0
        self.invcheck_duration_secs = 0
        self.ctielimcheck_duration_secs = 0
        self.state_cache_duration_secs = 0
        self.total_duration_secs = 0
        self.total_num_ctis_eliminated = 0
        self.total_num_cti_elimination_rounds = 0

        # Clear and create directory for generated files if needed.
        os.system(f"rm -rf {os.path.join(self.specdir, GEN_TLA_DIR)}")
        os.system(f"rm -rf {os.path.join(self.specdir, 'states')}")
        os.system(f"mkdir -p {os.path.join(self.specdir, GEN_TLA_DIR)}")

    def constants_obj_to_constants_str(self, constants_obj):
        if type(constants_obj) == list:
            return "CONSTANTS\n" + "\n".join(constants_obj)
        if type(constants_obj) == dict:
            out = ""
            for c in constants_obj:
                val = constants_obj[c]
                # TODO: Consider how to handle multi-valued parameters.
                # for minimal CTI generation. For now take the last parameter
                # in the list.
                if type(constants_obj[c]) == list:
                    val = constants_obj[c][-1] 
                out += f"{c} = {val}\n"
            return "CONSTANTS\n" + out
        return constants_obj

    def get_tlc_config_constants_str(self):
        """ Return string for CONSTANT definitions in TLC config. """
        # return self.get_config_constant_instances()[-1]
        return self.constants_obj_to_constants_str(self.get_config_constant_instances()[-1])
    
    def get_tlc_overrides_str(self):
        out = ""
        if "tlc_overrides" in self.spec_config:
            for k in self.spec_config["tlc_overrides"]:
                out += k + " <- " + self.spec_config["tlc_overrides"][k] + "\n"
        return out

    
    def get_config_constant_instances(self):
        """ 
        If the CONSTANT parameter settings are multi-valued, enumerate the possible
        parameterized instantiations based on each multi-valued parameters e.g. the Cartesian product
        of all possible parameter values for each field.

        TODO: Eventually would need to think more about enumeration order here (e.g. smallest first).
        """

        if not type(self.constants) == dict:
            return [self.constants]

        # First convert fields of dict to 1 element lists if they are not lists.
        listified_constants = dict(self.constants)
        for k in listified_constants:
            if not type(listified_constants[k]) == list:
                listified_constants[k] = [listified_constants[k]]
        return dict_product(listified_constants)

    def initialize_quant_inv(self):
        """ Set up quantifier template function."""
        quant_inv_str = self.quant_inv

        # Optionally enable optimization to simplify quantifier expressions when
        # possible for faster invariant checking.
        if self.opt_quant_minimize:
            logging.info("Enabling quantifier minimization optimization for faster invariant checking.")
            var_quantifiers = list(filter(len,[q.strip() for q in quant_inv_str.split(":")]))

            def opt_quant_inv_fn(invarg):
                # Remove unnecessary quantified variables if they do not appear in the
                # unquantified expression. For example, we would simplify an expression like
                #
                #   \A i,j \in Server : i > 3
                #
                # to:
                #
                #   \A i \in Server : i > 3
                #
                # i.e. get rid of the extra quantified variable out front. This can
                # make it faster for TLC to check candidate invariants.
                quantifiers_to_keep = []
                for q in var_quantifiers:
                    quant_var_name = q.split(" ")[1]
                    if quant_var_name in invarg:
                        quantifiers_to_keep.append(q)
                return " : ".join(quantifiers_to_keep + [invarg])

            self.quant_inv = opt_quant_inv_fn
        else:
            quant_inv_fn_temp = lambda inv : quant_inv_str + inv
            self.quant_inv = quant_inv_fn_temp

    def run_cache_invs(self, invs_cache_filename, quant_inv_alt=None, quant_vars=[], preds_alt=None, min_num_conjuncts=2, max_num_conjuncts=2, symmetry=False, tlc_workers=6):
        """ Generate a set of invariants for a given protocol and save them to disk."""
        sat_invs = {}
        invs_file = open(invs_cache_filename, 'w')

        # Generate and check random set of invariants.
        logging.info("Generating %d invariants." % self.num_invs)
        process_local = False
        invs = mc.generate_invs(preds, self.num_invs, min_num_conjuncts=min_num_conjuncts, max_num_conjuncts=max_num_conjuncts, process_local=process_local, quant_vars=quant_vars)
        invs = sorted(list(invs))

        # Print invariants for debugging.
        # for inv in invs_sorted:
        #     print(self.quant_inv(inv))

        # Check the invariants.
        sat_invs = self.check_invariants(invs)
        sat_invs = sorted(list(sat_invs))

        for inv in sat_invs:
            invi = int(inv.replace("Inv",""))
            invexp = self.quant_inv(invs[invi])
            # print invexp
            invs_file.write(invexp)
            invs_file.write("\n")

        alt_sat_invs = {}
        # if quant_inv_alt:
        #     print("Generating %d invariants with quant alt." % num_invs)
        #     logging.debug("Generating %d invariants with quant alt." % num_invs)
        #     process_local = False
        #     invs = generate_invs(self.preds + self.preds_alt, num_invs, min_num_conjuncts=min_num_conjuncts, max_num_conjuncts=max_num_conjuncts, process_local=process_local, quant_vars=quant_vars)

        #     print("Checking %d unique invariants with quant alt." % len(invs))
        #     logging.debug("Checking %d unique invariants with quant alt." % len(invs))
        #     alt_sat_invs = self.check_invariants(invs)

        #     for inv in alt_sat_invs:
        #         invi = int(inv.replace("Inv",""))
        #         invexp = quant_inv_alt(sorted(invs)[invi])
        #         # print invexp
        #         invs_file.write(invexp)
        #         invs_file.write("\n")
        
        print("Found %d total invariants. Cached them to '%s'" % (len(sat_invs) + len(alt_sat_invs), invs_cache_filename))
        invs_file.close()

    def save_result(self, results_dirname="results"):
        # Create results directory if necessary.
        self.results_dirname = results_dirname
        os.system(f"mkdir -p {self.get_results_dir()}")
        os.system(f"mkdir -p {self.get_spec_results_dir()}")

        self.save_generated_inv()
        self.save_stats()

    def save_generated_inv(self):
        # Save generated inductive invariant to own TLA+ module.
        # Include random seed in filename.
        ind_spec_name = f"{self.specname}_IndAutoGen_{self.seed}.tla"
        spec_filepath = os.path.join(self.get_spec_results_dir(), ind_spec_name)
        f = open(spec_filepath, 'w')
        f.write(f"---- MODULE {self.specname}_IndAutoGen_{self.seed} ----\n")
        f.write(f"EXTENDS {self.specname}\n")
        f.write("\n")
        f.write(f"\* statistics\n")
        f.write(f"\* -----------------\n")
        stats = self.get_stats_obj()
        for stat in stats:
            f.write(f"\* {stat}: {stats[stat]}\n")
        f.write("\n")
        f.write("\* Inductive strengthening conjuncts\n")
        for c in self.strengthening_conjuncts:
            f.write(f"{c[0]}_def == {c[1]}\n")
        f.write("\n")
        f.write("\* The inductive invariant candidate.\n")
        f.write(f"IndAuto ==\n")
        f.write(f"  /\ {self.typeok}\n")
        f.write(f"  /\ {self.safety}\n")
        conj_def_names = [c[0]+"_def" for c in self.strengthening_conjuncts]
        for c in conj_def_names:
            f.write(f"  /\ {c}\n")

        f.write("\n")

        # Include a TLAPS proof skeleton.
        alldefs = ",".join(([self.typeok, "Init","Next","IndAuto",self.safety] + conj_def_names))
        proof_lines = [
            "\* TLAPS Proof skeleton.\n"
            "\* THEOREM Init => IndAuto \n",
            "\*  BY DEF " + alldefs + "\n",
            "\* THEOREM IndAuto /\ Next => IndAuto'\n"
            "\*  BY DEF " + alldefs + "\n",
        ]
        f.writelines(proof_lines)
        f.write(f"====\n")
        f.close()

    def save_java_version_info(self):
        # 'java -version' appears to go to stderr.
        cmd = self.java_exe + " -version"
        proc = subprocess.Popen(cmd, shell=True, stderr=subprocess.PIPE)
        out = proc.stderr.read().decode(sys.stderr.encoding)
        self.java_version_info = " ".join(out.splitlines())

    def get_stats_obj(self):
        now = datetime.now().isoformat()
        results_obj = {
            "date": now,
            "is_inductive" : self.is_inductive,
            "inv_size": len(self.strengthening_conjuncts) + 1,
            "invcheck_duration_secs": self.invcheck_duration_secs,
            "ctielimcheck_duration_secs": self.ctielimcheck_duration_secs,
            "state_cache_duration_secs": self.state_cache_duration_secs,
            "ctigen_duration_secs": self.ctigen_duration_secs,
            "total_duration_secs": self.total_duration_secs,
            "total_num_ctis_eliminated": self.get_total_num_ctis_eliminated(),
            "total_num_cti_elimination_rounds": self.get_total_num_cti_elimination_rounds(),
            "total_num_invs_generated": self.get_total_num_invs_generated(),
            "total_num_invs_checked": self.get_total_num_invs_checked(),
            "num_invs": self.num_invs,
            "num_iters": self.num_iters,
            "num_round": self.num_rounds,
            "num_simulate_traces": self.num_simulate_traces,
            "opt_quant_minimize": self.opt_quant_minimize,
            "tlc_workers": self.tlc_workers,
            "seed": self.seed,
            "os": os.name,
            "system": platform.system(),
            "java_exe": self.java_exe,
            "java_version_info": self.java_version_info,
            "processor": platform.processor(),
            "cpu_count": os.cpu_count(),
        }
        return results_obj        

    def get_results_dir(self):
        """ Return the directory to house all results."""
        return os.path.join(self.specdir, self.results_dirname)

    def get_spec_results_dir(self):
        """ Return the directory to house all results for this spec."""
        return os.path.join(self.get_results_dir(), self.specname)

    def save_stats(self):
        """ Save statistics about the invariant generation run. """
        # Create directory for results of this spec if needed.
        os.system(f"mkdir -p {self.get_spec_results_dir()}")

        # Include random seed in result filename.
        results_obj = self.get_stats_obj()
        results_fname = f"{self.get_spec_results_dir()}/{self.specname}_seed-{self.seed}.results.json"
        f = open(results_fname, 'w')
        json.dump(results_obj, f, indent=4)
        f.close()

    def start_timing_state_caching(self):
        self.state_cache_start = time.time()

    def end_timing_state_caching(self):
        dur_secs = time.time() - self.state_cache_start
        self.state_cache_duration_secs += dur_secs

    def start_timing_ctigen(self):
        self.ctigen_start = time.time()

    def end_timing_ctigen(self):
        dur_secs = time.time() - self.ctigen_start
        self.ctigen_duration_secs += dur_secs

    def start_timing_invcheck(self):
        self.invcheck_start = time.time()

    def end_timing_invcheck(self):
        dur_secs = time.time() - self.invcheck_start
        self.invcheck_duration_secs += dur_secs

    def start_timing_ctielimcheck(self):
        self.ctielimcheck_start = time.time()

    def end_timing_ctielimcheck(self):
        dur_secs = time.time() - self.ctielimcheck_start
        self.ctielimcheck_duration_secs += dur_secs

    def get_state_cache_duration(self):
        return self.state_cache_duration_secs

    def get_ctigen_duration(self):
        return self.ctigen_duration_secs
    
    def get_invcheck_duration(self):
        return self.invcheck_duration_secs

    def get_ctielimcheck_duration(self):
        return self.ctielimcheck_duration_secs

    def get_total_duration(self):
        return self.total_duration_secs

    def get_total_num_ctis_eliminated(self):
        return self.total_num_ctis_eliminated
    
    def get_total_num_cti_elimination_rounds(self):
        return self.total_num_cti_elimination_rounds

    def get_total_num_invs_generated(self):
        """ Returns the number of true invariants discovered during inductive invariant inference. """
        return len(self.all_sat_invs)

    def get_total_num_invs_checked(self):
        """ Returns the number of candidate lemma invariants that were checked during inductive invariant inference."""
        return len(self.all_checked_invs)

    def check_predicates(self, preds, tlc_workers=6):
        """ Check which of the given invariants are valid on every reachable state. """
        
        spec_suffix = "PredCheck"

        invcheck_tla = "---- MODULE %s_%s_%d ----\n" % (self.specname,spec_suffix,self.seed)
        invcheck_tla += "EXTENDS %s\n\n" % self.specname
        invcheck_tla += self.model_consts + "\n"

        invval_varname = "predval"

        for i,inv in enumerate(preds):    
            invcheck_tla += f"VARIABLE {invval_varname}_{i}\n"
        
        invcheck_tla += "\n"

        all_inv_names = set()
        for i,inv in enumerate(preds):    
            sinv = ("Pred_%d == " % i) + self.quant_inv(inv)
            all_inv_names.add("Pred_%d" % i)
            invcheck_tla += sinv + "\n"

        invcheck_tla += "InvInit ==\n"
        for i,inv in enumerate(preds):    
            invcheck_tla += f"  /\\ {invval_varname}_{i} = Pred_{i}\n"

        invcheck_tla += "InvNext ==\n"
        for i,inv in enumerate(preds):    
            invcheck_tla += f"  /\\ {invval_varname}_{i}' = Pred_{i}'\n"

        invcheck_tla += "\n"

        invcheck_tla += "PredInit == Init /\ InvInit\n"
        invcheck_tla += "PredNext == Next /\ InvNext\n"

        # invcheck_tla += "PredInit == Init\n"
        # invcheck_tla += "PredNext == Next\n"

        invcheck_tla += "===="

        invcheck_spec_name = f"{GEN_TLA_DIR}/{self.specname}_{spec_suffix}_{self.seed}"
        invcheck_spec_filename = f"{os.path.join(self.specdir, GEN_TLA_DIR)}/{self.specname}_{spec_suffix}_{self.seed}"
        invchecktlafile = invcheck_spec_filename + ".tla"
        f = open(invchecktlafile, 'w')
        f.write(invcheck_tla)
        f.close()

        invcheck_cfg = "INIT PredInit\n"
        invcheck_cfg += "NEXT PredNext\n"
        invcheck_cfg += self.get_tlc_config_constants_str()
        invcheck_cfg += self.get_tlc_overrides_str()
        invcheck_cfg += "\n"
        invcheck_cfg += f"CONSTRAINT {self.state_constraint}"
        invcheck_cfg += "\n"
        if self.symmetry:
            invcheck_cfg += "SYMMETRY Symmetry\n"

        # for invi in range(len(preds)):
        #     sinv = "INVARIANT Inv" + str(invi) 
        #     invcheck_cfg += sinv + "\n"

        invcheck_cfg_file = f"{os.path.join(self.specdir, GEN_TLA_DIR)}/{self.specname}_{spec_suffix}_{self.seed}.cfg"
        invcheck_cfg_filename = f"{GEN_TLA_DIR}/{self.specname}_{spec_suffix}_{self.seed}.cfg"

        f = open(invcheck_cfg_file, 'w')
        f.write(invcheck_cfg)
        f.close()

        dirpath = tempfile.mkdtemp()

        # args = (dirpath, TLC_MAX_SET_SIZE, simulate_flag, self.simulate_depth, ctiseed, tag, num_ctigen_tlc_workers, indcheckcfgfilename, indchecktlafilename)
        state_dump_file = os.path.join(GEN_TLA_DIR, 'predcheckstates')
        args = [
            self.java_exe,
            "-Xss16M",
            f'-Djava.io.tmpdir="{dirpath}"',
            "-cp tla2tools-checkall.jar tlc2.TLC",
            f"-maxSetSize {mc.TLC_MAX_SET_SIZE}",
            f"-seed {self.seed}",
            f"-noGenerateSpecTE -metadir states/predcheck_{self.seed}",
            "-continue -deadlock -workers 4",
            f"-config {invcheck_cfg_filename}",
            f"-dump json {state_dump_file}.json",
            f"{invcheck_spec_name}.tla"

        ]
        cmd = " ".join(args)
        # cmd = self.java_exe + ' -Djava.io.tmpdir="%s" -cp tla2tools-checkall.jar tlc2.TLC -maxSetSize %d %s -depth %d -seed %d -noGenerateSpecTE -metadir states/indcheckrandom_%d -continue -deadlock -workers %d -config %s %s' % args
        logging.debug("TLC command: " + cmd)
        workdir = None
        if self.specdir != "":
            workdir = self.specdir
        subproc = subprocess.Popen(cmd, shell=True, stdout=subprocess.PIPE, cwd=workdir)

        tlc_out = subproc.stdout.read().decode(sys.stdout.encoding)
        # logging.debug(tlc_out)

        dumppath = os.path.join(self.specdir, state_dump_file) + ".json"
        print(dumppath)

        fdump = open(dumppath)
        dumpstates = json.load(fdump)
        pred_vals = {}
        # Extract the valuation of each predicate on each reachable state.
        for s in dumpstates["states"]:
            # print(s)
            state_pred_vals = {}
            # print(s)
            # print(s["val"].keys())
            for k in s["val"]:
                if invval_varname in k:
                    state_pred_vals[int(k.split("_")[1])] = s["val"][k]
            # print(state_pred_vals)
            pred_vals[s["fp"]] = state_pred_vals
        # print(pred_vals)
        for fp in pred_vals:
            print(fp, pred_vals[fp])
        
        print("Size of pred vals:", sys.getsizeof(pred_vals)/1000, "KB")
        return pred_vals


        # predlines = fdump.read().splitlines()
        # fdump.close()
        # predlines = filter(lambda l : "State " in l or "invval_" in l, predlines)
        # for l in predlines:
        #     print(l)

        # # Check invariants.
        # logging.info("Checking %d candidate invariants in spec file '%s'" % (len(invs), invcheck_spec_name))
        # workdir = None if self.specdir == "" else self.specdir
        # violated_invs = runtlc_check_violated_invariants(invcheck_spec_name, config=invcheck_cfg_filename, tlc_workers=self.tlc_workers, cwd=workdir,java=self.java_exe)
        # sat_invs = (all_inv_names - violated_invs)
        # logging.info(f"Found {len(sat_invs)} / {len(invs)} candidate invariants satisfied.")

        # return sat_invs 

    # def check_invariants_fast_pred(self, predinvs, tlc_workers=6):
    #     logging.info("Using fast predicate evaluation.")

    #     pred_symbols = {}
        
    #     allpredids = list(self.pred_vals.items())[0][1].keys()
    #     print(allpredids)

    #     for (predid,predval) in self.pred_vals[list(self.pred_vals.keys())[0]].items():
    #         pred_symbols[predid] = sympy.symbols("x_"+str(predid).zfill(3))

    #     pred_lambdas = {}
    #     for p in predinvs:
    #         pstr = str(p).replace("~", "not ").replace("|", " or ")
    #         # print(pstr)
    #         args = ["x_" + str(a).zfill(3) for a in sorted(list(allpredids))]
    #         fstr = f"lambda {','.join(args)} : {pstr}"
    #         # print(fstr)
    #         f = eval(fstr)
    #         pred_lambdas[p] = f
    #         # print(f())

    #     sat_invs = {p:True for p in predinvs}
    #     s1 = time.time()
    #     is_inv = True
    #     num_invs_failed = 0
    #     for ind,fp in enumerate(self.pred_vals.keys()):
    #         # print(ind)
    #         state_pred_assignment = {}
    #         # print(self.pred_vals[fp])
    #         for (predid,predval) in self.pred_vals[fp].items():
    #             predvarname = "x_"+str(predid).zfill(3)
    #             # state_pred_assignment[pred_symbols[predid]] = predval
    #             state_pred_assignment[predvarname] = predval
    #         # print("state pred assignment:", state_pred_assignment)
    #         # print(f"checking {len(predinvs)} candidates")
    #         args = [state_pred_assignment[assg] for assg in sorted(list(state_pred_assignment.keys()))]

    #         for predinv in predinvs:
    #             # print(predinv)
    #             # Only need to check predicates that have not yet been falsified.
    #             if sat_invs[predinv]:
    #                 # res = eval("True | False | (not True)")
    #                 # f = lambda : True | False | (not True)
    #                 # res = f()
    #                 # print(args)
    #                 # res = True
    #                 res = pred_lambdas[predinv](*args)
    #                 # res = predinv.xreplace(state_pred_assignment)
    #                 # print(res)
    #                 if not res:
    #                     sat_invs[predinv] = False
    #                     num_invs_failed += 1
    #             # print(res)
    #         print(f"done checking {len(predinvs)} candidates, {len(predinvs)-num_invs_failed} remaining sat invs.")

    #         # res = invfn(pred_vals[fp])
    #         # if not res:
    #         #     is_inv = False
    #         #     break
    #     s2 = time.time()
    #     print("time to check invs (fast preds):", (s2-s1), "s")
    #     print("number of sat invs (fast preds):", len(sat_invs))
    #     # print("inv1:", self.preds[1])
    #     # print("inv7:", self.preds[7])
    #     # print("inv1 \/ ~inv7 invariant?", is_inv)
    #     sat_invs_set = set()
    #     for k in sat_invs:
    #         if sat_invs[k]:
    #             sat_invs_set.add(k)

    #     return sat_invs_set

    #     for predinv in predinvs:
    #         print(predinv)

    #     return set()

    def make_check_invariants_spec(self, invs, root_filepath, exclude_inv_defs=False, invname_prefix="Inv", defs_to_add=[]):
        specname = os.path.basename(root_filepath)
        invcheck_tla = f"---- MODULE {specname} ----\n"
        suffix = ""
        if self.tlc_specific_spec and not self.use_apalache_ctigen:
            suffix = "_TLC"
        invcheck_tla += "EXTENDS %s%s\n\n" % (self.specname, suffix)
        invcheck_tla += self.model_consts + "\n"

        all_inv_names = set()
        if not exclude_inv_defs:
            for i,inv in enumerate(invs):    
                sinv = (f"{invname_prefix}{i} == ") + self.quant_inv(inv)
                all_inv_names.add(f"{invname_prefix}{i}")
                invcheck_tla += sinv + "\n"

        for d in defs_to_add:
            invcheck_tla += f"{d[0]} == {d[1]}\n"

        invcheck_tla += "===="

        invcheck_spec_name = f"{GEN_TLA_DIR}/{self.specname}_InvCheck_{self.seed}"
        # invcheck_spec_filename = f"{os.path.join(self.specdir, GEN_TLA_DIR)}/{self.specname}_InvCheck_{self.seed}"
        # invcheck_spec_filename = f""
        invchecktlafile = root_filepath + ".tla"
        f = open(invchecktlafile, 'w')
        f.write(invcheck_tla)
        f.close()

        invcheck_cfg = "INIT Init\n"
        invcheck_cfg += "NEXT Next\n"
        invcheck_cfg += self.get_tlc_config_constants_str()
        invcheck_cfg += self.get_tlc_overrides_str()
        invcheck_cfg += "\n"
        invcheck_cfg += f"CONSTRAINT {self.state_constraint}"
        invcheck_cfg += "\n"
        if self.symmetry:
            invcheck_cfg += "SYMMETRY Symmetry\n"

        if not exclude_inv_defs:
            for invi in range(len(invs)):
                sinv = f"INVARIANT {invname_prefix}" + str(invi) 
                invcheck_cfg += sinv + "\n"

        invcheck_cfg_file = root_filepath + ".cfg"
        # invcheck_cfg_filename = f"{GEN_TLA_DIR}/{self.specname}_InvCheck_{self.seed}.cfg"
        invcheck_cfg_filename = root_filepath + ".cfg"

        f = open(invcheck_cfg_file, 'w')
        f.write(invcheck_cfg)
        f.close()

    def check_invariants(self, invs, tlc_workers=6, max_depth=2**30, 
                         skip_checking=False, cache_with_ignored=None, cache_state_load=False,
                         invcheck_file_path=None, tlc_flags=""):
        """ Check which of the given invariants are valid. """
        ta = time.time()
        # invcheck_tla = "---- MODULE %s_InvCheck_%d ----\n" % (self.specname,self.seed)
        # invcheck_tla += "EXTENDS %s\n\n" % self.specname
        # invcheck_tla += self.model_consts + "\n"

        all_inv_names = set()
        if not skip_checking:
            for i,inv in enumerate(invs):    
                all_inv_names.add("Inv%d" % i)

        rootpath = f"{os.path.join(self.specdir, GEN_TLA_DIR)}/{self.specname}_InvCheck_{self.seed}"
        invcheck_spec_name = f"{GEN_TLA_DIR}/{self.specname}_InvCheck_{self.seed}"
        invcheck_cfg_filename = f"{GEN_TLA_DIR}/{self.specname}_InvCheck_{self.seed}.cfg"

        self.make_check_invariants_spec(invs, rootpath, exclude_inv_defs=skip_checking)

        # Check invariants.
        if not skip_checking:
            logging.info("Checking %d candidate invariants in spec file '%s'" % (len(invs), invcheck_spec_name))

        workdir = None if self.specdir == "" else self.specdir

        violated_invs = mc.runtlc_check_violated_invariants(
                                invcheck_spec_name, 
                                config=invcheck_cfg_filename, 
                                tlc_workers=tlc_workers, 
                                cwd=workdir,
                                java=self.java_exe,
                                tlcjar = TLC_JAR,
                                max_depth=max_depth,
                                cache_with_ignored=cache_with_ignored,
                                cache_state_load = cache_state_load, tlc_flags=tlc_flags)
        sat_invs = set()
        if not skip_checking:
            sat_invs = (all_inv_names - violated_invs)
            logging.info(f"Found {len(sat_invs)} / {len(invs)} candidate invariants satisfied in {round(time.time()-ta,2)}s.")
        if cache_with_ignored:
            logging.info(f"Finished state caching run in {round(time.time()-ta,2)}s.")

        return sat_invs  

    """ 
    Sample CTI error trace:
    
    Error: Invariant InvStrengthened is violated.
    Error: The behavior up to this point is:
    State 1: <Initial predicate>
    /\ semaphore = (s1 :> TRUE @@ s2 :> TRUE)
    /\ clientlocks = (c1 :> {} @@ c2 :> {s1, s2})
    
    State 2: <Connect line 26, col 5 to line 29, col 51 of module lockserver>
    /\ semaphore = (s1 :> FALSE @@ s2 :> TRUE)
    /\ clientlocks = (c1 :> {s1} @@ c2 :> {s1, s2})
    
    State 3: <Connect line 26, col 5 to line 29, col 51 of module lockserver>
    /\ semaphore = (s1 :> FALSE @@ s2 :> FALSE)
    /\ clientlocks = (c1 :> {s1, s2} @@ c2 :> {s1, s2})
    
    Error: Invariant InvStrengthened is violated.
    Error: The behavior up to this point is:
    State 1: <Initial predicate>
    /\ semaphore = (s1 :> TRUE @@ s2 :> TRUE)
    /\ clientlocks = (c1 :> {s2} @@ c2 :> {s1})
    
    State 2: <Connect line 26, col 5 to line 29, col 51 of module lockserver>
    /\ semaphore = (s1 :> FALSE @@ s2 :> TRUE)
    /\ clientlocks = (c1 :> {s1, s2} @@ c2 :> {s1})
    """
    def parse_cti_trace(self, lines, curr_line, inv_name):
        # Step to the 'State x' line
        # curr_line += 1
        # res = re.match(".*State (.*)\: <(.*) .*>",lines[curr_line])
        # statek = int(res.group(1))
        # action_name = res.group(2)
        # print(res)
        # print(statek, action_name)

        # Error: Invariant Safety_Constraint is violated.
        # Error: The behavior up to this point is:
        # State 1: <Initial predicate>

        # print("Parsing CTI trace. Start line: " , lines[curr_line])
        # print(curr_line, len(lines))

        trace_states = []
        trace_ctis = []
        trace_action_names = []

        while curr_line < len(lines):
            # print(lines[curr_line])

            if re.search('Model checking completed', lines[curr_line]):
                break

            # if re.search('Error: The behavior up to this point is', lines[curr_line]):
            #     # print("--")
            #     break

            if re.search('Error: Invariant.*is violated', lines[curr_line]):
                break
                # print(inv_name)

            # Check for next "State N" line.
            if re.search("^State (.*)", lines[curr_line]):

                # res = re.match(".*State ([0-9]*)\: <([A-Za-z0-9_-]*)[(]{0,1}([A-Za-z0-9_-]*)[)]{0,1} .*>",lines[curr_line])

                # State 2: <BecomeLeader(n1,{n1, n3}) line 149, col 5 to line 157, col 35 of module AbstractStaticRaft>
                res = re.match(".*State ([0-9]*)\: <(.*)>",lines[curr_line])
                statek = int(res.group(1))
                action_name = res.group(2).split(" ")[0]
                trace_action_names.append(action_name)
                # TODO: Consider utilizing the action for help in inferring strengthening conjuncts.
                # print(res)
                # print(statek, action_name)

                # curr_line += 1
                # print(curr_line, len(lines), lines[curr_line])
                curr_cti = ""
                curr_cti_lines = []

                # Step forward until you hit the first empty line, and add
                # each line you see as you go as a new state.
                while not lines[curr_line]=='':
                    curr_line += 1
                    # print("curr line", lines[curr_line])
                    if len(lines[curr_line]):
                        curr_cti += (" " + lines[curr_line])

                # Save individual CTI variable lines.
                ctivars = list(filter(len, curr_cti.strip().split("/\\ ")))
                # print("varsplit:", ctivars)
                for ctivar in ctivars:
                    curr_cti_lines.append("/\\ " + ctivar)

                # Assign the action names below.
                cti = CTI(curr_cti.strip(), curr_cti_lines, None)
                trace_ctis.append(cti)

                # TODO: Can eventually merge 'State' and CTI' abstractions.
                state = State(curr_cti.strip(), curr_cti_lines)
                trace_states.append(state)

                # trace_ctis.append(curr_cti.strip())
            curr_line += 1

        # The trace associated with this CTI set.
        trace = Trace(trace_states)

        # Assign action names to each CTI.
        # print(trace_action_names)
        for k,cti in enumerate(trace_ctis[:-1]):
            # The action associated with a CTI is given in the state 1 
            # step ahead of it in the trace.
            action_name = trace_action_names[k+1]
            cti.setActionName(action_name)
            cti.setInvName(inv_name)
            cti.setTrace(trace)
            cti.trace_index = k
        
        # for cti in trace_ctis:
            # print(cti.getActionName())

        # The last state is a bad state, not a CTI.
        trace_ctis = trace_ctis[:-1]
        return (curr_line, set(trace_ctis), trace)

    def parse_ctis(self, lines):
        all_ctis = set()
        all_cti_traces = []

        curr_line = 0

        # Step forward to the first CTI error trace.
        # while not re.search('Error: The behavior up to this point is', lines[curr_line]):
        while not re.search('Error.*Invariant.*is violated.', lines[curr_line]):
            curr_line += 1
            if curr_line >= len(lines):
                break

        if curr_line >= len(lines):
            return (all_ctis, all_cti_traces)  

        res = re.match("Error: Invariant (.*) is violated",lines[curr_line])
        inv_name = res.group(1).replace("_Constraint", "")


        curr_line += 1
        while curr_line < len(lines):
            (curr_line, trace_ctis, trace) = self.parse_cti_trace(lines, curr_line, inv_name)
            all_ctis = all_ctis.union(trace_ctis)
            all_cti_traces.append(trace)

            if curr_line >= len(lines):
                break

            while not re.search('Error.*Invariant.*is violated.', lines[curr_line]):
                curr_line += 1
                if curr_line >= len(lines):
                    break

            # Parse invariant name of next CTI trace.
            res = re.match("Error: Invariant (.*) is violated",lines[curr_line])
            inv_name = res.group(1).replace("_Constraint", "")
            curr_line += 1
        
        # for cti in all_ctis:
        #     print("cti")
        #     print(cti)
        # print("Trace")
        # print(all_cti_traces[0].getStates())
        return (all_ctis, all_cti_traces)

    def itf_json_val_to_tla_val(self, itfval):
        if type(itfval) == int:
            return str(itfval)
        if type(itfval) == str:
            return itfval.replace("ModelValue_", "")
        if "#map" in itfval:
            return "<<" + ",".join(sorted([self.itf_json_val_to_tla_val(v) for v in itfval["#map"]])) + ">>"
        if "#set" in itfval:
            return "{" + ",".join(sorted([self.itf_json_val_to_tla_val(v) for v in itfval["#set"]])) + "}"
        if "#tup" in itfval:
            return "<<" + ",".join([self.itf_json_val_to_tla_val(v) for v in itfval["#tup"]]) + ">>"
        return str(itfval)

    def itf_json_state_to_tla(self, svars, state):
        tla_state_form = ""
        for svar in svars:
            # print(state[svar])
            svar_line = f"/\\ {svar} = {self.itf_json_val_to_tla_val(state[svar])} "
            tla_state_form += svar_line
            # print(svar_line)
        # print(state)
        # print(tla_state_form)

        return tla_state_form

    # def generate_ctis_apalache_run_async(self, n):
    #     # JVM_ARGS="-Xss16M" ~/Desktop/scratch/apalache-v0.19.3/bin/apalache-mc check --max-error=20 --init=Safety --inv=Safety --length=1 learning_switch.tla

    #     # args = (dirpath, TLC_MAX_SET_SIZE, simulate_flag, self.simulate_depth, ctiseed, tag, num_ctigen_tlc_workers, indcheckcfgfilename, indchecktlafilename)
    #     apalache_bin = "~/Desktop/scratch/apalache-v0.19.3/bin/apalache-mc"
    #     jvm_args="JVM_ARGS='-Xss16M'"
    #     cmd = f"{jvm_args} {apalache_bin} check --run-dir=gen_tla/apalache-cti-out --max-error=20 --init=Safety --inv=Safety --length=1 {specname}.tla"
    #     # cmd = self.java_exe + ' -Djava.io.tmpdir="%s" -cp tla2tools-checkall.jar tlc2.TLC -maxSetSize %d %s -depth %d -seed %d -noGenerateSpecTE -metadir states/indcheckrandom_%d -continue -deadlock -workers %d -config %s %s' % args
    #     logging.info("Apalache command: " + cmd)
    #     workdir = None
    #     if self.specdir != "":
    #         workdir = self.specdir
    #     subproc = subprocess.Popen(cmd, shell=True, stdout=subprocess.PIPE, cwd=workdir)
    #     return subproc

    def generate_ctis_apalache_run_await(self, subproc):
        """ Awaits completion of a CTI generation process, parses its results and returns the parsed CTIs."""
        tlc_out = subproc.stdout.read().decode(sys.stdout.encoding)
        logging.debug(tlc_out)
        # lines = tlc_out.splitlines()

        all_tla_ctis = set()
        all_cti_objs = []
        outfiles = os.listdir("benchmarks/gen_tla/apalache_ctigen")
        for outf in outfiles:
            if "itf.json" in outf:
                # print(outf)
                cti_obj = json.load(open(f"benchmarks/gen_tla/apalache_ctigen/{outf}"))
                print(cti_obj)
                all_cti_objs.append(cti_obj)

        for cti_obj in all_cti_objs:
            state_vars = cti_obj["vars"]
            print("state vars:", state_vars)
            tla_cti_str = self.itf_json_state_to_tla(state_vars, cti_obj["states"][0])
            print(tla_cti_str)
            print("---")
            tla_cti = CTI(tla_cti_str.strip(), [], None)
            all_tla_ctis.add(tla_cti)

        # parsed_ctis = self.parse_ctis(lines)     
        # return parsed_ctis 
        return all_tla_ctis    

    def generate_ctis_tlc_run_async(self, num_traces_per_worker, 
                                        props=None, depth=None, view=None, 
                                        action=None, typeok=None, constants_obj=None, 
                                        sampling_target_num_init_states=15000,
                                        sampling_target_time_limit_ms=8000):
        """ Starts a single instance of TLC to generate CTIs.
        
        Will generate CTIs for the conjunction of all predicates given in 'props'.
        """

        if props == None:
            props = [("Safety",self.safety,self.safety)] + self.strengthening_conjuncts

        # Avoid TLC directory naming conflicts.
        # Use small UUID.
        tag = uuid.uuid4().hex[:8]
        ctiseed = random.randint(0,10000)

        # Generate spec for generating CTIs.
        invcheck_tla_indcheck=f"---- MODULE {self.specname}_CTIGen_{ctiseed} ----\n"
        suffix = ""
        if self.tlc_specific_spec and not self.use_apalache_ctigen:
            suffix = "_TLC"
        invcheck_tla_indcheck += f"EXTENDS {self.specname}{suffix}\n\n"

        # We shouldn't need model constants for CTI generation.
        # invcheck_tla_indcheck += self.model_consts + "\n"

        # Add definitions for for all strengthening conjuncts and for the current invariant.
        for cinvname,cinvexp,_ in props:
            invcheck_tla_indcheck += ("%s == %s\n" % (cinvname, cinvexp))


        # if props is not None:
        #     for s in self.strengthening_conjuncts:
        #         invcheck_tla_indcheck += (f"S_{s[0]} == {s[1]}\n")


        # Create formula string which is conjunction of all strengthening conjuncts.
        strengthening_conjuncts_str = ""
        for cinvname,cinvexp,_ in props:
            strengthening_conjuncts_str += "    /\\ %s\n" % cinvname

        # Add definition of current inductive invariant candidate.
        invcheck_tla_indcheck += "InvStrengthened ==\n"
        # invcheck_tla_indcheck += "    /\\ %s\n" % self.safety
        invcheck_tla_indcheck += strengthening_conjuncts_str
        invcheck_tla_indcheck += "\n"

        # Add state constraint as an explicit precondition if needed in order to avoid 
        # invariant violations that would violate the constraint, due to TLC default
        # behavior: https://groups.google.com/g/tlaplus/c/nfd1H-tZbe8/m/eCV3DNKZOicJ.
        precond = self.state_constraint if len(self.state_constraint) else "TRUE"
        # invcheck_tla_indcheck += f'InvStrengthened_Constraint == {precond} => InvStrengthened \n'
        
        # Use for k-induction?
        # self.k_cti_induction_depth = 2
        invcheck_tla_indcheck += f'InvStrengthened_Constraint == {precond} /\ TLCGet("level") = {self.k_cti_induction_depth} => InvStrengthened \n'
        for cinvname,cinvexp,_ in props:
            invcheck_tla_indcheck += f'{cinvname}_Constraint == {precond} /\ TLCGet("level") = {self.k_cti_induction_depth} => {cinvexp} \n'


        invcheck_tla_indcheck += "IndCand ==\n"
        typeok_expr = self.typeok
        # Optionally overrride default TypeOK setting.
        if typeok is not None:
            typeok_expr = typeok

        if self.use_apalache_ctigen:
            typeok_expr = "ApaTypeOK" # use dedicated Apalache TypeOK.
        invcheck_tla_indcheck += "    /\\ %s\n" % typeok_expr
        invcheck_tla_indcheck += f"    /\ InvStrengthened\n"

        depth_bound = 2
        level_bound_precond = f'TLCGet("level") < {self.k_cti_induction_depth}'
        if self.use_apalache_ctigen:
            level_bound_precond = "TRUE"
        invcheck_tla_indcheck += f'NextBounded ==  {level_bound_precond} /\ Next\n'

        # Add VIEW expression if needed.
        view_expr_name = "CTIView"
        if view is not None:
            invcheck_tla_indcheck += "\n"
            invcheck_tla_indcheck += f"{view_expr_name} == {view}\n"

        invcheck_tla_indcheck += "===="

        indchecktlafile = f"{os.path.join(self.specdir, GEN_TLA_DIR)}/{self.specname}_CTIGen_{ctiseed}.tla"
        indchecktlafilename = f"{GEN_TLA_DIR}/{self.specname}_CTIGen_{ctiseed}.tla"
        f = open(indchecktlafile,'w')
        f.write(invcheck_tla_indcheck)
        f.close()

        # Generate config file for checking inductiveness.
        os.system(f"mkdir -p {os.path.join(self.specdir, GEN_TLA_DIR)}")
        
        indcheckcfg_name = f"{self.specname}_CTIGen_{ctiseed}"

        def indcheckcfgfile(tag=None):
            tag_str = "_" + tag if tag is not  None else ""
            return os.path.join(self.specdir, f"{GEN_TLA_DIR}/{indcheckcfg_name}{tag_str}.cfg")
        
        def indcheckcfgfilename(tag=None):
            tag_str = "_" + tag if tag is not  None else ""
            return f"{GEN_TLA_DIR}/{indcheckcfg_name}{tag_str}.cfg"

        invcheck_tla_indcheck_cfg = "INIT IndCand\n"
        if action is None:
            invcheck_tla_indcheck_cfg += "NEXT Next\n"
        # Optionally generate CTIs on a per action basis.
        else:
            invcheck_tla_indcheck_cfg += f"NEXT {action}\n"

        if constants_obj is None:
            constants_obj = self.constants

        invcheck_tla_indcheck_cfg += f"CONSTRAINT {self.state_constraint}\n"
        if view is not None:
            invcheck_tla_indcheck_cfg += f"VIEW {view_expr_name}\n"
        invcheck_tla_indcheck_cfg += "\n"
        # Only check the invariant itself for now, and not TypeOK, since TypeOK
        # might be probabilistic, which doesn't seem to work correctly when checking 
        # invariance.
        # invcheck_tla_indcheck_cfg += "INVARIANT InvStrengthened\n"
        # invcheck_tla_indcheck_cfg += "INVARIANT InvStrengthened_Constraint\n"

        # Check each taret invariant separately.
        for cinvname,cinvexp,_ in props:
            invcheck_tla_indcheck_cfg += f"INVARIANT {cinvname}_Constraint\n"
            # invcheck_tla_indcheck += f'{cinvname}_Constraint == {precond} /\ TLCGet("level") = {self.k_cti_induction_depth} => {cinvexp} \n'

        # invcheck_tla_indcheck_cfg += "INVARIANT OnePrimaryPerTerm\n"
        invcheck_tla_indcheck_cfg += self.constants_obj_to_constants_str(constants_obj)
        invcheck_tla_indcheck_cfg += self.get_tlc_overrides_str()
        invcheck_tla_indcheck_cfg += "\n"
        # TODO: See if we really want to allow symmetry here or not.
        # if symmetry:
        #     invcheck_tla_indcheck_cfg += "SYMMETRY Symmetry\n"

        f = open(indcheckcfgfile(action),'w')
        f.write(invcheck_tla_indcheck_cfg)
        f.close()

        # Use a single worker here, since we prefer to parallelize at the TLC
        # process level for probabilistic CTI generation.
        num_ctigen_tlc_workers = 1

        # Limit simulate depth for now just to avoid very long traces.
        simulate_flag = ""
        if self.simulate:
            # traces_per_worker = self.num_simulate_traces // num_ctigen_tlc_workers
            traces_per_worker = num_traces_per_worker
            simulate_flag = "-simulate num=%d" % traces_per_worker

        logging.debug(f"Using fixed TLC process '-workers={num_ctigen_tlc_workers}' count to ensure reproducible CTI generation.")
        dirpath = tempfile.mkdtemp()

        # Apalache run.
        if self.use_apalache_ctigen:
            # Clean the output directory.
            os.system("rm -rf benchmarks/gen_tla/apalache-cti-out")

            apalache_bin = "apalache/bin/apalache-mc"
            rundir = "gen_tla/apalache_ctigen"
            outdir = "gen_tla/apalache_ctigen"
            jvm_args="JVM_ARGS='-Xss16M'"
            max_num_ctis = 250
            inv_to_check = "InvStrengthened_Constraint"
            cmd = f"{apalache_bin} check --out-dir={outdir} --max-error={max_num_ctis} --view=vars --run-dir={rundir} --cinit=CInit --init=IndCand --next=Next --inv={inv_to_check} --length=1 {indchecktlafilename}"
            # cmd = f"{apalache_bin} check --out-dir={outdir} --run-dir={rundir} --cinit=CInit --init=IndCand --next=Next --inv={inv_to_check} --length=1 {indchecktlafilename}"
            logging.debug("Apalache command: " + cmd)
            workdir = None
            if self.specdir != "":
                workdir = self.specdir
            subproc = subprocess.Popen(cmd, shell=True, stdout=subprocess.PIPE, cwd=workdir)
            return subproc

        simulate_depth = self.simulate_depth
        if depth is not None:
            simulate_depth = depth
        if self.k_cti_induction_depth > 1:
            simulate_depth = self.k_cti_induction_depth
        
        sampling_args = f"-Dtlc2.tool.impl.Tool.autoInitStatesSampling=true -Dtlc2.tool.impl.Tool.autoInitSamplingTimeLimitMS={sampling_target_time_limit_ms} -Dtlc2.tool.impl.Tool.autoInitSamplingTargetNumInitStates={sampling_target_num_init_states}"
        args = (dirpath, sampling_args, "tla2tools-checkall.jar", mc.TLC_MAX_SET_SIZE, simulate_flag, simulate_depth, ctiseed, tag, num_ctigen_tlc_workers, indcheckcfgfilename(action), indchecktlafilename)
        cmd = self.java_exe + ' -Xss16M -Djava.io.tmpdir="%s" %s -cp %s tlc2.TLC -maxSetSize %d %s -depth %d -seed %d -noGenerateSpecTE -metadir states/indcheckrandom_%s -continue -deadlock -workers %d -config %s %s' % args
        logging.debug("TLC command: " + cmd)
        workdir = None
        if self.specdir != "":
            workdir = self.specdir
        subproc = subprocess.Popen(cmd, shell=True, stdout=subprocess.PIPE, cwd=workdir)
        return subproc

    def generate_ctis_tlc_run_await(self, subproc):
        """ Awaits completion of a CTI generation process, parses its results and returns the parsed CTIs."""
        tlc_out = subproc.stdout.read().decode(sys.stdout.encoding)
        # logging.debug(tlc_out)
        lines = tlc_out.splitlines()
        if "Error: parsing" in tlc_out:
            logging.error("Error in TLC execution, printing TLC output.")
            for line in lines:  
                logging.info("[TLC output] " + line)

        # Check for error:
        # 'Error: Too many possible next states for the last state in the trace'
        if "Error: Too many possible next states" in tlc_out:
            logging.error("Error in TLC execution, printing TLC output.")
            for line in lines:  
                logging.info("[TLC output] " + line)      
            return set()
        
        # Check for bad exit code.
        retcode = subproc.wait()
        if retcode == 151:
            logging.error(f"!!!!!!!! TLC exited with abnormal exit code: {retcode}. May indicate underlying error. !!!!!!!!")
            logging.error("Logging last 25 lines of TLC output:")
            logging.error("------")
            for last in lines[-25:]:
                logging.error(last)
            logging.error("------")
            raise Exception(f"TLC exited with non-zero exit code: {retcode}.")

        (parsed_ctis, parsed_cti_traces) = self.parse_ctis(lines)     
        return (parsed_ctis,parsed_cti_traces)       


    def generate_ctis_tlc_run_await_subprocs(self, subprocs, actions=None, all_ctis=set()):
        for cti_subproc in subprocs:
            if self.use_apalache_ctigen:
                parsed_ctis = self.generate_ctis_apalache_run_await(cti_subproc)
            else:
                if actions is not None:
                    action = cti_subproc["action"]
                    logging.info(f"Waiting for CTI generation process termination (action={action})")
                    (parsed_ctis, parsed_cti_traces) = self.generate_ctis_tlc_run_await(cti_subproc["proc"]) 
                    if action in all_ctis:
                        all_ctis[action].update(parsed_ctis)
                    else:
                        all_ctis[action] = parsed_ctis
                else:
                    logging.info(f"Waiting for CTI generation process termination.")
                    (parsed_ctis, parsed_cti_traces) = self.generate_ctis_tlc_run_await(cti_subproc["proc"]) 
                    all_ctis.update(parsed_ctis)

    def generate_ctis(self, props=None, reseed=False, depth=None, view=None, actions=None, typeok_override=None, constants_obj=None):
        """ Generate CTIs for use in counterexample elimination. """

        # Re-set random seed to ensure consistent RNG initial state.
        if reseed:
            random.seed(self.seed)

        all_ctis = set()
        print("props:", props)

        # Run CTI generation multiple times to gain random seed diversity. Each
        # run should call TLC with a different random seed, to generate a different
        # potential set of random initial states. We run each CTI generation process
        # in parallel, using a separate TLC instance.
        self.start_timing_ctigen()
        num_cti_worker_procs = 4

        # Only allow alternate CTI worker count if explicitly overridden from command line.
        if self.override_num_cti_workers:
            num_cti_worker_procs = self.override_num_cti_workers

        if self.use_apalache_ctigen:
            num_cti_worker_procs = 1
        cti_subprocs = []
        num_traces_per_tlc_instance = self.num_simulate_traces // num_cti_worker_procs

        # Break down CTIs by action in this case.
        if actions is not None:
            all_ctis = {}

        # Start the TLC processes for CTI generation.
        logging.info(f"Running {num_cti_worker_procs} parallel CTI generation processes")
        for n in range(num_cti_worker_procs):
            # if self.use_apalache_ctigen:
                # cti_subproc = self.generate_ctis_apalache_run_async(num_traces_per_tlc_instance)
            # else:
            MAX_CONCURRENT_PROCS = 3
            if actions is not None:
                actions_started = 0
                curr_proc_batch = []
                for action in actions:
                    logging.info(f"Starting CTI generation process {n} (of {num_cti_worker_procs} total workers), Action='{action}'")
                    
                    # TODO: Consider iterating over multiple config instances, ideally in order of "smallest" to "largest".
                    # constants_obj = self.get_config_constant_instances()[-1]
                    # for constants_obj in self.get_config_constant_instances()[-1:]:
                    print("CTI generation for config:", constants_obj)
                
                    cti_subproc = self.generate_ctis_tlc_run_async(
                                        num_traces_per_tlc_instance,
                                        props=props, 
                                        depth=depth, 
                                        view=view, 
                                        action=action, 
                                        typeok=typeok_override,
                                        constants_obj=constants_obj)
                    
                    proc_obj = {"action": action, "proc": cti_subproc}
                    cti_subprocs.append(proc_obj)
                    actions_started += 1
                    curr_proc_batch.append(proc_obj)
                    # Limit the number of concurrent procs running.
                    if actions_started % MAX_CONCURRENT_PROCS == 0 or (actions_started == len(actions) and len(curr_proc_batch)):
                        logging.info(f"Launched {actions_started} total CTI procs, awaiting previous to complete.")
                        self.generate_ctis_tlc_run_await_subprocs(curr_proc_batch, actions=actions, all_ctis=all_ctis)
                        curr_proc_batch = []

            else:
                logging.info(f"Starting CTI generation process {n} (of {num_cti_worker_procs} total workers)")
                target_sample_states = self.target_sample_states
                target_sample_time_limit_ms = self.target_sample_time_limit_ms
                cti_subproc = self.generate_ctis_tlc_run_async(
                                    num_traces_per_tlc_instance,
                                    props=props, 
                                    depth=depth, 
                                    view=view, 
                                    typeok=typeok_override,
                                    constants_obj=constants_obj,
                                    sampling_target_num_init_states=target_sample_states // num_cti_worker_procs,
                                    sampling_target_time_limit_ms=target_sample_time_limit_ms)
                
                cti_subprocs.append({"proc": cti_subproc})

        # Await completion and parse results.
        self.generate_ctis_tlc_run_await_subprocs(cti_subprocs, actions=None, all_ctis=all_ctis)

        # print("ALL CTIS")
        # defs = ""
        # init = "Init == \n"
        # for i,c in enumerate(random.sample(all_ctis, 300)):
        #     # print(c.cti_str)
        #     defs += f"C{i} == " + "\n" + c.cti_str + "\n"
        #     init += f"  \/ C{i}\n"

        # print(init)

        # FOR DIAGNOSTICS.
        # for x in sorted(list(all_ctis))[:10]:
            # print(x)

        self.end_timing_ctigen()
        return (all_ctis, [])

    def make_rel_induction_check_spec(self, spec_name, support_lemmas, S, rel_ind_pred_name, goal_inv_name):
        """ 
        Create a spec that allows to check whether a given boolean expression S is inductive relative to to a conjunction of
        given predicates L. Defines a predicate that is the conjunction of predicates in L as 'IndLemmas'.
        """
        
        # Build the spec.
        typeok = "ApaTypeOK" # Use TypeOK for Apalache.
        all_conjuncts = [typeok] + support_lemmas + [S]
        goal_inv_conjs = [S]
        # Include state constraint as a precondition on the invariant,
        # to ensure the constraint is respected in symbolic checking.
        if len(self.state_constraint):
            goal_inv_conjs = [self.state_constraint] + goal_inv_conjs
        spec_lines = [
            "---- MODULE %s ----\n" % spec_name,
            "EXTENDS %s,Naturals,TLC\n" % self.specname,
            f"{rel_ind_pred_name} == ",
            "\n".join(["  /\ " + c for c in all_conjuncts]),
            "",
            f"{goal_inv_name} == " + " => ".join(goal_inv_conjs),
            "===="
        ]
        return "\n".join(spec_lines)

    def make_indquickcheck_tla_spec(self, spec_name, invs, sat_invs_group, orig_k_ctis, quant_inv_fn):
        # print("invs:", invs)
        # print("sat_invs_group:", sat_invs_group)
        
        # invs_sorted = sorted(invs)
        invs_sorted = invs
        
        # Start building the spec.
        # invcheck_tla_indcheck="---- MODULE %s_IndQuickCheck ----\n" % self.specname
        invcheck_tla_indcheck="---- MODULE %s ----\n" % spec_name

        # Extend TLC specific spec if needed for other definitions.
        suffix = ""
        if self.tlc_specific_spec and not self.use_apalache_ctigen:
            suffix = "_TLC"

        invcheck_tla_indcheck += f"EXTENDS {self.specname}{suffix},Naturals,TLC\n\n"

        invcheck_tla_indcheck += self.model_consts + "\n"

        # Create a variable to represent the value of each invariant.
        for inv in sat_invs_group:
            invi = int(inv.replace("Inv",""))
            invname = "Inv%d" % invi
            invcheck_tla_indcheck += "VARIABLE %s_val\n" % invname
        aux_vars = [
            "ctiId", 
            "ctiCost"
        ]
        for v in aux_vars:
            invcheck_tla_indcheck += f"VARIABLE {v}\n"
        invcheck_tla_indcheck += "\n"

        # Add definitions for all invariants and strengthening conjuncts.
        for cinvname,cinvexp,cinvexp_unquant in self.strengthening_conjuncts:
            invcheck_tla_indcheck += ("%s == %s\n" % (cinvname, cinvexp))

        for inv in sat_invs_group:
            invi = int(inv.replace("Inv",""))
            invname = "Inv%d" % invi
            invexp = quant_inv_fn(invs_sorted[invi])
            # print(invname, invexp)
            invcheck_tla_indcheck += ("%s == %s\n" % (invname, invexp))
        invcheck_tla_indcheck += "\n"
        # print("---")

        kCTIprop = "kCTIs"
        invcheck_tla_indcheck += "%s == \n" % kCTIprop
        for cti in orig_k_ctis:
            # cti.getPrimedCTIStateString()
            invcheck_tla_indcheck += "\t\/ " + cti.getCTIStateString() + "\n"

            # Identify the CTI state by the hash of its string representation.
            invcheck_tla_indcheck += "\t   " + "/\\ ctiId = \"%d\"\n" % (hash(cti))
            invcheck_tla_indcheck += "\t   " + "/\\ ctiCost = CTICost\n"
            
            # invcheck_tla_indcheck += "\n"
        invcheck_tla_indcheck += "\n"

        strengthening_conjuncts_str = ""
        for cinvname,cinvexp,cinvexp_unquant in self.strengthening_conjuncts:
            strengthening_conjuncts_str += "    /\\ %s\n" % cinvname

        invcheck_tla_indcheck += "\n"

        # TODO: Handle case of no satisfied invariants more cleanly.
        invcheck_tla_indcheck += "InvVals ==\n"
        invcheck_tla_indcheck += "\t    /\\ TRUE\n"
        for inv in sat_invs_group:
            invcheck_tla_indcheck += "\t   " + "/\\ %s_val = %s\n" % (inv, inv)
        invcheck_tla_indcheck += "\n"

        invcheck_tla_indcheck += "CTICheckInit ==\n"
        invcheck_tla_indcheck += "    /\\ %s\n" % kCTIprop
        invcheck_tla_indcheck += "    /\\ InvVals\n"
        # TODO: I don't think we really should have these strengthening conjuncts here (?)
        # Remove for now.
        # invcheck_tla_indcheck += strengthening_conjuncts_str
        invcheck_tla_indcheck += "\n"

        # Add next-state relation that leaves the auxiliary variables unchanged.
        invcheck_tla_indcheck += "CTICheckNext ==\n"
        invcheck_tla_indcheck += "    /\\ NextUnchanged\n"
        for v in aux_vars:
            invcheck_tla_indcheck += f"    /\\ UNCHANGED {v}\n"
        for inv in sat_invs_group:
            invcheck_tla_indcheck += "    /\\ UNCHANGED %s_val\n" % inv

        # Also add alternate transition relation expression for doing bounded reachablity
        # from all CTI states.
        depth_bound = 3
        invcheck_tla_indcheck += "\n"
        invcheck_tla_indcheck += "CTICheckNext_DepthBoundedReachability ==\n"
        invcheck_tla_indcheck += f'    /\ TLCGet("level") < {depth_bound}\n'
        invcheck_tla_indcheck += f"    /\ Next\n"
        for v in aux_vars:
            invcheck_tla_indcheck += f"    /\\ UNCHANGED {v}\n"
        for inv in sat_invs_group:
            invcheck_tla_indcheck += "    /\\ UNCHANGED %s_val\n" % inv


        invcheck_tla_indcheck += "===="

        return invcheck_tla_indcheck

    def make_ctiquickcheck_cfg(self, invs, sat_invs_group, orig_k_ctis, quant_inv_fn, next_pred="CTICheckNext", constants_obj=None):

        # Generate config file.
        invcheck_tla_indcheck_cfg = "INIT CTICheckInit\n"
        invcheck_tla_indcheck_cfg += f"NEXT {next_pred}\n"
        invcheck_tla_indcheck_cfg += f"CONSTRAINT {self.state_constraint}"
        invcheck_tla_indcheck_cfg += "\n"
        if constants_obj is not None:
            invcheck_tla_indcheck_cfg += self.constants_obj_to_constants_str(constants_obj)
        else:
            invcheck_tla_indcheck_cfg += self.get_tlc_config_constants_str()
        invcheck_tla_indcheck_cfg += self.get_tlc_overrides_str()
        invcheck_tla_indcheck_cfg += "\n"
        
        # for inv in sat_invs_group:
        #     invi = int(inv.replace("Inv",""))
        #     invname = "Inv%d" % invi        
        #     invcheck_tla_indcheck_cfg += ("INVARIANT %s\n" % invname)

        return invcheck_tla_indcheck_cfg

    def pre_generate_invs(self):
        self.start_timing_invcheck()
        # Arguments: <outfile> <nthreads>
        invfile = "pregen.invs"
        cmd = self.pregen_inv_cmd + f" {invfile} {self.tlc_workers}"
        subproc = subprocess.Popen(cmd, shell=True, stdout=subprocess.PIPE)
        ret = subproc.stdout.read().decode(sys.stdout.encoding)
        for line in ret.splitlines():
            logging.info(line)
        invs = set(open(invfile).read().splitlines())
        self.cached_invs = invs
        logging.info(f"Pre-generated and cached {len(self.cached_invs)} total invariants")
        self.end_timing_invcheck()

    def check_cti_elimination(self, orig_ctis, sat_invs, constants_obj=None):
        """ Computes CTI elimination mapping for the given set of CTIs and invariants.
        
        That is, this function computes and returns a mapping from each invariant to the set of CTIs 
        that it eliminates.
        """

        #
        # TODO: Sort out how we handle 'invs' and 'sat_invs' and CTI tables here, etc.
        #

        # logging.info(f"Checking invariant elimination for {len(orig_ctis)} CTIs.")

        # Initialize table mapping from invariants to a set of CTI states they violate.
        cti_states_eliminated_by_invs = {}
        cti_costs = {}

        # Create metadir if necessary.
        os.system("mkdir -p states")

        MAX_INVS_PER_GROUP = 1000
        curr_ind = 0

        quant_inv_fn = self.quant_inv 

        # Run CTI elimination checking in parallel.
        n_tlc_workers = 4
        cti_chunks = list(chunks(list(orig_ctis), n_tlc_workers))

        sat_invs = sat_invs + [("DUMMY_INV", "TRUE")]

        # sat_invs = sorted(sat_invs)
        invs = sorted([x[1] for x in sat_invs])
        sat_invs = ["Inv" + str(i) for i,x in enumerate(sat_invs)]
        # print("invs")
        # print(invs)
        # print("sat_invs")
        # print(sat_invs)

        for inv in sat_invs:
            cti_states_eliminated_by_invs[inv] = set()


        def cti_states_relative_file(ci, curr_ind, tag="", ext=".json"):                
            return f"states/cti_quick_check_chunk{ci}_{curr_ind}{tag}{ext}"

        def cti_states_file(ci, curr_ind, tag=""):
            return os.path.join(self.specdir, cti_states_relative_file(ci, curr_ind, tag=tag))

        # Generate reachability graphs for CTI sets along with other checking.
        generate_reachable_graphs = False
        self.cti_out_degrees = None

        while curr_ind < len(sat_invs):
            sat_invs_group = sat_invs[curr_ind:(curr_ind+MAX_INVS_PER_GROUP)]
            logging.info("Checking invariant group of size %d (starting invariant=%d) for CTI elimination." % (len(sat_invs_group), curr_ind))
            tlc_procs = []
            tlc_procs_reach = []

            # Create the TLA+ specs and configs for checking each chunk.
            for ci,cti_chunk in enumerate(cti_chunks):

                # Build and save the TLA+ spec.
                spec_name = f"{self.specname}_IndQuickCheck_chunk{ci}"
                spec_str = self.make_indquickcheck_tla_spec(spec_name, invs, sat_invs_group, cti_chunk, quant_inv_fn)

                ctiquicktlafile = f"{os.path.join(self.specdir, GEN_TLA_DIR)}/{spec_name}.tla"
                ctiquicktlafilename = f"{GEN_TLA_DIR}/{spec_name}.tla"

                f = open(ctiquicktlafile,'w')
                f.write(spec_str)
                f.close()

                # Generate config file.
                ctiquickcfgfile=f"{os.path.join(self.specdir, GEN_TLA_DIR)}/{self.specname}_CTIQuickCheck_chunk{ci}.cfg"
                ctiquickcfgfilename=f"{GEN_TLA_DIR}/{self.specname}_CTIQuickCheck_chunk{ci}.cfg"
                cfg_str = self.make_ctiquickcheck_cfg(invs, sat_invs_group, cti_chunk, quant_inv_fn, constants_obj=constants_obj)
                
                with open(ctiquickcfgfile,'w') as f:
                    f.write(cfg_str)


                # Generate alternate config file for computing reachability graph from each CTI.
                ctiquickcfgfile_reach=f"{os.path.join(self.specdir, GEN_TLA_DIR)}/{self.specname}_CTIQuickCheck_Reachable_chunk{ci}.cfg"
                ctiquickcfgfilename_reach=f"{GEN_TLA_DIR}/{self.specname}_CTIQuickCheck_Reachable_chunk{ci}.cfg"
                cfg_str = self.make_ctiquickcheck_cfg(invs, sat_invs_group, cti_chunk, quant_inv_fn, next_pred="CTICheckNext_DepthBoundedReachability", constants_obj=constants_obj)
                
                with open(ctiquickcfgfile_reach,'w') as f:
                    f.write(cfg_str)

                # cti_states_file = os.path.join(self.specdir, f"states/cti_quick_check_chunk{ci}_{curr_ind}.json")
                # cti_states_relative_file = f"states/cti_quick_check_chunk{ci}_{curr_ind}.json"
                
                workdir = None if self.specdir == "" else self.specdir

                # Run TLC.
                # Create new tempdir to avoid name clashes with multiple TLC instances running concurrently.
                def run_with_config(cfg_filename, tag=""):
                    dirpath = tempfile.mkdtemp()
                    cmdargs = (dirpath, mc.TLC_MAX_SET_SIZE, cti_states_relative_file(ci, curr_ind, tag=tag), self.specname, ci, curr_ind, tag, cfg_filename, ctiquicktlafilename)
                    cmd = self.java_exe + ' -Xss16M -Djava.io.tmpdir="%s" -cp tla2tools-checkall.jar tlc2.TLC -maxSetSize %d -dump json %s -noGenerateSpecTE -metadir states/ctiquick_%s_chunk%d_%d_%s -continue -checkAllInvariants -deadlock -workers 1 -config %s %s' % cmdargs
                    logging.debug("TLC command: " + cmd)
                    subproc = subprocess.Popen(cmd, shell=True, stdout=subprocess.PIPE, cwd=workdir)
                    return subproc

                subproc = run_with_config(ctiquickcfgfilename)
                tlc_procs.append(subproc)

                if generate_reachable_graphs:
                    subproc_reach = run_with_config(ctiquickcfgfilename_reach, tag="_reach")
                    tlc_procs_reach.append(subproc_reach)
        
            cti_states_reach = {"states": [], "edges": []}

            for ci,subproc in enumerate(tlc_procs):
                logging.info("Waiting for TLC termination " + str(ci))

                subproc.wait()
                ret = subproc.stdout.read().decode(sys.stdout.encoding)

                # logging.info(f"Opening CTI states JSON file: '{cti_states_file}'")
                with open(cti_states_file(ci, curr_ind)) as fcti:
                    text = fcti.read()
                    cti_states = json.loads(text)["states"]
                # print "cti states:",len(cti_states)

                # Record the CTIs eliminated by each invariant.
                for cti_state in cti_states:
                    sval = cti_state["val"]
                    ctiHash = sval["ctiId"]
                    ctiCost = sval["ctiCost"]

                    # print(sval)
                    # if ctiCost == 0:
                    #     print(sval)
                    #     print(ctiCost)

                    cti_costs[ctiHash] = ctiCost

                    # for inv in sat_invs_group:
                    # for inv in inv_chunks[ci]:
                    for inv in sat_invs_group:
                        if not sval[inv + "_val"]:
                            cti_states_eliminated_by_invs[inv].add(ctiHash)

                #
                # Optionally load the states reachable from CTIs as initial states.
                #

                if generate_reachable_graphs:
                    tlc_procs_reach[ci].wait()
                    ret = tlc_procs_reach[ci].stdout.read().decode(sys.stdout.encoding)

                    json_file = cti_states_file(ci, curr_ind, tag="_reach")
                    logging.info(f"Loading bounded depth reachable states from CTIs from JSON file: {json_file}")
                    with open(json_file) as fcti:
                        text = fcti.read()
                        states = json.loads(text)["states"]
                        edges = json.loads(text)["edges"]
                        # print(states)
                        # print(edges)
                        cti_states_reach["states"] += states
                        cti_states_reach["edges"] += edges
                    print(f"Total found states reachable from cti states in bounded depth:", len(cti_states_reach["states"]))
                    print(f"Total found edges reachable from cti states in bounded depth:", len(cti_states_reach["edges"]))


            if generate_reachable_graphs:
                # TODO: Store CTI graph and look for motifs.
                import networkx as nx
                G = nx.DiGraph()
                for e in cti_states_reach["states"]:
                    G.add_node(e["fp"], initial=e["initial"], val=e["val"], ctiId=e["val"]["ctiId"])
                for e in cti_states_reach["edges"]:
                    G.add_edge(e["from"], e["to"])
                print("num nodes:", G.number_of_nodes())

                num_init = 0
                local_neighborhoods = {}
                cti_root_nodes = []
                out_degrees = []
                for n in G.nodes():
                    node = G.nodes[n]
                    # print(node)
                    # CTI states will be marked as initial states in the graph.
                    if node["initial"]:
                        cti_root_nodes.append(n)
                        num_init += 1
                        neighborhood = nx.bfs_tree(G, n, depth_limit=3)
                        # print(f"neighborhood of {n}")
                        # print("nodes:", neighborhood.number_of_nodes())
                        # print("edges:", neighborhood.number_of_edges())
                        # print(f"outdegree: {G.out_degree(n)}")
                        out_degrees.append((n, G.out_degree(n)))
                        local_neighborhoods[n] = neighborhood

                print("Ascending out degrees")
                out_degree_nums = [d[1] for d in out_degrees]
                unique_out_degrees = set(out_degree_nums)
                deg_counts = {n:out_degree_nums.count(n) for n in unique_out_degrees}
                print("Out-degree histogram table:", deg_counts)
                
                self.cti_out_degrees = {str(G.nodes[d[0]]["val"]["ctiId"]):d[1] for d in out_degrees}

                print("Printing some CTIs with smallest out-degree")
                for d in list(sorted(out_degrees, key = lambda x : x[1]))[:7]:
                    print("out degree:", d)
                    outdegree = d[1]
                    if outdegree <= 2:
                        cti = [c for c in orig_ctis if int(G.nodes[d[0]]["val"]["ctiId"]) == hash(c)][0]
                        # print(d)
                        print(cti.action_name)
                        for l in cti.cti_lines:
                            print(l)
                        print("--")

                print("Printing some CTIs with highest out-degree")
                for d in list(sorted(out_degrees, key = lambda x : x[1]))[-4:]:
                    print("out degree:", d)
                    outdegree = d[1]
                    cti = [c for c in orig_ctis if int(G.nodes[d[0]]["val"]["ctiId"]) == hash(c)][0]
                    # print(d)
                    print(cti.action_name)
                    for l in cti.cti_lines:
                        print(l)
                    print("--")

                #
                # TODO: Re-enable isomorphic clustering if desired.
                #

                # logging.info("Checking isomorphism between local neighborhoods")
                # unclustered_nodes = list(local_neighborhoods.keys())
                # clusters = []
                # while len(unclustered_nodes):
                #     # Get next unclustered node.
                #     next_node = unclustered_nodes.pop()
                #     # See if this node is isomorphic to any existing cluster.
                #     iso_to_cluster = None
                #     for i,c in enumerate(clusters):
                #         cluster_member = c[0]
                #         iso = nx.is_isomorphic(local_neighborhoods[next_node], local_neighborhoods[cluster_member])
                #         if iso:
                #             iso_to_cluster = i
                #             break

                #     # If it is not isomorphic to any existing cluster,
                #     # then create a new cluster with this node. Otherwise add
                #     # it to correct cluster.
                #     if iso_to_cluster is not None:
                #         clusters[iso_to_cluster].append(next_node)
                #     else:
                #         clusters.append([next_node])

                    
                # for n in local_neighborhoods:
                #     isomorphic_cousins = []
                #     for other in local_neighborhoods:
                #         iso = nx.is_isomorphic(local_neighborhoods[n], local_neighborhoods[other])
                #         if iso:
                #             # print(f"isomorphic, {n} to {other}:", iso)
                #             isomorphic_cousins.append(other)

                    # print(f"Num isomorphic cousins found for node {n}:", len(isomorphic_cousins))
                
                # Mapping from CTI id to CTI object.
                cti_table = {}
                for c in orig_ctis:
                    cti_table[hash(c)] = c

                # Sort clusters by size.
                # print('num init:', num_init)
                # clusters = sorted(clusters, key=lambda c : len(c), reverse=True)

                # print(f"{len(clusters)} Isomorphic clusters")
                # for i,c in enumerate(clusters):
                #     print(f"cluster of size {len(c)}:", c)
                #     nx.nx_pydot.write_dot(local_neighborhoods[c[0]], f"ctigraphs/cluster_{i}_{len(c)}.dot")

                #     for n in c:
                #         sval = G.nodes[n]["val"]
                #         for k in sval:
                #             print(k, sval[k])
                            


            curr_ind += MAX_INVS_PER_GROUP
        # Return various CTI info.
        # print("CTI costs:", cti_costs)
        # print(cti_states_eliminated_by_invs)
        # print("CTI COSTS:", cti_costs)

        # Remove the last dummy invariant, which is there just to ensure we compute costs for
        # each CTI even if there are no invariants to check elimination for.

        last_inv_ind = (len(sat_invs) - 1)
        del cti_states_eliminated_by_invs["Inv" + str(last_inv_ind)]

        return {
            "eliminated": cti_states_eliminated_by_invs,
            "cost": cti_costs
        }


    def cache_projected_states(self, cache_states_with_ignored_var_sets, max_depth=2**30, tlc_workers=6):
        # Ensure references to variable slice sets are always sorted to maintain consistent order.
        cache_states_with_ignored_var_sets = sorted([tuple(sorted(c)) for c in cache_states_with_ignored_var_sets])

        logging.info(f"Running state caching step with {len(cache_states_with_ignored_var_sets)} ignored var sets: {cache_states_with_ignored_var_sets}")
        dummy_inv = "3 > 2"
        simulation_inv_tlc_flags = ""
        if "simulation_inv_check" in self.spec_config and self.spec_config["simulation_inv_check"]:
            # Get value from dict self.spec_config or use default value.
            depth = self.spec_config.get("simulation_inv_check_depth", 50)
            num_states = self.spec_config.get("simulation_inv_check_num_states", 100000)

            # Compute the number of traces to run for each simulation worker based on the depth
            # and total state count target.
            num = num_states // depth // tlc_workers

            logging.info(f"Running state caching step in simulation with (depth={depth}, num={num},workers={tlc_workers}) for num_states={num_states}")
            simulation_inv_tlc_flags=f"-depth {depth} -simulate num={num}"
        self.start_timing_state_caching()

        # Option to memoize state projection cache computations.
        self.memoize_state_projection_caches = True

        cache_states_with_ignored_var_sets_new = [c for c in cache_states_with_ignored_var_sets if c not in self.state_projection_cache]
        if len(cache_states_with_ignored_var_sets_new) == 0:
            logging.info(f"State projection caches for all {len(cache_states_with_ignored_var_sets)} slices were already computed.")
        else:
        # check which subsets of vars are already in the cache.
        # if tuple(sorted(cache_states_with_ignored_vars)) not in self.state_projection_cache:
            logging.info(f"Computing {len(cache_states_with_ignored_var_sets_new)}/{len(cache_states_with_ignored_var_sets)} slices based on current cache.")
            self.check_invariants([dummy_inv], tlc_workers=tlc_workers, max_depth=max_depth, 
                                            cache_with_ignored=cache_states_with_ignored_var_sets_new, skip_checking=True,
                                            tlc_flags=simulation_inv_tlc_flags)

            if self.memoize_state_projection_caches:
                for c in cache_states_with_ignored_var_sets_new:
                    self.state_projection_cache[c] = True
        # else:
            # logging.info(f"State projection cache for slice {cache_states_with_ignored_vars} was already computed.")
        logging.info(f"state projection cache has {len(self.state_projection_cache)} var slices.")
        # for c in self.state_projection_cache:
            # logging.info([s for s in self.state_vars if s not in c])
        self.end_timing_state_caching()

    def eliminate_ctis(self, orig_k_ctis, num_invs, roundi, subroundi=None, preds=None, preds_alt=[], 
                       quant_inv_alt=None, tlc_workers=6, specdir=None, append_inv_round_id=True,
                       cache_states_with_ignored_vars=None):
        """ Check which of the given satisfied invariants eliminate CTIs. """
        
        if preds is None:
            preds = self.preds

        assert len(orig_k_ctis) > 0 

        # TODO: Can we also project CTIs onto variable slice for faster CTI elimination checking? (3/13/24)
        # orig_k_ctis
        if self.enable_cti_slice_projection:
            logging.info(f"Projecting {len(orig_k_ctis)} CTIs onto variable slice for faster CTI elimination checking.")
            first_cti = orig_k_ctis[0]
            first_cti_vals = first_cti.var_vals()
            print("total CTIs:", len(orig_k_ctis))
            if cache_states_with_ignored_vars is not None:
                for ind,c in enumerate(orig_k_ctis):
                    # print("ignore vars:", cache_states_with_ignored_vars)
                    # print("pre-projected:")
                    # for l in c.cti_lines:
                    #     print(l)
                    for sv in cache_states_with_ignored_vars:
                        orig_k_ctis[ind].set_var_val(sv, first_cti_vals[sv])
                    # print("post-projected:")
                    # for l in c.cti_lines:
                        # print(l)
            print("total projected ctis:", len(set(orig_k_ctis)))
            orig_k_ctis = list(set(orig_k_ctis))

        # Save CTIs, indexed by their hashed value.
        cti_table = {}
        for cti in orig_k_ctis:
            hashed = str(hash(cti))
            cti_table[hashed] = cti

        eliminated_ctis = set()

        # Parameters for invariant generation.
        init_conjs = 1
        min_conjs, max_conjs = (init_conjs, init_conjs)
        process_local = False
        quant_inv_fn = self.quant_inv

        # Keep track of all strengthening conjuncts added in this round.
        conjuncts_added_in_round = []

        iteration = 1
        uniqid = 0

        if cache_states_with_ignored_vars is not None:
            var_slice = [v for v in self.state_vars if v not in cache_states_with_ignored_vars]
        else:
            var_slice = None

        # Run the initial state caching step.
        # State vars in local grammar:
        max_depth = 2**30
        if "max_tlc_inv_depth" in self.spec_config:
            max_depth = self.spec_config["max_tlc_inv_depth"]


        # Upfront caching run for this round. If we are doing partitioned state caching, don't bother doing
        # this caching step upfront, since we will do it below when first trying to check invariants.
        if self.auto_lemma_action_decomposition and not self.enable_partitioned_state_caching:
            self.cache_projected_states([cache_states_with_ignored_vars], max_depth=max_depth, tlc_workers=tlc_workers)
            logging.info("Finished initial state caching.")
        else:
            logging.info("Skipping initial state caching step for round since we are running with partitioned state caching.")

        # If we are partitioned state caching, though, and we have small var count, then cache upfront.
        SMALL_VAR_COUNT = 5
        if self.auto_lemma_action_decomposition and self.enable_partitioned_state_caching and len(self.state_vars) <= SMALL_VAR_COUNT:
            all_var_sets = list(powerset(self.state_vars))
            logging.info(f"Caching all {len(all_var_sets)} var sets upfront, since only {len(self.state_vars)} total state vars.")
            self.cache_projected_states(all_var_sets, max_depth=max_depth, tlc_workers=tlc_workers)

        inv_candidates_generated_in_round = set()
        num_ctis_remaining = None

        t_round_begin = time.time()
        num_iter_repeats = 0
        while iteration <= self.num_iters:
            tstart = time.time()
            self.latest_elimination_iter = iteration

            # TODO: Possibly use these for optimization later on.
            self.sat_invs_in_iteration = set()
            self.invs_checked_in_iteration = set()

            # On first iteration, look for smallest predicates.
            if iteration == 1:
                (min_conjs, max_conjs) = (1, 1)
                process_local=False
                quant_inv_fn = self.quant_inv

            # On second iteration, search for non process local invariants.
            if iteration==2:
                num_conjs = init_conjs + 1
                (min_conjs, max_conjs) = (num_conjs, num_conjs)
                process_local=False
                quant_inv_fn = self.quant_inv

            # On third and following iterations, search for non process local invariants with more conjuncts.
            if iteration==3:
                num_conjs = init_conjs + 2
                (min_conjs, max_conjs) = (num_conjs, num_conjs)
                process_local=False
                if quant_inv_alt:
                    quant_inv_fn = quant_inv_alt
                    preds = preds + preds_alt

            if iteration==4:
                num_conjs = init_conjs + 3
                (min_conjs, max_conjs) = (num_conjs, num_conjs)
                process_local=False
                if quant_inv_alt:
                    quant_inv_fn = quant_inv_alt
                    preds = preds + preds_alt

            if iteration==5:
                num_conjs = init_conjs + 4
                (min_conjs, max_conjs) = (num_conjs, num_conjs)
                process_local=False
                if quant_inv_alt:
                    quant_inv_fn = quant_inv_alt
                    preds = preds + preds_alt

            if iteration==6:
                min_conjs = 3
                max_conjs = 3
                process_local=False
                if quant_inv_alt:
                    quant_inv_fn = quant_inv_alt
                    preds = preds + preds_alt

            var_slice_str = "None"
            if var_slice is not None:
                var_slice_str = "{" + ",".join(var_slice) + "}"
            logging.info("\n>>> (Round %d, sub-round %d) Iteration %d (num_conjs=(min=%d,max=%d),process_local=%s,var_slice=%s)" % (roundi, subroundi, iteration,min_conjs,max_conjs,process_local,str(var_slice_str))) 

            logging.info("Starting iteration %d of eliminate_ctis (min_conjs=%d, max_conjs=%d)" % (iteration,min_conjs,max_conjs))
            
            # Make the seed at each iteration and round fixed so that
            # sampling amounts in one round don't affect randomness in
            # later rounds.
            new_seed = (self.seed*1000) + (roundi*100) + (iteration*10) + num_iter_repeats
            logging.info(f"Re-seeding iteration with {new_seed} = {self.seed} + (roundi={roundi} * 100) + (iter={iteration}*10) + num_iter_repeats={num_iter_repeats}")
            random.seed(new_seed)

            sat_invs = set()

            # Allow optional use of more efficient, C++ based invariant checking procedure.
            if self.use_cpp_invgen:
                logging.info("Using C++ invariant checking procedure")
                invfile = f"cpp-invgen-iter_{iteration}.invs"

                invseed = random.randint(0,10000)
                cmd = f"python3 cppinvs.py --seed {invseed} --ninvs {num_invs} --minconjuncts {min_conjs} --maxconjuncts {max_conjs} --nthreads {self.tlc_workers} --outfile {invfile}"
                subproc = subprocess.Popen(cmd, shell=True, stdout=subprocess.PIPE)
                ret = subproc.stdout.read().decode(sys.stdout.encoding)
                invs = set(open(invfile).read().splitlines())

                # Run with alternate quantifier.
                if iteration >= 3:
                    logging.info(f"Looking for C++ invariants with alternate quantifier template.")
                    invseed = random.randint(0,10000)
                    num_conjs_alt_min = 2
                    num_conjs_alt_max = 2
                    num_invs_alt = 3000
                    cmd = f"python3 cppinvs.py --seed {invseed} --ninvs {num_invs_alt} --minconjuncts {num_conjs_alt_min} --maxconjuncts {num_conjs_alt_max} --nthreads {self.tlc_workers} --outfile {invfile} --quantalt"
                    subproc = subprocess.Popen(cmd, shell=True, stdout=subprocess.PIPE)
                    ret = subproc.stdout.read().decode(sys.stdout.encoding)
                    invs_alt = set(open(invfile).read().splitlines())
                    invs = invs.union(invs_alt)

                sat_invs = ["Inv%d"%i for i in range(len(invs))]
                quant_inv_fn = lambda v : v

                logging.info(f"Number of C++ generated invs: {len(sat_invs)}")

            elif self.cached_invs:
                # defer_exists_quantifiers = False # defer exists quantifiers to later rounds.
                invs = sorted(self.cached_invs)
                logging.info("Loaded %d cached invariants" % len(invs))

                # # Filter out existentially quantified invariants.
                # if iteration==1 and defer_exists_quantifiers:
                #     print("Filtering out existentially quantified invariants on first round.")
                #     invs = list(filter(lambda einv : "\\E" not in einv, invs))
                #     print(f"{len(invs)} invariants remaining after exists quantifier filter.")

                sat_invs = ["Inv%d"%i for i in range(len(invs))]
                # Cached invariants come with quantifier structure.
                quant_inv_fn = lambda v : v
                self.invcheck_duration_secs = self.cached_invs_gen_time_secs
            
            else:
                self.start_timing_invcheck()

                # Generate and check random set of invariants.
                logging.info("Generating %d candidate invariants." % num_invs)
                use_pred_identifiers = self.use_fast_pred_eval
                boolean_style = "pyeda" if self.use_fast_pred_eval else "tla"
                all_invs = mc.generate_invs(
                    preds, num_invs, min_num_conjuncts=min_conjs, max_num_conjuncts=max_conjs, 
                    process_local=process_local, quant_vars=self.quant_vars, 
                    boolean_style = boolean_style,
                    use_pred_identifiers=use_pred_identifiers,
                    invs_avoid_set=inv_candidates_generated_in_round)
                
                invs = all_invs["raw_invs"]

                # Add in existing strengthening conjuncts to the set of invariants to consider.
                # This will cause these conjuncts to be checked again, but that's okay for now, since we will
                # choose them first over new invariants if they are useful, below during CTI elimination.
                # TODO: May consider cleaner ways for re-using existing strengthening conjuncts.

                # Try to do a bit of inference without resorting to existing conjuncts, and then add them back in after a round or
                # two. 
                # Not sure how much effect this may have on quality of learned invariants or proof graphs.
                iter_to_start_adding_existing_conjuncts = 1

                if self.proof_tree_mode and iteration >= iter_to_start_adding_existing_conjuncts and self.all_args["include_existing_conjuncts"]:
                    added = 0
                    for c in self.strengthening_conjuncts:
                        # Only include strengthening conjunct if its variables are in this slice.
                        # print(c)
                        defs = self.spec_obj_with_lemmas.get_all_user_defs(level=["1"])
                        # print(defs)
                        if c[0] in defs:
                            conjunct_vars = set(self.spec_obj_with_lemmas.get_vars_in_def(c[0])[0])
                            var_slice_set = set(var_slice)
                            # print("conjunct_vars", c[0], conjunct_vars)
                            # print("var_slice", var_slice_set)
                            if set(conjunct_vars).issubset(var_slice_set):
                                logging.info(f"Adding strengthening conjunct {c} to invs since it is in the var slice.")
                                invs.add(c[2])
                                added += 1
                    logging.info(f"Added {added}/{len(self.strengthening_conjuncts)} existing strengthening conjuncts to candidate invariant set.")

                invs_symb_strs = all_invs["pred_invs"]
                # Count the number of generated candidates that were already checked previously.
                repeated_invs = 0
                for ivs in invs_symb_strs:
                    if ivs in self.all_generated_inv_candidates:
                        repeated_invs += 1
                # inv_candidates_generated_in_round.update(invs_symb_strs)
                self.all_generated_inv_candidates.update(invs_symb_strs)
                logging.info(f"Found {repeated_invs} repeated generated invariants (total generated in round {roundi}: {len(self.all_generated_inv_candidates)}).")

                # Sort the set of invariants to give them a consistent order.
                invs = sorted(list(invs))
                # print("Raw invs")
                # print(invs[:5])
                # print(hashlib.md5("".join(invs).encode()).hexdigest())
                pred_var_set_counts = {}
                pred_var_sets_for_invs = []
                for xinv in invs:
                    # print("generated pred:",quant_inv_fn(xinv))
                    def svar_in_inv(v, i):
                        # avoid variables with shared substrings.
                        qi = self.quant_inv(i)
                        return f"{v}[" in qi or f"{v} " in qi or f"{v}:" in qi
                    svars = []
                    for s in self.state_vars:
                        if svar_in_inv(s, xinv):
                            svars.append(s)
                    k = tuple(sorted(svars))
                    pred_var_sets_for_invs.append(k)
                    if k in pred_var_set_counts:
                        pred_var_set_counts[tuple(sorted(svars))] += 1
                    else:
                        pred_var_set_counts[tuple(sorted(svars))] = 1
                    # print(xinv, svars, len(svars))

                    # print(p, ":", pred_var_set_counts[p])


                # print(self.all_sat_invs)

                # No need to re-check invariants if they have already been
                # discovered in past. Remove them from the set of invariants to
                # check, and then add them back to the set of satisfied
                # invariants after running invariant checking.
                # TODO: Finish implementing this optimization.
                prechecked_invs = set(invs).intersection(self.all_sat_invs) 
                # invs = set(invs) - self.all_sat_invs
                # invs = sorted(list(invs))

                compute_subsumption = False
                if compute_subsumption:
                    logging.info("Computing subsumption ordering.")

                    # (subsumption_edges_inds,subsumption_edges,redundant) = mc.compute_subsumption_ordering(invs_symb_strs)
                    (subsumption_edges_inds,subsumption_edges,redundant) = mc.compute_subsumption_ordering(invs_symb_strs, num_samples_to_check=500)
                    logging.info(f"{len(subsumption_edges)} Subsumption edges:")
                    
                    import graphviz
                    sat_invs_inds = [int(s.replace("Inv","")) for s in sat_invs]
                    nodes = set()
                    for e in subsumption_edges_inds:
                        nodes.add(e[0])
                        nodes.add(e[1])
                    dot = graphviz.Digraph(comment='The Round Table', strict=True)
                    dot.attr(rankdir="LR", ranksep="1.5", pad="1.6")
                    for n in nodes:
                        # create a green node.
                        color = "green" if n in sat_invs_inds else "red"
                        dot.node(str(n), style="filled", fillcolor=color)
                    for e in subsumption_edges_inds:
                        dot.edge(str(e[0]), str(e[1]))
                    dot.render(f"subsumption_graphs/subsumption_graph_R{roundi}_I{iteration}_conjs{min_conjs}", format="pdf")
                    # for e in subsumption_edges:
                    #     print(e)


                # Check all generated candidate invariants.
                if not self.use_fast_pred_eval:
                    # Pass max exploration depth if given. Otherwise we just use (effectively) infinite depth.
                    max_depth = 2**30
                    if "max_tlc_inv_depth" in self.spec_config:
                        max_depth = self.spec_config["max_tlc_inv_depth"]


                    if self.enable_partitioned_state_caching:
                        print("predicate var counts:")
                        pred_var_counts_tups = [(pred_var_set_counts[p],p) for p in pred_var_set_counts]
                        pred_var_counts_tups = sorted(pred_var_counts_tups, reverse=True)
                        for p in sorted(pred_var_counts_tups, reverse=True):
                            print(p)

                    invcheck_start = time.time()

                    #
                    # Consider the top few predicate var counts and test projected property checking.
                    # (EXPERIMENTAL)
                    #
                    # TODO: May still be some work to ensure correctness here.
                    partition_sat_invs = set()
                    main_invs_to_check = [(ind, inv) for ind,inv in enumerate(invs)]

                    # Don't bother doing this partitioned caching for tiny numbers of conjuncts.
                    LARGE_PRED_GROUP_COUNT = 0 # don't bother with the overhead of this except for relatively large predicate groups.
                    if self.enable_partitioned_state_caching and min_conjs > 0:
                        logging.info(f"Partitioned property checking enabled for projection caching.")
                        # TODO: Consider enabling this and/or computing more of these cached state projections 
                        # upfront.
                        # top_k = 14

                        # Do static caching upfront.
                        ignored_var_subsets = []
                        for p in pred_var_counts_tups[:]:
                            predvar_set = p[1]
                            ignored = tuple(sorted([svar for svar in self.state_vars if svar not in predvar_set]))
                            ignored_var_subsets.append(ignored)
                        self.cache_projected_states(ignored_var_subsets, max_depth=max_depth, tlc_workers=tlc_workers)

                        for p in pred_var_counts_tups[:]:
                            # print(p)
                            if p[0] < LARGE_PRED_GROUP_COUNT:
                                # If we reached a group that is too small, we stop, even if we haven't dont all top K.
                                logging.info(f"Exiting partitioned state caching loop due to small group size: {p}.")
                                break  
                                
                            predvar_set = p[1]
                            ignored = sorted([svar for svar in self.state_vars if svar not in predvar_set])
                            # print(ignored)

                            invs_to_check = [(ind, inv) for ind,inv in enumerate(invs) if pred_var_sets_for_invs[ind] == predvar_set]

                            # If var count is empty, then just remove these and don't check them, since they should be constant expressions.
                            if len(predvar_set) == 0:
                                invs_to_check_names = set([iv[1] for iv in invs_to_check])
                                main_invs_to_check = [mi for mi in main_invs_to_check if mi[1] not in invs_to_check_names]
                                logging.info(f"Skipping group of {p[0]} invs with empty var slice.")
                                continue

                            partition_var_slice = [s for s in self.state_vars if s not in ignored]
                            logging.info(f"Running partitioned state caching step with {len(ignored)} ignored vars (slice={partition_var_slice}), num invs to check: {len(invs_to_check)}")
                            
                            # Do the caching run.
                            self.cache_projected_states([ignored], max_depth=max_depth, tlc_workers=tlc_workers)

                            # Check the invariants on the cached states.
                            # local_sat_invs will return indices of invariants that were satisfied in the given 'invs_to_check' array.
                            local_sat_invs = self.check_invariants([iv[1] for iv in invs_to_check], tlc_workers=tlc_workers, max_depth=max_depth, cache_with_ignored=[ignored], cache_state_load=True)
                            logging.info(f"Found {len(local_sat_invs)} local partition sat invs.")
                            orig_invs_to_remove = []
                            local_invs_sat = [m for (mind,m) in enumerate(invs_to_check) if f"Inv{mind}" in local_sat_invs]

                            for si in local_sat_invs:
                                invs_to_check_ind = int(si.replace("Inv", ""))
                                inv = invs_to_check[invs_to_check_ind]
                                orig_inv_ind = inv[0]
                                orig_invs_to_remove.append(inv[1])
                            
                            # These no longer need to be checked.
                            invs_to_check_names = set([iv[1] for iv in invs_to_check])
                            main_invs_to_check = [mi for mi in main_invs_to_check if mi[1] not in invs_to_check_names]
                            partition_sat_invs.update(set([f"Inv{iv[0]}" for iv in local_invs_sat]))
                    
                        logging.info(f"Found {len(partition_sat_invs)} partitioned sat invs")

                    # Check all candidate invariants.
                    logging.info("Checking main invariant candidate group.")
                        
                    # Use cached states if specified.
                    cache_load = False
                    if cache_states_with_ignored_vars is not None:
                        cache_load = True

                    if len(main_invs_to_check) > 0:
                        # If we are not caching, then use simulation for checking invariants here, if specified.
                        tlc_flags = "" 
                        if "simulation_inv_check" in self.spec_config and self.spec_config["simulation_inv_check"] and not cache_load:
                            # Get value from dict self.spec_config or use default value.
                            depth = self.spec_config.get("simulation_inv_check_depth", 50)
                            num_states = self.spec_config.get("simulation_inv_check_num_states", 100000)

                            # Compute the number of traces to run for each simulation worker based on the depth
                            # and total state count target.
                            num = num_states // depth // tlc_workers

                            logging.info(f"Will check invariants in simulation with (depth={depth}, num={num},workers={tlc_workers}) for num_states={num_states}")
                            simulation_inv_tlc_flags=f"-depth {depth} -simulate num={num}"
                            tlc_flags = simulation_inv_tlc_flags

                        # We now always pass a list of ignored var sets to the model checker.
                        cache_states_with_ignored_vars_arg = cache_states_with_ignored_vars
                        if cache_states_with_ignored_vars is not None:
                            cache_states_with_ignored_vars_arg = [sorted(cache_states_with_ignored_vars)]
                        main_sat_invs = self.check_invariants([mi[1] for mi in main_invs_to_check], tlc_workers=tlc_workers, 
                                                              max_depth=max_depth, cache_state_load=cache_load, 
                                                              cache_with_ignored=cache_states_with_ignored_vars_arg, tlc_flags=tlc_flags)
                        main_invs_to_check_sat = [m for (mind,m) in enumerate(main_invs_to_check) if f"Inv{mind}" in main_sat_invs]
                        sat_invs = set([f"Inv{iv[0]}" for iv in main_invs_to_check_sat])
                    
                    # print("sat_invs")
                    # print(sat_invs)
                    # print("invs")
                    # print(len(invs))
                    # print(partition_sat_invs)

                    # Add in the sat invariants already found in partitioned, cached state checks.
                    # print(type(sat_invs))
                    # print(type(partition_sat_invs))
                    sat_invs.update(partition_sat_invs)
                else:
                    print("Doing fast check of candidate predicates.")
                    violated_invs = set()
                    # Check invariants for each state.
                    for state_fp in self.pred_vals:
                        # print(s)
                        pred_state_vals = self.pred_vals[state_fp]
                        for inv_ind,inv in enumerate(invs):
                            if inv_ind in violated_invs:
                                # No need to keep re-checking violated invariants.
                                continue
                            for p_ind in pred_state_vals:
                                inv = inv.replace(f"(PRED_{p_ind})", "(" + str(pred_state_vals[p_ind]) + ")")
                            # print("state inv:", inv)
                            pred_res = eval(inv)
                            if not pred_res:
                                violated_invs.add(inv_ind)
                    # print(violated_invs)
                                
                    print(f"[FASTPRED] Found {len(invs)-len(violated_invs)} satisfied invariants:")
                    sat_invs = []
                    for inv_ind,inv in enumerate(invs):

                        # Replace abstract pred identifiers with original pred expressions.
                        orig_inv_expr = inv
                        for p_ind,p in enumerate(preds):
                            orig_inv_expr = orig_inv_expr.replace(f"(PRED_{p_ind})", f"({p})")
                            orig_inv_expr = orig_inv_expr.replace(f"not", "~")
                            orig_inv_expr = orig_inv_expr.replace(f" or ", " \/ ")
                        invs[inv_ind] = orig_inv_expr

                        # Save the satisfied invariants.
                        if inv_ind not in violated_invs:
                            # print(f"Satisfied invariant (Inv{inv_ind}):", orig_inv_expr)
                            sat_invs.append(f"Inv{inv_ind}")

                # Report total invariant checking time.
                invcheck_duration = time.time() - invcheck_start
                logging.info(f"Discovered {len(sat_invs)} / {len(invs)} total invariants in {round(invcheck_duration,2)}s.")

                sat_invs = list(sorted(sat_invs))
                # print("first few sat invs:")
                # print(sat_invs[:5])

                print_invs = False # disable printing for now.
                if print_invs:
                    for inv in sat_invs:
                        invi = int(inv.replace("Inv",""))
                        invname = "Inv%d" % invi
                        invexp = quant_inv_fn(invs[invi])
                        logging.info("%s %s %s", invname,"==",invexp)
                self.end_timing_invcheck()

            if len(sat_invs)==0:
                logging.info("No invariants found. Continuing.")
                iteration += 1
                continue

            if self.use_fast_pred_eval:
                orig_invs_sorted = invs
            else:
                orig_invs_sorted = sorted(invs)

            # Try to select invariants based on size ordering.
            # First, sort invariants by the number of CTIs they eliminate.
            def get_invexp(inv):
                invi = int(inv.replace("Inv",""))
                return quant_inv_fn(orig_invs_sorted[invi])
        
            # Cache all generated invariants so we don't need to unnecessarily re-generate them
            # in future rounds.
            self.all_sat_invs = self.all_sat_invs.union(set(map(get_invexp, list(sat_invs))))
            self.all_checked_invs = self.all_checked_invs.union(set(map(quant_inv_fn, list(invs))))
            logging.info(f"Total number of unique satisfied invariants generated so far: {len(self.all_sat_invs)}")
            logging.info(f"Total number of unique checked invariants so far: {len(self.all_checked_invs)}")


            #############
            #
            # For each invariant we generated, we want to see what set of CTIs it removes, so that we 
            # can better decide which invariant to pick as a new strengthening conjunct. That's the goal
            # of the prototype code below.
            #
            ############

            logging.info(f"Checking which invariants eliminate CTIs ({len(orig_k_ctis)} total CTIs).")

            # Initialize table mapping from invariants to a set of CTI states they violate.
            cti_states_eliminated_by_invs = {}
            for inv in sat_invs:
                cti_states_eliminated_by_invs[inv] = set()

            # Create metadir if necessary.
            os.system("mkdir -p states")

            #
            # Generate specs for checking CTI elimination with TLC. Note that we
            # partition the invariants into sub groups for checking with TLC, since
            # it can get overwhelmed when trying to check too many invariants at
            # once.
            #
            # TODO: Properly parallelize CTI elimination checking.
            #
            MAX_INVS_PER_GROUP = 2000
            curr_ind = 0
            workdir = None
            if specdir != "":
                workdir = specdir


            # Run CTI elimination checking in parallel.
            n_tlc_workers = self.n_cti_elimination_workers
            # inv_chunks = list(chunks(sat_invs, n_tlc_workers))
            cti_chunks = list(chunks(list(orig_k_ctis), n_tlc_workers))

            self.start_timing_ctielimcheck()

            while curr_ind < len(sat_invs):
                sat_invs_group = sat_invs[curr_ind:(curr_ind+MAX_INVS_PER_GROUP)]
                logging.info("Checking invariant group of size %d (starting invariant=%d) for CTI elimination." % (len(sat_invs_group), curr_ind))
                tlc_procs = []

                # Create the TLA+ specs and configs for checking each chunk.
                for ci,cti_chunk in enumerate(cti_chunks):

                    # Build and save the TLA+ spec.
                    spec_name = f"{self.specname}_IndQuickCheck_chunk{ci}"
                    spec_str = self.make_indquickcheck_tla_spec(spec_name, invs, sat_invs_group, cti_chunk, quant_inv_fn)

                    ctiquicktlafile = f"{os.path.join(self.specdir, GEN_TLA_DIR)}/{spec_name}.tla"
                    ctiquicktlafilename = f"{GEN_TLA_DIR}/{spec_name}.tla"

                    f = open(ctiquicktlafile,'w')
                    f.write(spec_str)
                    f.close()

                    # Generate config file.
                    ctiquickcfgfile=f"{os.path.join(self.specdir, GEN_TLA_DIR)}/{self.specname}_CTIQuickCheck_chunk{ci}.cfg"
                    ctiquickcfgfilename=f"{GEN_TLA_DIR}/{self.specname}_CTIQuickCheck_chunk{ci}.cfg"
                    cfg_str = self.make_ctiquickcheck_cfg(invs, sat_invs_group, cti_chunk, quant_inv_fn)
                    
                    f = open(ctiquickcfgfile,'w')
                    f.write(cfg_str)
                    f.close()

                    cti_states_file = os.path.join(self.specdir, f"states/cti_quick_check_chunk{ci}_{curr_ind}.json")
                    cti_states_relative_file = f"states/cti_quick_check_chunk{ci}_{curr_ind}.json"

                    # Run TLC.
                    # Create new tempdir to avoid name clashes with multiple TLC instances running concurrently.
                    dirpath = tempfile.mkdtemp()
                    cmd = self.java_exe + ' -Xss16M -Djava.io.tmpdir="%s" -cp tla2tools-checkall.jar tlc2.TLC -maxSetSize %d -dump json %s -noGenerateSpecTE -metadir states/ctiquick_%s_chunk%d_%d -continue -checkAllInvariants -deadlock -workers 1 -config %s %s' % (dirpath, mc.TLC_MAX_SET_SIZE ,cti_states_relative_file, self.specname, ci, curr_ind, ctiquickcfgfilename, ctiquicktlafilename)

                    
                    logging.debug("TLC command: " + cmd)
                    workdir = None if self.specdir == "" else self.specdir
                    subproc = subprocess.Popen(cmd, shell=True, stdout=subprocess.PIPE, cwd=workdir)
                    # time.sleep(0.25)
                    tlc_procs.append(subproc)
            
                for ci,subproc in enumerate(tlc_procs):
                    logging.info("Waiting for TLC termination " + str(ci))

                    subproc.wait()
                    ret = subproc.stdout.read().decode(sys.stdout.encoding)
                    # print(ret)

                    # TODO: Determine cause of flakiness when reading JSON states file.
                    # time.sleep(0.5)

                    # print ret
                    lines = ret.splitlines()
                    lines = mc.greplines("State.*|/\\\\", lines)

                    cti_states_file = os.path.join(self.specdir, f"states/cti_quick_check_chunk{ci}_{curr_ind}.json")
                    cti_states_relative_file = f"states/cti_quick_check_chunk{ci}_{curr_ind}.json"

                    # logging.info(f"Opening CTI states JSON file: '{cti_states_file}'")
                    fcti = open(cti_states_file)
                    text = fcti.read()
                    cti_states = json.loads(text)["states"]
                    # cti_states = json.load(fcti)["states"]
                    fcti.close()
                    # print "cti states:",len(cti_states)

                    # Record the CTIs eliminated by each invariant.
                    for cti_state in cti_states:
                        sval = cti_state["val"]
                        ctiHash = sval["ctiId"]
                        # for inv in sat_invs_group:
                        # for inv in inv_chunks[ci]:
                        for inv in sat_invs_group:
                            if not sval[inv + "_val"]:
                                cti_states_eliminated_by_invs[inv].add(ctiHash)

                    for inv in cti_states_eliminated_by_invs:
                        if len(cti_states_eliminated_by_invs[inv]):
                            invi = int(inv.replace("Inv",""))
                            invexp = quant_inv_fn(sorted(invs)[invi])

                curr_ind += MAX_INVS_PER_GROUP

            # The estimated syntactic/semantic "cost" (i.e complexity) of an invariant expression.
            def get_invexp_cost(inv):
                exp = get_invexp(inv)
                return exp

            # Key function for sorting invariants by the number of new CTIs they eliminate.
            def inv_sort_key(inv):
                return (len(cti_states_eliminated_by_invs[inv]),-len(get_invexp_cost(inv)))

            logging.info(f"Sorting {len(sat_invs)} invariants for CTI elimination")

            sorted_invs = sorted(sat_invs, reverse=True, key=inv_sort_key)
            chosen_invs = []
            cti_states_eliminated_in_iter = 0

            #
            # Check CTI elimination for each invariant.
            #

            logging.info(f"Checking {len(sat_invs)} satisfied invariants for CTI elimination")


            # Given a list of invariants and the set of CTIs they eliminate, we
            # want to compute a new CTI set covering that, ideally, eliminates
            # the max number of CTIs with the smallest set of invariants. In
            # practice, we try to do our best, by using a greedy heuristic for
            # invariant selection.

            new_conjuncts_to_add = []

            # The set of CTIs eliminated so far in this iteration of elimination checking.
            ctis_eliminated_this_iter = set()

            conjuncts_this_iter = []

            # Consider all existing conjuncts and new conjuncts as candidates for
            # next elimination invariant to pick.
            logging.info(f"Re-computing CTI elimination with both existing and new conjuncts (round={roundi}, subround={subroundi}).")
            if self.auto_lemma_action_decomposition:
                logging.info(f"CTI obligation action: {orig_k_ctis[0].action_name}.")

            subiter = 0
            while True:

                # Rank all new invariant candidates based on the set of CTIs they eliminate.
                sorter = lambda inv: (len(cti_states_eliminated_by_invs[inv] - ctis_eliminated_this_iter), -len(get_invexp_cost(inv)))
                new_inv_cands = sorted(sorted_invs, reverse=True, key=sorter)

                # Rank all existing invariant conjuncts based on the set of CTIs they eliminate.
                existing_inv_cands = sorted(conjuncts_added_in_round, reverse=True, key = lambda conj : len(conj["ctis_eliminated"] - ctis_eliminated_this_iter))

                top_new_inv_cand = new_inv_cands[0]
                if len(existing_inv_cands) == 0:
                    invi = int(top_new_inv_cand.replace("Inv", ""))
                    chosen_cand = {"inv": top_new_inv_cand, "invexp": orig_invs_sorted[invi], "ctis_eliminated": cti_states_eliminated_by_invs[top_new_inv_cand]}
                    new_ctis_eliminated = cti_states_eliminated_by_invs[top_new_inv_cand] - ctis_eliminated_this_iter
                else:
                    # Pick invariant for elimination.
                    if len((cti_states_eliminated_by_invs[top_new_inv_cand] - ctis_eliminated_this_iter)) > len(existing_inv_cands[0]["ctis_eliminated"] - ctis_eliminated_this_iter):
                        invi = int(top_new_inv_cand.replace("Inv", ""))
                        chosen_cand = {"inv": top_new_inv_cand, "invexp": orig_invs_sorted[invi], "ctis_eliminated": cti_states_eliminated_by_invs[top_new_inv_cand]}
                        new_ctis_eliminated = cti_states_eliminated_by_invs[top_new_inv_cand] - ctis_eliminated_this_iter
                    else:
                        chosen_cand = existing_inv_cands[0]
                        new_ctis_eliminated = existing_inv_cands[0]["ctis_eliminated"] - ctis_eliminated_this_iter

                if len(new_ctis_eliminated) > 0:
                    conjuncts_this_iter.append(chosen_cand)
                    ctis_eliminated_this_iter.update(new_ctis_eliminated)
                    ctis_left = len(orig_k_ctis) - len(ctis_eliminated_this_iter)
                    logging.info(f" - Chose {chosen_cand['inv']} (elim_iter={subiter}, new CTIs eliminated={len(new_ctis_eliminated)}, with {ctis_left} now remaining)")
                else:
                    logging.info("No new CTIs eliminated. Continuing.")
                    break
                subiter += 1

            # Prune out any graph nodes referring to conjuncts added earlier in this round.
            # graph_nodes_to_remove = set()
            # for c in conjuncts_added_in_round:
            #     for n in self.proof_graph["nodes"]:
            #         if c["inv"] in n:
            #             graph_nodes_to_remove.add(n)
            #     keep_edge = lambda e : (c["inv"] not in e[0] and c["inv"] not in e[1])
            #     edges_to_prune = [e for e in self.proof_graph["edges"] if not keep_edge(e)]
            #     for e in edges_to_prune:
            #         logging.info(f"Pruning edge {e} from proof graph.")
            #     self.proof_graph["edges"] = [e for e in self.proof_graph["edges"] if keep_edge(e)]

            # for n in graph_nodes_to_remove:
            #     logging.info(f"Pruning node {n} from proof graph.")
            #     del self.proof_graph["nodes"][n]

            curr_conjuncts = [c["inv"] for c in conjuncts_added_in_round]
            new_conjuncts = [c["inv"] for c in conjuncts_this_iter]
            logging.info(f"Current conjunct set computed in round (subround={subroundi}): {curr_conjuncts}")
            logging.info(f"New conjunct set computed in round (subround={subroundi}): {new_conjuncts}")

            # Mark whether we computed a new set of conjuncts in this iteration.
            new_conjuncts_found_in_iter = len(curr_conjuncts) < len(new_conjuncts)
            # sorted(curr_conjuncts) != sorted(new_conjuncts)

            conjuncts_added_in_round = conjuncts_this_iter
            chosen_invs = conjuncts_this_iter

            new_ctis_were_eliminated_this_iter = False
            if len(ctis_eliminated_this_iter) > len(eliminated_ctis):
                logging.info("NEW CTIs eliminated in this iteration.")
                logging.info(f"-- Existing set of eliminated CTIs ({len(curr_conjuncts)} conjuncts) -> {len(eliminated_ctis)}")
                logging.info(f"-- New set of eliminated CTIs      ({len(new_conjuncts)} conjuncts) -> {len(ctis_eliminated_this_iter)}")
                new_ctis_were_eliminated_this_iter = True


            # Update global set of eliminated CTIs.
            eliminated_ctis = ctis_eliminated_this_iter


            #####################################
            # Disable this selection logic for now
            #
            # for i in range(len(sorted_invs)):
            for i in []:
                # Sort the remaining invariants by the number of new CTIs they eliminate.
                compare_fn = lambda inv: (len(cti_states_eliminated_by_invs[inv] - eliminated_ctis), -len(get_invexp_cost(inv)))
                sorted_invs = sorted(sorted_invs, reverse=True, key=compare_fn)

                compare_fn_all_ctis = lambda inv: (len(cti_states_eliminated_by_invs[inv]), -len(get_invexp_cost(inv)))
                sorted_invs_all_ctis = sorted(sorted_invs, reverse=True, key=compare_fn_all_ctis)
                next_inv = sorted_invs.pop(0)

                ind =  int(next_inv.split("_")[1])
                invname = f"Inv_EXISTING_{ind}" 
                invexp = conjuncts_added_in_round[ind][1]

                cti_states_eliminated_in_iter += len(new_ctis_eliminated)

                if len(conjuncts_added_in_round) >= self.max_num_conjuncts_per_round and num_ctis_remaining > 0:
                    break

                if len(new_ctis_eliminated)>0:
                    logging.info("New CTIs eliminated by inv %s %s: %d" % (next_inv, invexp, len(new_ctis_eliminated)))
                    logging.info("* " + next_inv + " -> new CTIs eliminated: %d" % len(new_ctis_eliminated))
                    # for cti in new_ctis_eliminated:
                        # print(cti_table[cti].getActionName())
                    chosen_invs.append(next_inv)
                    eliminated_ctis = eliminated_ctis.union(new_ctis_eliminated)
                    conjunct_obj = {
                        "inv": next_inv,
                        "invexp": invexp,
                        "ctis_eliminated": cti_states_eliminated_by_invs[next_inv]
                    }
                    # conjuncts_added_in_round.append(conjunct_obj)
                    new_conjuncts_to_add.append(conjunct_obj)
                    # conjuncts_added_in_this_round.append((next_inv, invexp))
                    # conjuncts_added_in_round_ctis_eliminated.append(cti_states_eliminated_by_invs[next_inv])
                    # conjuncts_added_in_round_ctis_eliminated.append(all_ctis_eliminated)
                    # conjuncts_added_in_this_round_ctis_eliminated.append(all_ctis_eliminated)
                    num_ctis_remaining = len(list(cti_table.keys()))-len(eliminated_ctis)

                    # Check to see if this chosen invariant subsumes any existing chosen invariant i.e.
                    # it eliminates a superset of states eliminated by a previous chosen invariant.
                    # for ind,prev_conj in enumerate(conjuncts_added_in_round):
                    #     prev_eliminated = conjuncts_added_in_round_ctis_eliminated[ind]
                    #     subsumes = cti_states_eliminated_by_invs[next_inv].issuperset(prev_eliminated)
                    #     logging.info(f"{next_inv} subsumes existing conjunct {prev_conj}: {subsumes}")

                    if len(chosen_invs) >= self.max_num_conjuncts_per_round:
                        logging.info(f"Moving on since reached max num conjuncts per round: {self.max_num_conjuncts_per_round}")
                        break 
                else:
                    logging.info("Moving on since no remaining invariants eliminate CTIs.")
                    break
            ###########################



            #
            # Record the new chosen strengthening conjuncts.
            #
            iter_repeat = False
            if len(chosen_invs):
                logging.info("*** New strengthening conjuncts *** ")
                for cind,inv in enumerate(chosen_invs):
                    # if "EXISTING" in inv:
                    #     ind = int(inv.split("_")[1])
                    #     invexp = conjuncts_added_in_round[ind][1]
                    #     # invexp = quant_inv_fn(unquant_invexp)
                    # else:
                    # invi = int(inv.replace("Inv",""))
                    # unquant_invexp = sorted(invs)[invi]
                    unquant_invexp = inv["invexp"]
                    invexp = quant_inv_fn(unquant_invexp)
            
                    inv_suffix = ""
                    if append_inv_round_id:
                        inv_suffix = "_" + "R" + str(roundi) 
                        if subroundi is not None:
                            inv_suffix += "_" + str(subroundi)
                        inv_suffix += "_I" + str(iteration) # + "_" + str(uniqid)
                        
                    # Add the invariant as a conjunct.
                    # If there is an existing strengthening conjunct with an identical expression, no
                    # need to add this as a new strengthening conjunct.
                    # existing_conjuncts = [self.proof_graph["nodes"][n]["inv"] for n in self.proof_graph["nodes"] if self.proof_graph["nodes"][n] == invexp]
                    # if len(existing_conjuncts) == 0:
                    #     # self.strengthening_conjuncts.append((inv + inv_suffix, invexp, unquant_invexp))
                    #     self.strengthening_conjuncts.append((inv["inv"] + inv_suffix, invexp, unquant_invexp))
                    #     uniqid += 1
                    # else:
                    #     logging.info("Skipping adding invariant as strengthening conjunct, since equivalent expression is already present.")

                    logging.info("%s %s", inv["inv"], invexp) #, "(eliminates %d CTIs)" % len(cti_states_eliminated_by_invs[inv])


                curr_duration = time.time() - t_round_begin
                if curr_duration > self.max_duration_secs_per_round:
                    logging.info(f"Exiting iteration since we exceeded max round duration of {self.max_duration_secs_per_round}s, with current duration of {curr_duration}s.")
                    break

          
                # print "CTIs eliminated by this invariant: %d" % len(cti_states_eliminated_by_invs[inv])
                # Re-run the iteration if new conjuncts were discovered.
                # Don't re-run iterations where max_conjs=1, since they are small and quick.
                # TODO: Deal with this in the face of conjunct set re-computation on every iteration.
                # if self.rerun_iterations and new_conjuncts_found_in_iter and max_conjs > 1:
                if self.rerun_iterations and new_ctis_were_eliminated_this_iter and max_conjs > 1:
                    logging.info("Re-running iteration.")
                    iteration -= 1
                    iter_repeat = True

            if self.proof_tree_mode:
                self.proof_graph["curr_node"] = None
            
            if iter_repeat:
                num_iter_repeats += 1
            else:
                num_iter_repeats = 0

            # conjuncts_added_in_round = conjuncts_added_in_this_round
            # conjuncts_added_in_round_ctis_eliminated = conjuncts_added_in_this_round_ctis_eliminated

            num_ctis_remaining = len(list(cti_table.keys()))-len(eliminated_ctis)
            num_orig_ctis = len(list(cti_table.keys()))
            duration = time.time()-tstart
            logging.info("[ End iteration {}. (took {:.2f} secs.) ]".format(iteration, duration))
            logging.info("%d original CTIs." % num_orig_ctis)
            logging.info("%d new CTIs eliminated in this iteration." % len(eliminated_ctis))
            logging.info("%d total CTIs eliminated." % len(eliminated_ctis))
            logging.info("%d still remaining." % num_ctis_remaining)
            self.total_num_ctis_eliminated += cti_states_eliminated_in_iter
            self.end_timing_ctielimcheck()

            # logging.info("")
            if num_ctis_remaining == 0:
                # Update set of all strengthening conjuncts added in this round.
                for cind,c in enumerate(conjuncts_added_in_round):
                    inv_suffix = ""
                    if append_inv_round_id:
                        inv_suffix = "_" + "R" + str(roundi) 
                        if subroundi is not None:
                            inv_suffix += "_" + str(subroundi)
                        inv_suffix += "_I" + str(iteration) # + "_" + str(uniqid)
                    unquant_invexp = c["invexp"]
                    invexp = quant_inv_fn(unquant_invexp)
                    # uniqid += 1
                
                    invname = c["inv"] + inv_suffix

                    # # If there exists a proof graph node with the same expression don't add a new named node.
                    # existing_lemma_nodes = [n for n in self.proof_graph["nodes"].keys() if "is_lemma" in self.proof_graph["nodes"][n] and self.proof_graph["nodes"][n]["expr"] == invexp]
                    # if len(existing_lemma_nodes) > 0:
                    #     invname = existing_lemma_nodes[0]
                    #     print("existing invname: ", invname)
                    #     # Update to existing invariant name.
                    #     # conjuncts_added_in_round[cind]["inv"] = invname
                    #     logging.info("Skipping adding invariant as strengthening conjunct, since equivalent expression is already present.")
                    # else:
                    if not self.proof_tree_mode:
                        self.strengthening_conjuncts.append((invname, invexp, unquant_invexp))

                    #
                    # Save edges for inductive proof graph.
                    #
                    if self.proof_tree_mode and self.auto_lemma_action_decomposition:

                        # If there exists a proof graph node with the same expression don't add a new named node.
                        existing_lemma_nodes = [n for n in self.proof_graph["nodes"].keys() if "is_lemma" in self.proof_graph["nodes"][n] and self.proof_graph["nodes"][n]["expr"] == invexp]
                        if len(existing_lemma_nodes) > 0:
                            invname = existing_lemma_nodes[0]
                            print("existing invname: ", invname)
                            # Update to existing invariant name.
                            # conjuncts_added_in_round[cind]["inv"] = invname
                            logging.info("Skipping adding invariant as strengthening conjunct, since equivalent expression is already present.")
                        else:
                            self.strengthening_conjuncts.append((invname, invexp, unquant_invexp))

                        lemma_node = (invname, invexp, unquant_invexp)
                        # self.proof_obligation_queue.append(lemma_node)

                        action_node = f"{orig_k_ctis[0].inv_name}_{orig_k_ctis[0].action_name}"
                        e1 = (f"{orig_k_ctis[0].inv_name}_{orig_k_ctis[0].action_name}", f"{orig_k_ctis[0].inv_name}")
                        e2 = (invname, f"{orig_k_ctis[0].inv_name}_{orig_k_ctis[0].action_name}")
                        self.proof_graph["edges"].append(e1)
                        self.proof_graph["edges"].append(e2)
                        num_ctis_remaining = len(list(cti_table.keys()))-len(eliminated_ctis)
                        # if action_node in self.proof_graph:
                            # self.proof_graph[action_node].append(inv + inv_suffix)
                        lemma_action_coi = [v for v in self.state_vars if v not in cache_states_with_ignored_vars]

                        all_lemma_nodes = [n for n in self.proof_graph["nodes"].keys() if "is_lemma" in self.proof_graph["nodes"][n]]
                        if invname not in self.proof_graph["nodes"]:
                            self.proof_graph["nodes"][lemma_node[0]] = {
                                "discharged": False, 
                                "is_lemma": True,
                                "expr": lemma_node[1],
                                "order": len(all_lemma_nodes) + 1,
                                "depth": self.curr_obligation_depth + 1
                            }

                        self.proof_graph["nodes"][action_node] = {
                            "ctis_remaining": num_ctis_remaining, 
                            "coi_vars": lemma_action_coi,
                            "num_grammar_preds": len(preds),
                            "is_action": True,
                            "discharged": num_ctis_remaining == 0
                        }
                        self.proof_graph["curr_node"] = action_node
                        # print(f"{orig_k_ctis[0].inv_name}_{orig_k_ctis[0].action_name}",  "->", f"{orig_k_ctis[0].inv_name}", "// EDGE")
                        # print(inv + inv_suffix, "->", f"{orig_k_ctis[0].inv_name}_{orig_k_ctis[0].action_name}", "// EDGE")

                        if self.save_dot and len(self.proof_graph["edges"]) > 0:
                            # Render updated proof graph as we go.
                            self.render_proof_graph()     

            if len(conjuncts_added_in_round) >= self.max_num_conjuncts_per_round and num_ctis_remaining > 0:
                logging.info(f"Exiting round since reached max num conjuncts per round: {self.max_num_conjuncts_per_round}")
                return None

            # logging.info("")
            if len(self.strengthening_conjuncts) > 0:
                logging.info("Current strengthening conjuncts:")
                for c in self.strengthening_conjuncts:
                    logging.info("%s %s %s", c[0],"==",c[1])
            else:
                logging.info("No current strengthening conjuncts.")

            # logging.info("")
            if num_ctis_remaining == 0:
                logging.info(f"~~~ DONE! We have eliminated all CTIs of this round. ~~~")
                return self.strengthening_conjuncts

            # Skip to the next iteration, since we've already checked invariants for CTI elimination and
            # added any good ones as strengthening conjuncts.
            iteration +=1

        # Failed to eliminate all CTIs.
        if (num_ctis_remaining is None) or num_ctis_remaining > 0:
            return None
        return self.strengthening_conjuncts
    
    def apalache_induction_check(self, node):
        logging.info("Checking for full proof with Apalache.")
        # We want to check that this node lemma is inductive relative to the conjunction
        # of all its children lemmas.
        spec_name = f"{self.specname}_rel_ind_check"
        support_lemmas = [c.expr for c in node.children_list()]
        rel_ind_pred_name = "IndSupportLemmas"
        goal_inv_name = "Inv"
        spec_str = self.make_rel_induction_check_spec(spec_name, support_lemmas, node.expr, rel_ind_pred_name, goal_inv_name)

        tla_file = f"{os.path.join(self.specdir, GEN_TLA_DIR)}/{spec_name}.tla"
        tla_filename = f"{GEN_TLA_DIR}/{spec_name}.tla"

        f = open(tla_file,'w')
        f.write(spec_str)
        f.close()

        # TODO: Factor out Apalache process management.
        apalache_bin = "apalache/bin/apalache-mc"
        outdir = "gen_tla/apalache_ctigen"
        rundir = "gen_tla/apalache_ctigen"

        # Use this tuning option to avoid unnecessary checking of inductive invariant at bound 0.
        tuning_opt_inv_filter = "search.invariantFilter=1->.*"

        tuning_opts = f"search.smt.timeout={self.apalache_smt_timeout_secs}:{tuning_opt_inv_filter}"
        cmd = f"{apalache_bin} check --out-dir={outdir} --tuning-options='{tuning_opts}' --run-dir={rundir} --cinit=CInit --init={rel_ind_pred_name} --next=Next --inv={goal_inv_name} --length=1 {tla_filename}"
        logging.debug("Apalache command: " + cmd)
        workdir = None
        if self.specdir != "":
            workdir = self.specdir
        subproc = subprocess.Popen(cmd, shell=True, stdout=subprocess.PIPE, cwd=workdir)
        tlc_out = subproc.stdout.read().decode(sys.stdout.encoding)
        # logging.debug(tlc_out)
        lines = [x.strip() for x in tlc_out.splitlines()]
        # Check for successful Apalache run.
        for l in lines:
            if "Checker reports no error up to computation length 1" in l:
                logging.info("No error reported by Apalache. Full proof check passed!")
                node.apalache_proof_check = True

        if not node.apalache_proof_check:
            logging.info("Apalache proof check failed, logging final lines of output.")
            for tail_line in lines[-10:]:
                logging.info(tail_line)


    def run_interactive_mode(self):

        ###########
        # Build a demo proof structure.
        ###########
        self.proof_base_filename = f"benchmarks/{self.specname}.proof"

        lemmaTRUE = StructuredProofNode("LemmaTrue", "TRUE")
        lemmaTRUEShim = StructuredProofNode("LemmaTrueShim", "1=1")

        # Import proof structure definitions for various protocols.
        import proof_2pc
        import proof_asr
        import proof_adr
        import proof_asr_coreLogInv
        import proof_consensus_epr
        import proof_consensus_epr_demo
        import proof_basic_consensus
        import proof_simple_consensus
        import proof_async_raft
        import proof_async_raft_no_truncate
        import proof_Paxos
        import proof_EPaxos
        import proof_Zab
        import proof_Boulanger
        import proof_Hermes

        #
        # Set the specified spec appropriately.
        #
        root = None
        actions = None
        nodes = None
        print(self.proof_struct_tag)
        if self.specname == "TwoPhase":
            root = proof_2pc.root
            actions = proof_2pc.actions
            nodes = proof_2pc.nodes
        elif self.specname == "Hermes":
            root = proof_Hermes.root
            actions = proof_Hermes.actions
            nodes = proof_Hermes.nodes
        elif self.specname == "AbstractRaft":
            if self.proof_struct_tag == "coreLogInv":
                print(f"Loading from proof struct tag: {self.proof_struct_tag}")
                root = proof_asr_coreLogInv.asr_root
                actions = proof_asr_coreLogInv.asr_actions
                nodes = proof_asr_coreLogInv.asr_nodes
            else:
                root = proof_asr.asr_root
                actions = proof_asr.asr_actions
                nodes = proof_asr.asr_nodes
        elif self.specname == "AbstractDynamicRaft":
            root = proof_adr.adr_root
            actions = proof_adr.adr_actions
            nodes = proof_adr.adr_nodes
        elif self.specname == "Boulanger":
            root = proof_Boulanger.root
            actions = proof_Boulanger.actions
            nodes = proof_Boulanger.nodes
        elif self.specname == "consensus_epr":
            if self.proof_struct_tag == "demo":
                root = proof_consensus_epr_demo.root
                actions = proof_consensus_epr_demo.actions
                nodes = proof_consensus_epr_demo.nodes
            else:
                root = proof_consensus_epr.root
                actions = proof_consensus_epr.actions
                nodes = proof_consensus_epr.nodes 
        elif self.specname == "SimpleConsensus":
            root = proof_simple_consensus.root
            actions = proof_simple_consensus.actions
            nodes = proof_simple_consensus.nodes 
        elif self.specname == "AsyncRaft":
            # if self.proof_struct_tag == "no_truncate":
            
            # For now just always use this version of the proof.
            root = proof_async_raft_no_truncate.root
            actions = proof_async_raft_no_truncate.actions
            nodes = proof_async_raft_no_truncate.nodes
            # else:
            #     root = proof_async_raft.root
            #     actions = proof_async_raft.actions
            #     nodes = proof_async_raft.nodes
        elif self.specname == "EPaxos":
            root = proof_EPaxos.root
            actions = proof_EPaxos.actions
            nodes = proof_EPaxos.nodes
        elif self.specname == "Zab":
            root = proof_Zab.root
            actions = proof_Zab.actions
            nodes = proof_Zab.nodes
        elif self.specname == "basic_consensus":
            root = proof_basic_consensus.root
            actions = proof_basic_consensus.actions
            nodes = proof_basic_consensus.nodes
        elif self.specname == "Paxos":
            root = proof_Paxos.root
            actions = proof_Paxos.actions
            nodes = proof_Paxos.nodes
        else:
            logging.info("Unknown spec for proof structure: " + self.specname)
            root = StructuredProofNode("Safety", self.safety)
            nodes = []
            # actions = self.spec_config["actions"]
            # return

        ###########
        ###########

        # root_obligation = ("Safety", safety)
        # Optionally save proof structure as DOT graph.
        # proof.save_as_dot("benchmarks/" + self.specname + "_ind-proof-tree")

        proof = None

        #
        # Handle interactive proof tree commands.
        #

        # Load parsed spec and vars appearing in actions and lemma defs.
        # TODO: Eventually we want to actually implement the more precise slicing
        # technique here, that projects out variables based on a more accurate data flow
        # computation i.e. taking into account the cone of influence of modified variables 
        # that appear in a target lemma. Right now we're just implementing a conservative 
        # approximation by looking at all non-UNCHANGED variables that appear in the transition
        # relation, plus all variables that appear in the target lemma.
        assert self.load_parse_tree
        vars_in_action = {}
        vars_in_action_non_updated = {}
        vars_in_lemma_defs = {}
        lemma_action_coi = {}
        action_updated_vars = {}

        # Override above and try to just extract all actions directly from the spec, based on
        # the 'Action' suffix naming convention.
        actions_from_spec = []
        for udef in self.tla_spec_obj.get_all_user_defs(level="2"):
            if udef.endswith("Action"):
                # print("ACTION:", udef)
                actions_from_spec.append(udef)
        if len(actions_from_spec):
            actions = actions_from_spec




        # Extract variables per action.
        all_state_vars = self.tla_spec_obj.get_all_vars()
        for action in actions:
            # print(f"{action} action: extracting vars")
            try:
                vars_in_action[action] = self.tla_spec_obj.get_vars_in_def(action)[0]
                # vars_in_action_non_updated[action] = self.tla_spec_obj.get_vars_in_def(action, ignore_update_expressions=)[0]
                print(f"Vars in action '{action}' ({len(vars_in_action[action])}):", vars_in_action[action])
            except Exception as e:
                # Fall back to just adding all variables for now.
                # raise e
                print(f"Action '{action}': failed to get variables in action. Using all state variables ({len(all_state_vars)}).")
                vars_in_action[action] = all_state_vars

        # Extract variables per lemma.
        for udef in self.tla_spec_obj.get_all_user_defs(level="1"):
            # Getting all level 1 definitions should be sufficient here.
            # Invariants (i.e. state predicates) should all be at level 1.
            # if udef.startswith("H_"):
            try:
                vars_in_lemma_defs[udef] = self.tla_spec_obj.get_vars_in_def(udef)[0]
                print(udef, vars_in_lemma_defs[udef])
            except:
                print(f"Def '{udef}': failed to get variables for. Using all state variables.")
                vars_in_lemma_defs[udef] = all_state_vars


        # Compute COI for each action-lemma pair
        # Refer to actions by their underlying operator definition for computing COI.
        actions_real_defs = [a.replace("Action", "") for a in actions]
        lemma_action_coi = {}
        all_vars_in_lemma_defs = set(vars_in_lemma_defs.keys())
        try:
            print("Computing COI table")
            lemma_action_coi = self.tla_spec_obj.compute_coi_table(all_vars_in_lemma_defs, actions_real_defs)
        except Exception as e:
            print(e)
            print("ERROR: Failed to generate lemma-action COI table, defaulting to all variable COI.")
            # Fall back to most conservative COI computation, including all vars.
            for a in actions:
                lemma_action_coi[a.replace("Action", "")] = {lemma:all_state_vars for lemma in vars_in_lemma_defs.keys()}


        build_coi_closure = False
        if build_coi_closure:
            print("======= BACKWARDS COI CLOSURE =========")
            G_coi_closure = graphviz.Digraph()
            coi_closure_edges = self.tla_spec_obj.compute_backwards_coi_closure(lemma_action_coi, self.safety)
            # Generate simple DOT graph.
            for e in coi_closure_edges:
                e0_str = "_".join(sorted(list(e[1])))
                e1_str = "_".join(sorted(list(e[0])))
                G_coi_closure.edge(e0_str, e1_str, label=f"{e[2]}")
            G_coi_closure.render(f"notes/{self.specname}_coi_closure", view=False)

        # TODO: Eventually have COI properly drill down into action definitions.
        orig_keys = list(lemma_action_coi.keys())
        for a in orig_keys:
            # Rename actions to original.
            lemma_action_coi[a + "Action"] = lemma_action_coi[a]
        for a in orig_keys:
            del lemma_action_coi[a]
        
        # Optionally print out full action-lemma COI table.
        # print("LEMMA COI", lemma_action_coi)
        # for a in lemma_action_coi:
        #     print("ACTION: ", a)
        #     for l in lemma_action_coi[a]:
        #         if "H_" in l:
        #             print("  ", l, lemma_action_coi[a][l])

        # Optionally reload proof structure from locally defined template.
        if self.proof_tree_cmd and self.proof_tree_cmd[0] in ["reload", "reload_proof_struct", "check_proof_apalache", "check_proof_tlc"]:
            logging.info(f"Reloading entire proof and re-generating CTIs.")
            proof = StructuredProof(root, 
                                    specname = self.specname, 
                                    actions=actions, 
                                    nodes=nodes, 
                                    safety=self.safety)
            proof.vars_in_action = vars_in_action
            proof.vars_in_lemma_defs = vars_in_lemma_defs
            proof.lemma_action_coi = lemma_action_coi

            # Re-generate CTIs.
            if self.proof_tree_cmd[0] == "reload":
                proof.gen_ctis_for_node(indgen, root)
        else:
            # Otherwise load serialized proof object.
            # f = open(f"{self.proof_base_filename}.json")
            # proof_obj = json.load(f)
            # f.close()

            # Load from pickle file for now.
            logging.info(f"Loading proof from pickle file: {self.proof_base_filename}.pickle")
            f = open(f"{self.proof_base_filename}.pickle", 'rb')
            proof = pickle.load(f)

        root = proof.root
        proof.save_tex = True

        # Add spec definitions.
        if self.load_parse_tree:
            proof.spec_defs = self.spec_defs

        if self.proof_tree_cmd and self.proof_tree_cmd[0] == "check_proof_apalache":
            # Allow lemma filter to be passed in as comma separated lemma list.
            print("Checking all proof obligations with Apalache.")
            lemma_filter = None
            if len(self.proof_tree_cmd) > 1:
                lemma_filter = self.proof_tree_cmd[1].split(",")
                print("Using lemma filter for proof checking:", lemma_filter)
            proof.apalache_check_all_nodes(save_dot=self.save_dot, lemma_filter=lemma_filter)
            return

        if self.proof_tree_cmd and self.proof_tree_cmd[0] == "check_proof_tlc":
            print("Checking all proof obligations with TLC.")
            start_node = proof.root

            # Retrieve all proof graph nodes.
            nodes = []
            seen = set()
            proof.walk_proof_graph(proof.root, seen=seen, all_nodes=nodes)

            # Check all proof graph nodes.
            for n in nodes:
                # proof.get_node_by_name()
                node = proof.get_node_by_name(proof.root, n.name)
                print(node.expr)
                proof.gen_ctis_for_node(self, node, target_node_name=node.name)

            errs = []
            print("--- Status of proof obligations after checking.")
            for n in nodes:
                for a in n.ctis:
                    num_remaining_ctis = len(n.ctis[a]) - len(n.ctis_eliminated[a])
                    if num_remaining_ctis > 0:
                        print((n.expr, a), ": remaining CTIS:", num_remaining_ctis, "(ERROR)")
                        errs.append((n.expr, a))
                    else:
                        print((n.expr, a), ": no remaining CTIS.")

            print(f"Checked proof obligations for {len(nodes)} lemmas of {self.specname} proof graph.")
            if len(errs) > 0:
                print(f"--- Found {len(errs)} errors when checking proof graph obligations:")
                for e in errs:
                    print(e)
            else:
                print(f"No errors found in proof checking! (Obligations checked for {len(nodes)} lemmas).")
            return

        proof.save_proof(include_dot=self.save_dot)

        run_server = True
        if run_server:
            import flask
            from flask import Flask
            from flask_cors import CORS
            app = Flask(__name__, static_folder="benchmarks")
            CORS(app)
            import threading

            self.active_ctigen_threads = set()

            @app.route('/', defaults={'path': ''})
            @app.route('/<path:path>')
            def home(path):
                # For empty path, send base spec HTML.
                if path == "":
                    return flask.send_from_directory('benchmarks', f"{self.specname}.proof.html")
                return flask.send_from_directory('benchmarks', path)

            @app.route('/api/getProofGraph')
            def getProofGraph():
                proof_json = proof.serialize(include_ctis=True, cti_hashes_only=True)
                response = flask.jsonify({'ok': True, 'proof_graph': proof_json})
                response.headers.add('Access-Control-Allow-Origin', '*')
                # Save TLAPS proof.
                if "tlaps_proof_config" in self.spec_config:
                    proof.to_tlaps_proof_skeleton(self.spec_config["tlaps_proof_config"])
                # Save Apalache inductive proof obligations.
                proof.to_apalache_proof_obligations()
                return response

            @app.route('/api/getNode/<expr>')
            def getNode(expr):
                node = proof.get_node_by_name(proof.root, expr)
                if node is None:
                    print(f"Node '{expr}' not found.")
                    response = flask.jsonify({'ok': False})
                    response.headers.add('Access-Control-Allow-Origin', '*')
                else:
                    response = flask.jsonify(node.serialize())
                    response.headers.add('Access-Control-Allow-Origin', '*')
                return response
            
            @app.route('/api/addNode/<expr>')
            def addNode(expr):
                # Create new node without any children or edges to other nodes.
                newNode = StructuredProofNode(expr.replace("H_", ""), expr)
                # newNode.children = dict()
                proof.nodes.append(newNode)
                print("Adding new proof node, expr:", newNode.expr, "name:", newNode.name)
                proof.save_proof()
                response = flask.jsonify({'ok': True})
                response.headers.add('Access-Control-Allow-Origin', '*')
                return response

            @app.route('/api/addSupportEdge/<target>/<action>/<src>')
            def addSupportEdge(target, action, src):
                target_node = proof.get_node_by_name(proof.root, target)

                if target_node is None:
                    print(f"Target node '{target}' not found.")
                    response = flask.jsonify({'ok': False})
                    response.headers.add('Access-Control-Allow-Origin', '*')
                    return response

                src_node = proof.get_node_by_name(proof.root, src)

                if src_node is None:
                    print(f"Target node '{src}' not found.")
                    response = flask.jsonify({'ok': False})
                    response.headers.add('Access-Control-Allow-Origin', '*')
                    return response

                print("Target:", target_node, target_node.name)
                print("Source:", src_node, src_node.name)
                print("Source:", src_node, src_node.name)

                # print("Target children:", target_node.children, id(target_node.children))
                # print("Source children:", src_node.children, id( src_node.children))

                if action not in target_node.children:
                    target_node.children[action] = []
                target_node.children[action].append(src_node)

                proof.save_proof()

                response = flask.jsonify({'ok': True})
                response.headers.add('Access-Control-Allow-Origin', '*')
                return response

            @app.route('/api/deleteSupportEdge/<target>/<action>/<src>')
            def deleteSupportEdge(target, action, src):
                target_node = proof.get_node_by_name(proof.root, target)
                src_node = proof.get_node_by_name(proof.root, src)
                print("Target:", target_node)
                print("Source:", src_node)
                
                response = flask.jsonify({'ok': False})
                response.headers.add('Access-Control-Allow-Origin', '*')

                if target_node is None or src_node is None:
                    print("Target or source node not found.")
                    return response

                if action not in target_node.children:
                    print("Action does not exist.")
                    return response

                # Delete the appropriate child node.
                target_node.children[action] = [c for c in target_node.children[action] if c.name != src]
                proof.save_proof()

                response = flask.jsonify({'ok': True})
                response.headers.add('Access-Control-Allow-Origin', '*')
                return response

            @app.route('/api/getActiveCtiGenThreads')
            def getActiveCtiGenThreads():
                response = flask.jsonify({
                    'ok': True, 
                    'active_threads': list(self.active_ctigen_threads),
                    'current_config_instance_ind': proof.current_config_instance_index,
                    'num_config_instances': len(self.get_config_constant_instances()),
                    'ctigen_state': proof.ctigen_state
                })
                response.headers.add('Access-Control-Allow-Origin', '*')
                return response

            @app.route('/api/genCtis/<flag>/<expr>')
            def genCtis(flag, expr):
                logging.info(f"genCtis({flag}, {expr})")
                print(flag, expr)

                response = flask.jsonify({'ok': True, 'expr': expr})
                response.headers.add('Access-Control-Allow-Origin', '*')

                self.active_ctigen_threads.add(expr)

                # Launch proof generation process in separate thread and return response right away.
                def ctigen_fn():
                    subtree = flag == "subtree"
                    start = time.time()

                    start_node = proof.get_node_by_name(proof.root, expr)
                    if start_node is None:
                        print(f"no node found: {expr}")
                        return
                    if subtree:
                        proof.gen_ctis_for_node(self, start_node)
                    else:
                        proof.gen_ctis_for_node(self, start_node, target_node_name=expr)
                    duration = time.time() - start
                    print("-- Finished generating CTIs for node:", expr, f" in {round(duration,1)}s --")
                    self.active_ctigen_threads.remove(expr)

                p = threading.Thread(target=ctigen_fn) # create a new Process
                p.start()

                return response
            
            # Start up server API.
            app.run(debug=False, port=9000)
            return


            # logging.info(f"Loading proof from object file: {self.proof_base_filename}.json")
            # proof = StructuredProof(load_from_obj=proof_obj)

        # Re-save proof at this point.
        self.save_proof(proof, include_dot=self.save_dot)
        if not self.proof_tree_cmd:
            return
        
        logging.info(f"Handling proof tree command: {self.proof_tree_cmd[0]}")


        if self.proof_tree_cmd[0] == "ctigen_all":
            logging.info("(proof_structure) [ctigen_all] Re-generating CTIs for all proof nodes.")
            proof.gen_ctis_for_node(root)

            # Save final proof html.
            proof.save_proof()

        elif self.proof_tree_cmd[0] == "ctigen":
            proof_node_name = self.proof_tree_cmd[1]
            logging.info(f"(proof_structure) [ctigen] Re-generating CTIs for all proof node '{proof_node_name}'.")
            proof.gen_ctis_for_node(root, target_node_name=proof_node_name)

            # Save final proof html.
            proof.save_proof()

        elif self.proof_tree_cmd[0] in ["add_child", "remove_child"]:
            cmd = self.proof_tree_cmd[0]
            parent_proof_node_name = self.proof_tree_cmd[1]
            child_expr = self.proof_tree_cmd[2]
            child_name = child_expr[2:] # cut off the 'H_'.

            parent_node = proof.get_node_by_name(parent_proof_node_name)
            if parent_node is None:
                logging.info(f"No parent node {parent_proof_node_name} exists")
                return

            if cmd == "add_child":

                logging.info(f"(proof_structure) [add_child] Adding child to node '{parent_proof_node_name}'.")
                new_child = StructuredProofNode(child_name, child_expr)
                parent_node.children += [new_child]

                logging.info(f"Added new child node: {child_name}")

            if cmd == "remove_child":
                parent_node.children = [c for c in parent_node.children if c.name != child_name]
                logging.info(f"Removed child node: {child_name}")

            # Save final proof html.
            proof.save_proof()

        if self.proof_tree_cmd == None:
            logging.info("No proof tree command specified. Terminating.")

        return
    
    def proofgraph_filename(self):
        fname = f"{self.specdir}/{self.specname}_ind-proof-tree-sd{self.seed}.proofgraph.json"
        return fname

    def clean_proof_graph(self):
        """ Clear out any persisted proof graphs. """
        fname = self.proofgraph_filename()
        # Delete proof graph object if exists.
        logging.info("Cleaning proof graph file: '{fname}'")
        try:
            os.remove(fname)
        except OSError:
            pass

    def proof_graph_lemma_nodes(self):
        lemma_nodes = [n for n in self.proof_graph["nodes"] if "is_lemma" in self.proof_graph["nodes"][n]]
        return lemma_nodes
    
    def proof_graph_failed_lemma_nodes(self):
        return [n for n in self.proof_graph["nodes"].keys() if "is_lemma" in self.proof_graph["nodes"][n] and "failed" in self.proof_graph["nodes"][n]]

    def persist_proof_graph(self, roundi):
        # Save the generated proof graph to disk.
        fname = self.proofgraph_filename()
        proof_graph_object = {}
        proof_graph_object["proof_graph"] = self.proof_graph
        proof_graph_object["strengthening_conjuncts"] = self.strengthening_conjuncts
        proof_graph_object["roundi"] = roundi
        proof_graph_object["num_rounds"] = self.num_rounds
        proof_graph_object["num_iters"] = self.num_iters
        proof_graph_object["seed"] = self.seed
        proof_graph_object["stats"] = {
            "num_lemma_nodes": len(self.proof_graph_lemma_nodes()),
            "num_failed_lemma_nodes": len(self.proof_graph_failed_lemma_nodes()),
            "state_cache_duration_secs": indgen.get_state_cache_duration(),
            "invcheck_duration_secs": indgen.get_invcheck_duration(),
            "ctielimcheck_duration_secs": indgen.get_ctielimcheck_duration(),
            "total_duration_secs": time.time() - self.invgen_tstart,
            "date": datetime.datetime.now().strftime("%Y-%m-%d %H:%M:%S")
        }
        with open(fname, 'w') as f:
            json.dump(proof_graph_object, f, indent=2)

    def load_proof_graph(self):
        # Try to load the proof graph from disk.
        fname = self.proofgraph_filename()
        try:
            logging.info(f"Trying to load proof graph from '{fname}'")
            with open(fname) as f:
                proof_obj = json.load(f)
                self.proof_graph = proof_obj["proof_graph"]
                self.strengthening_conjuncts = proof_obj["strengthening_conjuncts"]
                logging.info(f"Reloaded persisted proof graph from '{fname}'")
        except Exception as e:
            logging.info(f"No proof graph loaded from '{fname}': {e}")

    def auto_check_simulation_bound(self):
        # Prototype of auto-tuning simulation bounds.
        # TODO: Would need to make simulation work properly with checkAllInvariants mode I think.
        logging.info("Checking simulation bound for all invariants.")
        use_pred_identifiers = self.use_fast_pred_eval
        boolean_style = "tla"
        ninvs = 1000
        logging.info("Generating %d candidate invariants." % ninvs)
        all_invs = mc.generate_invs(
            self.preds, ninvs, min_num_conjuncts=2, max_num_conjuncts=3,quant_vars=self.quant_vars, 
            boolean_style = boolean_style,
            use_pred_identifiers=use_pred_identifiers)
        invs = all_invs["raw_invs"]
        depth = 20
        sat_inv_table = []
        logging.info("CHECKING SIMULATION INV BOUNDS\n---------------------")
        # nums = [10,100,200,1000,2000,8000]
        # state_nums = [1000,2000,5000,7500,10000,15000,25000,30000,40000,50000,75000,90000]
        state_nums = [10000,50000,100000,200000]
        for state_num in state_nums:
            num = state_num // tlc_workers // depth
            simulation_inv_tlc_flags=f"-depth {depth} -simulate num={num}"
            logging.info(f"(num_states={state_num},depth={depth},num={num},workers={tlc_workers})")
            main_sat_invs = self.check_invariants(invs, tlc_workers=tlc_workers, tlc_flags=simulation_inv_tlc_flags)
            # sat_invs = set([f"Inv{iv[0]}" for iv in main_sat_invs])
            logging.info(f"Found {len(main_sat_invs)} sat invariants. (num={num})")
            logging.info("\n= = = = =\n")
            sat_inv_table.append(len(main_sat_invs))
        print("sat inv counts:")
        for ind,num in enumerate(state_nums):
            print("num states=", num, ", num_sat_invs=", sat_inv_table[ind])
                    

    def do_invgen_proof_tree_mode(self):
        """ Do localized invariant synthesis based on an inductive proof graph structure."""

        logging.info("Starting automatic invariant generation in inductive proof tree mode.")

        self.auto_lemma_action_decomposition = True

        # TODO: Make node/action configurable.
        # target_node = ("NewestVALMsgImpliesAllValidNodesMatchVersion", "H_NewestVALMsgImpliesAllValidNodesMatchVersion")
        # target_node = ("WriteNodeWithAllAcksImpliesAllAliveAreValid", "HH_WriteNodeWithAllAcksImpliesAllAliveAreValid")
        # target_node = ("Safety", "HConsistent", "")
        # target_action = "HSendValsAction"
        # target_action = "HRcvValAction"

        self.reparsing_duration_secs = 0

        # Start with the root safety property.
        root_node = ("Safety", self.safety, "")

        # self.lemma_obligations = [("Safety", self.safety)]
        # self.lemma_obligations = [target_node]

        # The set of all generated invariant candidates across all rounds.
        self.all_generated_inv_candidates = set()

        self.curr_obligation_depth = 0

        self.invgen_tstart = time.time()

        # TODO: Optionally reload from file for interactive mode.
        self.proof_graph = {
            "edges": [], 
            "nodes": {}, 
            "safety": self.safety
        }
        self.proof_graph["nodes"][root_node[0]] = {
            "discharged": False, 
            "is_lemma": True, 
            "expr": root_node[1],
            "order": 1,
            "depth": self.curr_obligation_depth,
            "is_root": True
        }

        # For proof tree we look for single step inductive support lemmas.
        self.simulate_depth = 1

        count = 0

        logging.info("Extracting variables present in each grammar predicate.")
        vars_in_preds = self.extract_vars_from_preds()

        vars_in_action_local_preds = {}
        if "action_local_preds" in self.spec_config:
            logging.info("Extracting variables present in action-local grammar predicates.")
            for a in self.spec_config["action_local_preds"]:
                logging.info(f"Extracting variables in action-local grammar predicates for action '{a}'.")
                vars_in_action_local_preds[a] = self.extract_vars_from_preds(preds=self.spec_config["action_local_preds"][a])

        # for p in sorted(vars_in_preds.keys()):
            # print(p, self.preds[p], vars_in_preds[p])
        
        # Maintain a potential list of lemma-action proof obligations that could not be discharged
        # successfully after some number of iteration attempts.
        failed_obligations = set()

        elim_round_failed = False

        # Stores map of state variables projections of the state space that we have already cached.
        self.state_projection_cache = {}


        ###
        ## We probably want to maintain a queue of proof obligations to discharge, to keep this organized
        ## cleanly, and each round will work on discharging one proof obligation.
        ###

        # Actually, can we just store the proof graph itself, with obligation status at each node?
        self.proof_obligation_queue = [root_node]
        # self.proof_obligation_queue.append(target_node)


        self.spec_obj_with_lemmas = self.tla_spec_obj

        # Re-parse spec object to include definitions of any newly generate strengthening lemmas.
        # if len(self.strengthening_conjuncts) > 0:
        #     specname = f"{self.specname}_lemma_parse"
        #     rootpath = f"benchmarks/{specname}"
        #     self.make_check_invariants_spec([], rootpath, defs_to_add=self.strengthening_conjuncts)

        #     logging.info("Re-parsing spec for any newly discovered lemma definitions.")
        #     spec_obj_with_lemmas = tlaparse.parse_tla_file(self.specdir, specname)
        
        self.strengthening_conjuncts = []

        self.latest_roundi = 0


        if self.persistent_proof_tree_mode:
            self.load_proof_graph()
        else:
            self.clean_proof_graph()

        # Initial rendering.
        if self.save_dot and len(self.proof_graph["edges"]) > 0:
            self.render_proof_graph()

        for roundi in range(self.num_rounds):
            logging.info("### STARTING ROUND %d" % roundi)
            logging.info("Num remaining lemma obligations %d" % len(self.proof_obligation_queue))
            self.latest_roundi = roundi
            if len(self.proof_obligation_queue) == 0:
                logging.info("No remaining lemma obligations. Stopping now!")
                return
            
            logging.info("ALL proof graph nodes")
            lemma_nodes = [n for n in self.proof_graph["nodes"] if "is_lemma" in self.proof_graph["nodes"][n]]
            for n in self.proof_graph["nodes"]:
                ntype = "Lemma" if "is_lemma" in self.proof_graph["nodes"][n] else "Action"
                print(f" ({ntype})", n, self.proof_graph["nodes"][n])
            logging.info(f"Total lemma nodes: {len(lemma_nodes)}")


            # Pick a next proof graph obligation to discharge.
            # TODO: Consider obligations marked as failed when choosing.
            def valid_proof_node(node):
                # Criteria for next proof obligation to be chosen.
                return ("is_lemma" in node) and (not node["discharged"]) and ("failed" not in node)
            
            undischarged = [n for n in self.proof_graph["nodes"].keys() if valid_proof_node(self.proof_graph["nodes"][n])]
            logging.info(f"Remaining, undischarged lemma obligations: {len(undischarged)}")

            failed = [n for n in self.proof_graph["nodes"].keys() if "failed" in self.proof_graph["nodes"][n]]
            logging.info(f"Failed lemma obligations: {len(failed)}")
            for f in failed:
                print(" - ", f)

            if len(undischarged) == 0:
                logging.info("All proof obligations discharged.")
                break

            # Choose next most recently added obligation.
            curr_obligation = sorted(undischarged, key = lambda n : self.proof_graph["nodes"][n]["order"])[0]
            # for n in self.proof_graph["nodes"]:
            #     node = self.proof_graph["nodes"][n]
            #     if "is_lemma" in node and not node["discharged"]:
            #         curr_obligation = n
            #         break

            # Set current depth.
            self.curr_obligation_depth = self.proof_graph["nodes"][curr_obligation]["depth"]

            logging.info("Generating CTIs.")
            t0 = time.time()
            # curr_obligation = self.proof_obligation_queue.pop(0)
            print("Current obligation:", curr_obligation)
            # k_ctis = self.generate_ctis(props=[("LemmaObligation" + str(count), curr_obligation[1])])
            curr_obligation_expr = self.proof_graph["nodes"][curr_obligation]["expr"]
            curr_obligation_pred_tup = (curr_obligation, curr_obligation_expr, "")

            cobjs = list(self.get_config_constant_instances())
            logging.info(cobjs)
            for c in cobjs:
                print(c)
            # cobj = cobjs[-1]
            # print("constant obj:", cobj)

            # Start with CTIs for smallest cobj you can find.
            # EXPERIMENTAL
            # for c in cobjs:
            #     print("Trying constant obj:", c)
            #     k_ctis, k_cti_traces = self.generate_ctis(props=[curr_obligation_pred_tup], constants_obj=c)
            #     print(f"Found {len(k_ctis)} CTIs")
            #     if len(k_ctis) > 0:
            #         print("constant obj:", c)
            #         break
                
            k_ctis, k_cti_traces = self.generate_ctis(props=[curr_obligation_pred_tup])
            count += 1

            # for kcti in k_ctis:
                # print(str(kcti))
            logging.info("Number of total unique k-CTIs found: {}. (took {:.2f} secs)".format(len(k_ctis), (time.time()-t0)))

            subround = 0

            # Limit number of CTIs if necessary.
            if len(k_ctis) > self.MAX_NUM_CTIS_PER_ROUND:
                logging.info(f"Limiting num k-CTIs to {self.MAX_NUM_CTIS_PER_ROUND} of {len(k_ctis)} total found.")
                # Sort CTIS to give a consistent order first, and then shuffle to ensure sample diversity.
                sorted_k_ctis = sorted(list(k_ctis))
                random.shuffle(sorted_k_ctis)
                k_ctis = set(sorted_k_ctis[:self.MAX_NUM_CTIS_PER_ROUND])
            
            if len(k_ctis) == 0:
                is_root_node = self.proof_graph["nodes"][curr_obligation]["order"] == 1
                if roundi==0 and is_root_node:
                    logging.info("No initial CTIs found. Marking invariant as inductive and exiting.")
                    self.is_inductive = True
                    return
                else:
                    logging.info("Current obligation appears likely to be inductive!")
                    self.proof_graph["nodes"][curr_obligation]["discharged"] = True
                logging.info("")
                continue
            else:
                logging.info("Not done. Current invariant candidate is not inductive.")

            self.total_num_cti_elimination_rounds = (roundi + 1)


            preds = self.preds
            state_vars_in_local_grammar = self.state_vars
            state_vars_not_in_local_grammar = set(self.state_vars)

            while len(k_ctis) > 0:
                logging.info(f"Starting subround {subround} with {len(k_ctis)} k_ctis")

                k_ctis_to_eliminate = k_ctis

                cti_action_invs_found = set()

                # Break down CTIs by lemma-action pair.
                for kcti in k_ctis_to_eliminate:
                    # print(str(kcti))
                    if kcti.inv_name == "Safety":
                        cti_action_invs_found.add((self.safety, kcti.action_name))
                    else:
                        cti_action_invs_found.add((kcti.inv_name, kcti.action_name))
                logging.info(f"{len(cti_action_invs_found)} distinct k-CTI lemma-action proof obligations found:")
                cti_action_invs_found = sorted(cti_action_invs_found, key = lambda c : c[1]) # sort by action name for consistent odering of proof obligations.

                # Optional CTI action filter.
                # action_filter = ["HRcvValAction", "HSendValsAction", "HWriteAction", "HRcvInvAction", "HRcvInvNewerAction"]
                # hermes action filter.
                if self.action_filter is not None:
                    logging.info(f"Using CTI action_filter: {self.action_filter}")
                    # self.action_filter = [
                    #     "HRcvValAction", 
                    #     "HSendValsAction"
                    #     "HWriteAction", 
                    #     "HRcvInvAction", 
                    #     "HCoordWriteReplayAction", 
                    #     "NodeFailureAction", 
                    #     "HFollowerWriteReplayAction", 
                    #     "HReadAction",

                    #     # Last 2 actions to add.
                    #     "HRcvAckAction"
                    #     # "HRcvInvNewerAction"
                    # ]
                    # cti_action_invs_found = [c for c in cti_action_invs_found if c[1] in action_filter]
                    cti_action_invs_found = [c for c in cti_action_invs_found if c[1] in self.action_filter]

                for kcti in cti_action_invs_found:
                    logging.info(f" - {kcti}")

                # Re-parse spec object to include definitions of any newly generate strengthening lemmas.
                # if len(self.strengthening_conjuncts) > 0:
                if len(self.proof_graph["nodes"]) > 0:
                    specname = f"{self.specname}_lemma_parse"
                    rootpath = f"benchmarks/{specname}"
                    # self.make_check_invariants_spec([], rootpath, defs_to_add=self.strengthening_conjuncts + [curr_obligation])
                    # self.make_check_invariants_spec([], rootpath, defs_to_add=[curr_obligation_pred_tup] + self.strengthening_conjuncts)
                    node_conjuncts = [(n, self.proof_graph["nodes"][n]["expr"], "") for n in self.proof_graph["nodes"] if "is_lemma" in self.proof_graph["nodes"][n]]
                    self.make_check_invariants_spec([], rootpath, defs_to_add=node_conjuncts)
                    # self.make_check_invariants_spec([], rootpath, defs_to_add=self.strengthening_conjuncts)

                    logging.info("Re-parsing spec for any newly discovered lemma definitions.")
                    s1 = time.time()
                    self.spec_obj_with_lemmas = tlaparse.parse_tla_file(self.specdir, specname)
                    self.reparsing_duration_secs += (time.time() - s1)
                    logging.info("Done re-parsing. Total time spent parsing so far: {:.2f}s".format(self.reparsing_duration_secs))

                defs = self.spec_obj_with_lemmas.get_all_user_defs(level="1")
                # for d in defs:
                    # print(d)
                
                # if len(cti_action_lemmas_with_grammars) == 0:
                if len(cti_action_invs_found) == 0:
                    print("No more current outstanding CTI lemma actions with local grammars.")
                    self.proof_graph["nodes"][curr_obligation]["discharged"] = True
                    break

                # k_cti_lemma_action = random.choice(cti_action_lemmas_with_grammars)
                k_cti_lemma_action = cti_action_invs_found[0]
                (k_cti_lemma, k_cti_action) = k_cti_lemma_action
                print(f"Chose {k_cti_lemma_action} proof obligation")

                lemma_name = "Safety" if k_cti_lemma == self.safety else k_cti_lemma
                action_node = f"{lemma_name}_{k_cti_action}"
                
                # Filter CTIs based on this choice.
                cti_filter = lambda c  : (c.inv_name == k_cti_lemma or (c.inv_name == "Safety" and k_cti_lemma == self.safety)) and c.action_name == k_cti_action
                k_ctis_to_eliminate = [c for c in k_ctis if cti_filter(c)]
                # k_ctis_remaining = [c for c in k_ctis if not cti_filter(c)]
                logging.info(f"Have {len(k_ctis_to_eliminate)} total k-CTIs after filtering to {k_cti_lemma_action}.")

                # Limit number of CTIs if necessary.
                # if len(k_ctis_to_eliminate) > self.MAX_NUM_CTIS_PER_ROUND:
                #     logging.info(f"Limiting num k-CTIs to {self.MAX_NUM_CTIS_PER_ROUND} of {len(k_ctis_to_eliminate)}.")
                #     # Sort CTIS first to ensure we always select a consistent subset.
                #     k_ctis_to_eliminate = k_ctis_to_eliminate[:self.MAX_NUM_CTIS_PER_ROUND]


                logging.info(f"Computing COI for {(k_cti_lemma, k_cti_action)}")
                # actions_real_defs = [a.replace("Action", "") for a in actions]
                lemma_action_coi = {}

                k_cti_action_opname = k_cti_action.replace("Action", "")
                ret = self.spec_obj_with_lemmas.get_vars_in_def(k_cti_action_opname)
                vars_in_action,action_updated_vars = ret
                print("vars in action:", vars_in_action)
                print("action updated vars:", action_updated_vars)
                vars_in_action_non_updated,_ = self.spec_obj_with_lemmas.get_vars_in_def(k_cti_action_opname, ignore_update_expressions=True)
                logging.info(f"Getting variables in lemma definition: {k_cti_lemma}")
                vars_in_lemma_defs = self.spec_obj_with_lemmas.get_vars_in_def(k_cti_lemma)[0]

                lemma_action_coi = self.spec_obj_with_lemmas.compute_coi(None, None, None,action_updated_vars, vars_in_action_non_updated, vars_in_lemma_defs)
                print("Lemma-action COI")
                print(lemma_action_coi)
                # for ind,p in enumerate(self.preds):
                    # print(p, vars_in_preds[ind], lemma_action_coi)

                #
                # Filter predicates based on this COI.
                #
                # We select only predicates that contain variable sets that are a subset of the COI.
                # If they, for example, contain a variable set with some variables in the COI and some not, then
                # we don't include that predicate.
                #
                # Note that the set subset operator is "<=" here.

                # Add in action specific predicates if they are given for this action.
                action_local_preds = []
                if "action_local_preds" in self.spec_config and k_cti_action in self.spec_config["action_local_preds"]:
                    action_local_preds = self.spec_config["action_local_preds"][k_cti_action]

                all_preds_unfiltered = self.preds + action_local_preds

                # Filter preds.
                preds = [p for (pi,p) in enumerate(self.preds) if vars_in_preds[pi].issubset(lemma_action_coi)]
                action_local_preds_filtered = [p for (pi,p) in enumerate(action_local_preds) if vars_in_action_local_preds[k_cti_action][pi].issubset(lemma_action_coi)]

                # Add in action local predicates.
                logging.info(f"Adding in {len(action_local_preds)} action local predicates for action '{k_cti_action}'.")
                preds = preds + action_local_preds_filtered

                # If we have disabled grammar slicing, then we just forcibly use all predicates.
                if self.disable_grammar_slicing:
                    logging.info("Grammar slicing disabled, so we are using all predicates.")
                    preds = all_preds_unfiltered

                pct_str = "{0:.1f}".format(len(preds)/len(all_preds_unfiltered) * 100)
                logging.info(f"{len(preds)}/{len(all_preds_unfiltered)} ({pct_str}% of) predicates being used based on COI slice filter.")

                cache_with_ignored_vars = [v for v in self.state_vars if v not in lemma_action_coi]

                # If we explicitly disable slicing here, then we just always use the full set of variables.
                if self.disable_state_cache_slicing:
                    logging.info("State cache slicing disabled, so we are just using the all vars in the slice.")
                    cache_with_ignored_vars = []

                # self.proof_graph["edges"].append((action_node, lemma_name))
                # self.proof_graph["nodes"][action_node] = {"ctis_remaining": 1000, "coi_vars": lemma_action_coi}  # initialize with positive CTI count, to be updated later.
                tstart = time.time()


                # TODO: Way to show progress while action node is being worked on.
                if self.auto_lemma_action_decomposition:
                    # Add initial lemma-action edges for the proof graph.
                    e1 = (action_node, f"{lemma_name}")
                    self.proof_graph["edges"].append(e1)
                    print("ACTION NODE:", action_node)
                    self.proof_graph["nodes"][action_node] = {
                        "ctis_remaining": len(k_ctis_to_eliminate), 
                        "coi_vars": list(lemma_action_coi),
                        "num_grammar_preds": len(preds),
                        "is_action": True,
                        "discharged": False
                    }
                    self.proof_graph["curr_node"] = action_node

                    # Render to show progress dynamically.
                    self.render_proof_graph()

                self.latest_elimination_iter = 1

                # Run CTI eliminatinon.
                ret = self.eliminate_ctis(k_ctis_to_eliminate, self.num_invs, roundi, tlc_workers=self.tlc_workers, subroundi=subround, preds=preds, 
                                            append_inv_round_id=True, cache_states_with_ignored_vars=cache_with_ignored_vars)
                subround += 1

                logging.info(f"[ END CTI elimination Round {roundi}, subround {subround}. ]")

                # Update timing spent on proof node.
                if action_node in self.proof_graph["nodes"]:
                    self.proof_graph["nodes"][action_node]["time_spent"] = time.time() - tstart
                    self.proof_graph["nodes"][action_node]["latest_elimination_iter"] = self.latest_elimination_iter


                if self.save_dot and len(self.proof_graph["edges"]) > 0:
                    # Render updated proof graph as we go.
                    self.render_proof_graph()

                            
                # if self.persistent_proof_tree_mode:
                # Persist proof graph, in case we want to reload it later.
                self.persist_proof_graph(roundi)

                # If we did not eliminate all CTIs in this round, then exit with failure.
                if ret == None:
                    logging.info(f"Could not eliminate all CTIs in this round. Exiting with failure and marking {curr_obligation} as failed.")
                    # Mark the proof node as failed.
                    self.proof_graph["nodes"][curr_obligation]["failed"] = True
                    self.proof_graph["nodes"][action_node]["failed"] = True
                    break
                else:
                    # Successfully eliminated all CTIs.
                    logging.info(f"Successfully eliminated all CTIs in this subround, for obligation {curr_obligation}.")
                    pass
                    # print("Adding new proof obligations:" + str(len(self.strengthening_conjuncts)))
                    # self.lemma_obligations += self.strengthening_conjuncts
                    # for support_lemma in self.strengthening_conjuncts:
                        # Check for existence of the predicate expression in existing lemma set.
                        # if support_lemma[1] not in [x[1] for x in self.all_generated_lemmas]:
                            # self.proof_graph["edges"].append((support_lemma,curr_obligation))
                            # self.all_generated_lemmas.add(support_lemma)
                
                logging.info(f"")

                # Determines whether we will re-generate CTIs after every new strengthening lemma discovered.
                k_ctis = [c for c in k_ctis if c not in k_ctis_to_eliminate]

                if len(k_ctis) == 0:
                    self.proof_graph["nodes"][curr_obligation]["discharged"] = True

            if self.save_dot and len(self.proof_graph["edges"]) > 0:
                # Render updated proof graph as we go.
                self.render_proof_graph()
            self.persist_proof_graph(roundi)

            logging.info(f"k-ctis remaining after Round {roundi} elimination step: {len(k_ctis)} (eliminated {len(k_ctis_to_eliminate)})")
            logging.info("")
            logging.info(f"(Round {roundi}) Cumulative CTI generation duration: %f secs.", indgen.get_ctigen_duration())
            logging.info(f"(Round {roundi}) Cumulative State caching duration: %f secs.", indgen.get_state_cache_duration())
            logging.info(f"(Round {roundi}) Cumulative Invariant checking duration: %f secs.", indgen.get_invcheck_duration())
            logging.info(f"(Round {roundi}) Cumulative CTI elimination checks duration: %f secs.", indgen.get_ctielimcheck_duration())

            logging.info("")

#
#
# Older logic that is based on using explicit local grammar defs.
#
# state_vars_in_local_grammar = self.state_vars
# state_vars_not_in_local_grammar = set(self.state_vars)
# if "local_grammars" in self.spec_config and k_cti_action in self.spec_config["local_grammars"]:
#     lgrammar = self.spec_config["local_grammars"][k_cti_action][k_cti_lemma]
#     if "max_depth" in lgrammar:
#         self.spec_config["max_tlc_inv_depth"] = lgrammar["max_depth"]

#     preds = lgrammar["preds"]
#     self.quant_vars = lgrammar["preds"]
#     self.quant_inv = lgrammar["quant_inv"]
#     self.initialize_quant_inv()
#     logging.info(f"Using local grammar for node ({k_cti_lemma}, {k_cti_action}) with {len(preds)} predicates.")

#     def svar_in_pred(v, p):
#         # avoid variables with shared substrings.
#         return f"{v}[" in p or f"{v} " in p or f"{v}:" in p

#     state_vars_in_local_grammar = set()
#     for p in (preds + [lgrammar["quant_inv"]]):
#         svars = []
#         for svar in self.state_vars:
#             if svar_in_pred(svar, p):
#                 svars.append(svar)
#                 state_vars_in_local_grammar.add(svar)
#                 state_vars_not_in_local_grammar.discard(svar)
#         # print(p, svars)
#     print(f"{len(state_vars_in_local_grammar)} state vars in local grammar:", state_vars_in_local_grammar)
#     print(f"{len(state_vars_not_in_local_grammar)} state vars not in local grammar:", state_vars_not_in_local_grammar)
#     cache_with_ignored_vars = state_vars_not_in_local_grammar
#

    def extract_vars_from_preds(self, preds=None):
        """ Compute the set of variables that appears in each grammar predicate."""

        # For each predicate, parse the set of state variables that appear in that predicate.
        if preds is None:
            pred_invs = [p for p in self.preds]
        else:
            pred_invs = preds

        # print(f"{len(pred_invs)} Predicates:")
        # for p in pred_invs:
        #     print(p)
        # self.check_invariants(pred_invs)
        specname = f"{self.specname}_extract_preds"
        rootpath = f"benchmarks/{specname}"
        invname_prefix = "PredInvDef"
        self.make_check_invariants_spec(pred_invs, rootpath, invname_prefix=invname_prefix)

        # Parse spec and get defs.
        tla_spec_obj = tlaparse.parse_tla_file(self.specdir, specname)
        self.spec_defs = tla_spec_obj.get_all_user_defs(level=["0","1"])
        self.tla_spec_obj = tla_spec_obj
        self.state_vars = self.tla_spec_obj.get_all_vars()
        vars_in_preds = {}
        for d in self.spec_defs:
            if d.startswith(invname_prefix):
                dvars,dvars_updated = self.tla_spec_obj.get_vars_in_def(d)
                # print("DEF:", d, dvars)
                invind = int(d.replace(invname_prefix, "")) 
                vars_in_preds[invind] = dvars
        return vars_in_preds

    def check_all_actions_parse(self):
        actions_from_spec = []
        for udef in self.tla_spec_obj.get_all_user_defs(level="2"):
            if udef.endswith("Action"):
                actions_from_spec.append(udef)

        for a in actions_from_spec:
            print("ACTION:", a)
            self.tla_spec_obj.get_vars_in_def(a)

    def do_invgen(self):
        # Record Java version for stat recording.
        self.save_java_version_info()

        if self.pregen_inv_cmd is not None:
            logging.info(f"Pre-generating invariants with command '{self.pregen_inv_cmd}'")
            self.pre_generate_invs()

        #
        # Check valuation of all predicates on reachable states.
        # (EXPERIMENTAL)
        #
        self.pred_vals = None
        # self.use_fast_pred_eval = True
        self.use_fast_pred_eval = False
        if self.use_fast_pred_eval:
            logging.info("Checking predicates on reachable states")
            self.pred_vals = self.check_predicates(self.preds)

        elim_round_failed = False

        self.all_generated_inv_candidates = set()

        # Stores map of state variables projections of the state space that we have already cached.
        self.state_projection_cache = {}

        for roundi in range(self.num_rounds):
            logging.info("---------")
            logging.info("### STARTING ROUND %d" % roundi)

            logging.info("Generating CTIs.")
            t0 = time.time()
            (k_ctis,k_cti_traces) = self.generate_ctis()
            logging.info("Number of total unique k-CTIs found: {}. (took {:.2f} secs)".format(len(k_ctis), (time.time()-t0)))

            # Limit number of CTIs if necessary.
            if len(k_ctis) > self.MAX_NUM_CTIS_PER_ROUND:
                logging.info(f"Limiting num k-CTIs to {self.MAX_NUM_CTIS_PER_ROUND} of {len(k_ctis)} total found.")
                # Sort CTIS first to ensure we always select a consistent subset.
                limited_ctis = sorted(list(k_ctis))[:self.MAX_NUM_CTIS_PER_ROUND]
                k_ctis = set(limited_ctis)
            
            if len(k_ctis) == 0:
                if roundi==0:
                    logging.info("No initial CTIs found. Marking invariant as inductive and exiting.")
                    self.is_inductive = True
                    return
                else:
                    logging.info("Invariant appears likely to be inductive!")
                break
            else:
                logging.info("Not done. Current invariant candidate is not inductive.")

            subround = 0
            while len(k_ctis) > 0:

                # Could potentially be a subset of the overall CTIs.
                logging.info(f"Total k-CTIs remaining at sub-round: {len(k_ctis)}")

                k_ctis_to_eliminate = k_ctis

                preds = self.preds

                self.total_num_cti_elimination_rounds = (roundi + 1)
                # ret = self.eliminate_ctis(k_ctis, self.num_invs, roundi, preds=preds, cache_states_with_ignored_vars=cache_with_ignored_vars)
                ret = self.eliminate_ctis(k_ctis_to_eliminate, self.num_invs, roundi, subroundi=subround, preds=preds, tlc_workers=self.tlc_workers)
                subround += 1
                
                # If we did not eliminate all CTIs in this round, then exit with failure.
                if ret == None:
                    logging.info(f"Could not eliminate all CTIs in this round (Round {roundi}). Exiting with failure.")
                    elim_round_failed = True
                    break

                # Determines whether we will re-generate CTIs after every new strengthening lemma discovered.
                k_ctis = [c for c in k_ctis if c not in k_ctis_to_eliminate]

                logging.info(f"k-ctis remaining after Round {roundi} elimination step: {len(k_ctis)} (eliminated {len(k_ctis_to_eliminate)})")
                logging.info("")
                logging.info(f"(Round {roundi}) Cumulative CTI generation duration: %f secs.", indgen.get_ctigen_duration())
                logging.info(f"(Round {roundi}) Cumulative State caching duration: %f secs.", indgen.get_state_cache_duration())
                logging.info(f"(Round {roundi}) Cumulative Invariant checking duration: %f secs.", indgen.get_invcheck_duration())
                logging.info(f"(Round {roundi}) Cumulative CTI elimination checks duration: %f secs.", indgen.get_ctielimcheck_duration())
            if elim_round_failed:
                break
            

        # Do a final inductive check.
        # TODO: Possibly run this CTI generation with a different seed.
        logging.info(f"Running final CTI generation step after {roundi} rounds.")
        (k_ctis,k_cti_traces) = self.generate_ctis()
        logging.info("Number of new k-CTIs found: %d" % len(k_ctis)) 
        if len(k_ctis) == 0:
            # Optional: try to drop first conjunct to minimize size of invariant.
            if self.try_final_minimize:
                logging.info("Trying to minimize final invariant slightly.")
                first_conjunct = self.strengthening_conjuncts[0]
                self.strengthening_conjuncts = self.strengthening_conjuncts[1:]
                (k_ctis,k_cti_traces) = self.generate_ctis()
                # If we can drop the first conjunct and remain inductive, then 
                # we drop it. Otherwise, we put it back and continue.
                if len(k_ctis) != 0:
                    logging.info("Failed to minimize final invariant, leaving as is.")
                    self.strengthening_conjuncts = [first_conjunct] + self.strengthening_conjuncts
                else:
                    logging.info("Successfully minimized final invariant by dropping conjunct.")

            self.is_inductive = True
            logging.info("REALLY DONE! Final invariant appears likely to be inductive!")


            # Optionally do final induction check with Apalache (experimental).
            if self.do_apalache_final_induction_check:
                logging.info("Doing final inductive check with Apalache.")
                lemmas = [("Safety",self.safety)] + self.strengthening_conjuncts
                defs = {name:exp for name,exp in lemmas}
                typeok = "TypeOK" # Apalache always uses normal TypeOK.
                defs["IndCurr"] = "\n  /\\ " +  " \n  /\\ ".join([typeok] + [name for name,exp in lemmas])
                # Check induction step.
                apalache = mc.Apalache(self.specdir)
                apa_subproc = apalache.check(self.specname, "IndCurr", "IndCurr", defs = defs, length=1)
                res = apalache.await_output(apa_subproc)
                logging.debug(res["stdout"])
                if not res["error"]:
                    logging.info("Apalache final induction check: PASS!")

                    # Try computing minimal support graph.
                    # TODO: Consider optionally enabling this once faster.
                    # inductive_inv = [self.typeok, "Safety"] + [c[0] for c in self.strengthening_conjuncts] 
                    # apalache.compute_minimal_support_graph(self.specname, defs, self.typeok, inductive_inv)
                else:
                    logging.info("Apalache final induction check: FAIL (not truly inductive)")


            logging.info(f"Final inductive invariant ({len(self.strengthening_conjuncts)} strengthening lemmas):")
            logging.info("----" * 10)
            # Print the final inductive invariant in a paste-able TLA+ format.
            for c in self.strengthening_conjuncts:
                logging.info(f"{c[0]}_def == {c[1]}")
            logging.info("")
            logging.info("\* The inductive invariant candidate.")
            logging.info(f"IndAuto ==")
            logging.info(f"  /\ {self.safety}")
            for c in self.strengthening_conjuncts:
                logging.info(f"  /\ {c[0]}_def")
            logging.info("----" * 10)
        else:
            logging.info("Not fully done. Discovered invariant is not inductive.")

    def render_proof_graph(self, save_tex=False, include_seed=True):
        dot = graphviz.Digraph(f'{self.specname}-proof-graph', comment='The Round Table', strict=True)  
        #  dot.graph_attr["rankdir"] = "LR"
        dot.node_attr["fontname"] = "courier"
        dot.node_attr["shape"] = "box"
        
        # Store all nodes.
        for e in self.proof_graph["edges"]:
            for n in e:
                color = "black"
                fillcolor = "white"
                coi = ""
                shape = "ellipse"
                fontsize="20pt"
                penwidth="1"
                lightgreen="#90EE90"
                if n in self.proof_graph["nodes"]:
                    num_ctis_left = 0
                    node = self.proof_graph["nodes"][n]
                    if "is_action" in node:
                        shape = "box"
                        num_ctis_left = self.proof_graph["nodes"][n]["ctis_remaining"]
                        fillcolor = lightgreen if num_ctis_left == 0 else "orange"
                        coi = "{" + ",".join(sorted(self.proof_graph["nodes"][n]["coi_vars"])) + "}"
                        if "curr_node" in self.proof_graph and self.proof_graph["curr_node"] == n and self.proof_graph["nodes"][n]["ctis_remaining"] > 0:
                            # Mark node.
                            fillcolor = "yellow"
                        if "failed" in node and node["failed"]:
                            # color = "red"
                            fillcolor = "salmon"
                        if len(self.proof_graph["nodes"][n]["coi_vars"]) > 0:
                            nlabel = n.split("_")[-1].replace("Action", "") # just show the action name.
                            coi_vars = sorted(self.proof_graph["nodes"][n]["coi_vars"])
                            coi_str = coi
                            # if len(coi_str) > 20:
                                # coi_str_break_ind = coi_str.find(",", len(coi)//2 - 1)
                                # coi_str = coi_str[:coi_str_break_ind] + "<BR/>" + coi_str[coi_str_break_ind:]
                            label = "< " + nlabel + "<BR/>" + "<FONT POINT-SIZE='10'>" + str(coi) + "<BR/>" + " (" + str(len(coi_vars)) + "/" + str(len(self.state_vars)) + " vars) </FONT>"
                            if "num_grammar_preds" in self.proof_graph["nodes"][n]:
                                label += "<FONT POINT-SIZE='10'>|preds|=" + str(self.proof_graph["nodes"][n]["num_grammar_preds"]) + "/" + str(len(self.preds)) + "</FONT>"
                            if "time_spent" in node:
                                label += "<FONT POINT-SIZE='10'> (" + "{0:.2f}".format(self.proof_graph["nodes"][n]["time_spent"]) + "s) </FONT>"
                            if "latest_elimination_iter" in node:
                                latest_iter = self.proof_graph["nodes"][n]["latest_elimination_iter"]
                                label += f"<FONT POINT-SIZE='10'>(iters={latest_iter}) </FONT>"
                            label += ">"
                            fontsize="14pt"
                    if "is_lemma" in node:
                        # Split something like 'Inv249_R3_2_I2_0'.
                        name_parts = n.partition("_")
                        label = "< " + name_parts[0]
                        depth_str = ""
                        if len(name_parts[2]) > 0:
                            label += " <BR/> <FONT POINT-SIZE='12'>" + str(name_parts[2]) + " </FONT>"
                        if "depth" in node:
                            depth_str = ",d=" + str(node["depth"])
                        if "order" in node:
                            # label += "<BR/>"
                            label += " <BR/> <FONT POINT-SIZE='12'>(" + str(node["order"]) + depth_str + ") </FONT>"
                        label += " >"
                        penwidth="3"
                        if node["discharged"]:
                            fillcolor = "green"
                        else:
                            fillcolor = "orange"
                        if "failed" in node:
                            # color = "red"
                            fillcolor = "salmon"
                else:
                    label = n
                dot.node(n, fillcolor=fillcolor, style="filled", color=color, label=label, shape=shape, fontsize=fontsize, penwidth=penwidth)

        for e in self.proof_graph["edges"]:
            dot.edge(e[0], e[1])

        logging.info(f"Rendering proof graph ({len(self.proof_graph['edges'])} edges)")
        suffix = ""
        if include_seed:
            suffix = f"-sd{self.seed}"
        dot.render(self.specdir + "/" + self.specname + "_ind-proof-tree" + suffix)

        if save_tex:
            old_stdout = sys.stdout # backup current stdout
            sys.stdout = open(os.devnull, "w")
            tex_out_file = self.specdir + "/" + self.specname + "_ind-proof-tree.tex"
            figpreamble=f"""
            \Large
            """
            texcode = dot2tex.dot2tex(dot.source, debug=False, output="dot2tex.log", format='tikz', figpreamble=figpreamble, autosize=True, crop=False, figonly=True, texmode="math")
            sys.stdout = old_stdout # reset old stdout
            f = open(tex_out_file, 'w')
            f.write(texcode)
            f.close()

    def proof_graph_get_support_nodes(self, node):
        """ Get all support nodes for a given node of the auto-generated proof graph. """
        support_nodes = {}
        action_nodes = [e[0] for e in self.proof_graph["edges"] if e[1] == node]
        # Safety_RMChooseToAbortAction
        for a in action_nodes:
            action = a.split("_")[-1]
            action_incoming_nodes = [e[0] for e in self.proof_graph["edges"] if e[1] == a]
            support_nodes[action] = action_incoming_nodes
        return support_nodes

    def proof_graph_to_structured_proof(self, start_node, seen=[]):
        """ Convert auto-generated proof graph into a StructuredProof object. """

        # Get all children of this graph node i.e. all incoming edges.
        root_proof_node = StructuredProofNode("L_" + start_node, start_node)
        support_nodes = self.proof_graph_get_support_nodes(start_node)
        seen.append(start_node)
        # print("SUPPORT:", support_nodes)
        for action in support_nodes:
            # print(support_nodes[action])
            children_to_add = [c for c in support_nodes[action] if c not in seen]
            root_proof_node.children[action] = [self.proof_graph_to_structured_proof(child, seen=seen) for child in children_to_add] 
        return root_proof_node

    def run(self):
        tstart = time.time()

        self.load_parse_tree = True
        self.use_fast_pred_eval = False

        print("Config CONSTANT instances.")
        for c in self.get_config_constant_instances():
            print(c)

        # Parse and save AST of spec if needed.
        if self.load_parse_tree:
            logging.info(f"Parsing spec '{self.specname}' into parse tree.")
            try:
                tla_spec_obj = tlaparse.parse_tla_file(self.specdir, f"{self.specname}")
                self.spec_defs = tla_spec_obj.get_all_user_defs(level="1")
                self.tla_spec_obj = tla_spec_obj
                self.state_vars = self.tla_spec_obj.get_all_vars()
                self.actions = []
                for udef in self.tla_spec_obj.get_all_user_defs(level="2"):
                    if udef.endswith("Action"):
                        self.actions.append(udef)
                        action_vars,action_vars_coi = self.tla_spec_obj.get_vars_in_def(udef)
                        updated_vars = list(action_vars_coi.keys())
                        logging.info(f"Action '{udef}':")
                        logging.info(f"  - {len(action_vars)} vars in action : {str(action_vars)}")
                        logging.info(f"  - updated vars ({len(updated_vars)}): {updated_vars}")
                        # logging.info(action_vars_coi)
                        # for a in action_vars_coi:
                            # logging.info(f"  COI of updated action var {a}: " + str(action_vars_coi[a]))

            except Exception as e:
                print("ERROR: error parsing TLA+ spec:", e)
                self.tla_spec_obj = None

        # self.auto_check_simulation_bound()
        # return
        self.latest_roundi = 0

        if self.proof_tree_mode:

            # Run interactive mode and then exit.
            if self.interactive_mode:
                logging.info("Running in interactive proof tree mode.")
                self.run_interactive_mode()
                return
            


            logging.info("Running invariant generation in proof tree mode.")
            self.do_invgen_proof_tree_mode()

            # Render once more.
            if self.save_dot and len(self.proof_graph["edges"]) > 0:
                # Render updated proof graph as we go.
                self.render_proof_graph()
                self.persist_proof_graph(self.latest_roundi)

                # Also save TLAPS obligations for proof graph.
                structured_proof_root = self.proof_graph_to_structured_proof("Safety")
                structured_proof = StructuredProof(structured_proof_root, 
                                    specname = self.specname, 
                                    actions=self.actions, 
                                    # nodes=nodes, 
                                    safety=self.safety)
                proof_config = {}
                if "tlaps_proof_config" in self.spec_config:
                    proof_config = self.spec_config["tlaps_proof_config"]
                lemma_nodes = [n for n in self.proof_graph["nodes"] if "is_lemma" in self.proof_graph["nodes"][n]]
                structured_proof.to_tlaps_proof_skeleton(proof_config, add_lemma_defs=[(n, self.proof_graph["nodes"][n]["expr"]) for n in lemma_nodes])
            
                

            # print("")
            # print("Proof graph edges")
            # dot = graphviz.Digraph('round-table', comment='The Round Table')  
            # dot.graph_attr["rankdir"] = "LR"
            # dot.node_attr["fontname"] = "courier"
            # dot.node_attr["shape"] = "box"
            
            # # Store all nodes.
            # for e in self.proof_graph["edges"]:
            #     print(e[0])
            #     print(e[1])
            #     dot.node(e[0][0], e[0][1].replace("\\", "\\\\"))
            #     dot.node(e[1][0], e[1][1].replace("\\", "\\\\"))

            # for e in self.proof_graph["edges"]:
            #     print(e[0])
            #     print(e[1])
            #     dot.edge(e[0][0], e[1][0])
            #     # print(e)

            # print("Final proof graph:")
            # print(dot.source)
            # f = open("notes/" + self.specname + "_ind-proof-tree.dot", 'w')
            # f.write(dot.source)
            # f.close()
            # dot.render("notes/" + self.specname + "_ind-proof-tree")
                
            print("Finished inductive invariant generation in proof tree mode.")
        else:
            self.do_invgen()

            if self.auto_lemma_action_decomposition and len(self.proof_graph["edges"]) > 0:
                self.render_proof_graph()

        tend = time.time()
        self.total_duration_secs = (tend - tstart)
        if self.cached_invs_gen_time_secs != None:
            self.total_duration_secs += self.cached_invs_gen_time_secs

    def is_inv_inductive(self):
        """ Return whether the current discovered invariant is believed to be inductive. """
        return self.is_inductive

    def get_inductive_inv(self):
        """ 
        Return the discovered inductive invariant, which is the conjunction of
        the original safety property with the discovered strengthening
        conjuncts.
        """
        return [self.safety] + self.strengthening_conjuncts

def permute_cti(cti, perm):
    nodes = ["n1", "n2", "n3"]
    temp_nodes = {
        "n1": "na", 
        "n2": "nb", 
        "n3": "nc"
    }
    # Mapping from original values to the new value under permutation.
    perm_map = {n:perm[i] for i,n in enumerate(nodes)}

    perm_cti = cti

    for varname in perm_cti:
        for i,p in enumerate(perm):
            node = nodes[i]
            # print varname
            # print perm_cti
            perm_cti[varname][temp_nodes[p]] = perm_cti[varname][node]
            # del perm_cti[p]
            # perm_cti[node] = perm_cti.replace(node, temp_nodes[p])

    for varname in perm_cti:
        for i,n in enumerate(nodes):
            perm_cti[varname][n] = perm_cti[varname][temp_nodes[n]]
            del perm_cti[varname][temp_nodes[n]]

    # Now we still need to permuate the 'config' variable values.
    for s in nodes:
        # print "init:",perm_cti["config"][s]
        nodes_to_remove = perm_cti["config"][s]
        nodes_to_add = set()
        for n in nodes_to_remove:
            nodes_to_add.add(perm_map[n])
        perm_cti["config"][s] = perm_cti["config"][s] - nodes_to_remove
        perm_cti["config"][s] = perm_cti["config"][s].union(nodes_to_add)
        # print "new:",perm_cti["config"][s]

    return perm_cti   

#
# Main entry point.
#
if __name__ == "__main__":

    DEFAULT_NUM_SIMULATE_TRACES = 800
    DEFAULT_SIMULATE_DEPTH = 8
    DEFAULT_TLC_WORKERS = 6
    DEFAULT_CTI_ELIMINATION_WORKERS = 3

    # Use default faster Java on Mac if it exists.

    if os.path.exists(MAC_FAST_JAVA_EXE):
        print(f"Setting default Java to fast Mac version: '{MAC_FAST_JAVA_EXE}'")
        JAVA_EXE = MAC_FAST_JAVA_EXE

    # Parse command line arguments.
    parser = argparse.ArgumentParser(description='')
    parser.add_argument('--spec', help="Name of the protocol benchmark to run (given as 'benchmarks/<spec_name>').", required=True, type=str)
    parser.add_argument('--ninvs', help='Maximum number of invariants to generate at each iteration.', required=False, type=int, default=5000)
    parser.add_argument('--niters', help='Maximum number of invariant generation iterations to run in each CTI elimination round.', required=False, type=int, default=3)
    parser.add_argument('--nrounds', help='Maximum number of CTI elimination rounds to run.', required=False, type=int, default=3)
    parser.add_argument('--seed', help='Seed for RNG.', required=False, default=0, type=int)
    parser.add_argument('--safety', help='Safety property to verify (will override safety prop in config).', required=False, default=None, type=str)
    
    parser.add_argument('--num_simulate_traces', help='The maximum number of traces TLC will generate when searching for counterexamples to inductions (CTIs).', required=False, type=int, default=DEFAULT_NUM_SIMULATE_TRACES)
    parser.add_argument('--simulate_depth', help='Maximum depth of counterexample to induction (CTI) traces to search for.', required=False, type=int, default=DEFAULT_SIMULATE_DEPTH)
    parser.add_argument('--tlc_workers', help='Number of TLC worker threads to use when checking candidate invariants.', required=False, type=int, default=DEFAULT_TLC_WORKERS)
    parser.add_argument('--cti_elimination_workers', help='Number of TLC worker threads to use when checking CTI elimination.', required=False, type=int, default=DEFAULT_CTI_ELIMINATION_WORKERS)
    parser.add_argument('--java_exe', help='Path to Java binary.', required=False, type=str, default=JAVA_EXE)
    parser.add_argument('--tlc_jar', help='Path to Java binary.', required=False, type=str, default=TLC_JAR)
    parser.add_argument('--debug', help='Output debug info to log.', default=False, action='store_true')
    parser.add_argument('--cache_invs', help='Save generated invariants to the given file.', default=None, type=str)
    parser.add_argument('--cache_num_conjuncts', help='Number of conjuncts in generated invariants to be cached.', required=False, default=2, type=int)
    parser.add_argument('--load_inv_cache', help='Load pre-generated invariants from a file.', required=False, default=None, type=str)
    parser.add_argument('--log_file', help='Log output file.', required=False, default=None, type=str)
    parser.add_argument('--save_result', help='Whether to save result statistics to a file', required=False, default=False, action='store_true')
    parser.add_argument('--opt_quant_minimize', help='Enable quantifier minimization optimization for faster invariant checking.', required=False, default=False, action='store_true')
    parser.add_argument('--try_final_minimize', help='Attempt to minimize the final discovered invariant.', required=False, default=False, action='store_true')
    parser.add_argument('--results_dir', help='Directory to save results.', required=False, type=str, default="results")
    
    parser.add_argument('--max_num_conjuncts_per_round', help='Max number of conjuncts to learn per round.', type=int, default=10000)
    parser.add_argument('--max_duration_secs_per_round', help='Max number of seconds to spend on each iteration.', type=int, default=10000)
    parser.add_argument('--max_num_ctis_per_round', help='Max number of CTIs per round.', type=int, default=10000)
    parser.add_argument('--override_num_cti_workers', help='Max number of TLC workers for CTI generation.', type=int, default=None)
    parser.add_argument('--k_cti_induction_depth', help='CTI k-induction depth.', type=int, default=1)
    parser.add_argument('--auto_lemma_action_decomposition', help='Automatically split inductive proof obligations by action and lemmas.', required=False, default=False, action='store_true')
    parser.add_argument('--disable_state_cache_slicing', help='Disable slicing of state caches.', required=False, default=False, action='store_true')# how to make one argument exclusive with another?
    parser.add_argument('--disable_grammar_slicing', help='Disable slicing of grammars.', required=False, default=False, action='store_true')# how to make one argument exclusive with another?
    
    
    # Proof tree related commands.
    parser.add_argument('--proof_tree_mode', help='Run in inductive proof tree mode (EXPERIMENTAL).', default=False, action='store_true')
    parser.add_argument('--persistent_mode', help='Run in inductive proof tree mode with persistent caching/reloading. (EXPERIMENTAL).', default=False, action='store_true')
    parser.add_argument('--interactive', help='Run in interactive proof tree mode (EXPERIMENTAL).', default=False, action='store_true')
    parser.add_argument('--max_proof_node_ctis', help='Maximum number of CTIs per proof node.', type=int, default=5000)
    parser.add_argument('--proof_tree_cmd', help='Proof tree command (EXPERIMENTAL).', default=None, type=str, required=False, nargs="+")
    parser.add_argument('--proof_struct_tag', help='Tag of proof structure to load (EXPERIMENTAL).', default=None, type=str, required=False)
    parser.add_argument('--target_sample_states', help='Target # initial states to sample. (EXPERIMENTAL).', default=10000, type=int, required=False)
    parser.add_argument('--target_sample_time_limit_ms', help='Target initial state sampling time (EXPERIMENTAL).', default=10000, type=int, required=False)
    parser.add_argument('--save_dot', help='Save proof graphs in DOT and TeX info.', default=False, action='store_true')
    parser.add_argument('--enable_partitioned_state_caching', help='Enable finer grained partitioned variable subset based state caching.', default=False, action='store_true')
    parser.add_argument('--enable_cti_slice_projection', help='Enable slicing of CTI sets.', default=False, action='store_true')
    parser.add_argument('--action_filter', help='CTI action filter.', required=False, default=None, type=str)
    parser.add_argument('--include_existing_conjuncts', help='Whether to include existing conjuncts as invariant candidates during CTI elimination.', default=True, action='store_true')

    # Apalache related commands.
    parser.add_argument('--use_apalache_ctigen', help='Use Apalache for CTI generation (experimental).', required=False, default=False, action='store_true')
    parser.add_argument('--do_apalache_final_induction_check', help='Do final induction check with Apalache (experimental).', required=False, default=False, action='store_true')
    parser.add_argument('--apalache_smt_timeout_secs', help='Apalache SMT timeout. (experimental).', required=False, type=int, default=15)
    

    args = vars(parser.parse_args())

    # Parse out spec name and directory, if needed.
    spec = args["spec"]
    specdir = os.path.split(spec)[0]
    specname = os.path.split(spec)[1]

    # Create directory for generated files if needed.
    os.system(f"mkdir -p {os.path.join(specdir, GEN_TLA_DIR)}")
    os.system(f"mkdir -p {os.path.join(specdir, STATECACHE_DIR)}")

    # Can't disable state cache slicing if we have enabled partitioned state caching.
    assert not (args["disable_state_cache_slicing"] and args["enable_partitioned_state_caching"]), "Can't disable state cache slicing if partitioned state caching is enabled."

    # Initialize command line args.
    num_invs = args["ninvs"]
    seed = args["seed"] 
    safety_arg = args["safety"]
    numiters = args["niters"] 
    num_rounds = args["nrounds"] 
    NUM_SIMULATE_TRACES = args["num_simulate_traces"] 
    simulate_depth = args["simulate_depth"] 
    tlc_workers = args["tlc_workers"] 
    cache_invs = args["cache_invs"]
    cache_num_conjuncts = args["cache_num_conjuncts"]
    load_inv_cache = args["load_inv_cache"]
    log_file = args["log_file"]
    save_result = args["save_result"]
    opt_quant_minimize = args["opt_quant_minimize"]
    try_final_minimize = args["try_final_minimize"]
    DEBUG = args["debug"] 
    random.seed(seed)

    # Set up logging system.
    logfile = 'invgen.log'
    log_level = logging.DEBUG if DEBUG else logging.INFO 
    log_format = '%(message)s'
    if log_file:
        logging.basicConfig(filename=log_file, format=log_format, filemode='w', level=log_level)
        print(f"Logging output to '{logfile}'")
    else:
        # Log to stdout if no log file is specified.
        logging.basicConfig(stream=sys.stdout, format=log_format, filemode='w', level=log_level)

    # Set Java binary path.
    JAVA_EXE = args["java_exe"]
    TLC_JAR = args["tlc_jar"]
    spec_config_file = os.path.join(specdir, specname) + ".config.json"
    fcfg = open(spec_config_file)
    spec_config = json.load(fcfg)

    # Load config parameters.
    preds = spec_config["preds"]
    # preds_alt = spec_config["preds_alt"]    
    safety = spec_config["safety"]

    # Override safety prop in config with command line arg, if one is given.
    if safety_arg is not None:
        logging.info(f"Overriding safety property in config with command line arg: '{safety_arg}'")
        safety = safety_arg

    # TODO: Make 'constants' parameter a list of lines.
    constants = spec_config["constants"]

    constraint = spec_config["constraint"]
    quant_inv = spec_config["quant_inv"]
    # quant_inv_alt = spec_config["quant_inv_alt"]
    quant_vars = spec_config.get("quant_vars", [])
    model_consts = spec_config["model_consts"]
    symmetry = spec_config["symmetry"]    
    typeok = spec_config["typeok"]
    tlc_specific_spec = spec_config.get("tlc_specific_spec", False)
    simulate = spec_config["simulate"]
    results_dir = args["results_dir"]
    local_grammars = spec_config.get("local_grammars", None)

    if "use_cpp_invgen" in spec_config:
        use_cpp_invgen = spec_config["use_cpp_invgen"]
    else:
        use_cpp_invgen = False
    pregen_inv_cmd = spec_config.get("pregen_inv_cmd", None)

    logging.info(f"Loaded config for '{specname}' spec.")
    for k in spec_config:
        if k != "local_grammars":
            logging.info(f"{k}: {spec_config[k]}")
        if k == "safety":
            logging.info(f" 'safety' overriden with command line arg: '{safety_arg}'")

    # Print out the command line args.
    logging.info("Command line args: " + str(sys.argv[1:]))


    # Read pre-cached invariants from a file if specified.
    cached_invs = None
    cached_invs_gen_time_secs = None
    if load_inv_cache:
        invf = open(load_inv_cache)
        lines = invf.read().splitlines()
        cached_invs = lines[1:]
        cached_invs_gen_time_secs = int(lines[0])
        logging.info("Loaded %d cached invariants from cache file: '%s'" % (len(cached_invs), load_inv_cache))

    tstart = time.time()
    logging.info("Starting invariant discovery for spec '%s' and safety property '%s' with %d seed predicates. DEBUG=%s" % (specname, safety, len(preds), DEBUG))
    
    # Log the date.
    now = datetime.datetime.now()
    logging.info("Current date: " + now.strftime("%Y-%m-%d %H:%M:%S"))

    # Generate an inductive invariant.
    indgen = InductiveInvGen(specdir, specname, safety, constants, constraint, quant_inv, model_consts, preds, 
                                num_invs=num_invs, num_rounds=num_rounds, seed=seed, typeok=typeok, tlc_specific_spec=tlc_specific_spec, num_iters=numiters, 
                                num_simulate_traces=NUM_SIMULATE_TRACES, simulate_depth=simulate_depth, tlc_workers=tlc_workers, quant_vars=quant_vars, symmetry=symmetry,
                                simulate=simulate, java_exe=JAVA_EXE, cached_invs=cached_invs, cached_invs_gen_time_secs=cached_invs_gen_time_secs, use_cpp_invgen=use_cpp_invgen,
                                pregen_inv_cmd=pregen_inv_cmd, opt_quant_minimize=args["opt_quant_minimize"],try_final_minimize=try_final_minimize,
                                proof_tree_mode=args["proof_tree_mode"],
                                proof_tree_mode_persistent=args["persistent_mode"],
                                interactive_mode=args["interactive"],
                                max_num_conjuncts_per_round=args["max_num_conjuncts_per_round"], max_num_ctis_per_round=args["max_num_ctis_per_round"],
                                override_num_cti_workers=args["override_num_cti_workers"],use_apalache_ctigen=args["use_apalache_ctigen"],all_args=args,
                                spec_config=spec_config, 
                                enable_partitioned_state_caching=args["enable_partitioned_state_caching"],
                                enable_cti_slice_projection=args["enable_cti_slice_projection"],
                                auto_lemma_action_decomposition=args["auto_lemma_action_decomposition"],
                                action_filter=args["action_filter"])


    # Only do invariant generation, cache the invariants, and then exit.
    if cache_invs:
        logging.info("Caching generated invariants only.")
        indgen.run_cache_invs(cache_invs, num_invs, min_num_conjuncts=cache_num_conjuncts, max_num_conjuncts=cache_num_conjuncts)
        logging.info("Total duration: {:.2f} secs.".format(((time.time() - tstart))))
        exit(0)
    
    logging.info("======= Starting inductive invariant generation run. =======")

    indgen.run()
    logging.info("Initial random seed: %d", indgen.seed)
    logging.info("opt_quant_minimize: %d", indgen.opt_quant_minimize)
    logging.info("Total number of CTIs eliminated: %d", indgen.get_total_num_ctis_eliminated())
    logging.info("Total number of invariants generated: %d", indgen.get_total_num_invs_generated())
    logging.info("Total number of invariants checked: %d", indgen.get_total_num_invs_checked())
    logging.info("CTI generation duration: %f secs.", indgen.get_ctigen_duration())
    logging.info("State caching duration: %f secs.", indgen.get_state_cache_duration())
    if indgen.proof_tree_mode:
        logging.info("Re-parsing duration: %f secs.", indgen.reparsing_duration_secs)
    logging.info("State caching duration: %f secs.", indgen.get_state_cache_duration())
    logging.info("Invariant checking duration: %f secs.", indgen.get_invcheck_duration())
    logging.info("CTI elimination checks duration: %f secs.", indgen.get_ctielimcheck_duration())
    logging.info("Total duration: {:.2f} secs.".format(((time.time() - tstart))))

    if save_result:
        indgen.save_result(results_dirname=results_dir)
