"""
Various utilities for model checking TLA+ specs with TLC and/or Apalache.
"""
import subprocess
import logging
import os
import sys

from itertools import chain, combinations

def powerset(iterable):
    "powerset([1,2,3]) --> () (1,) (2,) (3,) (1,2) (1,3) (2,3) (1,2,3)"
    s = list(iterable)
    return chain.from_iterable(combinations(s, r) for r in range(len(s)+1))

class Apalache:
    """ Utilities for model checking TLA+ with Apalache. """
    def __init__(self, specdir) -> None:
        self.apalache_bin = "apalache/bin/apalache-mc"
        self.specdir = specdir
        self.GEN_TLA_DIR = "gen_tla" # TODO: pass this in.

    def gen_check_spec(self, orig_spec_name, check_spec_name, defs):
        """ 
        Create a spec that allows for various model checking tasks.

        Adds all given 'defs' as new definitions in a spec that extends the given original spec. Expects
        'defs' to be given as a map from definition names to TLA+ expressions.
        """
        
        # Build the spec.
        spec_lines = [
            "---- MODULE %s ----\n" % check_spec_name,
            f"EXTENDS {orig_spec_name},Naturals,TLC\n"
        ] + [
            f"{d} == {defs[d]}" for d in defs
        ] + [
            "===="
        ]
        return "\n".join(spec_lines)

    def check(self, orig_spec_name, init, inv, defs={}, length=1):
        # Clean the output directory.
        os.system("rm -rf benchmarks/gen_tla/apalache-cti-out")

        check_spec_name = f"{orig_spec_name}_ApaCheck"
        spec_text = self.gen_check_spec(orig_spec_name, check_spec_name, defs)
        tla_file = f"{os.path.join(self.specdir, self.GEN_TLA_DIR)}/{check_spec_name}.tla"
        tla_filename = f"{self.GEN_TLA_DIR}/{check_spec_name}.tla"

        f = open(tla_file, 'w')
        f.write(spec_text)
        f.close()

        rundir = "gen_tla/apalache_ctigen"
        outdir = "gen_tla/apalache_ctigen"
        jvm_args="JVM_ARGS='-Xss16M'"
        args = [
            f"--out-dir={outdir}",
            f"--run-dir={rundir}",
            # f"--max-error={max_num_ctis}",
            # f"--view=vars",
            f"--cinit=CInit",
            f"--init={init}",
            f"--next=Next",
            f"--inv={inv}",
            f"--length={length}",
            tla_filename
        ]
        cmd = f"{self.apalache_bin} check {' '.join(args)}"
        logging.debug("Apalache command: " + cmd)
        workdir = None
        if self.specdir != "":
            workdir = self.specdir
        subproc = subprocess.Popen(cmd, shell=True, stdout=subprocess.PIPE, cwd=workdir)
        return subproc
    
    def await_output(self, apalache_subproc):
        apa_out = apalache_subproc.stdout.read().decode(sys.stdout.encoding)
        lines = [x.strip() for x in apa_out.splitlines()]
        # Check for successful Apalache run.
        for l in lines:
            if "Checker reports no error up to computation length 1" in l:
                return {"error":False, "stdout": apa_out}
        return {"error":True, "stdout": apa_out}

    def compute_minimal_support_graph(self, orig_spec_name, defs, typeok, inductive_inv):
        """ 
        Computes the minimal support graph for the given inductive invariant passed as a list of lemmas given
        as (name, expr) pairs.
        """
        logging.info(f"Computing minimal support graph for inductive invariant: {inductive_inv}")
        support_sets = {}
        lemma_subsets = powerset(inductive_inv)
        lemma_subsets_by_size = [[s for s in lemma_subsets if len(s) == size] for size in range(len(inductive_inv))]
        for lemma_name in inductive_inv:
            logging.info(f"Computing support graph for lemma: {lemma_name}")
            # TODO: Use binary search for computing support sets more efficiently?
            for support_lemmas in powerset(inductive_inv):
                if lemma_name not in support_lemmas:
                    # Only need to check support sets that include ourself.
                    continue
                    
                logging.info(f"Checking support set {support_lemmas}, for lemma {lemma_name}")
                defs["IndCheck"] = "\n  /\\ " + " \n  /\\ ".join([typeok] + [name for name in support_lemmas])
                
                # Check induction of current lemma relative to subsets of other lemmas.
                subproc = self.check(orig_spec_name, "IndCheck", lemma_name, defs = defs, length=1)
                res = self.await_output(subproc)
                # print(res["error"])
                # print(res["stdout"])
                if not res["error"]:
                    # Found valid support set.
                    logging.info(f"Found support set: {support_lemmas}, lemma: {lemma_name}")
                    support_sets[lemma_name] = support_lemmas
                    # Finish and move on to next lemma.
                    break

if __name__ == "__main__":
    log_level = logging.DEBUG
    log_format = '%(message)s'
    logging.basicConfig(stream=sys.stdout, format=log_format, filemode='w', level=log_level)


    #
    # Testing some Apalache class features.
    #
    specname = "TwoPhase"
    typeok = "TypeOK"
    logging.info("Doing final inductive check with Apalache.")

    strengthening_conjuncts = [
        ("A_Inv89_1_0_def" , '\A rmi \in RM : ([type |-> "Prepared", rm |-> rmi] \in msgsPrepared) \/ (~(tmPrepared = tmPrepared \cup {rmi}))'),
        ("A_Inv326_1_1_def" , '(tmPrepared = RM) \/ (~([type |-> "Commit"] \in msgsAbortCommit))'),
        ( "A_Inv51_1_2_def" , '\A rmi \in RM : ([type |-> "Commit"] \in msgsAbortCommit) \/ (~(rmState[rmi] = "committed"))'),
        ("A_Inv446_1_3_def" , '\A rmi \in RM : ~([type |-> "Prepared", rm |-> rmi] \in msgsPrepared) \/ (~(rmState[rmi] = "working"))'),
        ( "A_Inv380_1_4_def" , '(tmState = "committed") \/ (~([type |-> "Commit"] \in msgsAbortCommit))'),
        ("A_Inv362_1_5_def", '(tmState = "aborted") \/ (~([type |-> "Abort"] \in msgsAbortCommit))'),
        ( "A_Inv479_1_6_def" , '\A rmi \in RM : ~(rmState[rmi] = "aborted") \/ (~(tmState = "committed"))'),
        ("A_Inv2450_2_7_def" , '\A rmi \in RM : (rmState[rmi] = "prepared") \/ (~(tmPrepared = tmPrepared \cup {rmi})) \/ (~(tmState = "init"))'),
        ("A_Inv115_1_0_def" , '\A rmj \in RM : ([type |-> "Prepared", rm |-> rmj] \in msgsPrepared) \/ (~(rmState[rmj] = "prepared"))'),
        ("A_Inv339_1_1_def" , '(tmPrepared = RM) \/ (~(tmState = "committed"))'),
        ("A_Inv2469_2_2_def" , '\A rmi \in RM : (rmState[rmi] = "prepared") \/ (~(tmState = "init")) \/ (~([type |-> "Prepared", rm |-> rmi] \in msgsPrepared))')
    ]

    lemmas = [("Safety","TCConsistent")] + strengthening_conjuncts
    defs = {name:exp for name,exp in lemmas}
    defs["IndCurr"] = f"\n  /\\ {typeok} \n  /\\ " +  " \n  /\\ ".join([name for name,exp in lemmas])
    # Check induction step.
    apalache = Apalache("benchmarks")
    apa_subproc = apalache.check("TwoPhase", "IndCurr", "IndCurr", defs = defs, length=1)
    res = apalache.await_output(apa_subproc)
    logging.debug(res["stdout"])
    if not res["error"]:
        logging.info("Apalache final induction check: PASS!")

        # Try computing minimal support graph.
        inductive_inv = ["Safety"] + [c[0] for c in strengthening_conjuncts] 
        apalache.compute_minimal_support_graph(specname, defs, typeok, inductive_inv)
    else:
        logging.info("Apalache final induction check: FAIL (not truly inductive)")