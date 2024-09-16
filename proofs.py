#
# Classes and definitions used for constructing structured inductive invariant proof objects.
#

import random
import pickle
import graphviz
import logging
import json
import dot2tex
import subprocess
import sys
import multiprocessing
import time
import io
import contextlib

from mc import CTI
import mc
import tlaps

log = logging.getLogger("dot2tex")
log.setLevel(logging.WARNING)

def find_ind_containing(l,substr):
    for ind in range(len(l)):
        if substr in l[ind]:
            return ind
    return -1

# Count spec and proof LOC.
def count_spec_loc(specfile):
    lines = open(specfile).read().splitlines()
    # Remove commented lines.
    lines = [l for l in lines if (not l.startswith("\*") or "START_PROOF" in l)]
    spec_loc = find_ind_containing(lines, "START_PROOF")
    proof_loc = len(lines) - spec_loc
    return {"spec_loc": spec_loc, "proof_loc": proof_loc}

def runcmd(c):
    print("RUNNING CMD:", c)
    cmd = c[0]
    expr = c[1]
    start = time.time()
    sys.stdout.flush()
    proc = subprocess.Popen(cmd, shell=True, stderr=subprocess.PIPE, cwd="benchmarks")
    exitcode = proc.wait()
    duration = int(time.time() - start)
    print("EXIT CODE:", exitcode)
    return (expr, exitcode, duration)

def mean(S):
    return sum(S) / len(S)

def median(S):
    if len(S) == 0:
        return -1
    S.sort()
    return S[len(S)//2]

class StructuredProofNode():
    """ Single node (i.e. lemma) of a structured proof tree. """
    def __init__(self, name="", expr="", children=None, parent=None, load_from_obj = None):
        # Name used to identify the expression.
        self.name = name
        # Top level goal expression to be proven.
        self.expr = expr

        self.children = dict() if children is None else children

        self.cti_view = None

        # Allow nodes to optionally override TypeOK for potentially faster local CTI generation.
        self.ctigen_typeok = None

        # Set of variables to project to (i.e keep only these) for CTI generation and analysis.
        self.cti_project_vars = None

        # Each proof node/lemma can maintain a current set of CTIs, which are
        # computed based on whether the lemma is inductive relative to its
        # current set of direct children.
        self.ctis = {}

        # Flag telling whether CTIs were attempted to be generated yet
        # for this proof node. Initially set to Flas,e it will go True
        # once a call to set some CTIs on this node occur.
        self.had_ctis_generated = False

        # Set to true if we completed a full proof of this node's inductiveness
        # relative to its supporting lemmas using Apalache model checker.
        self.apalache_proof_check = False

        # Set of CTIs eliminated by set of this node's direct children.
        # self.ctis_eliminated = []
        self.ctis_eliminated = {}

        # CTIs eliminated uniquely by each child, per action.
        self.ctis_eliminated_uniquely = {}

        # Pointer to this node's parent, or None if it has no parent.
        self.parent = parent

        # Set of CTIs of parent that this lemma eliminates.
        self.parent_ctis_eliminated = []

        # Set of CTIs of parent that are eliminated by this predicate alone and
        # none of its siblings.
        self.parent_ctis_uniquely_eliminated = []

        if load_from_obj:
            self.load_from(load_from_obj)

    def num_children(self):
        cnt = 0
        for a in self.children:
            for c in self.children[a]:
                cnt += 1
        return cnt

    def serialize_rec(self, include_ctis=True, cti_hashes_only=False, seen=set(), serialize_children=True):
        # if self.expr in seen:
        #     None
        # print(seen)

        # Deal with cycles in the proof graph by tracking visited nodes.
        seen.add(self.expr)

        # If we have already visited this node in the proof graph, then retain it as a child,
        # but don't recursively serialize its children.
        def serialize_child(c):
            if c.expr in seen:
                return c.serialize_rec(include_ctis=include_ctis, cti_hashes_only=cti_hashes_only, seen=set(seen), serialize_children=False)
            else:
                return c.serialize_rec(include_ctis=include_ctis, cti_hashes_only=cti_hashes_only, seen=set(seen))

        children_serialized = {}
        if serialize_children:
            children_serialized = { 
                a:[serialize_child(c) for c in self.children[a]] 
                    for a in self.children
            }

        ret = {
            "name": self.name, 
            "expr": self.expr, 
            "apalache_proof_check": self.apalache_proof_check, 
            "children": children_serialized, 
            "project_vars": self.cti_project_vars
        }

        cti_sort_key = lambda c : c.cost
        remaining_ctis_cost_sorted = sorted(self.get_remaining_ctis(), key = cti_sort_key)

        if cti_hashes_only:
            ctis_serialized = {a:[str(hash(c)) for c in self.ctis[a]] for a in self.ctis}
        else:
            ctis_serialized = {a:[c.serialize() for c in self.ctis[a]] for a in self.ctis}

        cti_info = {
            "ctis": ctis_serialized,
            "ctis_eliminated": self.ctis_eliminated, # eliminated CTIs are stored as CTI hashes, not full CTIs.
            "ctis_eliminated_uniquely": {a:{c:list(v[c]) for c in v} for a,v in self.ctis_eliminated_uniquely.items()}, # eliminated CTIs are stored as CTI hashes, not full CTIs.
            "ctis_remaining": {a:[str(hash(cti)) for cti in self.get_remaining_ctis(a)] for a in self.ctis},
            "num_parent_ctis_eliminated": len(self.parent_ctis_eliminated),
            # "parent_ctis_eliminated": [c for c in self.parent_ctis_eliminated],
            "had_ctis_generated": self.had_ctis_generated
        }

        # print(type(cti_info["ctis"]))
        if include_ctis:
            for k in cti_info:
                ret[k] = cti_info[k]
        return ret

    def serialize(self, include_ctis=True, cti_hashes_only=False, serialize_children=True):
        seen_nodes = set()
        return self.serialize_rec(include_ctis=include_ctis, cti_hashes_only=cti_hashes_only, serialize_children=serialize_children, seen=seen_nodes)


    def load_from(self, obj):
        """ Load serialized proof object into the current one after deserializing. """
        self.name = obj["name"]
        self.expr = obj["expr"]
        self.apalache_proof_check = obj.get("apalache_proof_check", False)
        self.ctis = [CTI(load_from_obj=c) for c in obj["ctis"]]
        # self.ctis_eliminated = [c for c in obj["ctis_eliminated"]]
        self.ctis_eliminated = obj["ctis_eliminated"]
        self.parent_ctis_eliminated = obj.get("parent_ctis_eliminated", [])
        self.children = [StructuredProofNode(load_from_obj=c, parent=self) for c in obj["children"]]

    # <span style='color:{color}'>
    #     {self.expr} ({len(self.ctis)-len(self.ctis_eliminated)} CTIs remaining, eliminates {len(self.parent_ctis_eliminated)} parent CTIs)
    # </span>
    def list_elem_html(self):
        all_ctis_eliminated = len(self.ctis) == len(self.ctis_eliminated)
        color = "darkred" if len(self.ctis) > len(self.ctis_eliminated) else "green"
        if not self.had_ctis_generated:
            color = "goldenrod"
        # if all_ctis_eliminated and self.apalache_proof_check:
        #     color = "blue"
        if self.parent is not None and len(self.parent.ctis) > 0:
            pct_parent_ctis_eliminated = float(len(self.parent_ctis_eliminated)) / len(self.parent.ctis)
        else:
            pct_parent_ctis_eliminated = 0.0
        parent_info_text = ""
        if self.parent is not None:
            parent_info_text = f"(eliminates {len(self.parent_ctis_eliminated)} ({int(pct_parent_ctis_eliminated * 100.0)}% of) parent CTIs, {len(self.parent_ctis_uniquely_eliminated)} uniquely)"
        local_rand = random.Random()
        local_rand.seed(13)
        cti_elim_viz = ""
        sample_size = 50
        if self.parent and len(self.parent.ctis) >= sample_size:
            elim_cti_sample = local_rand.sample(self.parent.ctis, sample_size)
            cti_elim_viz = "".join(["x" if str(hash(c)) in self.parent_ctis_eliminated else "-" for c in elim_cti_sample])
        proof_check_badge = "&#10004;" if self.apalache_proof_check else "<span style='color:darkred'>&cross;</span>"
        # <td style='color:{color}'> FP:{proof_check_badge} </td>
        return f"""
        <table class='proof-struct-table'>
            <tr>
                <td style='color:{color}' class='proof-node-expr'>{self.expr}</td>
                <td style='color:{color}' class='ctis-remaining-count'>({len(self.ctis)-len(self.ctis_eliminated)}/{len(self.ctis)} CTIs remaining) (Apalache proof? {proof_check_badge})</td>
                <td class='proof-parent-cti-info'> {parent_info_text} </td>
                <td class='gen-ctis-button' onclick='genCtis("{self.name}")'> Gen CTIs </td>
                <td class='gen-ctis-button' onclick='genCtisSubtree("{self.name}")'> Gen CTIs (subtree) </td>
            </tr>
        </table>
        """
        
        # CTI elim viz row.
        # <td class='proof-cti-grid-row'>{cti_elim_viz}</td>


    def to_html(self):
        child_elems = "\n".join([f"<span>{c.to_html()}</span>" for c in self.children_list()])
        return f"""
                <li>{self.list_elem_html()}
                    <ul>{child_elems}</ul> 
                </li>
            """

    def children_list(self):
        if type(self.children) == dict:
            out = sum(list(self.children.values()), [])
            return out
        return self.children

    def set_ctis(self, ctis, action):
        """ Set CTIs for this node and mark it as having CTIs generated. """
        self.had_ctis_generated = True
        self.ctis[action] = ctis
    
    def get_ctis(self, action):
        return self.ctis[action]

    def reset_ctis(self):
        """ Set CTIs for this node and mark it as having CTIs generated. """
        logging.info(f"Resetting CTIs for node: {self.name}")
        self.had_ctis_generated = False
        self.ctis = {}
        self.ctis_eliminated = {}
        self.apalache_proof_check = False
        # self.parent_ctis_eliminated = []

    def get_remaining_ctis(self, action=None):
        if action is None:
            return []
        return [c for c in self.ctis[action] if str(hash(c)) not in self.ctis_eliminated[action]]

    def sample_remaining_ctis(self, max_num_ctis):
        remaining_ctis = self.get_remaining_ctis()
        num_ctis = min(len(remaining_ctis), max_num_ctis)
        return random.sample(remaining_ctis, num_ctis)

    def num_ctis_remaining(self):
        return len(self.ctis) - len(self.ctis_eliminated)

    def get_cti_clusters(self, serialize=False):
        """ Cluster CTIs according to various metrics."""
        
        # 1. Cluster by action name.
        actions = set()
        cti_clusters = {}
        for c in self.ctis:
            actions.add(c.action_name)
            if c.action_name not in cti_clusters:
                cti_clusters[c.action_name] = []
            cti_clusters[c.action_name].append(c)

        if serialize:
            return {a:[str(hash(c)) for c in cti_clusters[a]] for a in cti_clusters}
        return cti_clusters
    
    def to_apalache_inductive_proof_obligation(self, modname, action=None):
        """ Export this node and support lemmas as base for Apalache checking."""
        # "THEOREM IndAuto /\ Next => IndAuto'"
        metadir = f"apa_indcheck/{modname}"
        out_str = "\n"
        action_suffix = "" if action is None else action + "_"
        def_name = f"{self.expr}_{action_suffix}IndCheck"
        next_expr = "Next" if action is None else action
        outdir = f"{metadir}/{self.expr}"
        if action is not None:
            outdir += "_" + action
        smtprof = ""
        # smtprof = "--smtprof" # can enable if you want.
        apa_cmd = f"""JVM_ARGS="-Xss16m" ./apalache/bin/apalache-mc check --init={def_name} --next={next_expr} --inv={self.expr} --cinit=CInit --tuning-options='search.invariantFilter=1->.*' --no-deadlock --length=1 {smtprof} --debug --out-dir={outdir} --run-dir={outdir} {modname}.tla"""
        out_str += f"(** \nApalache command:\n{apa_cmd}\n **)\n"
        out_str += f"{def_name} == \n"
        typeok = "ApaTypeOK"
        land = "/\\"
        out_str += f"  {land} {typeok}\n"
        for a in self.children:
            supports = [c.expr for c in self.children[a]]
            supports_conj = land.join(supports)
            supports_list = ",".join(supports)
            if action is not None and a != action:
                continue
            out_str += f"  \* Action support lemmas: {a}\n"
            for s in supports:
                out_str += f"  {land} {s}\n"
        out_str += f"  \* Target lemma.\n"
        out_str += f"  {land} {self.expr}\n"
        return {
            "out_str": out_str,
            "cmd": apa_cmd
        }

    def to_tlaps_proof_obligation(self, actions, action_def_expands, lemma_def_expands, global_def_expands, assumes_list, theorem_name=None):
        """ Export this node and support lemmas as TLAPS proof obligation skeleton."""
        # "THEOREM IndAuto /\ Next => IndAuto'"
        
        typeok = "TypeOK"
        land = " /\\ "

        oblig_source_map = {}

        # Collect all support lemmas across all actions.
        all_support_lemmas = []
        for (ind,a) in enumerate(actions):
            if a in self.children:
                all_support_lemmas += [c.expr for c in self.children[a]]

        out_str = ""
        top_level_goal_anteced = [typeok] + all_support_lemmas + [self.expr]
        top_level_goal_anteced_str = land.join(top_level_goal_anteced)
        theorem_name_str = ""
        if theorem_name is not None:
            theorem_name_str = f"{theorem_name} =="
        # Make the top level goal as proving this target lemma inductive, using all support lemmas
        # concatenated from all actions.
        out_str += f"THEOREM {theorem_name_str} {top_level_goal_anteced_str} /\\ Next => {self.expr}'\n"

        if len(assumes_list) > 0:
            assumes_str = ",".join(assumes_list)
            out_str += f"""  <1>. USE {assumes_str}\n"""

        # Export obligations for all actions.
        for (ind,a) in enumerate(actions):
            support_set = []
            # For actions without any children the support set will be empty.
            if a in self.children:
                support_set = [c.expr for c in self.children[a]]

            supports_list = [typeok] + support_set + [self.expr]
            supports_conj_str = land.join(supports_list)
        
            defs_list = [typeok] + support_set + [a, a.replace('Action', ''), self.expr]
            # If action is listed in custom proof def expands list, add those definitions here.
            defs_list += global_def_expands
            if a in action_def_expands:
                defs_list += action_def_expands[a]
            if self.expr in lemma_def_expands:
                defs_list += lemma_def_expands[self.expr]
            out_str += f"  \* ({self.expr},{a})\n"
            oblig_source_map[(self.expr, a)] = len(out_str.split("\n")) - 1
            out_str += f"""  <1>{ind+1}. {supports_conj_str}{land}{a} => {self.expr}'"""
            out_str += f" BY DEF {','.join(defs_list)}\n" 
            out_str += ""

        out_str += f"<1>{len(actions)+1}. " + "QED BY " + (",".join([f"<1>{ind}" for ind in range(1, len(actions)+1)])) + " DEF Next"
        out_str += "\n"
        return {
            "out_str": out_str,
            "source_map": oblig_source_map
        }

class StructuredProof():
    """ Structured safety proof of an inductive invariant. 
    
    May also represent a "partial" proof i.e. one in an incomplete state that is yet to be completed.
    """

    def __init__(self, root=None, load_from_obj=None, specname=None, actions=None, spec_defs=None, nodes=None, safety=""):
        # Top level goal expression to be proven.
        self.safety_goal = safety
        self.root = root 

        self.nodes = nodes

        self.specname = specname
        self.proof_base_filename = f"benchmarks/{self.specname}.proof"

        self.actions = actions

        self.spec_defs = spec_defs
        self.vars_in_action = dict()

        self.ctigen_state = "idle"

        self.current_config_instance_index = -1

        self.save_tex = True

        if load_from_obj:
            self.load_from(load_from_obj)

    def walk_proof_graph(self, curr_node, visit_fn=None, seen = set(), all_nodes=[]):
        if visit_fn is not None:
            visit_fn(curr_node)
        seen.add(curr_node.expr)
        all_nodes.append(curr_node)
        for a in curr_node.children:
            for c in curr_node.children[a]:
                # print(c)
                if c is not None and c.expr not in seen:
                    self.walk_proof_graph(c, visit_fn, seen, all_nodes=all_nodes)

    def to_tlaps_proof_skeleton(self, tlaps_proof_config, add_lemma_defs=None, seed=None, tag=None, workdir="benchmarks", include_typeok=True):
        """ Export proof graph obligations to TLAPS proof structure."""
        seed_str = ""
        if seed is not None:
            seed_str = f"_{seed}"
        tag_str = ""
        if tag is not None:
            tag_str = f"_{tag}"
        modname = self.specname + f"_IndDecompProof{seed_str}{tag_str}"
        fname = f"{workdir}/" + modname + ".tla"
        f = open(fname, 'w')
        spec_lines = f"---- MODULE {modname} ----\n"
        spec_lines += f"EXTENDS {self.specname},TLAPS\n"

        # Maintain a source map which records lines that proof obligations live on.
        lemma_source_map = {}

        nodes = []
        seen = set()
        self.walk_proof_graph(self.root, seen=seen, all_nodes=nodes)
        # print(nodes)

        # Some proof graph info.
        spec_lines += "\n"
        spec_lines += f"\* Proof Graph Stats\n"
        spec_lines += f"\* ==================\n"
        spec_lines += f"\* seed: {seed}\n"
        spec_lines += f"\* num proof graph nodes: {len(nodes)}\n"
        spec_lines += f"\* num proof obligations: {len(nodes) * len(self.actions)}\n"
        in_degrees = list(map(lambda n : n.num_children(), nodes))
        mean_in_degree = sum(in_degrees)/len(nodes)
        sorted_in_degrees = list(sorted(in_degrees))
        median_in_degree = sorted_in_degrees[len(sorted_in_degrees)//2]
        
        assumes_name_list = []

        if add_lemma_defs is not None:
            for (name,expr) in add_lemma_defs:
                spec_lines += f"{name} == {expr}\n"

        spec_lines += "\nIndGlobal == \n"
        spec_lines += f"  /\\ TypeOK\n"
        for n in nodes:
            spec_lines += f"  /\\ {n.expr}\n"

        assume_spec_lines = ""
        if "assumes" in tlaps_proof_config:
            for ind,assume in enumerate(tlaps_proof_config["assumes"]):
                name = f"A{ind}"
                assume_spec_lines += f"ASSUME {name} == {assume}\n"
                assumes_name_list.append(name)

        # Create a separate node for TypeOK to include as proof obligation.
        if include_typeok:
            typeok_node = StructuredProofNode("H_TypeOK", "TypeOK")
            nodes = [typeok_node] + nodes

        all_var_slices = []
        proof_obligation_lines = ""
        global_def_expands = []
        if "global_def_expands" in tlaps_proof_config:
            global_def_expands = tlaps_proof_config["global_def_expands"]
        for ind,n in enumerate(nodes):
            # if len(n.children.keys()) == 0:
                # continue
            # for a in n.children:
                # if a in self.lemma_action_coi:
                    # slicevars = self.lemma_action_coi[a][n.expr]
                    # all_var_slices.append(slicevars)

            if n.expr == self.root.expr:
                proof_obligation_lines += "\n\* (ROOT SAFETY PROP)"
            proof_obligation_lines += f"\n\*** {n.expr}\n"

            curr_line = len(proof_obligation_lines.split("\n")) - 1

            ret = n.to_tlaps_proof_obligation(self.actions, 
                                                tlaps_proof_config["action_def_expands"], 
                                                tlaps_proof_config["lemma_def_expands"], 
                                                global_def_expands,
                                                assumes_name_list,
                                                theorem_name=f"L_{ind}")
            proof_obligation_lines += ret["out_str"]
            # print(ret["source_map"])
            for obl in ret["source_map"]:
                lemma_source_map[ret["source_map"][obl] + curr_line] = obl
            proof_obligation_lines += "\n"

        var_slice_sizes = [len(s) for s in all_var_slices]
        if len(var_slice_sizes):
            mean_slice_size = mean(var_slice_sizes)
        else:
            mean_slice_size = 0

        # Add lines to the spec.
        spec_lines += "\n\n"
        spec_lines += f"\* mean in-degree: {mean_in_degree}\n"
        spec_lines += f"\* median in-degree: {median_in_degree}\n"
        spec_lines += f"\* max in-degree: {max(in_degrees)}\n"
        spec_lines += f"\* min in-degree: {min(in_degrees)}\n"
        spec_lines += f"\* mean variable slice size: {mean_slice_size}\n"
        spec_lines += "\n"

        # Add assumes.
        spec_lines += assume_spec_lines

        # Re-adjust source map.
        curr_line = len(spec_lines.split("\n"))
        lemma_source_map_new = {}
        for ln in lemma_source_map:
            lemma_source_map_new[ln + curr_line] = lemma_source_map[ln]
        lemma_source_map = lemma_source_map_new

        # Add proof obligation lines.
        spec_lines += proof_obligation_lines


        #
        # For a sanity check, add as a top level theorem the property that the conjunction of lemma nodes
        # is inductive.
        #

        # Initiation. 
        spec_lines += "\* Initiation." 
        spec_lines += "\nTHEOREM Init => IndGlobal\n"
        init_defs = ",".join([f"{n.expr}" for ind,n in enumerate(nodes)])
        if len(assumes_name_list) > 0:
            spec_lines += "    <1> USE " + ",".join(assumes_name_list) + "\n"
        if len(global_def_expands) > 0:
            spec_lines += "<1> USE DEF " + ",".join(global_def_expands) + "\n"
        for ind,n in enumerate(nodes):
            # Decomposed proof obligation for each oncjunction.
            spec_lines +=  f"    <1>{ind}. Init => {n.expr} BY DEF Init, {n.expr}, IndGlobal\n"
        spec_lines += "    <1>a. QED BY " + ",".join([f"<1>{ind}" for ind in range(len(nodes))]) + " DEF IndGlobal\n"
        spec_lines += "\n"


        # Consecution.
        spec_lines += "\* Consecution.\n" 
        spec_lines += "THEOREM IndGlobal /\\ Next => IndGlobal'\n"
        spec_lines += "  BY " + ",".join([f"L_{ind}" for ind,n in enumerate(nodes)]) + " DEF Next, IndGlobal\n"

        spec_lines += "\n"
        spec_lines += "===="
        logging.info(f"Saving proof graph TLAPS obligations to file '{fname}'.")
        f.write(spec_lines)
        f.close()
        return {
            "tlaps_filename": fname,
            "lemma_source_map": lemma_source_map
        }


    def apalache_check_all_nodes(self, save_dot=False, lemma_filter=None):
        # Save Apalache proof obligations to own spec file.
        self.to_apalache_proof_obligations()

        # Check all the obligations.
        nodes = []
        seen = set()
        self.walk_proof_graph(self.root, seen=seen, all_nodes=nodes)
        modname = self.specname + "_ApaIndProofCheck"
        cmds = []
        node_exprs = []
        metadir = f"apa_indcheck/{modname}"

        clean_cmd = f"rm -rf {metadir}"
        proc = subprocess.Popen(clean_cmd, shell=True, stderr=subprocess.PIPE, cwd="benchmarks")
        exitcode = proc.wait()

        # nodes = nodes[:6]
        # Just the 3 nodes that we expect to have breakages in AsyncRaft.
        if lemma_filter is not None:
            # filtered = [
            #     "H_NoLogDivergence",    
            #     "H_CommitIndexCoveredOnQuorum", 
            #     "H_CommitIndexInAppendEntriesImpliesCommittedEntryExists"
            # ]
            nodes = [n for n in nodes if n.expr in lemma_filter]

        do_per_action_checks = True

        print(f"All {len(nodes)} lemmas to check:")
        for n in nodes:
            print(f"- `{n.expr}`")
        
        # Gather all proof checking commands to run.
        for n in nodes:
            obl = n.to_apalache_inductive_proof_obligation(modname)
            cmd = obl["cmd"]

            if do_per_action_checks:
                for a in self.actions:
                    obl = n.to_apalache_inductive_proof_obligation(modname, action=a)
                    cmd = obl["cmd"]
                    cmds.append(cmd)
                    node_exprs.append((n.expr, a))
            else:
                # proc = subprocess.Popen(cmd, shell=True, stderr=subprocess.PIPE, cwd="benchmarks")
                # out = proc.stdout.read().decode(sys.stdout.encoding)
                # exitcode = proc.wait()
                # print("EXIT CODE:", exitcode)
                # if exitcode != 0:
                    # raise Exception(f"Apalache proof check failed for node '{n.expr}'. Command: " + cmd)
                cmds.append(cmd)
                node_exprs.append(n.expr)
        
        #
        # Submit all commands to a multiprocessing pool to run in parallel.
        #
        num_threads = 4
        cmds_to_run = list(zip(cmds, node_exprs))
        # print("CMDS TO RUN:", cmds_to_run)
        pool = multiprocessing.Pool(processes=num_threads)
        results = pool.map(runcmd, cmds_to_run)
        pool.close()
        pool.join()

        # Optionally save graph with proof status map.
        status_map = {r[0]:r[1] for r in results}
        # status_map = {}

        # print("RESULTS:", results)

        # If there are any obligations that failed, then now go back and check these per action.
        # print("---- Checking to see if any obligations failed.")
        # sys.stdout.flush()
        # for ind,r in enumerate(results):
        #     # Error was found.
        #     if r[1] != 0:
        #         for a in self.actions:
        #             obl = nodes[ind].to_apalache_inductive_proof_obligation(modname, action=a)
        #             cmd = obl["cmd"]
        #             # Just run the command now.

        #             start = time.time()
        #             proc = subprocess.Popen(cmd, shell=True, stderr=subprocess.PIPE, cwd="benchmarks")
        #             exitcode = proc.wait()
        #             duration = int(time.time() - start)
        #             print("EXIT CODE:", exitcode)
        #             res = ((r[0],a), exitcode, duration)
        #             status_map[(r[0], a)] = res[1]
        #             sys.stdout.flush()

            # Otherwise, just save the results on a per action basis.
            # else:
            #     for a in self.actions:
            #         status_map[(r[0], a)] = r[1]

        # print("- Proof status Map")
        # for s in status_map:
        #     print(s, status_map[s])

        if save_dot:
            self.save_as_dot(f"benchmarks/{self.specname}_proof_with_status.dot", omit_labels=True, proof_status_map=status_map)

        print(f"--- Proof checking RESULTS ({len(cmds)} total obligations checked, for {len(nodes)} lemmas):")
        error_found = False
        for r in results:
            if r[1] != 0:
                print(r, "ERROR")
                error_found = True
            else:
                print(r)
        if error_found:
            print("*** Some ERRORs found:")
            for r in results:
                if r[1] != 0:
                    print(r, "ERROR")
                    error_found = True
        else:
            print(f"No errors found in proof checking! ({len(cmds)} obligations checked, for {len(nodes)} lemmas).")


    def to_apalache_proof_obligations(self):
        """ Export proof graph obligations to TLAPS proof structure."""
        modname = self.specname + "_ApaIndProofCheck"
        f = open("benchmarks/" + modname + ".tla", 'w')
        spec_lines = f"---- MODULE {modname} ----\n"
        spec_lines += f"EXTENDS {self.specname}\n"

        nodes = []
        seen = set()
        self.walk_proof_graph(self.root, seen=seen, all_nodes=nodes)
        # print(nodes)

        stats = {}

        # Some proof graph info.
        spec_lines += "\n"
        spec_lines += f"\* Proof Graph Stats\n"
        spec_lines += f"\* ==================\n"
        spec_lines += f"\* num proof graph nodes: {len(nodes)}\n"
        in_degrees = list(map(lambda n : n.num_children(), nodes))
        mean_in_degree = sum(in_degrees)/len(nodes)
        median_in_degree = median(in_degrees)
        sorted_in_degrees = list(sorted(in_degrees))
        median_in_degree = sorted_in_degrees[len(sorted_in_degrees)//2]
        spec_lines += f"\* mean in-degree: {mean_in_degree}\n"
        spec_lines += f"\* median in-degree: {median_in_degree}\n"
        spec_lines += f"\* max in-degree: {max(in_degrees)}\n"
        spec_lines += f"\* min in-degree: {min(in_degrees)}\n"

        all_var_slices = []
        apa_cmds = []
        for n in nodes:
            # if len(n.children.keys()) == 0:
            #     continue
            # if n.expr == self.root.expr:
                # spec_lines += "\n\* (ROOT SAFETY PROP)"
            # spec_lines += f"\n\* -- {n.expr}\n"
            obl = n.to_apalache_inductive_proof_obligation(modname)
            spec_lines += obl["out_str"]

            # Also add a separate obligation for each action.
            for a in self.actions:
                obl = n.to_apalache_inductive_proof_obligation(modname, action=a)
                spec_lines += obl["out_str"]

            apa_cmds.append(obl["cmd"])
            spec_lines += "\n"

            for a in n.children:
                if a in self.lemma_action_coi:
                    slicevars = self.lemma_action_coi[a][n.expr]
                    all_var_slices.append(list(slicevars))
        spec_lines += "\n"
        spec_lines += "===="
        f.write(spec_lines)
        f.close()

        metadir = f"apa_indcheck/{modname}"

        f = open(f"benchmarks/apacheck_{self.specname}.sh", 'w')
        f.write("#!/bin/bash\n\n")
        f.write(f"#\n# Inductive proof obligations for '{self.specname}'\n")
        f.write(f"# Total num proof obligations: {len(nodes)}\n#\n\n")
        f.write(f"rm -rf {metadir}\n")
        for cmd in apa_cmds:
            f.write(cmd)
            f.write("\n")
        f.close()

        # Dump stats JSON file.
        stats["mean_in_degree"] = mean_in_degree
        stats["median_in_degree"] = median_in_degree
        stats["all_var_slices"] = all_var_slices
        stats["num_lemmas"] = len(nodes)
        stats["num_actions"] = len(self.lemma_action_coi.keys())

        # TODO: Could compute this more simply.
        all_vars = set()
        for x in all_var_slices:
            all_vars.update(set(x))
        stats["num_state_vars"] = len(all_vars)

        stats["median_slice_size"] = median([len(s) for s in all_var_slices])
        if len(all_vars) == 0:
            stats["median_slice_pct"] = 0
        else:
            stats["median_slice_pct"] = stats["median_slice_size"] / len(all_vars)

        f = open(f"benchmarks/{self.specname}_proofstats.json", 'w')
        json.dump(stats, f, indent=2)
        f.close()

        # Also get some general spec stats for LaTeX stats.
        spec_path = f"benchmarks/{self.specname}.tla"
        res = count_spec_loc(spec_path)
        stats["spec_loc"] = res["spec_loc"]
        stats["proof_loc"] = res["proof_loc"]

        # Save proof graph stats in LaTeX format too.
        f = open(f"benchmarks/{self.specname}_proofstats.tex", 'w')
        tex_stats = [
            "num_state_vars", "mean_in_degree", "median_slice_size", 
            "median_in_degree", "num_lemmas", "num_actions", "spec_loc",
            "proof_loc"
        ]
        for stat in tex_stats:
            f.write("\\newcommand*{\\%s%s}{%d}\n" % (self.specname.replace("_", ""), stat.replace("_", ""), stats[stat]))
        stat = "median_slice_pct"
        f.write("\\newcommand*{\\%s%s}{%.2f}\n" % (self.specname.replace("_", ""), stat.replace("_", ""), stats[stat]))
        f.close()


    def serialize(self, include_ctis=True, cti_hashes_only=False):
        return {
            "safety": self.safety_goal, 
            "root": self.root.serialize(include_ctis=include_ctis, cti_hashes_only=cti_hashes_only),
            "nodes": [n.serialize(serialize_children=True, cti_hashes_only=cti_hashes_only) for n in self.nodes],
            "spec_defs": self.spec_defs,
            "vars_in_action": {a:list(v) for a,v in self.vars_in_action.items()},
            "vars_in_lemma_defs": {a:list(v) for a,v in self.vars_in_lemma_defs.items()},
            "lemma_action_coi": {a:{l:list(self.lemma_action_coi[a][l]) for l in self.lemma_action_coi[a]} for a in self.lemma_action_coi}
        }
    
    def save_proof(self, include_json=False, include_dot=False):
        """ Visualize proof structure in HTML format for inspection, and serialize to JSON. """
        filename = f"{self.proof_base_filename}.html"
        pickle_filename = f"{self.proof_base_filename}.pickle"
        dot_filename = f"{self.proof_base_filename}.dot"

        print(f"Saving latest proof HTML to '{filename}'")
        with open(filename, 'w') as f:
            html = self.gen_html(self, self.specname)
            f.write(html)

        # Save structured proof object.
        if include_json:
            json_filename = f"{self.proof_base_filename}.json"
            print(f"Saving latest proof JSON to '{json_filename}'")
            with open(json_filename, 'w') as f:
                proof_json = self.serialize()
                json.dump(proof_json, f, indent=2)

        print(f"Saving latest proof pickled to '{pickle_filename}'")
        # Save pickled proof object.
        with open(pickle_filename, 'wb') as f:
            pickle.dump(self, f)

        if include_dot:
            print(f"Saving latest proof as DOT to '{dot_filename}'")
            self.save_as_dot(dot_filename)
            self.save_as_dot(dot_filename, omit_labels=True)

        print(f"Finished saving proof objects.")

    def load_from(self, obj):
        self.safety_goal = obj["safety"]
        self.root = StructuredProofNode(load_from_obj=obj["root"])

    def root_to_html(self):
        html = "<ul>"+self.root.to_html()+"</ul>"
        return html

    def node_cti_html(self, node):
        html = ""
        max_ctis_to_show = 30
        cti_sort_key = lambda c : c.cost
        # remaining_ctis_sampled = node.sample_remaining_ctis(max_ctis_to_show, sort_by = cti_sort_key)

        # Sort remaining CTIs by cost.
        remaining_ctis = sorted(node.get_remaining_ctis(), key = cti_sort_key)
        remaining_ctis_sampled = remaining_ctis[:max_ctis_to_show]
        # remaining_ctis_sampled = node.sample_remaining_ctis(max_ctis_to_show, sort_by = cti_sort_key)

        # Aggregate statistics.
        all_remaining_ctis = node.get_remaining_ctis()
        cti_action_names = [cti.getActionName() for cti in all_remaining_ctis]
        action_names_set = set(cti_action_names)
        action_counts = {a:cti_action_names.count(a) for a in action_names_set}

        html += f"<div class='cti-container cti_{node.expr}'>"
        action_name_info = ','.join([a + f"({action_counts[a]})" for a in list(action_names_set)])
        html += f"<div>Actions present in CTIs: [{action_name_info}]</div>"
        for i,one_cti in enumerate(remaining_ctis_sampled):
            html += f"<div class='cti-box'>"
            html += (f"<h3>CTI {i} for {node.expr} (Action: {one_cti.getActionName()}, cost={one_cti.cost})</h3>\n")
            html += ("<pre>")
            for k,s in enumerate(one_cti.getTrace().getStates()):
                html += (f"<b>CTI State {k}</b> \n")
                html += (s.pretty_str())
                html += ("\n")
            html += ("</pre>")
            html += "</div>"  
        html += "</div>"  
        # for c in node.children_list():
            # html += self.node_cti_html(c)
        return html      

    def cti_viewer_html(self):
        return self.node_cti_html(self.root)

    def dump(self):
        out_file = open("proof.proof", 'w')
        json.dump(self.serialize(), out_file, indent=2)

    def gen_html(self, indgen, specname):
        """ Generate HTML visualization of structured proof. """
        html = ""

        html += ("<head>")
        html += ('<link rel="stylesheet" type="text/css" href="proof.css">')
        html += '<link rel="stylesheet" href="https://cdnjs.cloudflare.com/ajax/libs/font-awesome/4.7.0/css/font-awesome.min.css">'
        # html += """<script src="{{ url_for('static',filename='proof.js') }}"> </script>"""
        # html += ("""<link rel="stylesheet" type="text/css" href="{{ url_for('static',filename='proof.css') }}">""")
        html += '<script src="https://ajax.googleapis.com/ajax/libs/jquery/3.6.4/jquery.min.js"></script>'
        html += """
        <!-- CytoscapeJS (for graph visualizations) -->
        <script src="https://cdnjs.cloudflare.com/ajax/libs/cytoscape/3.20.0/cytoscape.min.js" integrity="sha512-cjmYAonfXK+azDmWqvnqq8xmygHRHqVI7S0zuRxQnvcYVeoakwthRX6pPKoXfG1oIjDvMUtteRV9PhQjJwKWxQ==" crossorigin="anonymous" referrerpolicy="no-referrer"></script>
        <script src="https://unpkg.com/dagre@0.7.4/dist/dagre.js"></script>
        <script src="https://cdn.jsdelivr.net/npm/cytoscape-dagre@2.5.0/cytoscape-dagre.min.js"></script>
        <script src="https://cdn.jsdelivr.net/npm/underscore@1.13.6/underscore-umd-min.js"></script>
        """

        html += ('<script type="text/javascript" src="proof.js"></script>')
        html += ("</head>")

        # html += ("<div>")
        html += ("<div hidden>")
        html += (f"<h1>Proof Structure: {specname}</h1>")
        # html += (f"<div>seed={self.indgen.seed}, num_simulate_traces={self.indgen.num_simulate_traces}</div>")
        
        # html += (self.root_to_html())
        
        html += ("</div>")
        html += ("<div>") 
        # html += (f"<h2>Sample of {self.root.num_ctis_remaining()} Remaining CTIs for {self.root.expr}</h2>")      
        # html += (f"<h2>Sample of remaining CTIs</h2>")      
        html += (f"<h2 hidden>Sample of remaining CTIs</h2>")      
        
        html += self.cti_viewer_html()
        
        # for i,one_cti in enumerate(remaining_ctis):
        #     html += "<div class='cti-box'>"
        #     html += (f"<h3>CTI {i}</h3>\n")
        #     html += ("<pre>")
        #     for i,s in enumerate(one_cti.getTrace().getStates()):
        #         html += (f"<b>CTI State {i}</b> \n")
        #         html += (s.pretty_str())
        #         html += ("\n")
        #     html += ("</pre>")
        #     html += "</div>"
        html += ("</div>")

        return html

    def add_node_to_dot_graph(self, dot, node, seen=set(), omit_labels=False, proof_status_map=None):
        """ Add this node and its children, recursively, to DOT graph."""
        color = "black"
        penwidth="2"
        if node.expr == self.safety_goal:
            color="black"
            penwidth="5"
            style="filled"
        else:
            style="rounded corners"

        if node.expr in seen:
            return
        # print("NODEEXP:", node.expr)

        nodes_to_include_var_slice = [
            ("H_LeaderMatchIndexValid", "ClientRequestAction"),
            ("H_LeaderMatchIndexBound", "HandleAppendEntriesResponseAction"),
            ("H_QuorumsSafeAtTerms", "BecomeLeaderAction")
        ]
        
        lemmas_to_always_show = [
            # AsyncRaft key lemmas.
            "H_LeaderMatchIndexValid",
            "H_LeaderMatchIndexBound",
            "H_LeaderMatchIndexValidAppendEntries",
            self.safety_goal,
            "H_LogMatching",
            "H_LogMatchingAppendEntries",
            "H_OnePrimaryPerTerm",
            "H_PrimaryHasEntriesItCreated",
            "H_QuorumsSafeAtTerms",
            # "H_CommitIndexInAppendEntriesImpliesCommittedEntryExists",
            "H_CommitIndexCoveredOnQuorum",

            # Zab lemmas.
            "H_PrefixConsistency",
            "H_CommittedEntryExistsInLeaderHistory",
            "H_CommittedEntryExistsOnQuorum",
            "H_UniqueLeadership",
            "H_UniqueEstablishedLeader",
            "H_TxnZxidsUniqueHistoriesAndMessages",
            "H_TwoLeadersCantHaveSameCEPOCH",

            # TwoPhase lemmas.
            "H_RMCommittedImpliesNoRMsWorking",
            "H_RMCommittedImpliesNoAbortMsg",
            "H_RMAbortedImpliesNoCommitMsg"
        ]

        lemmas_to_show_for_graph_diff = [
            "H_LeaderMatchIndexValid",
            self.safety_goal
        ]

        if not omit_labels or node.expr in lemmas_to_always_show:
            # Make selected lemmas display larger.
            label = node.expr.replace("H_", "")
            # style += ",font=\\huge"
            # if node.expr not in lemmas_to_show_for_graph_diff and self.specname == "AsyncRaft":
            #     texbl = "\phantom{\Huge" + "\emph{" + label + "}}"
            # else:
            texbl = "\Huge" + "\emph{" + label + "}"
        else:
            label = "L_{" + str(self.dotnode_ind) + "}"
            self.dotnode_ind += 1
            texbl = f"${label}$"

        dot.node(node.expr, color=color, fillcolor="green!50", shape="box", font="\Huge", style=style, penwidth=penwidth, label=label, texlbl=texbl)
        seen.add(node.expr)

        actions_to_always_show = {
            "AppendEntriesAction" : "AEAction",
            "AcceptAppendEntriesRequestAppendAction": "AcceptAEAction",
            "AcceptAppendEntriesRequestLearnCommitAction": "LearnCommitAction",
            # "ClientRequestAction",
            # "BecomeLeaderAction"
            "RMChooseToAbortAction": "RMChooseAbortAction",
            "RMRcvAbortMsgAction": "RMRcvAbortMsgAction",
            "RMRcvCommitMsgAction": "RMRcvCommitMsgAction"
        }

        edges_to_highlight = [
            ("H_LogMatching",("H_LogMatchingAppendEntries", "AppendEntriesAction")),
            ("H_LogMatchingAppendEntries",("H_LogMatching", "AcceptAppendEntriesRequestAppendAction")),
            # ("H_LeaderMatchIndexBound", "HandleAppendEntriesResponseAction"),
            # ("H_QuorumsSafeAtTerms", "BecomeLeaderAction")
        ]

        # Add sub-nodes for each action child.
        for ai,action in enumerate(self.actions):
            action_node_id = node.expr + "_" + action
            if omit_labels and action not in actions_to_always_show:
                label = "A_{" + str(ai) + "}"
            else:
                if action in actions_to_always_show:
                    label = actions_to_always_show[action].replace("Action", "")
                else:
                    label = action.replace("Action", "")

            # Merge 'UpdateTerm' action nodes for now.
            if action.startswith("UpdateTerm"):
                action_node_id = node.expr + "_" + "UpdateTermAction"
                label = "A_{" + str(ai) + "}"

            slice_label = ""
            if (node.expr, action) in nodes_to_include_var_slice:
                slice_vars = self.lemma_action_coi[action][node.expr]
                sliced = ",".join(slice_vars)
                slice_font_size="\Larger"
                slice_label="-90:{%s\{%s\}}" % (slice_font_size,sliced)

                # slice_label=""

            fillcolor="lightgray"
            proof_status_style = ""
            if proof_status_map is not None and (node.expr, action) in proof_status_map and proof_status_map[(node.expr, action)] != 0:
                # fillcolor = ""
                proof_status_style = ",broken"

            if action in node.children:
                # style = f"fill={fillcolor}"
                style = f"fill={fillcolor},proofactionnode" + proof_status_style
                if slice_label != "":
                    style += ",label=" + slice_label
                edgestyle = "proofactionedge"
                if (node.expr, action) in [x[1] for x in edges_to_highlight]:
                    edgestyle += ",edgehighlight"
                dot.node(action_node_id, label=label, style=style, fillcolor=fillcolor)
                dot.edge(action_node_id, node.expr, style=edgestyle)
            # If the action is not in the node's children, we may still add it to the graph in case proof status is red for it.
            else:
                if proof_status_map is not None and (node.expr, action) in proof_status_map and proof_status_map[(node.expr, action)] != 0:
                    # fillcolor = "red"
                    style = "proofactionedge"
                    style += proof_status_style
                    dot.node(action_node_id, label=label, style="proofactionnode," + proof_status_style, fillcolor=fillcolor)
                    dot.edge(action_node_id, node.expr, style=style)                


        for action in node.children:
            for c in node.children[action]:
                action_node_id = node.expr + "_" + action
                if action.startswith("UpdateTerm"):
                    action_node_id = node.expr + "_" + "UpdateTermAction"
                # dot.edge(c.expr, node.expr)
                style = "prooflemmaedge"
                if (c.expr, (node.expr, action)) in edges_to_highlight:
                    style += ",edgehighlight"
                dot.edge(c.expr, action_node_id, style=style)
                self.add_node_to_dot_graph(dot, c, seen=seen, omit_labels=omit_labels, proof_status_map=proof_status_map)


    def save_as_dot(self, out_file, omit_labels=False, proof_status_map=None):
        """ Generate DOT graph representation of this structured proof. """
        dot = graphviz.Digraph('proof-graph', strict=True, comment='Proof Structure')  
        # dot.graph_attr["rankdir"] = "LR"
        dot.node_attr["fontname"] = "courier"
        dot.node_attr["shape"] = "box"
        
        # Store all nodes.
        self.dotnode_ind = 0
        self.add_node_to_dot_graph(dot, self.root, seen=set(), omit_labels=omit_labels, proof_status_map=proof_status_map)


        # print("Final proof graph:")
        # print(dot.source)
        if omit_labels:
            dot.render(out_file + "_nolabels", quiet=True)
            tex_out_file = out_file + "_nolabels.tex"
        else:
            dot.render(out_file, quiet=True)
            tex_out_file = out_file + ".tex"

        # Convert to TeX.
        if self.save_tex:
            output_capture = io.StringIO()

            # Use context manager to redirect stdout
            with contextlib.redirect_stdout(output_capture):
                import os
                old_stdout = sys.stdout # backup current stdout
                sys.stdout = open(os.devnull, "w")
                figpreamble=f"""
                \Large
                """
                if self.specname == "AsyncRaft":
                    if "proof_with_status" in out_file: 
                        figpreamble += "\AsyncRaftWithProofStatusFigPreamble{}"
                    else:
                        figpreamble += "\AsyncRaftFigPreamble{}"


                texcode = dot2tex.dot2tex(dot.source, debug=False, output="dot2tex.log", format='tikz', figpreamble=figpreamble, autosize=True, crop=False, figonly=True, texmode="math")
                sys.stdout = old_stdout # reset old stdout
                f = open(tex_out_file, 'w')
                f.write(texcode)
                f.close()

        return dot.source

    def get_node_by_name_rec(self, start_node, name, seen=set()):
        # If this was our target node, terminate.
        if name == start_node.name:
            return start_node
        else:
            seen.add(start_node.name)
            for c in start_node.children_list():
                if c.name not in seen:
                    ret = self.get_node_by_name_rec(c, name, seen=seen)
                    if ret is not None:
                        return ret
            return None

    def get_node_by_name(self, start_node, name):
        seen = set()
        ret = self.get_node_by_name_rec(start_node, name, seen=seen)
        if ret is not None:
            return ret

        # If you didn't find the node via traversing from the
        # start node, also check the set of all nodes.
        for n in self.nodes:
            if name == n.name:
                return n
        return None

    def compute_cti_elimination_for_node(self, indgen, node, ctis, action, constants_obj=None):
        """ Compute CTIs that are eliminated by the children of this node, for given set of CTIs. """

        # Mapping from CTI id to CTI object.
        cti_table = {}
        for c in ctis:
            cti_table[str(hash(c))] = c

        # Compute CTIs that are eliminated by each of the "support lemmas" for this node i.e.
        # its set of direct children.

        # if action not in node.children:
            # return {}
        
        print(f"Checking elimination of {len(ctis)} CTIs for support lemmas of node ({node.name},{node.expr}), action={action}")

        # If action is not in node's chidlren, we still check CTI elimination to compute CTI costs.
        if action in node.children:
            node_children = node.children[action]
        else:
            node_children = []


        cti_info = indgen.check_cti_elimination(ctis, [
            (child.name,child.expr) for child in node_children
        ], constants_obj=constants_obj)

        ctis_eliminated = cti_info["eliminated"]
        cti_cost = cti_info["cost"]
        # print(cti_cost)

        # Assign costs for each node CTI.
        # print(len(ctis))
        # print("cost len:", len(cti_cost))
        for c in cti_cost:
            cost = cti_cost[c]
            cti_table[c].cost = cost
            # print(cti_table[c].action_name)
            # if cost == 0:
                # print(cti_table[c])
                # print(cost)

        # print("CTI eliminate response:", ctis_eliminated.keys())

        ctis_eliminated_unique = {}

        # print("CTIs eliminated by invs")

        # TODO: Account for CTIs at different parameter instances when computing unique CTI elimination.

        all_eliminated_ctis = set()
        all_eliminated_uniquely_ctis = {}
        out_degrees_of_unique_eliminated = set()
        for i,inv in enumerate(sorted(ctis_eliminated.keys(), key=lambda k : int(k.replace("Inv", "")))):
            # print(inv, ":", len(ctis_eliminated[inv]))
            # print(ctis_eliminated_by_invs[k])

            child_node = sorted(node_children, key=lambda x : x.expr)[i]
            child_node.parent = node

            # Update the set of eliminated CTIs.
            all_eliminated_ctis.update(ctis_eliminated[inv])
            child_node.parent_ctis_eliminated = set(ctis_eliminated[inv])

            # Compute the set of uniquely eliminated CTIs for this lemma.
            unique = ctis_eliminated[inv]
            for other in (ctis_eliminated.keys() - {inv}):
                unique = unique.difference(ctis_eliminated[other])
            ctis_eliminated_unique[inv] = unique

            # print("Unique:", len(unique))
            # print(ctis_eliminated_unique)

            child_node.parent_ctis_uniquely_eliminated = set(ctis_eliminated_unique[inv])

            all_eliminated_uniquely_ctis[child_node.name] = set(ctis_eliminated_unique[inv])
            # print(all_eliminated_uniquely_ctis)

            # TODO: problematic for multiple parameter instance case.
            # if action not in node.ctis_eliminated_uniquely:
                # node.ctis_eliminated_uniquely[action] = {}

            # node.ctis_eliminated_uniquely[action][child_node.name] = list(ctis_eliminated_unique[inv])




            # if len(child_node.parent_ctis_uniquely_eliminated) > 0:
            #     one_unique_cti = random.sample(child_node.parent_ctis_uniquely_eliminated, 1)
            #     for c in one_unique_cti:
            #         # Are the low outdegree CTIs among those CTIs that are uniquely eliminated?
                    
            #         # print("Sample of uniquely eliminated CTI:")
            #         # print(child_node.name)
            #         # print(c)

            #         # print([str(hash(x)) for x in node.ctis])
            #         uniq_cti_obj = [x for x in ctis if str(hash(x)) == c][0]
            #         # print(uniq_cti_obj.pretty_str())

            #         if indgen.cti_out_degrees:
            #             # print(len(indgen.cti_out_degrees))
            #             out_degree = indgen.cti_out_degrees[c]
            #             # print(type(c), c)
            #             # print("out_degree:", out_degree)
            #             out_degrees_of_unique_eliminated.add(out_degree)

        if indgen.cti_out_degrees:
            print("uniquely eliminated out degrees:", out_degrees_of_unique_eliminated)
        
        return {
            "eliminated": all_eliminated_ctis,
            "eliminated_uniquely": all_eliminated_uniquely_ctis
        }
        # return all_eliminated_ctis
        # node.ctis_eliminated = all_eliminated_ctis

    def local_grammar_synth(self, indgen, node, actions, constants_obj):
        #
        # Predicates specifically for
        # lemma: RequestVoteResponseToNodeImpliesNodeSafeAtTerm
        # action: HandleRequestVoteRequestAction
        # (AsyncRaft)
        #

        test_preds = [
            "MJ.mtype = RequestVoteRequest",
            "MJ.mterm <= currentTerm[MJ.mdest]",
            "MI.mtype = RequestVoteResponse",
            "MI.mtype = RequestVoteResponse /\ MI.mvoteGranted",
            "currentTerm[MI.mdest] >= MI.mterm"
        ]

        actions_uneliminated = [a for a in actions if len(node.ctis_eliminated[a]) == len(node.ctis[a])]
        action = None
        if len(actions_uneliminated) > 0:
            action = actions_uneliminated[0]
        action = "BecomeLeaderAction"

        print(action)

        if action not in indgen.spec_config["local_grammars"]:
            return
        
        if node.expr not in indgen.spec_config["local_grammars"][action]:
            return

        local_grammar = indgen.spec_config["local_grammars"][action][node.expr]
        test_preds = local_grammar["preds"]
        print("preds:", test_preds)

        # test_quant_vars = ["MI", "MJ"]
        test_quant_vars = local_grammar["quant_vars"]
        num_inv_cands = 80
        all_invs = mc.generate_invs(test_preds, num_inv_cands, 
                                        min_num_conjuncts=2, max_num_conjuncts=3, 
                                        process_local=False, 
                                        quant_vars=test_quant_vars)
        print(all_invs)
        invs = list(all_invs["raw_invs"])
        invs.sort()
        for i in invs:
            print(i)

        # indgen.quant_inv = "\\A MI \\in requestVoteMsgs : \\A MJ \\in requestVoteMsgs : "
        indgen.quant_inv = local_grammar["quant_inv"]
        indgen.initialize_quant_inv()

        # Bound max depth for checking invariants.
        max_depth = 100
        if "max_depth" in local_grammar:
            max_depth = local_grammar["max_depth"]
        sat_invs = indgen.check_invariants(invs, max_depth=max_depth)
        sat_invs_exprs = []
        for s in sat_invs:
            inv_index = int(s.replace("Inv", ""))
            sat_invs_exprs.append(invs[inv_index])
            print(s, invs[inv_index])


        ctis = node.ctis[action]
        cti_info = indgen.check_cti_elimination(ctis, [
            (f"Inv{i}", invexpr) for i,invexpr in enumerate(sat_invs_exprs)
        ], constants_obj=constants_obj)

        ctis_eliminated = cti_info["eliminated"]
        for e in ctis_eliminated:
            print(e, ctis_eliminated[e])
        cti_cost = cti_info["cost"]

        print("==")
        

    def gen_ctis_for_node(self, indgen, node, target_node_name = None):
        """ Routine that updates set of CTIs for each proof node. 
        
        Generates CTIs and computes the set eliminated by each node's support lemmas i.e. its direct children
        """

        # TODO: Eventually may want a different unique naming scheme for proof nodes.
        if target_node_name is not None and target_node_name != node.name:
            # Recurse right away if this is not the target node.
            for child_node in node.children_list():
                self.gen_ctis_for_node(indgen, child_node, target_node_name=target_node_name)   
            return         

        print(f"Generating CTIs for structured proof node ({node.name},{node.expr})")

        node.reset_ctis()
        self.save_proof()

        # Generate CTIs for this proof node, and sort and then sample to ensure a consistent
        # ordering for a given random seed.
        # For proof tree we look for single step inductive support lemmas.
        actions = self.actions
        if self.actions is None:
            actions = ["Next"]

        typeok_override = None
        # Optionally use special TypeOK for this node.
        if node.ctigen_typeok is not None:
            typeok_override = node.ctigen_typeok

        # for constants_obj in indgen.get_config_constant_instances():
        
        all_ctis_by_action = {a:set() for a in actions}
        node.ctis_eliminated = {a:set() for a in actions}
        for ci,constants_obj in enumerate(indgen.get_config_constant_instances()):

            self.current_config_instance_index = ci

            # Actions that we should skip and those for which we keep searching for CTIs.
            actions_to_skip = [a for a in actions if
                a in all_ctis_by_action and 
                # Some CTIs exist for this action, and they have not yet all
                # been eliminated.
                len(all_ctis_by_action[a]) > 0 and 
                len(node.ctis_eliminated[a]) < len(all_ctis_by_action[a])          
            ]
            actions_to_check = [a for a in actions if a not in actions_to_skip]


            # Generate CTIs for all actions at once, and then break down into each action when we get the returned set of CTIs
            # labeled by action.
            # print(f"Generating CTIs for action {actions_to_check} of node ({node.name},{node.expr})")
            print(f"=== Generating CTIs for node ({node.name},{node.expr}), constants instance:", constants_obj)
            # print(f"CONSTANT instance:", constants_obj)
            print("Actions to skip:", actions_to_skip)
            print("Actions to check:", actions_to_check)
            self.ctigen_state = "ctigen"

            new_ctis, _ = indgen.generate_ctis(
                                props=[(node.name, node.expr, "")], 
                                reseed=True, depth=1, 
                                view=node.cti_view, 
                                # actions=actions, 
                                # actions=actions_to_check, 
                                # actions=[action], 
                                typeok_override=typeok_override,
                                constants_obj=constants_obj)
            

            # Add to CTI lines that are projected onto only the variables
            # that appear only in its action and the target lemma.
            for c in new_ctis:
                action_vars = self.vars_in_action[c.action_name]
                lemma_vars = self.vars_in_lemma_defs[node.expr]
                # all_vars = action_vars.union(lemma_vars)

                # Use cone-of-influence for projection (COI).
                all_vars = self.lemma_action_coi[c.action_name][node.expr]
                for s in c.trace.getStates():
                    s.state_var_projection_map = {}
                    s.state_lines_action_vars_projected = []
                    for line in s.state_lines:
                        vartext = line.split("=")[0]
                        varname = vartext.split(" ")[1].strip()
                        s.state_var_projection_map[varname] = False
                        # Record projected variables and their state lines.
                        for a in all_vars:
                            if a in vartext:
                                s.state_var_projection_map[a] = True
                                # print(line)
                                s.state_lines_action_vars_projected.append(line)
                        # print(line)
                # print(c.action_name)

            # Break down CTIs by action.
            new_ctis_by_action = {a:set() for a in actions}
            for c in new_ctis:
                # print("TRACE---")
                # print(c.action_name)
                # print(c.trace_index)
                # for s in c.trace.getStates():
                #     print(s)
                if c.action_name in actions_to_check:
                    new_ctis_by_action[c.action_name].add(c)

            
            
            for action in actions_to_check:
                # Sample CTIs if we generated more than desired.
                logging.info(f"Number of CTIs generated for proof node, action '{action}': {len(new_ctis_by_action[action])}. Sampling a max of {indgen.max_proof_node_ctis} CTIs.")
                if len(new_ctis_by_action[action]) > indgen.max_proof_node_ctis:
                    new_ctis_by_action[action] = random.sample(new_ctis_by_action[action], indgen.max_proof_node_ctis)
                all_ctis_by_action[action].update(new_ctis_by_action[action])
                node.set_ctis(all_ctis_by_action[action], action)

            #
            # Compute CTI elimination broken down per action.
            #

            # for action in actions:
            ctis_eliminated_by_action = {}
            ctis_eliminated_uniquely_by_action = {}
            for action in actions_to_check:
                # ctis_for_action = list(all_ctis_by_action[action])
                # ctis_for_action.sort()

                # Set CTIs for this node based on those generated and sample if needed.
                # logging.info(f"Number of proof node CTIs generated for action '{action}': {len(new_ctis_by_action[action])}. Sampling a limit of {indgen.max_proof_node_ctis} CTIs.")
                
                # Just skip this action is there are no CTIs.
                if len(new_ctis_by_action[action]) == 0:
                    ctis_eliminated_by_action[action] = set()
                    ctis_eliminated_uniquely_by_action[action] = set()
                    continue

                self.ctigen_state = "ctielim"
                cti_elimination_info = self.compute_cti_elimination_for_node(indgen, node, new_ctis_by_action[action], action, constants_obj = constants_obj)
                
                ctis_eliminated = cti_elimination_info["eliminated"]
                ctis_eliminated_uniquely = cti_elimination_info["eliminated_uniquely"]
                
                # Store CTIs eliminated per action.
                ctis_eliminated_by_action[action] = ctis_eliminated
                ctis_eliminated_uniquely_by_action[action] = ctis_eliminated_uniquely
                # print("CTIs eliminated uniquely", ctis_eliminated_uniquely)

            print("Actions to check:", actions_to_check)


            # Update CTIs eliminated.
            for action in actions_to_check:
                logging.info(f"CTIs eliminated for action={action}: {len(ctis_eliminated_by_action[action])}")
                node.ctis_eliminated[action].update(ctis_eliminated_by_action[action])


                if action not in node.ctis_eliminated_uniquely:
                    node.ctis_eliminated_uniquely[action] = {}

                # print("CTIs eliminated uniquely", ctis_eliminated_uniquely_by_action[action])
                # print("Node.CTIs eliminated uniquely", node.ctis_eliminated_uniquely[action])

                for c in ctis_eliminated_uniquely_by_action[action]:
                    # Merge new CTIs eliminated uniquely.
                    unique_ctis = set(ctis_eliminated_uniquely_by_action[action][c])
                    if c not in node.ctis_eliminated_uniquely[action]:
                        node.ctis_eliminated_uniquely[action][c] = set()
                    node.ctis_eliminated_uniquely[action][c].update(unique_ctis)
                    # print("CTIs uniquely elim:", c)
                    # print(f"CTIs eliminated uniquely, {c}", len(ctis_eliminated_uniquely_by_action[action][c]))


                # print("Node uniquely elim:", node.ctis_eliminated_uniquely[action])

        # Convert to list.
        for action in actions:
            node.ctis_eliminated[action] = list(node.ctis_eliminated[action])



        ##
        ## EXPERIMENTAL INVARIANT SYNTHESIS AFTER NODE CTI GENERATION.
        EXPERIMENTAL_INV_SYNTH = False
        if EXPERIMENTAL_INV_SYNTH and "local_grammars" in indgen.spec_config:
            self.local_grammar_synth(indgen, node, actions, constants_obj)

        ############################################################
        ############################################################

        # Re-write proof html.
        self.save_proof()

        # If all CTIs are eliminated for this node, optionally check
        # for a complete proof using Apalache.
        if len(node.get_remaining_ctis()) == 0 and indgen.do_apalache_final_induction_check:
            indgen.apalache_induction_check(node)

        # Re-write proof html.
        self.save_proof()

        # If this was our target node, terminate.
        if target_node_name is not None and target_node_name == node.name:
            return

        # Recursively generate CTIs for children as well.
        for child_node in node.children_list():
            self.gen_ctis_for_node(indgen, child_node, target_node_name=target_node_name)
