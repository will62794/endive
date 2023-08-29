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

import graphviz

import pyeda
import pyeda.inter

import mc

DEBUG = False
TLC_MAX_SET_SIZE = 10 ** 8
JAVA_EXE="java"
GEN_TLA_DIR="gen_tla"
LATEST_TLC_JAR = "tla2tools_2.18.jar"

def chunks(seq, n_chunks):
    """ Splits a given iterable into n evenly (as possible) sized chunks."""
    N = len(seq)
    chunk_size = max(N // n_chunks, 1)
    # print("chunk size:", chunk_size)
    return (seq[i:i+chunk_size] for i in range(0, N, chunk_size))

def pred_symmetry_reduction(invs, quant_vars):
    """ Takes a set of predicates and removes those which are equivalent under symmetry to other invariants. """
    # For now, only do symmetry reduction for exactly two quantified vars.
    if not len(quant_vars)==2:
        return invs
    qv1 = quant_vars[0]
    qv2 = quant_vars[1]
    inv_uniq_set = set()
    for inv in invs:
        swap_inv = inv
        swap_inv = swap_inv.replace(qv1, "__QV1_TEMP").replace(qv2, "__QV2_TEMP")
        swap_inv = swap_inv.replace("__QV1_TEMP", qv2).replace("__QV2_TEMP", qv1)
        # print("orig",inv)
        # print("swap",swap_inv)
        if (inv in inv_uniq_set) or (swap_inv in inv_uniq_set):
            continue
        else:
            inv_uniq_set.add(inv)
    return inv_uniq_set

def symb_equivalence_reduction(invs, invs_symb):
    """ 
    Reduce set of invariant candidates to those that are logically equivalent,
    using CNF based equivalence checking, where 'invs_symb' are symbolic version
    of the string predicates given in 'invs'. Returns the reduced set of
    invariant predicates.
    """
    # Ensure we return invariants in a consistent order i.e. avoid nondeterminism
    # of using a set here.
    invs_unique = []
    cnf_invs_set = set()
    for invi,inv in enumerate(invs):
        symb_inv = invs_symb[invi]
        cnf_str = str(symb_inv.to_cnf())

        # Only add predicate if there is not an equivalent one that already exists.
        if cnf_str not in cnf_invs_set:
            invs_unique.append(inv)
            cnf_invs_set.add(cnf_str)
    return invs_unique


def generate_invs(preds, num_invs, min_num_conjuncts=2, max_num_conjuncts=2, 
                    process_local=False, boolean_style="tla", quant_vars=[]):
    """ Generate 'num_invs' random invariants with the specified number of conjuncts. """
    # Pick some random conjunct.
    # OR and negations should be functionally complete
    symb_neg_op = "~"
    if boolean_style == "cpp":
        # ops = ["&&", "||"]
        ops = ["||"]
        andop = "&&"
        neg_op = "!"
    elif boolean_style == "tla":
        # ops = ["/\\", "\\/"]
        ops = ["\\/"]
        andop = "/\\"
        neg_op = "~"

    # Assign a numeric id to each predicate.
    pred_id = {p:k for (k,p) in enumerate(preds)}

    invs = []
    invs_symb = []
    invs_symb_strs = []
    for invi in range(num_invs):
        conjuncts = list(preds)
        # conjuncts = list(map(str, range(len(preds))))
        num_conjuncts = random.randint(min_num_conjuncts, max_num_conjuncts)
        
        # Select first atomic term of overall predicate.
        c = random.choice(conjuncts)
        conjuncts.remove(c)

        # Optionally negate it.
        negate = random.choice([True, False])
        (n,fn) = (neg_op,symb_neg_op) if negate else ("","")

        inv = n + "(" + c + ")"
        pred_id_var = f"x_{str(pred_id[c]).zfill(3)}"
        symb_inv_str = fn + "(" + pred_id_var + ")"

        for i in range(1,num_conjuncts):
            c = random.choice(conjuncts)
            conjuncts.remove(c)
            op = ""
            fop = "|"
            if i < num_conjuncts:
                op = random.choice(ops)
            negate = random.choice([True, False])
            (n,fn) = (neg_op,symb_neg_op) if negate else ("","")
            new_term = n + "(" + c + ")"

            # Sort invariant terms to produce more consistent output regardless of random seed.
            new_inv_args = [new_term,inv]
            new_inv_args = sorted(new_inv_args)
            inv  =  new_inv_args[0] + " " + op + " (" + new_inv_args[1] +")"

            # inv  =  n + "(" + c + ")" + " " + op + " (" + inv +")"
            
            # Symbolic version of the predicate. Used for quickly 
            # detecting logically equivalent predicate forms.
            pred_id_var = f"x_{str(pred_id[c]).zfill(3)}"
            symb_inv_str = fn + "(" + pred_id_var + ")" + " " + fop + " (" + symb_inv_str +")"

        if inv not in invs:
            invs.append(inv)
            invs_symb.append(pyeda.inter.expr(symb_inv_str))
            # print(type(invs_symb[-1]))
            invs_symb_strs.append(symb_inv_str)

    logging.info(f"number of invs: {len(invs)}")

    # Do CNF based equivalence reduction.
    invs = symb_equivalence_reduction(invs, invs_symb)
    logging.info(f"number of invs post CNF based equivalence reduction: {len(invs)}")

    # if len(quant_vars):
        # invs = pred_symmetry_reduction(invs, quant_vars)
    logging.info(f"number of post symmetry invs: {len(invs)}")

    # return invs_symb
    # return invs_symb_strs
    # return set(map(str, invs_symb))
    return {"raw_invs": set(invs), "pred_invs": invs_symb_strs}

def greplines(pattern, lines):
    return [ln for ln in lines if re.search(pattern, ln)]

def runtlc(spec,config=None,tlc_workers=6,cwd=None,java="java",tlc_flags=""):
    # Make a best effort to attempt to avoid collisions between different
    # instances of TLC running on the same machine.
    dirpath = tempfile.mkdtemp()
    metadir_path = f"states/states_{uuid.uuid4().hex[:16]}"
    cmd = java + (f' -Djava.io.tmpdir="{dirpath}" -cp tla2tools-checkall.jar tlc2.TLC {tlc_flags} -maxSetSize {TLC_MAX_SET_SIZE} -metadir {metadir_path} -noGenerateSpecTE -checkAllInvariants -deadlock -continue -workers {tlc_workers}')
    if config:
        cmd += " -config " + config
    cmd += " " + spec
    logging.debug("TLC command: " + cmd)
    subproc = subprocess.Popen(cmd, shell=True, stdout=subprocess.PIPE, cwd=cwd)
    tlc_raw_out = ""
    line_str = ""
    tlc_lines = []
    while True:
        new_stdout = subproc.stdout.read(1).decode(sys.stdout.encoding)
        if new_stdout == "": # reached end of file.
            break
        if new_stdout == os.linesep:
            # logging.debug("[TLC Output] " + line_str)
            tlc_lines.append(line_str)
            line_str = ""
        else:
            line_str += new_stdout
    return tlc_lines

# Run TLC on spec to check all invariants and return the set 
# of invariants that were violated.
def runtlc_check_violated_invariants(spec,config=None, tlc_workers=6, cwd=None,java="java"):
    #
    # TODO: Check for this type of error:
    # 'Error: The invariant of Inv91 is equal to FALSE'
    #
    lines = runtlc(spec,config=config,tlc_workers=tlc_workers,cwd=cwd,java=java)
    invs_violated = set()
    for l in greplines("is violated", lines):
        res = re.match(".*Invariant (Inv.*) is violated",l)
        invname = res.group(1)
        invs_violated.add(invname)
    return invs_violated


class State():
    """ A single TLA+ state. """
    def __init__(self, state_str="", state_lines=[], load_from_obj=None):
        self.state_str = state_str
        self.state_lines = state_lines
        if load_from_obj:
            self.load_from(load_from_obj)

    def __str__(self):
        return self.state_str

    def pretty_str(self):
        out = ""
        for l in self.state_lines:
            out += l + "\n"
        return out
    
    def serialize(self):
        return {
            "state_str": self.state_str,
            "state_lines": self.state_lines
        }
    
    def load_from(self, obj):
        self.state_str = (obj["state_str"])
        self.state_lines = (obj["state_lines"])

class Trace():
    """ Represents a trace of states. """
    def __init__(self, states):
        # List of states.
        self.states = states

    def getStates(self):
        return self.states
    
    def serialize(self):
        return [s.serialize() for s in self.states]

class CTI():
    """ Represents a single counterexample to induction (CTI) state. """
    def __init__(self, cti_str="", cti_lines=[], action_name="", trace=None, load_from_obj=None):
        self.cti_str = cti_str
        self.action_name = action_name
        self.cti_lines = cti_lines
        # The full counterexample trace associated with this CTI. The CTI state may fall at 
        # different points within this trace.
        self.trace = trace

        # Optional cost metric for this CTI
        self.cost = 0

        if load_from_obj:
            self.load_from(load_from_obj)

    def serialize(self):
        return {
            "cti_str": self.cti_str,
            "action_name": self.action_name,
            "cti_lines": self.cti_lines,
            "trace": [s.serialize() for s in self.trace.getStates()],
            "cost": self.cost,
            "hashId": str(hash(self))
        }
    
    def load_from(self, obj):
        self.cti_str = obj["cti_str"]
        self.action_name = obj["action_name"]
        self.cti_lines = obj["cti_lines"]
        self.trace = Trace([State(load_from_obj=s) for s in obj["trace"]])

    def getCTIStateString(self):
        return self.cti_str

    def getPrimedCTIStateString(self):
        """ Return CTI as TLA+ state string where variables are primed."""
        primed_state_vars = []
        for cti_line in self.cti_lines:
            # Remove the conjunction (/\) at the beginning of the line.
            cti_line = cti_line[2:].strip()
            # print(cti_line)
            # Look for the first equals sign.
            first_equals = cti_line.index("=")
            varname = cti_line[:first_equals].strip()
            varval = cti_line[first_equals+1:]
            # print("varname:", varname)
            # print("varval:", varval)
            primed_state_vars.append(f"/\\ {varname}' ={varval}")
        primed_state = " ".join(primed_state_vars)
        # print(primed_state)
        return primed_state
    
    def getActionName(self):
        return self.action_name
    
    def setActionName(self, action_name):
        self.action_name = action_name

    def setTrace(self, trace):
        self.trace = trace

    def getTrace(self):
        return self.trace

    def pretty_str(self):
        out = ""
        for l in self.cti_lines:
            out += l + "\n"
        return out
            

    def __hash__(self):
        return hash(self.cti_str)
    
    def __eq__(self, other):
        return hash(self.cti_str) == hash(other.cti_str)
    
    def __str__(self):
        return self.cti_str
    
    # Order CTIs as strings.
    def __lt__(self, other):
        return self.cti_str < other.cti_str

class StructuredProofNode():
    """ Single node (i.e. lemma) of a structured proof tree. """
    def __init__(self, name="", expr="", children={}, parent=None, load_from_obj = None, parent_action=None):
        # Name used to identify the expression.
        self.name = name
        # Top level goal expression to be proven.
        self.expr = expr
        self.children = children

        self.cti_view = None

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

        # Pointer to this node's parent, or None if it has no parent.
        self.parent = parent

        self.parent_action = parent_action

        # Set of CTIs of parent that this lemma eliminates.
        self.parent_ctis_eliminated = []

        # Set of CTIs of parent that are eliminated by this predicate alone and
        # none of its siblings.
        self.parent_ctis_uniquely_eliminated = []

        if load_from_obj:
            self.load_from(load_from_obj)

    def serialize(self, include_ctis=True):
        ret = {
            "name": self.name, 
            "expr": self.expr, 
            "apalache_proof_check": self.apalache_proof_check, 
            "children":  {a:[c.serialize(include_ctis=include_ctis) for c in self.children[a]] for a in self.children}, 
            "project_vars": self.cti_project_vars,
            "parent_action": self.parent_action
        }

        cti_sort_key = lambda c : c.cost
        remaining_ctis_cost_sorted = sorted(self.get_remaining_ctis(), key = cti_sort_key)

        cti_info = {
            # "ctis": [c.serialize() for c in self.ctis],
            "ctis": {a:[c.serialize() for c in self.ctis[a]] for a in self.ctis},
            # Eliminated CTIs are stored as CTI hashes, not full CTIs.
            # "ctis_eliminated": [c for c in self.ctis_eliminated],
            "ctis_eliminated": self.ctis_eliminated,
            "ctis_remaining": {a:[c.serialize() for c in self.get_remaining_ctis(a)] for a in self.ctis},
            # [c.serialize() for c in remaining_ctis_cost_sorted],
            # "cti_clusters": self.get_cti_clusters(serialize=True),
            "num_parent_ctis_eliminated": len(self.parent_ctis_eliminated),
            # "parent_ctis_eliminated": [c for c in self.parent_ctis_eliminated],
            "had_ctis_generated": self.had_ctis_generated
        }
        # print(type(cti_info["ctis"]))
        if include_ctis:
            for k in cti_info:
                ret[k] = cti_info[k]
        return ret

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
        child_elems = "\n".join([f"<span>{c.to_html()}</span>" for c in self.get_children()])
        return f"""
                <li>{self.list_elem_html()}
                    <ul>{child_elems}</ul> 
                </li>
            """

    def children_list(self):
        if type(self.children) == dict:
            out = sum(list(self.children.values()), [])
            print(out)
            return out
        return self.children

    def get_children(self):
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


class StructuredProof():
    """ Structured safety proof of an inductive invariant. 
    
    May also represent a "partial" proof i.e. one in an incomplete state that is yet to be completed.
    """

    def __init__(self, root=None, load_from_obj=None, specname=None, actions=None):
        # Top level goal expression to be proven.
        self.safety_goal = safety
        self.root = root 

        self.specname = specname
        self.proof_base_filename = f"benchmarks/{self.specname}.proof"

        self.actions = actions

        if load_from_obj:
            self.load_from(load_from_obj)

    def serialize(self, include_ctis=True):
        return {"safety": self.safety_goal, "root": self.root.serialize(include_ctis=include_ctis)}
    
    def save_proof(self, include_json=False):
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

        print(f"Saving latest proof as DOT to '{dot_filename}'")
        self.save_as_dot(dot_filename)

        print(f"Finished saving proof objects.")

    def load_from(self, obj):
        self.safety_goal = obj["safety"]
        self.root = StructuredProofNode(load_from_obj=obj["root"])

    def root_to_html(self):
        html = "<ul>"+self.root.to_html()+"</ul>"
        return html

    def get_node_by_name_rec(self, name, start_node):
        if start_node.name == name:
            return start_node
        else:
            for c in start_node.children:
                ret = self.get_node_by_name_rec(name, c)
                if ret is not None:
                    return ret
            return None

    def get_node_by_name(self, name):
        return self.get_node_by_name_rec(name, self.root)

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
        for c in node.get_children():
            html += self.node_cti_html(c)
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
        # html += """<script src="{{ url_for('static',filename='proof.js') }}"> </script>"""
        # html += ("""<link rel="stylesheet" type="text/css" href="{{ url_for('static',filename='proof.css') }}">""")
        html += '<script src="https://ajax.googleapis.com/ajax/libs/jquery/3.6.4/jquery.min.js"></script>'
        html += """
        <!-- CytoscapeJS (for graph visualizations) -->
        <script src="https://cdnjs.cloudflare.com/ajax/libs/cytoscape/3.20.0/cytoscape.min.js" integrity="sha512-cjmYAonfXK+azDmWqvnqq8xmygHRHqVI7S0zuRxQnvcYVeoakwthRX6pPKoXfG1oIjDvMUtteRV9PhQjJwKWxQ==" crossorigin="anonymous" referrerpolicy="no-referrer"></script>
        <script src="https://unpkg.com/dagre@0.7.4/dist/dagre.js"></script>
        <script src="https://cdn.jsdelivr.net/npm/cytoscape-dagre@2.5.0/cytoscape-dagre.min.js"></script>
        """

        html += ('<script type="text/javascript" src="proof.js"></script>')
        html += ("</head>")

        # html += ("<div>")
        html += ("<div hidden>")
        html += (f"<h1>Proof Structure: {specname}</h1>")
        # html += (f"<div>seed={self.indgen.seed}, num_simulate_traces={self.indgen.num_simulate_traces}</div>")
        html += (self.root_to_html())
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

    def add_node_to_dot_graph(self, dot, node):
        """ Add this node and its children, recursively, to DOT graph."""
        dot.node(node.expr)
        for c in node.get_children():
            dot.edge(c.expr, node.expr)
            self.add_node_to_dot_graph(dot, c)


    def save_as_dot(self, out_file):
        """ Generate DOT graph representation of this structured proof. """
        dot = graphviz.Digraph('proof-graph', strict=True, comment='Proof Structure')  
        # dot.graph_attr["rankdir"] = "LR"
        dot.node_attr["fontname"] = "courier"
        # dot.node_attr["shape"] = "box"
        
        # Store all nodes.
        self.add_node_to_dot_graph(dot, self.root)

        # print("Final proof graph:")
        # print(dot.source)
        dot.render(out_file)
        return dot.source

    def get_node_by_name(self, start_node, name):
        # If this was our target node, terminate.
        if name == start_node.name:
            return start_node
        else:
            for c in start_node.children_list():
                ret = self.get_node_by_name(c, name)
                if ret is not None:
                    return ret
            return None

    def compute_cti_elimination_for_node(self, indgen, node, ctis, action):
        """ Compute CTIs that are eliminated by the children of this node, for given set of CTIs. """

        ####
        # TODO: Update the logic below to deal with per-action CTI structure.
        ###

        # Mapping from CTI id to CTI object.
        cti_table = {}
        for c in ctis:
            cti_table[str(hash(c))] = c

        # Compute CTIs that are eliminated by each of the "support lemmas" for this node i.e.
        # its set of direct children.

        print(f"Checking CTI elimination for support lemmas of node ({node.name},{node.expr})")
        # ctis_eliminated = indgen.check_cti_elimination(node.ctis, [
        #     (child.name,child.expr) for child in node.children
        # ])

        # cti_info = indgen.check_cti_elimination(node.ctis, [

        # Compute CTI elimination for children that serve as support lemmas specifically for this action.
        # cti_info = indgen.check_cti_elimination(ctis, [
        #     (child.name,child.expr) for child in node.children if child.parent_action == action
        # ])

        if action not in node.children:
            return {}

        cti_info = indgen.check_cti_elimination(ctis, [
            (child.name,child.expr) for child in node.children[action]
        ])

        ctis_eliminated = cti_info["eliminated"]
        cti_cost = cti_info["cost"]
        # print(cti_cost)

        # Assign costs for each node CTI.
        # print(len(ctis))
        # print("cost len:", len(cti_cost))
        for c in cti_cost:
            cost = cti_cost[c]
            cti_table[c].cost = cost

        # print("CTI eliminate response:", ctis_eliminated.keys())

        ctis_eliminated_unique = {}

        print("CTIs eliminated by invs")
        all_eliminated_ctis = set()
        out_degrees_of_unique_eliminated = set()
        for i,inv in enumerate(sorted(ctis_eliminated.keys(), key=lambda k : int(k.replace("Inv", "")))):
        # for child in node.children:
            print(inv, ":", len(ctis_eliminated[inv]))
            # print(ctis_eliminated_by_invs[k])
            all_eliminated_ctis.update(ctis_eliminated[inv])

            unique = ctis_eliminated[inv]
            for other in (ctis_eliminated.keys() - {inv}):
                unique = unique.difference(ctis_eliminated[other])
            ctis_eliminated_unique[inv] = unique
            # print("Unique:", len(unique))
            # print(ctis_eliminated_unique)
            child_node = sorted(node.children[action], key=lambda x : x.expr)[i]
            child_node.parent = node
            child_node.parent_ctis_eliminated = set(ctis_eliminated[inv])
            child_node.parent_ctis_uniquely_eliminated = set(ctis_eliminated_unique[inv])
            if len(child_node.parent_ctis_uniquely_eliminated) > 0:
                one_unique_cti = random.sample(child_node.parent_ctis_uniquely_eliminated, 1)
                for c in one_unique_cti:
                    # Are the low outdegree CTIs among those CTIs that are uniquely eliminated?
                    
                    # print("Sample of uniquely eliminated CTI:")
                    # print(child_node.name)
                    # print(c)

                    # print([str(hash(x)) for x in node.ctis])
                    uniq_cti_obj = [x for x in ctis if str(hash(x)) == c][0]
                    print(uniq_cti_obj.pretty_str())

                    if indgen.cti_out_degrees:
                        # print(len(indgen.cti_out_degrees))
                        out_degree = indgen.cti_out_degrees[c]
                        # print(type(c), c)
                        # print("out_degree:", out_degree)
                        out_degrees_of_unique_eliminated.add(out_degree)

        if indgen.cti_out_degrees:
            print("uniquely eliminated out degrees:", out_degrees_of_unique_eliminated)
            
        return all_eliminated_ctis
        # node.ctis_eliminated = all_eliminated_ctis

    def gen_ctis_for_node(self, indgen, node, target_node_name = None):
        """ Routine that updates set of CTIs for each proof node. 
        
        Generates CTIs and computes the set eliminated by each node's support lemmas i.e. its direct children
        """

        # TODO: Eventually may want a different unique naming scheme for proof nodes.
        if target_node_name is not None and target_node_name != node.name:
            # Recurse right away if this is not the target node.
            for child_node in node.children:
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

        k_ctis, _ = indgen.generate_ctis(props=[(node.name, node.expr)], reseed=True, depth=1, view=node.cti_view, actions=actions)

        # if self.actions is not None:
        #     print(k_ctis.keys())
        #     for k in k_ctis:
        #         print(k, len(k_ctis[k]))


        # Compute CTI elimination broken down by action.
        for action in actions:
            ctis_for_action = list(k_ctis[action])
            ctis_for_action.sort()

            # Set CTIs for this node based on those generated and sample if needed.
            logging.info(f"Number of proof node CTIs generated for action '{action}': {len(ctis_for_action)}. Sampling a limit of {indgen.max_proof_node_ctis} CTIs.")
            num_to_sample = min(len(ctis_for_action), indgen.max_proof_node_ctis) # don't try to sample more CTIs than there are.
            ctis_for_action_sampled = random.sample(ctis_for_action, num_to_sample)
            node.set_ctis(ctis_for_action_sampled, action)

            ctis_eliminated = self.compute_cti_elimination_for_node(indgen, node, node.get_ctis(action), action)
            node.ctis_eliminated[action] = list(ctis_eliminated)


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
        for child_node in node.children:
            self.gen_ctis_for_node(indgen, child_node, target_node_name=target_node_name)


class InductiveInvGen():
    """ 
    Encapsulates the algorithm for inferring an inductive invariant given a
    protocol specification, safety property, and various other parameters.
    """

    def __init__(self, specdir, specname, safety, constants, state_constraint, quant_inv, model_consts, preds,
                    symmetry=False, simulate=False, simulate_depth=6, typeok="TypeOK", tlc_specific_spec=False, seed=0, num_invs=1000, num_rounds=3, num_iters=3, 
                    num_simulate_traces=10000, tlc_workers=6, quant_vars=[],java_exe="java",cached_invs=None, cached_invs_gen_time_secs=None, use_cpp_invgen=False,
                    pregen_inv_cmd=None, opt_quant_minimize=False, try_final_minimize=False, proof_tree_mode=False, interactive_mode=False, max_num_conjuncts_per_round=10000,
                    max_num_ctis_per_round=10000, override_num_cti_workers=None, use_apalache_ctigen=False,all_args={}):
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

        self.seed = seed
        self.num_rounds = num_rounds
        self.num_iters = num_iters
        self.num_invs = num_invs
        self.tlc_workers = tlc_workers
        self.use_apalache_ctigen = use_apalache_ctigen
        self.do_apalache_final_induction_check = all_args["do_apalache_final_induction_check"]

        # Ensure a reasonable default timeout on these checks for now.
        # See https://apalache.informal.systems/docs/apalache/tuning.html#timeouts for more details.
        self.apalache_smt_timeout_secs = all_args["apalache_smt_timeout_secs"]

        self.max_proof_node_ctis = all_args["max_proof_node_ctis"]
        self.proof_tree_mode = proof_tree_mode
        self.proof_tree_cmd = all_args["proof_tree_cmd"]
        self.interactive_mode = interactive_mode
        self.max_num_conjuncts_per_round = max_num_conjuncts_per_round
        self.override_num_cti_workers = override_num_cti_workers

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
        if type(constants)==list:
            constants = "\n".join(constants)
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
        self.ctigen_start = 0
        self.invcheck_start = 0
        self.ctielimcheck_start = 0

        self.ctigen_duration_secs = 0
        self.invcheck_duration_secs = 0
        self.ctielimcheck_duration_secs = 0
        self.total_duration_secs = 0
        self.total_num_ctis_eliminated = 0
        self.total_num_cti_elimination_rounds = 0

        # Clear and create directory for generated files if needed.
        os.system(f"rm -rf {os.path.join(self.specdir, GEN_TLA_DIR)}")
        os.system(f"rm -rf {os.path.join(self.specdir, 'states')}")
        os.system(f"mkdir -p {os.path.join(self.specdir, GEN_TLA_DIR)}")

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
        invs = generate_invs(preds, self.num_invs, min_num_conjuncts=min_num_conjuncts, max_num_conjuncts=max_num_conjuncts, process_local=process_local, quant_vars=quant_vars)
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
        f.write(f"\* endive.py stats\n")
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
        """ Check which of the given invariants are valid. """
        
        spec_suffix = "PredCheck"

        invcheck_tla = "---- MODULE %s_%s_%d ----\n" % (self.specname,spec_suffix,self.seed)
        invcheck_tla += "EXTENDS %s\n\n" % self.specname
        invcheck_tla += self.model_consts + "\n"

        invval_varname = "predval"

        # for i,inv in enumerate(preds):    
        #     invcheck_tla += f"VARIABLE {invval_varname}_{i}\n"

        # all_inv_names = set()
        # for i,inv in enumerate(preds):    
        #     sinv = ("Pred_%d == " % i) + self.quant_inv(inv)
        #     all_inv_names.add("Pred_%d" % i)
        #     invcheck_tla += sinv + "\n"

        # invcheck_tla += "InvInit ==\n"
        # for i,inv in enumerate(preds):    
        #     invcheck_tla += f"  /\\ {invval_varname}_{i} = Pred_{i}\n"

        # invcheck_tla += "InvNext ==\n"
        # for i,inv in enumerate(preds):    
        #     invcheck_tla += f"  /\\ {invval_varname}_{i}' = Pred_{i}'\n"


        # invcheck_tla += "PredInit == Init /\ InvInit\n"
        # invcheck_tla += "PredNext == Next /\ InvNext\n"

        invcheck_tla += "PredInit == Init\n"
        invcheck_tla += "PredNext == Next\n"

        invcheck_tla += "===="

        invcheck_spec_name = f"{GEN_TLA_DIR}/{self.specname}_{spec_suffix}_{self.seed}"
        invcheck_spec_filename = f"{os.path.join(self.specdir, GEN_TLA_DIR)}/{self.specname}_{spec_suffix}_{self.seed}"
        invchecktlafile = invcheck_spec_filename + ".tla"
        f = open(invchecktlafile, 'w')
        f.write(invcheck_tla)
        f.close()

        invcheck_cfg = "INIT PredInit\n"
        invcheck_cfg += "NEXT PredNext\n"
        invcheck_cfg += self.constants
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
            f"-maxSetSize {TLC_MAX_SET_SIZE}",
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
        for s in dumpstates["states"]:
            # print(s)
            state_pred_vals = {}
            # print(s)
            # print(s["val"].keys())
            for k in s["val"]:
                if invval_varname in k:
                    state_pred_vals[k.split("_")[1]] = s["val"][k]
            # print(state_pred_vals)
            pred_vals[s["fp"]] = state_pred_vals
        # print(pred_vals)
        # for fp in pred_vals:
            # print(fp, pred_vals[fp])
        
        print(sys.getsizeof(pred_vals)/1000, "KB")
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

    def check_invariants(self, invs, tlc_workers=6):
        """ Check which of the given invariants are valid. """
        ta = time.time()
        invcheck_tla = "---- MODULE %s_InvCheck_%d ----\n" % (self.specname,self.seed)
        invcheck_tla += "EXTENDS %s\n\n" % self.specname
        invcheck_tla += self.model_consts + "\n"

        all_inv_names = set()
        for i,inv in enumerate(invs):    
            sinv = ("Inv%d == " % i) + self.quant_inv(inv)
            all_inv_names.add("Inv%d" % i)
            invcheck_tla += sinv + "\n"

        invcheck_tla += "===="

        invcheck_spec_name = f"{GEN_TLA_DIR}/{self.specname}_InvCheck_{self.seed}"
        invcheck_spec_filename = f"{os.path.join(self.specdir, GEN_TLA_DIR)}/{self.specname}_InvCheck_{self.seed}"
        invchecktlafile = invcheck_spec_filename + ".tla"
        f = open(invchecktlafile, 'w')
        f.write(invcheck_tla)
        f.close()

        invcheck_cfg = "INIT Init\n"
        invcheck_cfg += "NEXT Next\n"
        invcheck_cfg += self.constants
        invcheck_cfg += "\n"
        invcheck_cfg += f"CONSTRAINT {self.state_constraint}"
        invcheck_cfg += "\n"
        if self.symmetry:
            invcheck_cfg += "SYMMETRY Symmetry\n"

        for invi in range(len(invs)):
            sinv = "INVARIANT Inv" + str(invi) 
            invcheck_cfg += sinv + "\n"

        invcheck_cfg_file = f"{os.path.join(self.specdir, GEN_TLA_DIR)}/{self.specname}_InvCheck_{self.seed}.cfg"
        invcheck_cfg_filename = f"{GEN_TLA_DIR}/{self.specname}_InvCheck_{self.seed}.cfg"

        f = open(invcheck_cfg_file, 'w')
        f.write(invcheck_cfg)
        f.close()

        # Check invariants.
        logging.info("Checking %d candidate invariants in spec file '%s'" % (len(invs), invcheck_spec_name))
        workdir = None if self.specdir == "" else self.specdir
        violated_invs = runtlc_check_violated_invariants(invcheck_spec_name, config=invcheck_cfg_filename, tlc_workers=self.tlc_workers, cwd=workdir,java=self.java_exe)
        sat_invs = (all_inv_names - violated_invs)
        logging.info(f"Found {len(sat_invs)} / {len(invs)} candidate invariants satisfied in {round(time.time()-ta,2)}s.")

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
    def parse_cti_trace(self, lines, curr_line):
        # Step to the 'State x' line
        # curr_line += 1
        # res = re.match(".*State (.*)\: <(.*) .*>",lines[curr_line])
        # statek = int(res.group(1))
        # action_name = res.group(2)
        # print(res)
        # print(statek, action_name)

        # print("Parsing CTI trace. Start line: " , lines[curr_line])
        # print(curr_line, len(lines))

        trace_states = []
        trace_ctis = []
        trace_action_names = []

        while curr_line < len(lines):
            # print(lines[curr_line])

            if re.search('Model checking completed', lines[curr_line]):
                break

            if re.search('Error: The behavior up to this point is', lines[curr_line]):
                # print("--")
                break

            # Check for next "State N" line.
            if re.search("^State (.*)", lines[curr_line]):

                # res = re.match(".*State ([0-9]*)\: <([A-Za-z0-9_-]*)[(]{0,1}([A-Za-z0-9_-]*)[)]{0,1} .*>",lines[curr_line])

                # State 2: <BecomeLeader(n1,{n1, n3}) line 149, col 5 to line 157, col 35 of module AbstractStaticRaft>
                res = re.match(".*State ([0-9]*)\: <(.*)>",lines[curr_line])
                statek = int(res.group(1))
                action_name = res.group(2)
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
            cti.setTrace(trace)
        
        # for cti in trace_ctis:
            # print(cti.getActionName())

        # The last state is a bad state, not a CTI.
        trace_ctis = trace_ctis[:-1]
        return (curr_line, set(trace_ctis), trace)

    def parse_ctis(self, lines):
        all_ctis = set()

        curr_line = 0

        # Step forward to the first CTI error trace.
        while not re.search('Error: The behavior up to this point is', lines[curr_line]):
            curr_line += 1
            if curr_line >= len(lines):
                break

        all_cti_traces = []
        curr_line += 1
        while curr_line < len(lines):
            (curr_line, trace_ctis, trace) = self.parse_cti_trace(lines, curr_line)
            all_ctis = all_ctis.union(trace_ctis)
            all_cti_traces.append(trace)
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


    def generate_ctis_tlc_run_async(self, num_traces_per_worker, props=None, depth=None, view=None, action=None):
        """ Starts a single instance of TLC to generate CTIs.
        
        Will generate CTIs for the conjunction of all predicates given in 'props'.
        """

        if props == None:
            props = [("Safety",self.safety)] + self.strengthening_conjuncts

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
        for cinvname,cinvexp in props:
            invcheck_tla_indcheck += ("%s == %s\n" % (cinvname, cinvexp))

        # Create formula string which is conjunction of all strengthening conjuncts.
        strengthening_conjuncts_str = ""
        for cinvname,cinvexp in props:
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
        invcheck_tla_indcheck += f"InvStrengthened_Constraint == {precond} => InvStrengthened \n"

        invcheck_tla_indcheck += "IndCand ==\n"
        typeok = self.typeok
        if self.use_apalache_ctigen:
            typeok = "TypeOK"
        invcheck_tla_indcheck += "    /\\ %s\n" % typeok
        invcheck_tla_indcheck += f"    /\ InvStrengthened\n"

        depth_bound = 2
        level_bound_precond = f'TLCGet("level") < {depth_bound}'
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


        invcheck_tla_indcheck_cfg += f"CONSTRAINT {self.state_constraint}\n"
        if view is not None:
            invcheck_tla_indcheck_cfg += f"VIEW {view_expr_name}\n"
        invcheck_tla_indcheck_cfg += "\n"
        # Only check the invariant itself for now, and not TypeOK, since TypeOK
        # might be probabilistic, which doesn't seem to work correctly when checking 
        # invariance.
        # invcheck_tla_indcheck_cfg += "INVARIANT InvStrengthened\n"
        invcheck_tla_indcheck_cfg += "INVARIANT InvStrengthened_Constraint\n"
        # invcheck_tla_indcheck_cfg += "INVARIANT OnePrimaryPerTerm\n"
        invcheck_tla_indcheck_cfg += self.constants
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

        logging.debug(f"Using fixed TLC worker count of {num_ctigen_tlc_workers} to ensure reproducible CTI generation.")
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
        
        args = (dirpath, "tla2tools-checkall.jar", TLC_MAX_SET_SIZE, simulate_flag, simulate_depth, ctiseed, tag, num_ctigen_tlc_workers, indcheckcfgfilename(action), indchecktlafilename)
        cmd = self.java_exe + ' -Xss16M -Djava.io.tmpdir="%s" -cp %s tlc2.TLC -maxSetSize %d %s -depth %d -seed %d -noGenerateSpecTE -metadir states/indcheckrandom_%s -continue -deadlock -workers %d -config %s %s' % args
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

        (parsed_ctis, parsed_cti_traces) = self.parse_ctis(lines)     
        return (parsed_ctis,parsed_cti_traces)       


    def generate_ctis(self, props=None, reseed=False, depth=None, view=None, actions=None):
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

        # Start the TLC processes for CTI generation.
        logging.info(f"Running {num_cti_worker_procs} parallel CTI generation processes")
        for n in range(num_cti_worker_procs):
            # if self.use_apalache_ctigen:
                # cti_subproc = self.generate_ctis_apalache_run_async(num_traces_per_tlc_instance)
            # else:
            if actions is not None:
                for action in actions:
                    logging.info(f"Starting CTI generation process {n} (of {num_cti_worker_procs} total workers), Action='{action}'")
                    cti_subproc = self.generate_ctis_tlc_run_async(num_traces_per_tlc_instance,props=props, depth=depth, view=view, action=action)
                    cti_subprocs.append({"action": action, "proc": cti_subproc})
            else:
                logging.info(f"Starting CTI generation process {n} (of {num_cti_worker_procs} total workers)")
                cti_subproc = self.generate_ctis_tlc_run_async(num_traces_per_tlc_instance,props=props, depth=depth, view=view)
                cti_subprocs.append({"proc": cti_subproc})

        # Await completion and parse results.
        all_cti_traces = []

        # Break down CTIs by action in this case.
        if actions is not None:
            all_ctis = {}
            all_cti_traces = {}

        for cti_subproc in cti_subprocs:
            if self.use_apalache_ctigen:
                parsed_ctis = self.generate_ctis_apalache_run_await(cti_subproc)
            else:
                if actions is not None:
                    action = cti_subproc["action"]
                    (parsed_ctis, parsed_cti_traces) = self.generate_ctis_tlc_run_await(cti_subproc["proc"]) 
                    all_ctis[action] = parsed_ctis
                    all_cti_traces[action] = parsed_cti_traces
                else:
                    (parsed_ctis, parsed_cti_traces) = self.generate_ctis_tlc_run_await(cti_subproc["proc"]) 
                    all_ctis = all_ctis.union(parsed_ctis)
                    all_cti_traces += parsed_cti_traces

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
        return (all_ctis, all_cti_traces)

    def make_rel_induction_check_spec(self, spec_name, support_lemmas, S, rel_ind_pred_name, goal_inv_name):
        """ 
        Create a spec that allows to check whether a given boolean expression S is inductive relative to to a conjunction of
        given predicates L. Defines a predicate that is the conjunction of predicates in L as 'IndLemmas'.
        """
        
        # Build the spec.
        typeok = "TypeOK" # Apalache always uses normal TypeOK.
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
        invs_sorted = sorted(invs)
        
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
        for cinvname,cinvexp in self.strengthening_conjuncts:
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
        for cinvname,cinvexp in self.strengthening_conjuncts:
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
        invcheck_tla_indcheck += strengthening_conjuncts_str
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

    def make_ctiquickcheck_cfg(self, invs, sat_invs_group, orig_k_ctis, quant_inv_fn, next_pred="CTICheckNext"):

        # Generate config file.
        invcheck_tla_indcheck_cfg = "INIT CTICheckInit\n"
        invcheck_tla_indcheck_cfg += f"NEXT {next_pred}\n"
        invcheck_tla_indcheck_cfg += f"CONSTRAINT {self.state_constraint}"
        invcheck_tla_indcheck_cfg += "\n"
        invcheck_tla_indcheck_cfg += self.constants
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

    def check_cti_elimination(self, orig_ctis, sat_invs):
        """ Computes CTI elimination mapping for the given set of CTIs and invariants.
        
        That is, this function computes and returns a mapping from each invariant to the set of CTIs 
        that it eliminates.
        """

        #
        # TODO: Sort out how we handle 'invs' and 'sat_invs' and CTI tables here, etc.
        #

        logging.info(f"Checking invariant elimination for {len(orig_ctis)} CTIs.")

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
                cfg_str = self.make_ctiquickcheck_cfg(invs, sat_invs_group, cti_chunk, quant_inv_fn)
                
                with open(ctiquickcfgfile,'w') as f:
                    f.write(cfg_str)


                # Generate alternate config file for computing reachability graph from each CTI.
                ctiquickcfgfile_reach=f"{os.path.join(self.specdir, GEN_TLA_DIR)}/{self.specname}_CTIQuickCheck_Reachable_chunk{ci}.cfg"
                ctiquickcfgfilename_reach=f"{GEN_TLA_DIR}/{self.specname}_CTIQuickCheck_Reachable_chunk{ci}.cfg"
                cfg_str = self.make_ctiquickcheck_cfg(invs, sat_invs_group, cti_chunk, quant_inv_fn, next_pred="CTICheckNext_DepthBoundedReachability")
                
                with open(ctiquickcfgfile_reach,'w') as f:
                    f.write(cfg_str)

                # cti_states_file = os.path.join(self.specdir, f"states/cti_quick_check_chunk{ci}_{curr_ind}.json")
                # cti_states_relative_file = f"states/cti_quick_check_chunk{ci}_{curr_ind}.json"
                
                workdir = None if self.specdir == "" else self.specdir

                # Run TLC.
                # Create new tempdir to avoid name clashes with multiple TLC instances running concurrently.
                def run_with_config(cfg_filename, tag=""):
                    dirpath = tempfile.mkdtemp()
                    cmdargs = (dirpath, TLC_MAX_SET_SIZE, cti_states_relative_file(ci, curr_ind, tag=tag), self.specname, ci, curr_ind, tag, cfg_filename, ctiquicktlafilename)
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
        return {
            "eliminated": cti_states_eliminated_by_invs,
            "cost": cti_costs
        }

    def eliminate_ctis(self, orig_k_ctis, num_invs, roundi, preds_alt=[], quant_inv_alt=None, tlc_workers=6, specdir=None, append_inv_round_id=True):
        """ Check which of the given satisfied invariants eliminate CTIs. """
        
        # Save CTIs, indexed by their hashed value.
        cti_table = {}
        for cti in orig_k_ctis:
            hashed = str(hash(cti))
            cti_table[hashed] = cti

        eliminated_ctis = set()

        # Parameters for invariant generation.
        min_conjs = 2
        max_conjs = 2
        process_local = False
        quant_inv_fn = self.quant_inv

        iteration = 1
        uniqid = 0
        while iteration <= self.num_iters:
            tstart = time.time()

            # TODO: Possibly use these for optimization later on.
            self.sat_invs_in_iteration = set()
            self.invs_checked_in_iteration = set()

            # On second iteration, search for non process local invariants.
            if iteration==2:
                min_conjs = 3
                max_conjs = 3
                process_local=False
                quant_inv_fn = self.quant_inv

            # On third and following iterations, search for non process local invariants with more conjuncts.
            if iteration==3:
                min_conjs = 4
                max_conjs = 4
                process_local=False
                if quant_inv_alt:
                    quant_inv_fn = quant_inv_alt
                    self.preds = self.preds + preds_alt

            if iteration==4:
                min_conjs = 5
                max_conjs = 5
                process_local=False
                if quant_inv_alt:
                    quant_inv_fn = quant_inv_alt
                    self.preds = self.preds + preds_alt

            if iteration==5:
                min_conjs = 6
                max_conjs = 6
                process_local=False
                if quant_inv_alt:
                    quant_inv_fn = quant_inv_alt
                    self.preds = self.preds + preds_alt

            if iteration==6:
                min_conjs = 3
                max_conjs = 3
                process_local=False
                if quant_inv_alt:
                    quant_inv_fn = quant_inv_alt
                    self.preds = self.preds + preds_alt

            logging.info("\n>>> Iteration %d (num_conjs=(min=%d,max=%d),process_local=%s)" % (iteration,min_conjs,max_conjs,process_local)) 

            logging.info("Starting iteration %d of eliminate_ctis (min_conjs=%d, max_conjs=%d)" % (iteration,min_conjs,max_conjs))

            sat_invs = {}

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
                all_invs = generate_invs(self.preds, num_invs, min_num_conjuncts=min_conjs, max_num_conjuncts=max_conjs, process_local=process_local, quant_vars=self.quant_vars)
                invs = all_invs["raw_invs"]

                # Sort the set of invariants to give them a consistent order.
                invs = sorted(list(invs))
                # print("Raw invs")
                # print(invs[:5])
                # print(hashlib.md5("".join(invs).encode()).hexdigest())
                # for inv in invs:
                #     print("invpred,",inv)
                # print(self.all_sat_invs)

                # No need to re-check invariants if they have already been
                # discovered in past. Remove them from the set of invariants to
                # check, and then add them back to the set of satisfied
                # invariants after running invariant checking.
                # TODO: Finish implementing this optimization.
                prechecked_invs = set(invs).intersection(self.all_sat_invs) 
                # invs = set(invs) - self.all_sat_invs
                # invs = sorted(list(invs))
                
                sat_invs = self.check_invariants(invs, tlc_workers=tlc_workers)
                
                sat_invs = list(sorted(sat_invs))
                print("sat invs")
                print(sat_invs[:5])

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

            logging.info("Checking which invariants eliminate CTIs.")

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
            MAX_INVS_PER_GROUP = 1000
            curr_ind = 0
            workdir = None
            if specdir != "":
                workdir = specdir


            # Run CTI elimination checking in parallel.
            n_tlc_workers = 4
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
                    # print("invs")
                    # print(invs[:5])
                    # print(len(invs))
                    # print("sat invs group")
                    # print(sat_invs_group[:5])
                    # print(len(sat_invs_group))
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
                    cmd = self.java_exe + ' -Xss16M -Djava.io.tmpdir="%s" -cp tla2tools-checkall.jar tlc2.TLC -maxSetSize %d -dump json %s -noGenerateSpecTE -metadir states/ctiquick_%s_chunk%d_%d -continue -checkAllInvariants -deadlock -workers 1 -config %s %s' % (dirpath, TLC_MAX_SET_SIZE ,cti_states_relative_file, self.specname, ci, curr_ind, ctiquickcfgfilename, ctiquicktlafilename)

                    
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
                    lines = greplines("State.*|/\\\\", lines)

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

            logging.info(f"Checking {len(sat_invs)} satisfied invariants for CTI elimination")

            for i in range(len(sorted_invs)):
                # Sort the remaining invariants by the number of new CTIs they eliminate.
                compare_fn = lambda inv: (len(cti_states_eliminated_by_invs[inv] - eliminated_ctis), -len(get_invexp_cost(inv)))
                sorted_invs = sorted(sorted_invs, reverse=True, key=compare_fn)
                next_inv = sorted_invs.pop(0)

                invi = int(next_inv.replace("Inv",""))
                invname = "Inv%d" % invi
                invexp = quant_inv_fn(orig_invs_sorted[invi])

                new_ctis_eliminated = (cti_states_eliminated_by_invs[next_inv] - eliminated_ctis)
                cti_states_eliminated_in_iter += len(new_ctis_eliminated)


                if len(new_ctis_eliminated)>0:
                    logging.info("New CTIs eliminated by inv %s %s: %d" % (next_inv, invexp, len(new_ctis_eliminated)))
                    logging.info("* " + next_inv + " -> new CTIs eliminated: %d" % len(new_ctis_eliminated))
                    # for cti in new_ctis_eliminated:
                        # print(cti_table[cti].getActionName())
                    chosen_invs.append(next_inv)
                    eliminated_ctis = eliminated_ctis.union(new_ctis_eliminated)

                    if len(chosen_invs) >= self.max_num_conjuncts_per_round:
                        logging.info(f"Moving on since reached max num conjuncts per round: {self.max_num_conjuncts_per_round}")
                        break 
                else:
                    logging.info("Moving on since no remaining invariants eliminate CTIs.")
                    break

            if len(chosen_invs):
                logging.info("*** New strengthening conjuncts *** ")
                for inv in chosen_invs:
                    invi = int(inv.replace("Inv",""))
                    invexp = quant_inv_fn(sorted(invs)[invi])
                
                    inv_suffix = ""
                    if append_inv_round_id:
                        inv_suffix = "_" + str(iteration) + "_" + str(uniqid)
                        
                    # Add the invariant as a conjunct.
                    self.strengthening_conjuncts.append((inv + inv_suffix, invexp))
                    uniqid += 1

                    logging.info("%s %s", inv, invexp) #, "(eliminates %d CTIs)" % len(cti_states_eliminated_by_invs[inv])
                    # print "CTIs eliminated by this invariant: %d" % len(cti_states_eliminated_by_invs[inv])
                # Re-run the iteration if new conjuncts were discovered.
                if self.rerun_iterations:
                    iteration -= 1

            num_ctis_remaining = len(list(cti_table.keys()))-len(eliminated_ctis)
            num_orig_ctis = len(list(cti_table.keys()))
            duration = time.time()-tstart
            logging.info("[ End iteration {}. (took {:.2f} secs.) ]".format(iteration, duration))
            logging.info("%d original CTIs." % num_orig_ctis)
            logging.info("%d new CTIs eliminated in this iteration." % cti_states_eliminated_in_iter)
            logging.info("%d total CTIs eliminated." % len(eliminated_ctis))
            logging.info("%d still remaining." % num_ctis_remaining)
            self.total_num_ctis_eliminated += cti_states_eliminated_in_iter
            self.end_timing_ctielimcheck()

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
        if num_ctis_remaining > 0:
            return None
        return self.strengthening_conjuncts
    
    def apalache_induction_check(self, node):
        logging.info("Checking for full proof with Apalache.")
        # We want to check that this node lemma is inductive relative to the conjunction
        # of all its children lemmas.
        spec_name = f"{self.specname}_rel_ind_check"
        support_lemmas = [c.expr for c in node.children]
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

        tMKnowsPrepareImpliesRMSentPrepare = StructuredProofNode("TMKnowsPrepareImpliesRMSentPrepare", "H_TMKnowsPrepareImpliesRMSentPrepare")

        ######
        ######
        ## lemmaelim
        # children = {
        #     "TMAbort" : ""
        #     "TMAbort" : StructuredProofNode("InitImpliesNoAbortMsg", "H_InitImpliesNoAbortMsg")
        # }
        commitMsgImpliesNoAbortMsg = StructuredProofNode("CommitMsgImpliesNoAbortMsg", "H_CommitMsgImpliesNoAbortMsg", children = {
            # lemmaTRUE,
            "TMAbort": [
                StructuredProofNode("InitImpliesNoCommitMsg", "H_InitImpliesNoCommitMsg", parent_action="TMAbort")
            ],
            "TMCommit": [
                StructuredProofNode("InitImpliesNoAbortMsg", "H_InitImpliesNoAbortMsg", parent_action="TMCommit")
            ]
        })
        commitMsgImpliesNoAbortMsg.parent_action ="RMChooseToAbortAction"

        rMSentPrepareImpliesNotWorking = StructuredProofNode("RMSentPrepareImpliesNotWorking", "H_RMSentPrepareImpliesNotWorking")
        rMSentPrepareImpliesNotWorking.parent_action = "TMRcvPreparedAction"

        commitMsgImpliesNoRMAborted = StructuredProofNode("CommitMsgImpliesNoRMAborted", "H_CommitMsgImpliesNoRMAborted", children = [
            StructuredProofNode("CommitMsgImpliesAllPreparesSent", "H_CommitMsgImpliesAllPreparesSent", children=[
                tMKnowsPrepareImpliesRMSentPrepare
            ]),
            StructuredProofNode("AllPreparedImpliesAllPreparesSent", "H_AllPreparedImpliesAllPreparesSent", children=[
                tMKnowsPrepareImpliesRMSentPrepare
            ], parent_action="TMCommit"),
            StructuredProofNode("RMAbortAfterPrepareImpliesTMAborted", "H_RMAbortAfterPrepareImpliesTMAborted", children = [
                StructuredProofNode("AbortMsgSentImpliesTMAborted", "H_AbortMsgSentImpliesTMAborted"),
                rMSentPrepareImpliesNotWorking
            ], parent_action="TMCommit"),
            commitMsgImpliesNoAbortMsg,
            rMSentPrepareImpliesNotWorking
        ])
        # commitMsgImpliesNoRMAborted.parent_action = "RMChooseToAbortAction"

        tMKnowsPrepareImpliesRMPreparedCommittedOrAborted = StructuredProofNode(
            "TMKnowsPrepareImpliesRMPreparedCommittedOrAborted", 
            "H_TMKnowsPrepareImpliesRMPreparedCommittedOrAborted", children = {
                # lemmaTRUE,
                "TMAbort": [rMSentPrepareImpliesNotWorking]
        })

        # TwoPhase proof structure.
        twopc_children = [
            # StructuredProofNode("CommitMsgImpliesAllPrepared", "H_CommitMsgImpliesAllPrepared", parent_action="RMChooseToAbortAction"),
            commitMsgImpliesNoAbortMsg,
            # commitMsgImpliesNoRMAborted,
            StructuredProofNode("CommittedRMImpliesCommitMsg", "H_CommittedRMImpliesCommitMsg"),
            tMKnowsPrepareImpliesRMPreparedCommittedOrAborted
        ]
        twopc_root = StructuredProofNode("Safety", safety, children = {
            "TMAbort": twopc_children,
            "RMRcvCommitMsgAction": [rMSentPrepareImpliesNotWorking]
        })



        #
        # AbstractStaticRaft proof structure.
        #

        quorumsSafeAtTerms = StructuredProofNode("QuorumsSafeAtTerms_C", "H_QuorumsSafeAtTerms")

        onePrimaryPerTerm = StructuredProofNode("OnePrimaryPerTerm_Lemma", "H_OnePrimaryPerTerm", children = [
            # lemmaTRUE,
            quorumsSafeAtTerms
        ])

        logEntryInTermImpliesSafeAtTerms = StructuredProofNode("LogEntryInTermImpliesSafeAtTerm", "H_LogEntryInTermImpliesSafeAtTerm", children = [        
            quorumsSafeAtTerms
        ])

        primaryHasEntriesItCreated = StructuredProofNode("PrimaryHasEntriesItCreated_A", "H_PrimaryHasEntriesItCreated")
        primaryHasEntriesItCreated.children = [
            lemmaTRUE,
            # quorumsSafeAtTerms,
            # onePrimaryPerTerm,
            # logEntryInTermImpliesSafeAtTerms
        ]
        primaryHasEntriesItCreated.cti_view = "<<state, currentTerm, log>>"
        primaryHasEntriesItCreated.cti_project_vars = ["state", "currentTerm", "log"]

        currentTermsAtLeastLargeAsLogTermsForPrimary =  StructuredProofNode("CurrentTermAtLeastAsLargeAsLogTermsForPrimary", "H_CurrentTermAtLeastAsLargeAsLogTermsForPrimary", children = [
                logEntryInTermImpliesSafeAtTerms
        ])

        termsGrowMonotonically = StructuredProofNode("TermsOfEntriesGrowMonotonically_A", "H_TermsOfEntriesGrowMonotonically", children = [
            currentTermsAtLeastLargeAsLogTermsForPrimary
        ])

        logMatching = StructuredProofNode("LogMatching_Lemma", "LogMatching", children = [
            primaryHasEntriesItCreated
        ])

        lemmaTRUEShim.children = [primaryHasEntriesItCreated]

        uniformLogEntriesInTerm = StructuredProofNode("UniformLogEntriesInTerm_T3", "H_UniformLogEntriesInTerm", children = [
            lemmaTRUEShim,
            # logMatching,
            # primaryHasEntriesItCreated
        ])


        asr_children = [
            StructuredProofNode("CommittedEntryExistsOnQuorum", "H_CommittedEntryExistsOnQuorum", children = [
                lemmaTRUE,
                # StructuredProofNode("LogsLaterThanCommittedMustHaveCommitted", "H_LogsLaterThanCommittedMustHaveCommitted", children = [lemmaTRUE]),
                # StructuredProofNode("LeaderCompletenessLemma", "LeaderCompleteness", children = [lemmaTRUE])
                StructuredProofNode("PrimaryOrLogsLaterThanCommittedMustHaveEarlierCommitted", "H_PrimaryOrLogsLaterThanCommittedMustHaveEarlierCommitted", children = [
                    lemmaTRUE,
                    # StructuredProofNode("CommittedEntryExistsOnQuorum_B", "H_CommittedEntryExistsOnQuorum"),
                    termsGrowMonotonically,
                    StructuredProofNode("EntriesCommittedInOwnTerm_W", "H_EntriesCommittedInOwnTerm"),
                    uniformLogEntriesInTerm,
                    # logEntryInTermImpliesSafeAtTerms
                ]),

                # termsGrowMonotonically,
                # StructuredProofNode("EntriesCommittedInOwnTerm_B", "H_EntriesCommittedInOwnTerm"),
                # logEntryInTermImpliesSafeAtTerms,
                # uniformLogEntriesInTerm
            ]),
        ]
        asr_root = StructuredProofNode("Safety", safety, children = asr_children)

        root = None
        actions = None
        if self.specname == "TwoPhase":
            root = twopc_root
            actions = [
                "TMCommit", 
                "TMAbort",
                "TMRcvPreparedAction",
                "RMPrepareAction",
                "RMChooseToAbortAction",
                "RMRcvCommitMsgAction",
                "RMRcvAbortMsgAction"    
            ]
        elif self.specname == "AbstractStaticRaft":
            root = asr_root
        else:
            logging.info("Unknown spec for proof structure: " + self.specname)
            return

        ###########
        ###########

        # root_obligation = ("Safety", safety)
        # Optionally save proof structure as DOT graph.
        # proof.save_as_dot("benchmarks/" + self.specname + "_ind-proof-tree")

        proof = None

        #
        # Handle interactive proof tree commands.
        #

        # Optionally reload proof structure from locally defined template.
        if self.proof_tree_cmd and self.proof_tree_cmd[0] in ["reload", "reload_proof_struct"]:
            logging.info(f"Reloading entire proof and re-generating CTIs.")
            proof = StructuredProof(root, specname = self.specname, actions=actions)
            proof.save_proof()

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
        proof.save_proof()

        run_server = True
        if run_server:
            import flask
            from flask import Flask
            from flask_cors import CORS
            app = Flask(__name__, static_folder="benchmarks")
            CORS(app)
            import threading

            @app.route('/getProofGraph')
            def getProofGraph():
                proof_json = proof.serialize(include_ctis=True)
                response = flask.jsonify({'ok': True, 'proof_graph': proof_json})
                response.headers.add('Access-Control-Allow-Origin', '*')
                # print(proof_json)
                return response

            @app.route('/getNode/<expr>')
            def getCtis(expr):
                node = proof.get_node_by_name(proof.root, expr)
                print(node)

                response = flask.jsonify(node.serialize())
                response.headers.add('Access-Control-Allow-Origin', '*')
                return response

            @app.route('/genCtis/<flag>/<expr>')
            def genCtis(flag, expr):
                logging.info(f"genCtis({flag}, {expr})")
                print(flag, expr)

                response = flask.jsonify({'ok': True, 'expr': expr})
                response.headers.add('Access-Control-Allow-Origin', '*')

                # Launch proof generation process in separate thread and return response right away.
                def bar():
                    subtree = flag == "subtree"
                    start_node = proof.get_node_by_name(proof.root, expr)
                    if subtree:
                        proof.gen_ctis_for_node(self, start_node)
                    else:
                        proof.gen_ctis_for_node(self, start_node, target_node_name=expr)
                    print("-- Finished generating CTIs for node:", expr, "--")

                p = threading.Thread(target=bar) # create a new Process
                p.start()

                return response
            
            # Start up server API.
            app.run(debug=False)
            return


            # logging.info(f"Loading proof from object file: {self.proof_base_filename}.json")
            # proof = StructuredProof(load_from_obj=proof_obj)

        # Re-save proof at this point.
        self.save_proof(proof)
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

    def do_invgen_proof_tree_mode(self, interactive_mode=False):
        self.lemma_obligations = [("Safety", self.safety)]
        self.all_generated_lemmas = set()

        # TODO: Optionally reload from file for interactive mode.
        self.proof_graph = {"edges": [], "safety": self.safety}

        # For proof tree we look for single step inductive support lemmas.
        self.simulate_depth = 1

        count = 0

        for roundi in range(self.num_rounds):
            logging.info("### STARTING ROUND %d" % roundi)
            logging.info("Num remaining lemma obligations %d" % len(self.lemma_obligations))
            if len(self.lemma_obligations) == 0:
                logging.info("No remaining lemma obligations. Stopping now!")
                return

            self.strengthening_conjuncts = []

            logging.info("Generating CTIs.")
            t0 = time.time()
            curr_obligation = self.lemma_obligations.pop(0)
            print("Current obligation:", curr_obligation)
            # k_ctis = self.generate_ctis(props=[("LemmaObligation" + str(count), curr_obligation[1])])
            k_ctis, k_cti_traces = self.generate_ctis(props=[curr_obligation])
            count += 1

            # for kcti in k_ctis:
                # print(str(kcti))
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
                logging.info("")
                continue
            else:
                logging.info("Not done. Current invariant candidate is not inductive.")

            self.total_num_cti_elimination_rounds = (roundi + 1)
            ret = self.eliminate_ctis(k_ctis, self.num_invs, roundi, append_inv_round_id=True)
            # If we did not eliminate all CTIs in this round, then exit with failure.
            if ret == None:
                logging.info("Could not eliminate all CTIs in this round. Exiting with failure.")
                break
            else:
                # Successfully eliminated all CTIs.
                print("Adding new proof obligations:" + str(len(self.strengthening_conjuncts)))
                self.lemma_obligations += self.strengthening_conjuncts
                for support_lemma in self.strengthening_conjuncts:
                    # Check for existence of the predicate expression in existing lemma set.
                    if support_lemma[1] not in [x[1] for x in self.all_generated_lemmas]:
                        self.proof_graph["edges"].append((support_lemma,curr_obligation))
                        self.all_generated_lemmas.add(support_lemma)
            logging.info("")

    def do_invgen(self):
        # Record Java version for stat recording.
        self.save_java_version_info()

        if self.pregen_inv_cmd is not None:
            logging.info(f"Pre-generating invariants with command '{self.pregen_inv_cmd}'")
            self.pre_generate_invs()

        # A correct invariant.
        # \A VARI \in Node : \A VARJ \in Node : (vote_request_msg[<<VARJ,VARI>>]) \/ (~(votes[<<VARJ,VARI>>]))

        # 1 vote_request_msg[<<VARJ,VARI>>]
        # 7 votes[<<VARJ,VARI>>]
        # inv1 = self.preds[1]
        # inv7 = self.preds[7]
        # inv1 \/ ~inv7
        # for i,p in enumerate(self.preds):
            # print(i,p)

        #
        # Check valuation of all predicates on reachable states.
        # (EXPERIMENTAL)
        #
        self.pred_vals = None
        self.use_fast_pred_eval = False
        if self.use_fast_pred_eval:
            logging.info("Checking predicates on reachable states")
            self.pred_vals = self.check_predicates(self.preds)

        # quant_inv_fn = self.quant_inv
        # quant_preds = []
        # for p in self.preds:
        #     quantp = quant_inv_fn(p)
        #     quant_preds.append(quantp)
        #     # print(p)
        #     print(quantp)
        # return


        for roundi in range(self.num_rounds):
            logging.info("### STARTING ROUND %d" % roundi)

            logging.info("Generating CTIs.")
            t0 = time.time()
            (k_ctis,k_cti_traces) = self.generate_ctis()
            # for kcti in k_ctis:
                # print(str(kcti))
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

            self.total_num_cti_elimination_rounds = (roundi + 1)
            ret = self.eliminate_ctis(k_ctis, self.num_invs, roundi)
            # If we did not eliminate all CTIs in this round, then exit with failure.
            if ret == None:
                logging.info("Could not eliminate all CTIs in this round. Exiting with failure.")
                break
            logging.info("")

        # Do a final inductive check.
        # TODO: Possibly run this CTI generation with a different seed.
        logging.info("Running final CTI generation step.")
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


            logging.info("Final inductive invariant:")
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

    def run(self):
        tstart = time.time()

        if self.proof_tree_mode:

            # Run interactive mode and then exit.
            if self.interactive_mode:
                logging.info("Running in interactive proof tree mode.")
                self.run_interactive_mode()
                return

            self.do_invgen_proof_tree_mode(interactive_mode=self.interactive_mode)
            # print("")
            # print("Proof graph edges")
            dot = graphviz.Digraph('round-table', comment='The Round Table')  
            dot.graph_attr["rankdir"] = "LR"
            dot.node_attr["fontname"] = "courier"
            # dot.node_attr["shape"] = "box"
            
            # Store all nodes.
            for e in self.proof_graph["edges"]:
                print(e[0])
                print(e[1])
                dot.node(e[0][0], e[0][1].replace("\\", "\\\\"))
                dot.node(e[1][0], e[1][1].replace("\\", "\\\\"))

            for e in self.proof_graph["edges"]:
                print(e[0])
                print(e[1])
                dot.edge(e[0][0], e[1][0])
                # print(e)

            print("Final proof graph:")
            print(dot.source)
            f = open("notes/" + self.specname + "_ind-proof-tree.dot", 'w')
            f.write(dot.source)
            f.close()
            dot.render("notes/" + self.specname + "_ind-proof-tree")
            print("Finished inductive invariant generation in proof tree mode.")
        else:
            self.do_invgen()

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

    # Parse command line arguments.
    parser = argparse.ArgumentParser(description='')
    parser.add_argument('--spec', help="Name of the protocol benchmark to run (given as 'benchmarks/<spec_name>').", required=True, type=str)
    parser.add_argument('--ninvs', help='Maximum number of invariants to generate at each iteration.', required=False, type=int, default=5000)
    parser.add_argument('--niters', help='Maximum number of invariant generation iterations to run in each CTI elimination round.', required=False, type=int, default=3)
    parser.add_argument('--nrounds', help='Maximum number of CTI elimination rounds to run.', required=False, type=int, default=3)
    parser.add_argument('--seed', help='Seed for RNG.', required=False, default=0, type=int)
    parser.add_argument('--num_simulate_traces', help='The maximum number of traces TLC will generate when searching for counterexamples to inductions (CTIs).', required=False, type=int, default=DEFAULT_NUM_SIMULATE_TRACES)
    parser.add_argument('--simulate_depth', help='Maximum depth of counterexample to induction (CTI) traces to search for.', required=False, type=int, default=DEFAULT_SIMULATE_DEPTH)
    parser.add_argument('--tlc_workers', help='Number of TLC worker threads to use when checking candidate invariants.', required=False, type=int, default=DEFAULT_TLC_WORKERS)
    parser.add_argument('--java_exe', help='Path to Java binary.', required=False, type=str, default=JAVA_EXE)
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
    parser.add_argument('--max_num_ctis_per_round', help='Max number of CTIs per round.', type=int, default=10000)
    parser.add_argument('--override_num_cti_workers', help='Max number of TLC workers for CTI generation.', type=int, default=None)
    
    # Proof tree related commands.
    parser.add_argument('--proof_tree_mode', help='Run in inductive proof tree mode (EXPERIMENTAL).', default=False, action='store_true')
    parser.add_argument('--interactive', help='Run in interactive proof tree mode (EXPERIMENTAL).', default=False, action='store_true')
    parser.add_argument('--max_proof_node_ctis', help='Maximum number of CTIs per proof node.', type=int, default=5000)
    parser.add_argument('--proof_tree_cmd', help='Proof tree command (EXPERIMENTAL).', default=None, type=str, required=False, nargs="+")

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

    # Initialize command line args.
    num_invs = args["ninvs"]
    seed = args["seed"] 
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
    spec_config_file = os.path.join(specdir, specname) + ".config.json"
    fcfg = open(spec_config_file)
    spec_config = json.load(fcfg)

    # Load config parameters.
    preds = spec_config["preds"]
    # preds_alt = spec_config["preds_alt"]    
    safety = spec_config["safety"]
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
    if "use_cpp_invgen" in spec_config:
        use_cpp_invgen = spec_config["use_cpp_invgen"]
    else:
        use_cpp_invgen = False
    pregen_inv_cmd = spec_config.get("pregen_inv_cmd", None)

    logging.info(f"Loaded config for '{specname}' spec.")
    for k in spec_config:
        logging.info(f"{k}: {spec_config[k]}")

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

    # Generate an inductive invariant.
    indgen = InductiveInvGen(specdir, specname, safety, constants, constraint, quant_inv, model_consts, preds, 
                                num_invs=num_invs, num_rounds=num_rounds, seed=seed, typeok=typeok, tlc_specific_spec=tlc_specific_spec, num_iters=numiters, 
                                num_simulate_traces=NUM_SIMULATE_TRACES, simulate_depth=simulate_depth, tlc_workers=tlc_workers, quant_vars=quant_vars, symmetry=symmetry,
                                simulate=simulate, java_exe=JAVA_EXE, cached_invs=cached_invs, cached_invs_gen_time_secs=cached_invs_gen_time_secs, use_cpp_invgen=use_cpp_invgen,
                                pregen_inv_cmd=pregen_inv_cmd, opt_quant_minimize=args["opt_quant_minimize"],try_final_minimize=try_final_minimize,proof_tree_mode=args["proof_tree_mode"],
                                interactive_mode=args["interactive"],
                                max_num_conjuncts_per_round=args["max_num_conjuncts_per_round"], max_num_ctis_per_round=args["max_num_ctis_per_round"],
                                override_num_cti_workers=args["override_num_cti_workers"],use_apalache_ctigen=args["use_apalache_ctigen"],all_args=args)


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
    logging.info("Invariant checking duration: %f secs.", indgen.get_invcheck_duration())
    logging.info("CTI elimination checks duration: %f secs.", indgen.get_ctielimcheck_duration())
    logging.info("Total duration: {:.2f} secs.".format(((time.time() - tstart))))

    if save_result:
        indgen.save_result(results_dirname=results_dir)
