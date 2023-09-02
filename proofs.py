#
# Classes and definitions used for constructing structured inductive invariant proof objects.
#

import random
import pickle
import graphviz
from mc import CTI
import logging
import json

class StructuredProofNode():
    """ Single node (i.e. lemma) of a structured proof tree. """
    def __init__(self, name="", expr="", children={}, parent=None, load_from_obj = None):
        # Name used to identify the expression.
        self.name = name
        # Top level goal expression to be proven.
        self.expr = expr
        self.children = children

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

        # Pointer to this node's parent, or None if it has no parent.
        self.parent = parent

        # Set of CTIs of parent that this lemma eliminates.
        self.parent_ctis_eliminated = []

        # Set of CTIs of parent that are eliminated by this predicate alone and
        # none of its siblings.
        self.parent_ctis_uniquely_eliminated = []

        if load_from_obj:
            self.load_from(load_from_obj)

    def serialize_rec(self, include_ctis=True, seen=set()):
        # if self.expr in seen:
        #     None
        # print(seen)
        # seen.add(self.expr)
        ret = {
            "name": self.name, 
            "expr": self.expr, 
            "apalache_proof_check": self.apalache_proof_check, 
            "children":  {a:[c.serialize_rec(include_ctis=include_ctis, seen=set(seen)) for c in self.children[a]] for a in self.children}, 
            "project_vars": self.cti_project_vars
        }

        cti_sort_key = lambda c : c.cost
        remaining_ctis_cost_sorted = sorted(self.get_remaining_ctis(), key = cti_sort_key)

        cti_info = {
            # "ctis": [c.serialize() for c in self.ctis],
            "ctis": {a:[c.serialize() for c in self.ctis[a]] for a in self.ctis},
            # Eliminated CTIs are stored as CTI hashes, not full CTIs.
            # "ctis_eliminated": [c for c in self.ctis_eliminated],
            "ctis_eliminated": self.ctis_eliminated,
            # "ctis_remaining": {a:[cti.serialize() for cti in self.get_remaining_ctis(a)] for a in self.ctis},
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

    def serialize(self, include_ctis=True):
        seen_nodes = set()
        return self.serialize_rec(include_ctis=include_ctis, seen=seen_nodes)


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

        if load_from_obj:
            self.load_from(load_from_obj)

    def serialize(self, include_ctis=True):
        return {
            "safety": self.safety_goal, 
            "root": self.root.serialize(include_ctis=include_ctis),
            "nodes": [n.serialize() for n in self.nodes],
            "spec_defs": self.spec_defs
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

    def add_node_to_dot_graph(self, dot, node):
        """ Add this node and its children, recursively, to DOT graph."""
        dot.node(node.expr)
        for c in node.children_list():
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

            # If you didn't find the node via traversing from the
            # start node, also check the set of all nodes.
            for n in self.nodes:
                if name == n.name:
                    return n
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
                    # print(uniq_cti_obj.pretty_str())

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

        typeok_override = None
        # Optionally use special TypeOK for this node.
        if node.ctigen_typeok is not None:
            typeok_override = node.ctigen_typeok

        k_ctis, _ = indgen.generate_ctis(
                            props=[(node.name, node.expr)], 
                            reseed=True, depth=1, 
                            view=node.cti_view, 
                            actions=actions, 
                            typeok_override=typeok_override)

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
        for child_node in node.children_list():
            self.gen_ctis_for_node(indgen, child_node, target_node_name=target_node_name)
