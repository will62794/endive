#
# TLA+ parser using XMLExporter of SANY.
#

import xml.etree.ElementTree as ET
import subprocess
import copy

class QuantPrefix:
    def __init__(self, quant_type, param_name):
        self.quant_type = quant_type
        self.paramName = param_name

class QuantPred:
    """ Represents a quantified TLA+ state predicate."""
    def __init__(self, quant_prefix_elems, pred_expr_elem):
        self.quant_prefix_elems = quant_prefix_elems # ordered list of quantifier prefix elements.
        self.pred_expr_elem = pred_expr_elem

    def quant_prefix_text(self):
        print("quant_prefix_text", self.quant_prefix_elems)
        for qp in self.quant_prefix_elems:
            for el in qp:
                print(el)

        return self.quant_prefix_elems


class TLASpec:
    """ Represents a parsed TLA+ spec file. """
    def __init__(self, xml_ast, spec_text_lines):
        self.ast = xml_ast

        # Extract XML AST into alternate structured representation
        # for convenience.
        self.spec_obj = self.extract_spec_obj(self.ast)
        self.spec_text_lines = spec_text_lines

    def get_spec_obj(self):
        return self.spec_obj
    
    def get_text_from_location_endpoints(self, begin, end):
        """ Retrieve text from spec given (line, col) begin and end points."""
        (line_begin, col_begin) = begin
        (line_end, col_end) = end

        # Shift to account for 1-indexing
        line_begin -= 1
        col_begin -= 1
        line_end -= 1
        col_end -= 1

        if line_end == line_begin:
            return self.spec_text_lines[line_begin][col_begin:col_end + 1]

        start_line = self.spec_text_lines[line_begin][col_begin:].strip()
        middle_lines = self.spec_text_lines[line_begin+1:line_end]
        if line_end > line_begin:
            end_line = self.spec_text_lines[line_end][:col_end]
        else:
            end_line = ""
        # print("start line:", start_line)
        # print("middle line:", middle_lines)
        # print("end line:", start_line)
        out = start_line + "".join(middle_lines) + end_line
        return out

    def extract_spec_obj(self, ast):
        """ Parse user definitions and variables, etc. from spec."""
        root = ast.getroot()

        entries = root.findall("context")[0].findall("./entry")
        builtins = {}
        constant_decls = {}
        variable_decls = {}
        defs_table = {}
        self.formal_params_table = {}

        # Extract all top-level definitions.
        for entry in entries:
            curr_uid = None
            for elem in entry:
                # print(f.tag)
                if elem.tag == "UID":
                    curr_uid = elem.text

            for elem in entry:
                if elem.tag == "FormalParamNode":
                    op = {"uid": curr_uid, "elem": elem, "uniquename": elem.find("uniquename").text}
                    # for opField in elem:
                        # op[opField.tag] = opField.text
                        # print("  ",opField.tag, ":", opField.text)
                    self.formal_params_table[curr_uid] = op

                # Extract user-defined ops.
                if elem.tag == "UserDefinedOpKind":
                    op = {"uid": curr_uid, "elem": elem}
                    for opField in elem:
                        op[opField.tag] = opField.text
                        # print("  ",opField.tag, ":", opField.text)
                    defs_table[curr_uid] = op

                # Extract VARIABLE declarations, also built-ins.
                if elem.tag == "OpDeclNode" or elem.tag == "BuiltInKind":
                    op = {"uid": curr_uid}
                    for opField in elem:
                        op[opField.tag] = opField.text
                        # print("  ",opField.tag, ":", opField.text)

                    if elem.tag == "OpDeclNode":
                        # op kind '3' appears to be CONSTANT declarations.
                        if op["kind"] == "2":
                            constant_decls[curr_uid] = op

                        # op kind '3' appears to be VARIABLE declarations.
                        if op["kind"] == "3":
                            variable_decls[curr_uid] = op
                    if elem.tag == "BuiltInKind":
                        builtins[curr_uid] = op

        # for e in defs_table:
        #     print(e, defs_table[e])

        # print("--- VARIABLES")
        # for v in variable_decls:
        #     print(v, variable_decls[v])

        spec_obj = {
            "defs": defs_table,
            "var_decls": variable_decls,
            "constant_decls": constant_decls,
            "builtins": builtins
        }
        return spec_obj
    
    def get_all_vars(self):
        varnames = []
        for k in self.spec_obj["var_decls"]:
            varname = self.spec_obj["var_decls"][k]["uniquename"]
            varnames.append(varname)
        return varnames

    def get_vars_in_def_rec(self, elem, level_filter=None):
        uid = None
        level_elem = elem.find("level")
        level_elem_val = None
        if level_elem is not None:
            level_elem_val = int(level_elem.text)
        if (level_filter is not None) and (level_elem is not None) and level_elem_val > level_filter: 
            return (set(), {})

        if elem.tag in ["OpDeclNodeRef", "BuiltInKindRef"]:
            children = list(elem)
            assert children[0].tag == "UID"
            uid = children[0].text

        updated_vars_with_coi = {}
        if elem.tag == "OpApplNode":
            # print(elem.tag)
            # Is this an equality operator where the left hand side is a primed oeprator.
            is_equality = False
            is_primed_var = False
            for c in elem:
                if c.tag == "operator":
                    # Equality operator.
                    x = c.find("BuiltInKindRef")
                    if x is not None and x.find("UID").text == "4":
                        is_equality = True
                if c.tag == "operands" and is_equality:
                    # print("EQUALITY OPERANDS")
                    operands = list(c)

                    # print(operands[0])
                    if operands[0].tag == "OpApplNode":
                        for el in operands[0]:
                            if el.tag == "operator":
                                # print(el)
                                firstchild = list(el)[0]
                                if firstchild.tag == "BuiltInKindRef":
                                    # Prime operator (') is UID=13.
                                    if list(firstchild)[0].text == "13":
                                        # print("FC:", firstchild.tag)
                                        # print("FC:", list(firstchild)[0].text)
                                        is_primed_var = True
                            if el.tag == "operands" and is_primed_var:
                                # print("PRIMED OPERANDS")
                                for oper in el:
                                    # print(oper.tag)
                                    # print(list(oper))
                                    loc = oper.find("location")
                                    line =  loc.find("line").find("begin")
                                    # print("line:", line.text)
                                    op = oper.find("operator")
                                    uid = op.find("OpDeclNodeRef").find("UID").text
                                    # The modified variable.
                                    # TODO: We also want to extract the cone-of-influence (COI) of this variable i.e.
                                    # any variables that appear in its update expression.
                                    var_decl = self.spec_obj["var_decls"][uid]
                                    # print(var_decl)
                                    var_name = var_decl["uniquename"]
                                    # updated_vars.add(var_decl["uniquename"])
                                    if var_name not in updated_vars_with_coi:
                                        # Initialize with empty cone of influence.
                                        updated_vars_with_coi[var_name] = set()

                                    # print(updated_vars_with_coi)

                                    # The update expression, for computing COI.
                                    # print("UPDATE EXPR:", operands[1])
                                    # print(operands[1])
                                    loc = operands[1].find("location").find("line").find("begin")
                                    # cone_of_influence_vars = self.get_vars_in_def_rec(operands[1], only_body=False)
                                    coi_vars = set()
                                    for sub in operands[1].iter():
                                        if sub.tag == "OpDeclNodeRef":
                                            uid = sub.find("UID").text
                                            if uid in self.spec_obj["var_decls"]:
                                                coi_var_name = self.spec_obj["var_decls"][uid]["uniquename"]
                                                # print("coi var:", coi_var_name)
                                                coi_vars.add(coi_var_name)

                                    # print("COI:", coi_vars)
                                    updated_vars_with_coi[var_name].update(coi_vars)
                                    return (set(), updated_vars_with_coi)


        if elem.tag == "OpDeclNodeRef":
            # CONSTANT references are not variables.
            if uid in self.spec_obj["constant_decls"]:
                return (set(), {})
            
            var_name = self.spec_obj["var_decls"][uid]["uniquename"]
            return (set([var_name]), {})
        
        body = None
        for child in elem:
            # print(child.tag)
            if child.tag == "body":
                body = child

        if body is None:
            return ([],{})
        
        all_vars = set()
        all_updated_vars = {}
        
        # Traverse the whole subtree for this definition, looking up 
        # definitions as needed.
        for sub_elem in body.iter():
            # print("Sub elem:",sub_elem.tag)
            if sub_elem.tag == "UserDefinedOpKindRef":
                # print(sub_elem.tag)
                children = list(sub_elem)
                assert children[0].tag == "UID"
                uid = children[0].text
                def_elem = self.spec_obj["defs"][uid]["elem"]
                (new_vars,new_updated_vars) = self.get_vars_in_def_rec(def_elem)
                # if len(new_vars) or len(new_updated_vars.keys()):
                # print("new updated vars:", new_updated_vars)
                all_vars.update(new_vars)
                for v in new_updated_vars:
                    if v in all_updated_vars:
                        # print("all updated:", all_updated_vars)
                        # print("all updated:", all_updated_vars[v])
                        # print("new updated:", new_updated_vars[v])
                        all_updated_vars[v].update(new_updated_vars[v])
                    else:
                        all_updated_vars[v] = new_updated_vars
            else:
                (new_vars,new_updated_vars) = self.get_vars_in_def_rec(sub_elem)
                # if len(new_vars) or len(new_updated_vars.keys()):
                #     print(new_vars, new_updated_vars)

                all_vars.update(new_vars)
                for v in new_updated_vars:
                    if v in all_updated_vars:
                        # print("all updated:", all_updated_vars[v])
                        # print("new updated:", new_updated_vars[v])
                        all_updated_vars[v].update(new_updated_vars[v])
                    else:
                        all_updated_vars[v] = new_updated_vars[v]
                # all_updated_vars.update(new_updated_vars)
        return (all_vars, all_updated_vars)

    def remove_unchanged_elems(self, elem):
        body = None
        for child in elem:
            if child.tag == "body":
                body = child

        unchanged = []

        for sub_elem in body.iter():
            # print(sub_elem.tag)
            for child in sub_elem:
                if child.tag == "OpApplNode":
                    # for v in sub_elem:
                    #     print(v.tag)
                    oper = child.find("operator")
                    builtInRef = oper.find("BuiltInKindRef")
                    # print(oper)
                    if builtInRef:
                        # print(builtInRef)
                        uid = builtInRef.find("UID").text
                        # print(uid)
                        name = self.spec_obj["builtins"][uid]["uniquename"]
                        # print(name)
                        if name == "UNCHANGED":
                            sub_elem.remove(child)
            if sub_elem.tag == "UserDefinedOpKindRef":
                children = list(sub_elem)
                assert children[0].tag == "UID"
                uid = children[0].text
                def_elem = self.spec_obj["defs"][uid]["elem"]
                new_unchanged = self.remove_unchanged_elems(def_elem)
                unchanged += new_unchanged
        # print("UNCHANGED elems:", unchanged_elems)
        return unchanged

    def remove_update_expressions(self, elem):
        body = None
        for child in elem:
            if child.tag == "body":
                body = child

        to_remove = []

        for sub_elem in body.iter():
            for child in sub_elem:
                if child.tag != "OpApplNode":
                    continue
                # print(sub_elem.tag)
                # Is this an equality operator where the left hand side is a primed oeprator.
                is_equality = False

                operator = child.find("operator")
                if operator is not None:
                    builtInRef = operator.find("BuiltInKindRef")
                    if builtInRef is not None and builtInRef.find("UID").text == "4":
                        is_equality = True
                        # print("IS EQUAL", operator)

                operands = child.find("operands")
                if operands is not None and is_equality:
                    # print(operands[0])
                    # for o in operands:
                    #     print("operands:", o.tag)
                    #     print(list(o))
                    if operands[0].tag == "OpApplNode":
                        # for el in operands[0]:
                        prime_oper = operands[0].find("operator")
                        prime_operands = operands[0].find("operands")
                        # print("PRIME OPERANDS:", list(prime_operands))
                        if prime_oper is not None:
                            firstchild = list(prime_oper)[0]
                            if firstchild.tag == "BuiltInKindRef":
                                # Prime operator (') is UID=13.
                                if firstchild.find("UID").text == "13":
                                    # print("FC:", firstchild.tag)
                                    # print("FC:", list(firstchild)[0].text)
                                    # print(f"!! REMOVING child: {child}")

                                    to_remove.append((sub_elem, child))

                                    for x in prime_operands:
                                        opDecl = x.find("operator").find("OpDeclNodeRef")
                                        if opDecl is not None:
                                            uid  = opDecl.find("UID").text
                                            # print("UID:", uid)
                                            if uid in self.spec_obj["var_decls"]:
                                                varname = self.spec_obj["var_decls"][uid]["uniquename"]
                                                # print("$$$$ REMOVAL of:", varname)

        # print("TO REMOVE:", to_remove)
        for (el,child) in to_remove:
            # print("Removing ", child)
            el.remove(child)

    def get_vars_in_def(self, name, ignore_unchanged=True, ignore_update_expressions=False, level_filter=None):
        """ Get the set of variables that appear in a given definition body. """ 
        node = self.get_def_node_by_uniquename(name)
        node_uid = node["uid"]

        # root = copy.deepcopy(self.ast.getroot())
        # entries = root.findall("context")[0].findall("./entry")
        # print(node_uid)
        res = [e for e in self.spec_obj["defs"].values() if e["uid"] == node_uid]
        if len(res) == 0:
            return None
        obj = res[0]
        elem = copy.deepcopy(obj["elem"])

        body = None
        for child in elem:
            if child.tag == "body":
                body = child

        # Remove unchanged elements from the tree just for 
        if ignore_unchanged:
            self.remove_unchanged_elems(elem)
        if ignore_update_expressions:
            self.remove_update_expressions(elem)

        all_vars,updated_vars = self.get_vars_in_def_rec(elem, level_filter=level_filter)
        # print("updated vars:", updated_vars)
        return (all_vars,updated_vars)

        # print(entries)
        # spec_obj = self.extract_spec_obj(spec_ast)
        # return self.spec_obj["defs"]
        # pass
    
    def extract_OpApplNode(self, elem, curr_quants, curr_preds):

        # bound = elem.find("boundSymbols")
        # if bound is not None:
            # print("BOUND symbols:", bound)
        operator = elem.find("operator")
        userDef = operator.find("UserDefinedOpKindRef")

        if userDef is not None:
            uid = userDef.find("UID").text
            udef = self.spec_obj["defs"][uid]
            udef_elem = udef["elem"]
            print(udef_elem.tag)
            # for op in udef_elem.find("operands"):
            #     print(op)
            for a in udef_elem:
                print(a)
            body = udef_elem.find("body")
            print("user def:", udef)
            if body is not None:
                self.extract_quant_preds(body, curr_quants, curr_preds)

        builtInRef = operator.find("BuiltInKindRef")

        if builtInRef is None:
            for o in operator:
                print(o.tag)
            return

        uid = builtInRef.find("UID")

        builtin = None
        if uid is not None and uid.text in self.spec_obj["builtins"]:
            builtin = self.spec_obj["builtins"][uid.text]

        # Conjunction list.
        if builtin is not None and builtin["uniquename"] in ["\\land", "\\lor"]:
            print(builtin)
            print(elem.find("operands"))
            for conj in elem.find("operands"):
                print(conj)
                if conj.tag == "OpApplNode":
                    self.extract_OpApplNode(conj, curr_quants, curr_preds)


        if builtin is not None and builtin["uniquename"] == "TRUE":
            pred = QuantPred(curr_quants, elem)
            curr_preds.append((curr_quants, elem))

        if builtin is not None and builtin["uniquename"] in ["$ConjList", "$DisjList"]:
            print("CONJUNCTION LIST")
            for conj in elem.find("operands"):
                level = conj.find("level").text
                print(conj)
                # print("conjunct level: ", level)
                # For now append level 1 conjunct predicates.
                if level in ["0", "1"]:
                    pred = QuantPred(curr_quants, conj)
                    print(pred.quant_prefix_text())
                    curr_preds.append((curr_quants, conj))

        # Bounded quantifier.
        if builtin is not None and builtin["uniquename"] in ["$BoundedForall", "$BoundedExists"]:
            # builtin = self.spec_obj["builtins"][uid.text]
            # if builtin["uniquename"] in ["$BoundedForall", "$BoundedExists"]:
            print("QUANT", builtin["uniquename"])
            print("uid", uid.text)
            operands = elem.find("operands")
            boundSymbols = elem.find("boundSymbols")

            for sym in boundSymbols:
                print("bound:", sym)
                for x in sym:
                    print("sym", x)
                    if x.tag == "FormalParamNodeRef":
                        formalParamUID = x.find("UID").text
                        param = self.formal_params_table[formalParamUID]["elem"]
                        paramName = param.find("uniquename").text
                        print("param name:", paramName)
                    if x.tag == "OpApplNode":

                        begin = self.elem_to_location_tuple(x, "begin")
                        end = self.elem_to_location_tuple(x, "end")
                        print(begin, end)
                        text = self.get_text_from_location_endpoints(begin, end)
                        print("bound text:", text)
                        for a in x:
                            # if a.tag == "operator":
                                # begin = self.elem_to_location_tuple(a, "begin")
                                # end = self.elem_to_location_tuple(a, "end")
                                # print("BEGIN:", begin)
                                # print("END  :", end)
                                # text = self.get_text_from_location_endpoints(begin, end)
                                # print(text)
                                # print(a)
                            print(a)
                            # print(list(a))
                            # for c in a:
                            #     print(c)
                        # self.extract_quant_and_predicate_grammar()
                            
                        begin = self.elem_to_location_tuple(elem, "begin")
                        end = self.elem_to_location_tuple(elem, "end")
                        txt = self.get_text_from_location_endpoints(begin, end)
                        print("TXT:", txt)

                        # curr_quants.append(x)

                        # curr_quants.append(QuantPrefix(builtin["uniquename"], ))

                        curr_quants.append((builtin["uniquename"], paramName, text))
            # curr_quants.append(builtin)
            # curr_quants.append(elem)
            print(curr_quants)
            for elem in operands:
                print("quant operand:", elem.tag)
                self.extract_quant_preds(elem, curr_quants, curr_preds)

                # print("operands:", operands)
                # opAppl = operands.find("OpApplNode")
                # if opAppl is not None:
                #     if opAppl.find("operator") is not None:
                #         v = opAppl.find("operator").find("BuiltInKindRef")
                #         print(v)

    def extract_quant_preds(self, elem, curr_quants=[], curr_preds=[]):
        """ Extract quantifier prefixes and predicates in their scope. """

        # Extract quantifier prefixes.
        # for el in elem:
        print("curr_quants:", curr_quants)

        if elem.tag == "UserDefinedOpKind":
            uid = elem.find("UID")
            udef = self.spec_obj["defs"][uid]
            print("user def:", udef)
            self.extract_quant_preds(udef["elem"], curr_quants, curr_preds)

        if elem.tag == "body":
            for el in elem:
                self.extract_quant_preds(el, curr_quants, curr_preds)

        if elem.tag == "OpApplNode":

            self.extract_OpApplNode(elem, curr_quants, curr_preds)
            return

    def elem_to_location_tuple(self, elem, begin_or_end):
        line = int(elem.find("location").find("line").find(begin_or_end).text)
        col = int(elem.find("location").find("column").find(begin_or_end).text)   
        return (line, col)    

    def extract_quant_and_predicate_grammar(self, defname):
        """ From a given quantified definition (either action or state predicate) extract quantifier prefix template and atomic predicates."""
        node = self.get_def_node_by_uniquename(defname)
        print(node)
        node_uid = node["uid"]
        node_elem = node["elem"]

        # print("--- EXTRACT QUANTS ---")
        curr_quants = []
        curr_preds = []
        body = node_elem.find("body")
        if body is None:
            return
        
        self.extract_quant_preds(body, curr_quants, curr_preds)
        print(curr_quants)
        print(curr_preds)

        print("###############")

        # for quant in curr_quants:
        #     # begin = self.elem_to_location_tuple(quant, "begin")
        #     # end = self.elem_to_location_tuple(quant, "end")
        #     # print("BEGIN:", begin)
        #     # print("END  :", end)
        #     # text = self.get_text_from_location_endpoints(begin, end)
        #     print(quant)           

        print("EXTRACTED PREDICATES:")
        for pred in curr_preds:
            begin = self.elem_to_location_tuple(pred[1], "begin")
            end = self.elem_to_location_tuple(pred[1], "end")
            # print("BEGIN:", begin)
            # print("END  :", end)
            text = self.get_text_from_location_endpoints(begin, end)
            print(pred[0], text)

        # print("---EXTRACT PREDS")
        # self.extract_predicates(node_elem)
 

    def get_all_user_defs(self, level=None):
        """ Get all user defined ops at an optionally specified level."""
        # spec_obj = self.extract_spec_obj(spec_ast)
        if type(level) == str:
            levels = [level]
        else:
            levels = level
        if level is None:
            return [v["uniquename"] for v in self.spec_obj["defs"].values()]
        else:
            return [v["uniquename"] for v in self.spec_obj["defs"].values() if v["level"] in levels] 

    def get_def_node_by_uniquename(self, uniquename):
        objs = [a for a in self.spec_obj["defs"].values() if a["uniquename"] == uniquename]
        if len(objs) == 0:
            return None
        return objs[0]
    
    def compute_coi(self, lemma, action, vars_in_action, action_updated_vars, vars_in_action_non_updated, vars_in_lemma):

        # # action = "RequestVote"
        # print("### Getting vars in action:", action)
        # vars_in_action, action_updated_vars = self.get_vars_in_def(action)
        # vars_in_action_non_updated, _ = self.get_vars_in_def(action, ignore_update_expressions=True)
        # print(f"### Vars in action '{action}'", vars_in_action)
        # print(f"### Vars in action non-updated '{action}'", vars_in_action_non_updated)
        # print("### Vars COI for updated in action:", action_updated_vars)
        # for v in action_updated_vars:
        #     print(f"var: '{v}'", ", COI:", action_updated_vars[v])

        # # lemma = "H_RequestVoteQuorumInTermImpliesNoOtherLeadersInTerm"
        # # print("### Getting vars in def:", lemma)
        # vars_in_lemma, updated_vars = self.get_vars_in_def(lemma)
        # print(f"### Vars in lemma '{lemma}'", vars_in_lemma)

        #
        # Compute the COI reduction.
        #
        # print("--------- Cone of influence ---------")
        # Consider any variable that appears and is not updated to be a non-modified var.
        # TODO: We may need to consider explicitly marking unchanged variables i.e. those only read in precondition.
        # i.e. need to detect if a variable appears but only in the update expression of a variable.
        # vars_in_action_not_updated = vars_in_action - action_updated_vars.keys()
        lemma_vars_updated = vars_in_lemma.intersection(action_updated_vars.keys())
        # print("All action vars:", vars_in_action)
        # print("All non-updated action vars:", vars_in_action_non_updated)
        # print("All updated action vars:", set(action_updated_vars.keys()))
        # print("All lemma vars:", vars_in_lemma)
        # print("All updated lemma vars:", lemma_vars_updated)
        coi_vars = set()
        for v in lemma_vars_updated:
            # print(f"COI for updated lemma var '{v}':", action_updated_vars[v])
            coi_vars.update(action_updated_vars[v])
        # print("All COI vars for updated lemma vars:", coi_vars)

        # TODO: Does 'vars_in_lemma' actually need to be included here?
        projection_var_sets = [
            vars_in_action_non_updated, # vars appearing in precondition.
            vars_in_lemma, # vars appearing in lemma.
            coi_vars, # cone-of-influence of all modified vars that appear in lemma.
        ]
        projected_vars = set.union(*projection_var_sets)
        # print("Overall projected vars:", projected_vars)
        return projected_vars        

    def compute_backwards_coi_closure(self, lemma_action_coi, target_prop):

        vars_in_action = {}
        vars_in_action_non_updated = {}
        # vars_in_lemma_defs = {}
        action_updated_vars = {}
        actions = list(lemma_action_coi.keys())

        # Extract variables per action.
        for action in actions:
            try:
                vars_in_action[action],action_updated_vars[action] = self.get_vars_in_def(action)
                # print(action_updated_vars[action])
                vars_in_action_non_updated[action],_ = self.get_vars_in_def(action, ignore_update_expressions=True)
            # print(f"Vars in action '{action}':", vars_in_action[action])
            except:
                # Fall back to conservative computation if we fail above.
                vars_in_action[action] = set(self.get_all_vars())
                action_updated_vars[action] = {v:set(self.get_all_vars()) for v in self.get_all_vars()}
                vars_in_action_non_updated[action] = set(self.get_all_vars())


        """ Iteratively compute the partitioned COI (one for each action) until fixpoints are reached."""
        vars_in_lemma = self.get_vars_in_def(target_prop)[0]
        var_set_frontier = [vars_in_lemma]
        visited_var_sets = []
        edges = []
        actions = lemma_action_coi.keys()
        
        print("Target prop:", target_prop)
        while len(var_set_frontier) > 0:
            curr_var_set = var_set_frontier.pop()
            # Get var set in next target lemma.
            visited_var_sets.append(curr_var_set)

            print("current prop vars:", curr_var_set)
            for a in actions:
                # vars_in_lemma = lemma_action_coi[a][target_prop]
                action_coi = self.compute_coi(None, None, None, action_updated_vars[a], vars_in_action_non_updated[a], vars_in_lemma)
                print("- ", vars_in_lemma, a, action_coi)

                if action_coi not in visited_var_sets:
                    var_set_frontier.append(action_coi)
                    edges.append((curr_var_set, action_coi, a))

        # # Print in simple DOT format.
        # for e in edges:
        #     e0_str = "_".join(sorted(list(e[1])))
        #     e1_str = "_".join(sorted(list(e[0])))
        #     print(e0_str, "->", e1_str, f" [label=\"{e[2]}\"]")
        # print("   ")
        return edges


    def compute_coi_table(self, lemmas, actions):
        "Compute the set of cone-of-influence (COI) variables for an action lemma pair."

        vars_in_action = {}
        vars_in_action_non_updated = {}
        vars_in_lemma_defs = {}
        lemma_action_coi = {}
        action_updated_vars = {}

        # Extract variables per action.
        for action in actions:
            try:
                ret = self.get_vars_in_def(action)
                vars_in_action[action],action_updated_vars[action] = ret
                # print("vars in action:", action_updated_vars[action])
                vars_in_action_non_updated[action],_ = self.get_vars_in_def(action, ignore_update_expressions=True)
                # print(f"Vars in action '{action}':", vars_in_action[action])
            except Exception as e:
                # Fall back to conservative computation if we fail above.
                print("exception while extracting variables:", e)
                vars_in_action[action] = set(self.get_all_vars())
                action_updated_vars[action] = {v:set(self.get_all_vars()) for v in self.get_all_vars()}
                vars_in_action_non_updated[action] = set(self.get_all_vars())
        

        # Extract variables per lemma.
        # for udef in self.get_all_user_defs(level="1"):
        for udef in lemmas:
            # Getting all level 1 definitions should be sufficient here.
            # Invariants (i.e. state predicates) should all be at level 1.
            # if udef.startswith("H_"):
            vars_in_lemma_defs[udef] = self.get_vars_in_def(udef)[0]
            # print(udef, vars_in_lemma_defs[udef])

        # Compute COI for each action-lemma pair
        for action in vars_in_action:
            if action not in lemma_action_coi:
                lemma_action_coi[action] = {}
            for lemma in vars_in_lemma_defs:
                # vars_in_action, action_updated_vars, vars_in_action_non_updated, vars_in_lemma
                lemma_action_coi[action][lemma] = self.compute_coi(lemma, 
                                                                   action, 
                                                                   vars_in_action[action], 
                                                                   action_updated_vars[action], 
                                                                   vars_in_action_non_updated[action], 
                                                                   vars_in_lemma_defs[lemma])

        return lemma_action_coi



def parse_tla_file(workdir, specname):
    xml_out_file = f"{specname}.xml"
    tlc_binary = "tla2tools-checkall.jar"
    cmd = f"java -cp {tlc_binary} tla2sany.xml.XMLExporter -o {specname}.tla > {xml_out_file}"

    print("XML export command: " + cmd)
    subproc = subprocess.Popen(cmd, shell=True, stdout=subprocess.PIPE, cwd=workdir)
    subproc.wait()

    spec_text_lines = open(f"{workdir}/{specname}.tla").readlines()

    xml_ast = f'{workdir}/{xml_out_file}'
    tree = ET.parse(xml_ast)
    return TLASpec(tree, spec_text_lines)
    # return tree

if __name__ == "__main__":
    tla_file = "Hermes"
    my_spec = parse_tla_file("benchmarks", tla_file)

    top_level_defs = my_spec.get_all_user_defs(level="1")
    spec_obj = my_spec.get_spec_obj()
    print(f"Found {len(top_level_defs)} top level defs.")
    # for d in top_level_defs:
    #     print(" ", d)

    # action_node = [a for a in spec_obj["defs"].values() if a["uniquename"] == "RollbackEntriesAction"][0]
    # print(action_node, )

    # print("EXTRACT QUANT")
    # # my_spec.extract_quant_and_predicate_grammar("HandleRequestVoteRequestAction")
    # defname = "AcceptAppendEntriesRequestAppendAction"
    # print(f"Extracting from: {defname}")
    # # my_spec.extract_quant_and_predicate_grammar("TMRcvPreparedAction")
    # my_spec.extract_quant_and_predicate_grammar(defname)
    # # my_spec.extract_quant_and_predicate_grammar("Inv362_1_4_def")
    # # my_spec.extract_quant_and_predicate_grammar("RMPrepareAction")
    # exit()

    action = "HWrite"
    print("### Getting vars in action:", action)
    vars_in_action, action_updated_vars = my_spec.get_vars_in_def(action)
    vars_in_action_non_updated, _ = my_spec.get_vars_in_def(action, ignore_update_expressions=True)
    print(f"### Vars in action '{action}'", vars_in_action)
    print("----")
    print(f"### Vars in action non-updated '{action}'", vars_in_action_non_updated)
    print("----")
    # print("### Vars COI for updated in action:", action_updated_vars)
    print("### Vars COI for updated in action:")
    print("----")
    for v in action_updated_vars:
        print(f" - var: '{v}'", ", COI:", action_updated_vars[v])

    lemma = "T1"
    # print("### Getting vars in def:", lemma)
    vars_in_lemma, updated_vars = my_spec.get_vars_in_def(lemma)
    print(f"### Vars in lemma '{lemma}'", vars_in_lemma)

    lemma_action_coi = my_spec.compute_coi(None, None, None,action_updated_vars, vars_in_action_non_updated, vars_in_lemma)
    print("COI:", lemma_action_coi)

    exit()

    #
    # Compute the COI reduction.
    #
    print("--------- Cone of influence ---------")
    # Consider any variable that appears and is not updated to be a non-modified var.
    # TODO: We may need to consider explicitly marking unchanged variables i.e. those only read in precondition.
    # i.e. need to detect if a variable appears but only in the update expression of a variable.
    # vars_in_action_not_updated = vars_in_action - action_updated_vars.keys()
    lemma_vars_updated = vars_in_lemma.intersection(action_updated_vars.keys())
    print("All action vars:", vars_in_action)
    print("All non-updated action vars:", vars_in_action_non_updated)
    print("All updated action vars:", set(action_updated_vars.keys()))
    print("All lemma vars:", vars_in_lemma)
    print("All updated lemma vars:", lemma_vars_updated)
    coi_vars = set()
    for v in lemma_vars_updated:
        print(f"COI for updated lemma var '{v}':", action_updated_vars[v])
        coi_vars.update(action_updated_vars[v])
    print("All COI vars for updated lemma vars:", coi_vars)

    projection_var_sets = [
        vars_in_action_non_updated, # vars appearing in precondition.
        vars_in_lemma, # vars appearing in lemma.
        coi_vars, # cone-of-influence of all modified vars that appear in lemma.
    ]
    projected_vars = set.union(*projection_var_sets)
    print("Overall projected vars:", projected_vars)

    # coi = my_spec.compute_coi_table(["H_RequestVoteQuorumInTermImpliesNoOtherLeadersInTerm"], ["RequestVoteAction"])
    # print(f"Computed COI: {coi}")


    print("EXTRACT QUANT")
    # my_spec.extract_quant_and_predicate_grammar("HandleRequestVoteRequestAction")
    my_spec.extract_quant_and_predicate_grammar("AppendEntries")
    my_spec.extract_quant_and_predicate_grammar("H_NoLogDivergenceAppendEntries")

    all_vars = my_spec.get_all_vars()
    print(all_vars)