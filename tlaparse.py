#
# TLA+ parser using XMLExporter of SANY.
#

import xml.etree.ElementTree as ET
import subprocess
import copy

class TLASpec:
    """ Represents a parsed TLA+ spec file. """
    def __init__(self, xml_ast):
        self.ast = xml_ast

        # Extract XML AST into alternate structured representation
        # for convenience.
        self.spec_obj = self.extract_spec_obj(self.ast)

    def get_spec_obj(self):
        return self.spec_obj

    def extract_spec_obj(self, ast):
        """ Parse user definitions and variables, etc. from spec."""
        root = ast.getroot()

        entries = root.findall("context")[0].findall("./entry")
        builtins = {}
        constant_decls = {}
        variable_decls = {}
        defs_table = {}

        # Extract all top-level definitions.
        for entry in entries:
            curr_uid = None
            for elem in entry:
                # print(f.tag)
                if elem.tag == "UID":
                    curr_uid = elem.text

            for elem in entry:
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

    def get_vars_in_def_rec(self, elem, uids_to_ignore=set()):
        uid = None
        if elem.tag in ["OpDeclNodeRef", "BuiltInKindRef"]:
            children = list(elem)
            assert children[0].tag == "UID"
            uid = children[0].text

        if uid in uids_to_ignore:
            return set()

        # if elem.tag == "BuiltInKindRef":
        #     name = self.spec_obj["builtins"][uid]["uniquename"]
        #     # print(name)
        #     # Ignore UNCHANGED in terms of variable occurrence counting.
        #     if name == "UNCHANGED":
        #         return set()

        if elem.tag == "OpDeclNodeRef":
            # CONSTANT references are not variables.
            if uid in self.spec_obj["constant_decls"]:
                return set()
            
            var_name = self.spec_obj["var_decls"][uid]["uniquename"]
            return set([var_name])
        
        body = None
        for child in elem:
            # print(child.tag)
            if child.tag == "body":
                body = child

        if body is None:
            return []
        
        all_vars = set()

        # unchanged = []
        # for sub_elem in body.iter():
        #     if elem.tag == "BuiltInKindRef":
        #         children = list(elem)
        #         assert children[0].tag == "UID"
        #         uid = children[0].text
        #         name = self.spec_obj["builtins"][uid]["uniquename"]
        #         # print(name)
        #         # Ignore UNCHANGED in terms of variable occurrence counting.
        #         if name == "UNCHANGED" and ignore_unchanged:
        #             return set()
        
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
                new_vars = self.get_vars_in_def_rec(def_elem, uids_to_ignore)
                all_vars.update(new_vars)
            else:
                new_vars = self.get_vars_in_def_rec(sub_elem, uids_to_ignore)
                all_vars.update(new_vars)
        return all_vars

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

    def get_vars_in_def(self, name, ignore_unchanged=True):
        """ Get the set of variables that appear in a given definition body. """ 
        node = self.get_def_node_by_uniquename(name)
        node_uid = node["uid"]

        # root = copy.deepcopy(self.ast.getroot())
        # entries = root.findall("context")[0].findall("./entry")
        print(node_uid)
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

        all_vars = self.get_vars_in_def_rec(elem, uids_to_ignore=[])
        print(all_vars)

        # print(entries)
        # spec_obj = self.extract_spec_obj(spec_ast)
        return self.spec_obj["defs"]
        # pass

    def get_all_user_defs(self, level=None):
        """ Get all user defined ops at an optionally specified level."""
        # spec_obj = self.extract_spec_obj(spec_ast)
        if level is None:
            return [v["uniquename"] for v in self.spec_obj["defs"].values()]
        else:
            return [v["uniquename"] for v in self.spec_obj["defs"].values() if v["level"]==level] 

    def get_def_node_by_uniquename(self, uniquename):
        objs = [a for a in spec_obj["defs"].values() if a["uniquename"] == uniquename]
        if len(objs) == 0:
            return None
        return objs[0]

def parse_tla_file(workdir, specname):
    xml_out_file = f"{specname}.xml"
    tlc_binary = "tla2tools-checkall.jar"
    cmd = f"java -cp {tlc_binary} tla2sany.xml.XMLExporter {specname}.tla > {xml_out_file}"

    print("XML export command: " + cmd)
    subproc = subprocess.Popen(cmd, shell=True, stdout=subprocess.PIPE, cwd=workdir)
    subproc.wait()

    xml_ast = f'{workdir}/{xml_out_file}'
    tree = ET.parse(xml_ast)
    return TLASpec(tree)
    # return tree

if __name__ == "__main__":
    tla_file = "AbstractStaticRaft"
    my_spec = parse_tla_file("benchmarks", tla_file)

    top_level_defs = my_spec.get_all_user_defs(level="1")
    spec_obj = my_spec.get_spec_obj()
    print(f"Found {len(top_level_defs)} top level defs.")
    for d in top_level_defs:
        print(" ", d)

    # action_node = [a for a in spec_obj["defs"].values() if a["uniquename"] == "RollbackEntriesAction"][0]
    # print(action_node, )
    my_spec.get_vars_in_def("H_OnePrimaryPerTerm")