#
# TLA+ parser using XMLExporter of SANY.
#

import xml.etree.ElementTree as ET
import subprocess

def parse_tla_file(workdir, specname):
    xml_out_file = f"{specname}.xml"
    tlc_binary = "tla2tools-checkall.jar"
    cmd = f"java -cp {tlc_binary} tla2sany.xml.XMLExporter {specname}.tla > {xml_out_file}"

    print("XML export command: " + cmd)
    subproc = subprocess.Popen(cmd, shell=True, stdout=subprocess.PIPE, cwd=workdir)
    subproc.wait()

    xml_ast = f'{workdir}/{xml_out_file}'
    tree = ET.parse(xml_ast)
    return tree

def get_all_user_defs(tla_ast_tree):
    root = tla_ast_tree.getroot()
    userDefinedOps = root.findall("context")[0].findall("./entry/UserDefinedOpKind")
    # print(userDefinedOps)
    top_level_defs = []
    for op in userDefinedOps:
        # print(op)
        level = None
        uniquename = None
        for c in op:
            # print(f"   '{c.tag}'", c.text)

            # if c.uniquename:
            #     print(c.uniquename)
            if c.tag == "uniquename":
                # print(c.tag)
                uniquename = c.text
            if c.tag == "level":
                level = int(c.text)
        
        if level == 1:
            top_level_defs.append(uniquename)

    # print(f"Found {len(userDefinedOps)} total user defined ops.")
    return top_level_defs

if __name__ == "__main__":
    tla_file = "AbstractStaticRaft.tla"
    tla_tree = parse_tla_file(tla_file)

    top_level_defs = get_all_user_defs(tla_tree)
    print(f"Found {len(top_level_defs)} top level defs.")
    for d in top_level_defs:
        print(" ", d)