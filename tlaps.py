#
# Helper library for checkin proof obligations with the TLA+ proof manager (TLAPM)
#
# The general output format is described here:
# https://github.com/tlaplus/tlaplus/blob/d977051118f63b9c97d7d4c4d6af27183971ada3/general/docs/tlapm-toolbox-interface.txt
#

import sys
import subprocess
import time
import argparse
import json

# Terminal print colors.
HEADER = '\033[95m'
OKBLUE = '\033[94m'
OKCYAN = '\033[96m'
OKGREEN = '\033[92m'
WARNING = '\033[93m'
FAIL = '\033[91m'
ENDC = '\033[0m'
BOLD = '\033[1m'
UNDERLINE = '\033[4m'

def parse_block_line_elems(elems, curr_block):
    key = elems[0]
    if key in ["status","type","id","prover","already","meth"]:
        curr_block[key] = elems[1]
    if key == "reason":
        curr_block[key] = ":".join(elems[1:])
    if key == "loc":
        curr_block[key] = {
            "startPos": (elems[1], elems[2]),
            "endPos": (elems[3], elems[4])
        }
    else:
        return

# Parse line of toolbox output like:
#
# @!!type:obligation
#
def parse_toolbox_block_line(line):
    assert line.startswith("@!!")
    parts = line[3:].split(":")
    # print(parts)
    key = parts[0]
    return parts

# Parse output of tlapm running in --toolbox mode.
# e.g.
#
# @!!BEGIN
# @!!type:obligation
# @!!id:1
# @!!loc:66:5:66:7
# @!!status:to be proved
# @!!END
#
def parse_tlapm_toolbox_log(lines):
    # Remove empty lines
    lines = filter(lambda l : len(l) > 0, lines)

    # Parser state machine.
    in_block = False
    all_blocks = []
    curr_block = {}
    for line in lines:
        # Skip non toolbox output.
        if not line.startswith("@!!"):
            continue
        elems = parse_toolbox_block_line(line)
        # print(elems)
        if not in_block and elems[0] == "BEGIN":
            in_block = True
            continue
        if elems[0] == "END":
            assert in_block
            all_blocks.append(curr_block)
            curr_block = {}
            in_block = False
            continue
        if in_block:
            # key = elems[0]
            parse_block_line_elems(elems, curr_block)
    
    # for block in all_blocks:
        # print(block)
    # print("BLOCKS:", len(all_blocks))
    return all_blocks

#
# Construct HTML report of proof obligation results from tlapm.
#
def html_proof_report_lines(obligation_stats, tla_file):
    html_lines = []
    tla_lines = open(tla_file).read().splitlines()

    def make_html_line(line):
        return f"<span>{line}</span><br>"

    html_lines.append("</html>")
    tla_spec_lines = [make_html_line(line) for line in tla_lines]

    # Append proof status info to each line.
    for blockid,obl in obligation_stats.items():
        if obl["type"] == "obligation":
            lineNo = int(obl["loc"]["startPos"][0])
            lineInd = lineNo - 1 # offset for 0-indexing into array
            hex_lightred = "#FFCCCB"
            annotateColor = "lightgreen" if obl["status"] in ["proved","trivial"] else hex_lightred
            annotatedLine = tla_spec_lines[lineInd].replace("<span", f"<span style='background-color:{annotateColor}'")
            tla_spec_lines[lineInd] = annotatedLine

    html_lines.append("<pre><code>")
    html_lines += tla_spec_lines
    html_lines.append("</code></pre>")
    html_lines.append("</html>")
    return html_lines

def tlapm_check_proof(tla_file, nthreads=1, stretch=1, tlapm_install_dir="/usr/local", smt_timeout=1):
    proofchecking_stats = {}
    nfail = 0

    checkproof_start = time.time()
    print(f"Checking proof in '{tla_file}' with tlapm")
    search_path = f"{tlapm_install_dir}/lib/tlaps/"
    solver_flag = f"""--method smt --solver '{search_path}bin/z3 -T:{smt_timeout} -smt2 "$file"'"""
    # solver_flag = ""
    cmd = f"{tlapm_install_dir}/bin/tlapm {solver_flag} --threads {nthreads} -I {search_path} --stretch {stretch} --toolbox 0 0 -I benchmarks --cleanfp --nofp {tla_file}"
    print("tlapm cmd:", cmd)
    sys.stdout.flush()
    proc = subprocess.Popen(cmd, shell=True, stderr=subprocess.PIPE, stdout=subprocess.PIPE)
    tlapm_toolbox_output = proc.stderr.read().decode(sys.stderr.encoding)
    checkproof_end = time.time()
    checkproof_time = round(checkproof_end - checkproof_start, 2)
    print("tlapm checked proof in " + str(checkproof_time) + "s")

    # Parse the output of tlapm.
    lines = tlapm_toolbox_output.splitlines()
    tlapm_obligation_blocks = parse_tlapm_toolbox_log(lines)

    # Reconstruct current proof state for each obligation.
    obligation_states = {}
    for block in tlapm_obligation_blocks:
        if block["type"] == "obligation":
            bid = block["id"]
            obligation_states[bid] = block
            # print("obl stat", obligation_states[bid])

    if len(obligation_states)==0:
        print("No proof obligations found, which likely indicates an error. Terminating now.")
        exit(0)

    html_report_file = f"{tla_file}.proofs.html"
    html_lines = html_proof_report_lines(obligation_states, tla_file)
    f = open(html_report_file, 'w')
    f.writelines(html_lines)

    # Print summary of results.
    num_total_obligations = len(obligation_states)
    num_proved_obligations = len([bid for bid in obligation_states if obligation_states[bid]["status"] in ["proved", "trivial"]])
    unproven = num_total_obligations - num_proved_obligations

    print(f"Parsed proof results for '{tla_file}'")
    print(f"Saved HTML proof report to '{html_report_file}'.")
    print(f"Proof obligation results: {num_proved_obligations}/{num_total_obligations} obligations proved.")
    if unproven == 0:
        print(f"{OKGREEN}Success{ENDC}: all obligations proven!" + ENDC)
    else:
        print(f"{FAIL}Fail{ENDC}: {unproven} obligations not proven.")
        nfail += 1
        # exit(1)

    for bid in obligation_states:
        if obligation_states[bid]["status"] not in ["trivial"]:
            print(bid, obligation_states[bid])

    proofchecking_stats = {
        "num_total_obligations": num_total_obligations,
        "num_proved_obligations": num_proved_obligations,
        "num_unproved_obligations": unproven,
        "proof_check_time_secs": checkproof_time,
        "obligation_states": obligation_states
    }

    return proofchecking_stats

if __name__ == "__main__":
    # Parse command line arguments.
    test_file = "benchmarks/TwoPhase_IndProofs.tla"
    stats = tlapm_check_proof(test_file)
    print(stats)



# parser = argparse.ArgumentParser(description='')
# parser.add_argument('--tla_file', help='TLA+ benchmark file containing proofs to check.', default=None, required=False, type=str)
# parser.add_argument('--report', help='Report containing proof checking stats.', default=None, required=False, type=str)
# args = vars(parser.parse_args())

# # Check all proofs by default.
# import benchmark
# benchmarks_to_check = benchmark.benchmark_specs
# # benchmarks_to_check = filter(lambda b : b[0] != "mongo-logless-reconfig", benchmarks_to_check) # ignore for now.
# proofs_to_check = [f"benchmarks/{bm[1]}_IndProofs.tla" for bm in benchmarks_to_check if bm[1] is not None]

# if args["tla_file"] != None:
#     proofs_to_check = [args["tla_file"]]

# # print(proofs_to_check)
# print(f"Checking proofs from {len(proofs_to_check)} files")

# nfail = 0
# proofchecking_stats = {}
# for ind,tla_file in enumerate(proofs_to_check):
#     # Check the proof with tlapm.


#     checkproof_start = time.time()
#     print(f"Checking proof in '{tla_file}' with tlapm ({ind+1}/{len(proofs_to_check)})")
#     tlapm_toolbox_output = tlapm_check_proof(tla_file)
#     checkproof_end = time.time()
#     checkproof_time = round(checkproof_end - checkproof_start, 2)
#     print("tlapm checked proof in " + str(checkproof_time) + "s")
#     lines = tlapm_toolbox_output.splitlines()
#     tlapm_obligation_blocks = parse_tlapm_toolbox_log(lines)

#     # Reconstruct current proof state for each obligation.
#     obligation_states = {}
#     for block in tlapm_obligation_blocks:
#         if block["type"] == "obligation":
#             bid = block["id"]
#             obligation_states[bid] = block
#             # print("obl stat", obligation_states[bid])

#     if len(obligation_states)==0:
#         print("No proof obligations found, which likely indicates an error. Terminating now.")
#         exit(0)

#     html_report_file = f"{tla_file}.proofs.html"
#     html_lines = html_proof_report_lines(obligation_states, tla_file)
#     f = open(html_report_file, 'w')
#     f.writelines(html_lines)

#     # Print summary of results.
#     num_total_obligations = len(obligation_states)
#     num_proved_obligations = len([bid for bid in obligation_states if obligation_states[bid]["status"] in ["proved", "trivial"]])
#     unproven = num_total_obligations - num_proved_obligations

#     print(f"Parsed proof results for '{tla_file}'")
#     print(f"Saved HTML proof report to '{html_report_file}'.")
#     print(f"Proof obligation results: {num_proved_obligations}/{num_total_obligations} obligations proved.")
#     if unproven == 0:
#         print(f"{OKGREEN}Success{ENDC}: all obligations proven!" + ENDC)
#     else:
#         print(f"{FAIL}Fail{ENDC}: {unproven} obligations not proven.")
#         nfail += 1
#         # exit(1)

#     proofchecking_stats[tla_file] = {
#         "num_total_obligations": num_total_obligations,
#         "num_proved_obligations": num_proved_obligations,
#         "num_unproved_obligations": unproven,
#         "proof_check_time_secs": checkproof_time
#     }
#     print("")

# if nfail == 0:
#     print("Checked all proofs successfully!")
# else:
#     print(f"ERROR: {nfail} proofs failed to check successfully.")

# # Write stats if specified.
# if args["report"] != None:
#     f = open(args["report"], 'w')
#     json.dump(proofchecking_stats, f)
#     f.close()

