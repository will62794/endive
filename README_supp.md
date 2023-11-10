## Supplementary Material for submission: "Interactive Safety Verification of Distributed Protocols by Inductive Proof Decomposition"

This directory contains the code for our interactive verification tool, Indigo, which impelmntats our inductive proof decompositiont echnique for interactive development of inductive invariants. It also contains the completed inductive proofg raphs for protocols presented in our evaluation. 

## Setup
In order to run the tool you will need the following prerequisites:

- Java version >= 11
- Python 3 with pip installed
- Install Python dependencies with `python3 -m pip install -r requirements.txt`

This paackage contains binaries for both the TLC and Apalache model checker, so you will not need to install these. 

## Running the tool and loading our proofs

Running the tool to load a proof graph can be done as follows:

```
$ python3 indigo.py --spec benchmarks/<SPECNAME> --seed 42 --num_simulate_traces 30000 --tlc_workers 7 --proof_tree_mode --interactive --max_proof_node_ctis 20 --override_num_cti_workers 5 --apalache_smt_timeout_secs 125  --proof_tree_cmd reload_proof_struct --debug --target_sample_time_limit_ms 28000 --target_sample_states 20000 --proof_struct_tag no_truncate --k_cti_induction_depth 1
```
where `<SPECNAME>` is the name of a protocol benchmark and proof to load. You can load the following specs, which correspond to those from Table of our paper:
- AsyncRaft
- TwoPhase
- Zab
- SimpleConsensus
- AbstractRaft

To check all inductive proof obligations of a proof graph, you can run the following command:
```
$ python3 indigo.py --spec benchmarks/<SPECNAME> --proof_tree_mode --interactive  --apalache_smt_timeout_secs 125 --proof_tree_cmd check_proof_apalache --proof_struct_tag no_truncate
```
