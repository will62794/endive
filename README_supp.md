## Supplementary Material for submission: "Scalable, Interpretable Distributed Protocol Verification by Inductive Proof Slicing"

This directory contains the code for our verification tool, *scimitar*, which implements our inductive proof slicing technique for synthesis of inductive invariants via inductive proof graphs. This repository constains the specifications of the protocols we tested along with their setup configurations.

## Setup

In order to run the tool you will need the following prerequisites:

- Java version >= 11
- Python 3 with pip installed
- Install Python dependencies with `python3 -m pip install -r requirements.txt`

This repository also contains binaries for the TLC model checker, so you will not need to install these separately. 

## Running the Benchmarks

As an example can run the `TwoPhase` benchmark from our paper by running the following command from the root directory of this repository:

```
python3 scimitar.py --spec benchmarks/TwoPhase --seed 2 --num_simulate_traces 100000 --tlc_workers 4 --debug --target_sample_time_limit_ms 20000 --target_sample_states 100000  --opt_quant_minimize --k_cti_induction_depth 1 --ninvs 30000 --max_num_ctis_per_round 5000 --save_dot --niters 4 --max_num_conjuncts_per_round 20 --override_num_cti_workers 4 --nrounds 45  --proof_tree_mode --auto_lemma_action_decomposition --enable_partitioned_state_caching
```

You should see the tool running and you can also inspect the `benchmarks/TwoPhase_ind-proof-tree-sd2.pdf` file as it runs to see the proof graph being constructed dynamically. When it completes, it should have produced a complete proof graph for the safety proeprty of the TwoPhase specification.

To run all benchmarks from the paper, you can execute the script `run_bms.sh`, which runs all benchmarks in sequence. This will require at least around 24 hours of computation time, which we tested on a 56 core Xeon machine. When a benchmark completes, you can inspect the proof graph for each protocol in the `benchmarks/<specname>_ind-proof-tree-*.pdf` files.