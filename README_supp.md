## Supplementary Material for PLDI 2024 submission: "Interactive Safety Verification of Distributed Protocols by Inductive Proof Decomposition"

This directory contains the code for our interactive verification tool, *Indigo*, which implements our inductive proof decomposition technique for interactive development of inductive invariants. This repository also constains the specifications of the protocols we tested along with their completed inductive proof graphs. 

## Setup

In order to run the tool you will need the following prerequisites:

- Java version >= 11
- Python 3 with pip installed
- Install Python dependencies with `python3 -m pip install -r requirements.txt`

This repository also contains binaries for both the TLC and Apalache model checker, so you will not need to install these separately. 

## Viewing the Proof Graphs

You can load the proof graph for each protocol from our benchmark set by running the following commands from the root directory of this repository.

```
python3 indigo.py --spec benchmarks/<SPECNAME> --seed 42 --num_simulate_traces 30000 --tlc_workers 4 --proof_tree_mode --interactive --max_proof_node_ctis 20 --override_num_cti_workers 3  --proof_tree_cmd reload_proof_struct --debug --target_sample_time_limit_ms 25000 --target_sample_states 20000 --k_cti_induction_depth 1
```
where `<SPECNAME>` is the name of a protocol benchmark and its corresponding proof graph to load. You can load the following specs, which correspond to those from Table of our paper:

- `SimpleConsensus`
- `TwoPhase`
- `AbstractRaft`
- `AsyncRaft`
- `Zab`

After running the above command for a chosen protocol, you can view and interact with its proof graph by opening a local browser window at `http://127.0.0.1:5000`. You will be presented with a graphical user interface for viewing the proof graph,
checking proof obligations for each node, and viewing local CTIs for invalid nodes. Note that the interactive tool uses TLC for generating CTIs, so there may be some nondeterminism in generated CTIs for some protocols. For complete proof checking with the Apalache symbolic model checker, you can use the instructions in the following section.

## Checking the Proof Graphs

For each protocol and proof graph, you can independently check that all nodes of its proof graph are locally valid. For this we use the [Apalache symbolic model checker](https://github.com/informalsystems/apalache), which is able to produce complete proofs of inductive invariants for bounded protocol parameters.

To check the proof for a protocol, you can run the following command:
```
python3 indigo.py --spec benchmarks/<SPECNAME> --proof_tree_mode --interactive --proof_tree_cmd check_proof_apalache
```
where `<SPECNAME>` is the name of the protocol benchmark. This should run Apalache on all inductive proof obligations for a given proof graph in parallel. Upon successful completion you should see a message reported like

```
No errors found in proof checking! (120 obligations checked, for 8 lemmas).
```
In our tests, running on a 2020 M1 Macbook Air, approximate proof checking times for each protocol was as follows:

- `SimpleConsensus`: 73 secs.
- `TwoPhase`: 184 secs.
- `AbstractRaft`: 969 secs. (16 minutes)
- `AsyncRaft`: 6592 secs. (~2 hours)
- `Zab`: (TODO)

