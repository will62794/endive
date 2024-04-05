#!/bin/sh

#
# Parameters for benchmarking runs.
#

# Consider adjusting these parameters to suit the resource limits of the target machine.
tlc_workers=24
num_cti_workers=16
cti_elimination_workers=8

nrounds=45
ninvs=80000
max_num_ctis_per_round=10000
target_sample_states=200000
num_simulate_traces=200000

common_flags=" --tlc_workers $tlc_workers --override_num_cti_workers $num_cti_workers --cti_elimination_workers=$cti_elimination_workers"
common_flags+=" --debug --target_sample_time_limit_ms 10000 --num_simulate_traces $num_simulate_traces --target_sample_states $target_sample_states"
common_flags+=" --opt_quant_minimize --k_cti_induction_depth 1"
common_flags+=" --ninvs $ninvs --max_num_ctis_per_round $max_num_ctis_per_round"
common_flags+=" --save_dot --max_num_conjuncts_per_round 16 --niters 4 --nrounds $nrounds"
common_flags+="--proof_tree_mode --auto_lemma_action_decomposition --enable_partitioned_state_caching"


seed=1

python3 scimitar.py --spec benchmarks/TwoPhase $common_flags --seed $seed
python3 scimitar.py --spec benchmarks/SimpleConsensus $common_flags --seed $seed
python3 scimitar.py --spec benchmarks/ZeusReliableCommit $common_flags --seed $seed
python3 scimitar.py --spec benchmarks/Hermes $common_flags --seed $seed
python3 scimitar.py --spec benchmarks/Bakery $common_flags --seed $seed
python3 scimitar.py --spec benchmarks/Boulanger $common_flags --seed $seed

# AsyncRaft, ElectionSafety.
python3 scimitar.py --spec benchmarks/AsyncRaft $common_flags --seed $seed --safety H_OnePrimaryPerTerm

# AsyncRaft, PrimaryHasEntriesItCreated.
python3 scimitar.py --spec benchmarks/AsyncRaft $common_flags --seed $seed --safety H_PrimaryHasEntriesItCreated
