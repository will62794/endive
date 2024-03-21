#!/bin/bash
#SBATCH -J Boulanger_endive_Job               # Job name
#SBATCH --partition short    # Partition name
#SBATCH --time=12:00:00       # Time limit.
#SBATCH -N 1                   # Number of nodes
#SBATCH -n 1                   # Number of tasks
#SBATCH --cpus-per-task 36                  # Number of cores
#SBATCH -o endive_logs/Boulanger/Boulanger_output_%j.txt       # Standard output file
#SBATCH -e endive_logs/Boulanger/Boulanger_error_%j.txt        # Standard error file

module load OpenJDK/19.0.1
cd endive
git pull --rebase
srun python3 endive.py --spec benchmarks/Boulanger \
    --seed 2444 --num_simulate_traces 120000 --tlc_workers 32 \
    --debug --target_sample_time_limit_ms 10000 --target_sample_states 10000 \
    --opt_quant_minimize --k_cti_induction_depth 1 --override_num_cti_workers 12 \
    --ninvs 40000 --max_num_ctis_per_round 1000 \
    --auto_lemma_action_decomposition --save_dot --max_num_conjuncts_per_round 8 --niters 4 \
    --enable_partitioned_state_caching --proof_tree_mode \
    --nrounds 45


# --action_filter "HRcvValAction,HSendValsAction,HWriteAction,HRcvInvAction,HCoordWriteReplayAction,NodeFailureAction,HFollowerWriteReplayAction,HReadAction,HRcvAckAction"
# --action_filter "HRcvValAction,HSendValsAction,HWriteAction,HRcvInvAction,HCoordWriteReplayAction,NodeFailureAction,HFollowerWriteReplayAction,HReadAction"


# HRcvValAction,HSendValsAction,HWriteAction,HRcvInvAction,HRcvAckAction,HRcvInvNewerAction,HCoordWriteReplayAction,NodeFailureAction,HFollowerWriteReplayAction,HReadAction