#!/bin/bash
#SBATCH -J consensus_epr_endive_Job               # Job name
#SBATCH --partition short    # Partition name
#SBATCH --time=12:00:00       # Time limit.
#SBATCH --constraint="[broadwell|cascadelake]"       # Newer processors.
#SBATCH -N 1                   # Number of nodes
#SBATCH -n 1                   # Number of tasks
#SBATCH --cpus-per-task 32                  # Number of cores
#SBATCH -o endive_logs/consensus_epr/consensus_epr_output_%j.txt       # Standard output file
#SBATCH -e endive_logs/consensus_epr/consensus_epr_error_%j.txt        # Standard error file

specname="consensus_epr"
lscpu # log CPU info.
module load OpenJDK/19.0.1
mkdir -p benchmarking
cd benchmarking
mkdir -p $specname
cd $specname
# Clone if not already cloned.
git clone -b ind-tree https://github.com/will62794/endive.git
cd endive
git pull --rebase

for seed in 1 2 3
do
echo "---"
echo "--- Running '$specname' benchmark with seed $seed ---"
echo "---"
srun python3 endive.py --spec benchmarks/$specname \
    --seed $seed --num_simulate_traces 200000 --tlc_workers 24 \
    --debug --target_sample_time_limit_ms 10000 --target_sample_states 200000 \
    --opt_quant_minimize --k_cti_induction_depth 1 --override_num_cti_workers 10 \
    --ninvs 40000 --max_num_ctis_per_round 5000 \
    --save_dot --max_num_conjuncts_per_round 16 --niters 4 \
    --auto_lemma_action_decomposition --enable_partitioned_state_caching --proof_tree_mode \
    --nrounds 45
done