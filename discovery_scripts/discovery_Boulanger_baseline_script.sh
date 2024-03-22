#!/bin/bash
#SBATCH -J Boulanger_baseline_endive_Job               # Job name
#SBATCH --partition short    # Partition name
#SBATCH --time=12:00:00       # Time limit.
#SBATCH --constraint=cascadelake       # Newer processors.
#SBATCH -N 1                   # Number of nodes
#SBATCH -n 1                   # Number of tasks
#SBATCH --cpus-per-task 36                  # Number of cores
#SBATCH -o endive_logs/Boulanger_baseline/Boulanger_baseline_output_%j.txt       # Standard output file
#SBATCH -e endive_logs/Boulanger_baseline/Boulanger_baseline_error_%j.txt        # Standard error file

# Running without any slicing optimizations i.e.
# essentially using the implementation of endive in FMCAD22.
specname="Boulanger"
rootdir="${specname}_baseline"
module load OpenJDK/19.0.1
mkdir -p benchmarking
cd benchmarking
mkdir -p $rootdir
cd $rootdir
# Clone if not already cloned.
git clone -b ind-tree https://github.com/will62794/endive.git
cd endive
git pull --rebase
srun python3 endive.py --spec benchmarks/$specname \
    --seed 2444 --num_simulate_traces 100000 --tlc_workers 32 \
    --debug --target_sample_time_limit_ms 10000 --target_sample_states 20000 \
    --opt_quant_minimize --k_cti_induction_depth 1 --override_num_cti_workers 4 \
    --ninvs 40000 \
    --save_dot --max_num_conjuncts_per_round 20 --niters 4 \
    --nrounds 45