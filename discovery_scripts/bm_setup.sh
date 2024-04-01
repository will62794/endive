#!/bin/bash
specname_arg=$1

lscpu # log CPU info.
module load OpenJDK/19.0.1

# Create work directory.
bmdir="/scratch/schultz.w/benchmarking/$specname_arg"
mkdir -p $bmdir
cd $bmdir

# Clone if not already cloned.
git clone --depth 1 -b ind-tree https://github.com/will62794/endive.git
cd endive
git pull --rebase

# Clean up old files.
rm -rf benchmarks/statecache
rm -rf benchmarks/states

#
# Common parameters for benchmarking runs.
#

tlc_workers=24
num_cti_workers=4
cti_elimination_workers=8

nrounds=45
ninvs=40000
max_num_ctis_per_round=5000
target_sample_states=200000
num_simulate_traces=200000