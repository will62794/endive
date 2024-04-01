#!/bin/bash
specname=$1

lscpu # log CPU info.
module load OpenJDK/19.0.1

# Create work directory.
bmdir="/scratch/schultz.w/benchmarking/$specname"
mkdir -p $bmdir
cd $bmdir

# Clone if not already cloned.
git clone --depth 1 -b ind-tree https://github.com/will62794/endive.git
cd endive
git pull --rebase

# Clean up old files.
rm -rf benchmarks/statecache
rm -rf benchmarks/states