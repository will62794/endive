#
# Zip up code and specs into supplementary material zip.
#
#!/bin/sh

target_dir="/Users/willyschultz/Dropbox/PhD/Research/inductive-invariant-inference/pldi24_supp_test"

# Clean
rm -rf $target_dir

mkdir -p $target_dir
mkdir -p $target_dir/benchmarks

# Copy all Python code files.
cp *.py $target_dir

#
# Copy benchmarks.
#

# AsyncRaft.
cp benchmarks/AsyncRaft.tla ${target_dir}/benchmarks
cp benchmarks/AsyncRaft_TLC.tla ${target_dir}/benchmarks
cp benchmarks/AsyncRaft_ApaIndProofCheck.tla ${target_dir}/benchmarks

# TwoPhase.
cp benchmarks/TwoPhase.tla ${target_dir}/benchmarks
cp benchmarks/TwoPhase_ApaIndProofCheck.tla ${target_dir}/benchmarks

# Copy TLC and Apalache binaries.
# cp -r benchmarks/apalache benchmarks/$target_dir
# cp -r benchmarks/tla2tools-checkall.jar benchmarks/$target_dir


# TODO: README?