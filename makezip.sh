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
cp README_supp.md $target_dir/README.md
# Rename some stuff.
mv $target_dir/endive.py $target_dir/indigo.py

#
# Copy benchmarks.
#

cp benchmarks/proof.js ${target_dir}/benchmarks
cp benchmarks/proof.css ${target_dir}/benchmarks

# SimpleConsensus.
cp benchmarks/SimpleConsensus.tla ${target_dir}/benchmarks
cp benchmarks/SimpleConsensus_TLC.tla ${target_dir}/benchmarks
cp benchmarks/SimpleConsensus.config.json ${target_dir}/benchmarks
# cp benchmarks/SimpleConsensus_ApaIndProofCheck.tla ${target_dir}/benchmarks

# SimpleConsensus.
cp benchmarks/AbstractRaft.tla ${target_dir}/benchmarks/
cp benchmarks/AbstractRaft_TLC.tla ${target_dir}/benchmarks/
cp benchmarks/AbstractRaft.config.json ${target_dir}/benchmarks/
# cp benchmarks/AbstractStaticRaft_ApaIndProofCheck.tla ${target_dir}/benchmarks

# TwoPhase.
cp benchmarks/TwoPhase.tla ${target_dir}/benchmarks
cp benchmarks/TwoPhase.config.json ${target_dir}/benchmarks
# cp benchmarks/TwoPhase_ApaIndProofCheck.tla ${target_dir}/benchmarks

# AsyncRaft.
cp benchmarks/AsyncRaft.tla ${target_dir}/benchmarks
cp benchmarks/AsyncRaft.config.json ${target_dir}/benchmarks
cp benchmarks/AsyncRaft_TLC.tla ${target_dir}/benchmarks
cp benchmarks/Apalache.tla ${target_dir}/benchmarks
# cp benchmarks/AsyncRaft_ApasIndProofCheck.tla ${target_dir}/benchmarks

# Zab.
cp benchmarks/Zab.tla ${target_dir}/benchmarks
cp benchmarks/Zab.config.json ${target_dir}/benchmarks
cp benchmarks/Zab_TLC.tla ${target_dir}/benchmarks
# cp benchmarks/AsyncRaft_ApaIndProofCheck.tla ${target_dir}/benchmarks

# Copy TLC and Apalache binaries.
cp -r benchmarks/apalache $target_dir/benchmarks
cp benchmarks/tla2tools-checkall.jar $target_dir/benchmarks


# TODO: README?