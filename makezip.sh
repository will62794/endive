#
# Zip up code and specs into supplementary material zip.
#
#!/bin/sh

base_dir="/Users/willyschultz/Dropbox/PhD/Research/artifacts"
target_dirname="pldi24_supp"
target_dir="$base_dir/$target_dirname"

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

# AsyncRaft. (anonymize it.)
sed -E "s/Will Schultz/X/g" benchmarks/AsyncRaft.tla | sed -E "s/Will S/X/g" > ${target_dir}/benchmarks/AsyncRaft.tla
# cp benchmarks/AsyncRaft.tla ${target_dir}/benchmarks
cp benchmarks/AsyncRaft.config.json ${target_dir}/benchmarks
cp benchmarks/AsyncRaft_TLC.tla ${target_dir}/benchmarks
cp benchmarks/Apalache.tla ${target_dir}/benchmarks
# cp benchmarks/AsyncRaft_ApasIndProofCheck.tla ${target_dir}/benchmarks

# Zab. (anonymize it.)
# sed -E "s/Will Schultz/X/g" benchmarks/Zab.tla
sed -E "s/Will Schultz/X/g" benchmarks/Zab.tla | sed -E "s/Will S/X/g" > ${target_dir}/benchmarks/Zab.tla
# cp benchmarks/Zab.tla ${target_dir}/benchmarks
cp benchmarks/Zab.config.json ${target_dir}/benchmarks
cp benchmarks/Zab_TLC.tla ${target_dir}/benchmarks
# cp benchmarks/AsyncRaft_ApaIndProofCheck.tla ${target_dir}/benchmarks

# Copy TLC and Apalache binaries.
cp -r benchmarks/apalache $target_dir/benchmarks
cp benchmarks/tla2tools-checkall.jar $target_dir/benchmarks

# Zip it up.
cd $base_dir
zip -r pldi24_supp.zip $target_dirname