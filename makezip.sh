#
# Zip up code and specs into supplementary material zip.
#
# ./makezip <target_dirname>
#
#!/bin/sh

base_dir="/Users/willyschultz/Dropbox/PhD/Research/artifacts"
target_dirname="$1"
target_dir="$base_dir/$target_dirname"

# Clean
rm -rf $target_dir

mkdir -p $target_dir
mkdir -p $target_dir/benchmarks

# Copy all Python code files.
cp requirements.txt $target_dir
cp *.py $target_dir
rm $target_dir/benchmark.py # unused
rm $target_dir/checkproofs.py # unused
rm $target_dir/proof_*.py # unused
cp README_supp.md $target_dir/README.md
cp run_bms.sh $target_dir
# Rename some stuff.
mv $target_dir/endive.py $target_dir/scimitar.py

#
# Copy benchmarks.
#

# cp benchmarks/proof.js ${target_dir}/benchmarks
# cp benchmarks/proof.css ${target_dir}/benchmarks

# SimpleConsensus.
cp benchmarks/SimpleConsensus.tla ${target_dir}/benchmarks
cp benchmarks/SimpleConsensus_TLC.tla ${target_dir}/benchmarks
cp benchmarks/SimpleConsensus.config.json ${target_dir}/benchmarks
# cp benchmarks/SimpleConsensus_ApaIndProofCheck.tla ${target_dir}/benchmarks

# SimpleConsensus.
# cp benchmarks/AbstractRaft.tla ${target_dir}/benchmarks/
# cp benchmarks/AbstractRaft_TLC.tla ${target_dir}/benchmarks/
# cp benchmarks/AbstractRaft.config.json ${target_dir}/benchmarks/
# cp benchmarks/AbstractStaticRaft_ApaIndProofCheck.tla ${target_dir}/benchmarks

# TwoPhase.
cp benchmarks/TwoPhase.tla ${target_dir}/benchmarks
cp benchmarks/TwoPhase.config.json ${target_dir}/benchmarks
# cp benchmarks/TwoPhase_ApaIndProofCheck.tla ${target_dir}/benchmarks

# ZeusReliableCommit.
cp benchmarks/ZeusReliableCommit.tla ${target_dir}/benchmarks/
cp benchmarks/ZeusReliableCommit_TLC.tla ${target_dir}/benchmarks/
cp benchmarks/ZeusReliableCommit.config.json ${target_dir}/benchmarks/

# Hermes.
cp benchmarks/Hermes.tla ${target_dir}/benchmarks/
cp benchmarks/Hermes_TLC.tla ${target_dir}/benchmarks/
cp benchmarks/Hermes.config.json ${target_dir}/benchmarks/

# Bakery.
cp benchmarks/Bakery.tla ${target_dir}/benchmarks
cp benchmarks/Bakery.config.json ${target_dir}/benchmarks
cp benchmarks/Bakery_TLC.tla ${target_dir}/benchmarks

# Boulanger.
cp benchmarks/Boulanger.tla ${target_dir}/benchmarks
cp benchmarks/Boulanger.config.json ${target_dir}/benchmarks
cp benchmarks/Boulanger_TLC.tla ${target_dir}/benchmarks


# AsyncRaft. (anonymize it.)
sed -E "s/Will Schultz/X/g" benchmarks/AsyncRaft.tla | sed -E "s/Will S/X/g" > ${target_dir}/benchmarks/AsyncRaft.tla
# cp benchmarks/AsyncRaft.tla ${target_dir}/benchmarks
cp benchmarks/AsyncRaft.config.json ${target_dir}/benchmarks
cp benchmarks/AsyncRaft_TLC.tla ${target_dir}/benchmarks
cp benchmarks/Apalache.tla ${target_dir}/benchmarks
# cp benchmarks/AsyncRaft_ApasIndProofCheck.tla ${target_dir}/benchmarks

# Copy TLC and Apalache binaries.
# cp -r benchmarks/apalache $target_dir/benchmarks
# cp -r /Users/willyschultz/Dropbox/PhD/Research/artifacts/apalache-0.44.0 $target_dir/benchmarks
# mv $target_dir/benchmarks/apalache-0.44.0 $target_dir/benchmarks/apalache
cp benchmarks/tla2tools-checkall.jar $target_dir/benchmarks

# Zip it up.
cd $base_dir
rm $target_dirname.zip
zip -r "${target_dirname}.zip" $target_dirname