#!/bin/sh

#
# Launch 2024 evaluation benchmarks on Discovery.
#

# Then fetch generated data with ./discovery_fetch_data.sh,
# which will be placed into discovery_data/ directory.


./discovery_launch.sh TwoPhase
./discovery_launch.sh consensus_epr
# ./discovery_launch.sh LamportMutex
# ./discovery_launch.sh ZeusReliableCommit
# ./discovery_launch.sh Hermes
# ./discovery_launch.sh Bakery
# ./discovery_launch.sh Boulanger