#!/bin/sh
#
# Launch 2024 evaluation benchmarks on Discovery.
#


./discovery_launch.sh TwoPhase
./discovery_launch.sh consensus_epr
./discovery_launch.sh LamportMutex
./discovery_launch.sh ZeusReliableCommit
./discovery_launch.sh Hermes
./discovery_launch.sh Bakery
./discovery_launch.sh Boulanger