#!/bin/sh
#
# Script for reproing CTIs used for running example in paper.
#
java_args="-Dtlc2.tool.impl.Tool.autoInitStatesSampling=true -Dtlc2.tool.impl.Tool.autoInitSamplingTimeLimitMS=6000 -Dtlc2.tool.impl.Tool.autoInitSamplingTargetNumInitStates=3333"
java_base_cmd="java $java_args -cp tla2tools-checkall.jar tlc2.TLC -continue -deadlock -workers 1 -maxSetSize 100000000 -simulate num=100 -depth 1 -seed 2141 -noGenerateSpecTE -metadir states/ctidemorandom  -simulate -depth 1"
$java_base_cmd -config consensus_epr_cti_demo_ind0.cfg consensus_epr_cti_demo | tee consensus_epr_cti_demo_ind0.log
$java_base_cmd -config consensus_epr_cti_demo_ind1.cfg consensus_epr_cti_demo | tee consensus_epr_cti_demo_ind1.log
$java_base_cmd -config consensus_epr_cti_demo_ind2.cfg consensus_epr_cti_demo | tee consensus_epr_cti_demo_ind2.log