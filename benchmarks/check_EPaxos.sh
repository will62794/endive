#!/bin/sh
javaexe=fastjava
$javaexe -cp tla2tools-1a92ec7.jar tlc2.TLC -noGenerateSpecTE -deadlock -simulate -depth 30 -workers 6 EPaxos | tee logout_EPaxos