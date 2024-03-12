#!/bin/sh
TLAJAR="../../tlaplus/tlatools/org.lamport.tlatools/dist/tla2tools.jar"

specname=$1

java -cp $TLAJAR tla2sany.SANY -D $specname.tla dot
dot -Tpdf ${specname}.dot > ${specname}_sany.pdf