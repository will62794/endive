"""
Various utilities for model checking TLA+ specs with TLC and/or Apalache.
"""
import subprocess
import logging
import os
import sys

class Apalache:
    """ Utilities for model checking TLA+ with Apalache. """
    def __init__(self, specdir) -> None:
        self.apalache_bin = "apalache/bin/apalache-mc"
        self.specdir = specdir
        self.GEN_TLA_DIR = "gen_tla" # TODO: pass this in.

    def gen_check_spec(self, orig_spec_name, check_spec_name, defs):
        """ 
        Create a spec that allows for various model checking tasks.

        Adds all given 'defs' as new definitions in a spec that extends the given original spec. Expects
        'defs' to be given as a map from definition names to TLA+ expressions.
        """
        
        # Build the spec.
        spec_lines = [
            "---- MODULE %s ----\n" % check_spec_name,
            f"EXTENDS {orig_spec_name},Naturals,TLC\n"
        ] + [
            f"{d} == {defs[d]}" for d in defs
        ] + [
            "===="
        ]
        return "\n".join(spec_lines)

    def check(self, orig_spec_name, init, inv, defs={}, length=1):
        # Clean the output directory.
        os.system("rm -rf benchmarks/gen_tla/apalache-cti-out")

        check_spec_name = f"{orig_spec_name}_ApaCheck"
        spec_text = self.gen_check_spec(orig_spec_name, check_spec_name, defs)
        tla_file = f"{os.path.join(self.specdir, self.GEN_TLA_DIR)}/{check_spec_name}.tla"
        tla_filename = f"{self.GEN_TLA_DIR}/{check_spec_name}.tla"

        f = open(tla_file, 'w')
        f.write(spec_text)
        f.close()

        rundir = "gen_tla/apalache_ctigen"
        outdir = "gen_tla/apalache_ctigen"
        jvm_args="JVM_ARGS='-Xss16M'"
        args = [
            f"--out-dir={outdir}",
            f"--run-dir={rundir}",
            # f"--max-error={max_num_ctis}",
            # f"--view=vars",
            f"--cinit=CInit",
            f"--init={init}",
            f"--next=Next",
            f"--inv={inv}",
            f"--length={length}",
            tla_filename
        ]
        cmd = f"{self.apalache_bin} check {' '.join(args)}"
        logging.debug("Apalache command: " + cmd)
        workdir = None
        if self.specdir != "":
            workdir = self.specdir
        subproc = subprocess.Popen(cmd, shell=True, stdout=subprocess.PIPE, cwd=workdir)
        return subproc
    
    def await_output(self, apalache_subproc):
        apa_out = apalache_subproc.stdout.read().decode(sys.stdout.encoding)
        lines = [x.strip() for x in apa_out.splitlines()]
        # Check for successful Apalache run.
        for l in lines:
            if "Checker reports no error up to computation length 1" in l:
                return {"error":False, "stdout": apa_out}
        return {"error":True, "stdout": apa_out}

    def induction_check(self, pre, post):
        """ Checks whether (pre /\ Next => post') holds. """
        pass