#!/usr/bin/env python3
"""Compile the operand-only generated modules in a fresh external tree."""
import pathlib
import compile_vectors as runner
runner.GENERATED=pathlib.Path("/workspace/scratch/h55-vectors-tables/oracle-generated")
runner.OUT=pathlib.Path("/workspace/scratch/h55-vectors-tables/oracle-lean-objects")
if __name__=="__main__": runner.main()
