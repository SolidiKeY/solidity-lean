#!/usr/bin/env python3
"""Generate exact H16 frame-operation signatures; no assumed theorem bodies."""
import argparse
from pathlib import Path
p=argparse.ArgumentParser();p.add_argument('output',type=Path);a=p.parse_args()
names=['Solidity.Source.St','Solidity.Source.FailureExecution.RuntimePlan','Solidity.Source.FailureExecution.check','Solidity.Source.FailureExecution.pending','Solidity.Source.FailureExecution.frame','Solidity.Source.FailureExecution.emit']
a.output.write_text('import Solidity.Source.FailureMachine\n'+'\n'.join('#print '+n for n in names)+'\n'+'\n'.join('#print axioms '+n for n in names[2:])+'\n')
