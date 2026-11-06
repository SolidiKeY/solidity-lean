#!/usr/bin/env python3
"""Deterministically regenerate the additive public theorem axiom report module."""
import argparse,re
from pathlib import Path

def main():
 p=argparse.ArgumentParser();p.add_argument('--check',action='store_true');a=p.parse_args()
 root=Path('tests/h62/item2/audit-g25-scalar-lowering')
 modules=['ScalarTotality','ClosedTotality','EnvironmentTotality','SuccessControls','BoundaryVectors']
 text='\n'.join('import tests.h62.item2.«audit-g25-scalar-lowering».'+m for m in modules)+'\n\n/-! Explicit axiom reports for every additive public theorem in checkpoint 3. -/\n'
 for module in modules:
  source=(root/(module+'.lean')).read_text();ns=re.search(r'^namespace (\S+)',source,re.M)[1]
  for name in re.findall(r'^theorem (\S+)',source,re.M): text+='#print axioms '+ns+'.'+name+'\n'
 dest=root/'SuccessAxioms.lean'
 if a.check:
  if dest.read_text()!=text: raise ValueError('generated axiom report drift')
  print('PASS: additive axiom report reproduces')
 else: dest.write_text(text)

if __name__=='__main__':main()
