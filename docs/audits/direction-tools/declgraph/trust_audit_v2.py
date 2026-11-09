#!/usr/bin/env python3
"""R3/H314 additive TrustAudit v2: one import plus byte-identical frozen v1.
This does not repair or replace v1 and does not repin declaration measurements.
The v2 owner review and Lean checks are separate obligations.
"""
import argparse,pathlib,runpy,subprocess
HERE=pathlib.Path(__file__).resolve().parent
Q=runpy.run_path(str(HERE/'capture_cached_checks.py'));API=Q['API']
PREFIX=b'import Solidity.Examples.Tactics.OpenLoops.RowsNine\n'
TARGET=HERE/'v2/TrustAuditV2.lean'
def build_v2(v1):
 assert PREFIX.rstrip() not in v1.splitlines(),'Frozen v1 already imports the child'
 return PREFIX+v1

def verify(v1,v2):
 assert v2==build_v2(v1),'v2 must be exactly one additive import plus unchanged v1 bytes'

def main():
 p=argparse.ArgumentParser();p.add_argument('--source-root',type=pathlib.Path,required=True);p.add_argument('--check',action='store_true');a=p.parse_args()
 with Q['writer_lease']():
  API['assert_sources'](a.source_root)
  v1=subprocess.check_output(['git','show',API['BASE']+':TrustAudit.lean'],cwd=HERE.parents[3]);assert (a.source_root/'TrustAudit.lean').read_bytes()==v1
  if a.check:verify(v1,TARGET.read_bytes())
  else:Q['atomic_text'](TARGET,build_v2(v1).decode())
  assert (a.source_root/'TrustAudit.lean').read_bytes()==v1
 print('TRUST_V2_PRESERVATION_PASS additive_import byte_identical_v1_suffix')
if __name__=='__main__':main()
