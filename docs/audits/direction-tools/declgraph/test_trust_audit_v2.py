#!/usr/bin/env python3
"""An additive v2 cannot drop, rewrite or wrap any frozen v1 statement/body."""
import pathlib,runpy
M=runpy.run_path(str(pathlib.Path(__file__).with_name('trust_audit_v2.py')))
def main():
 v1=b'import Lean\n\nexample : True := True.intro\nrun_cmd pure ()\n';v2=M['build_v2'](v1);M['verify'](v1,v2)
 for bad in [v1,v2.replace(b'True.intro',b'by trivial'),v2+b'\n',b'namespace Alternative\n'+v2]:
  try:M['verify'](v1,bad)
  except AssertionError:pass
  else:raise AssertionError('Non-additive v2 accepted')
 print('TRUST_V2_FIXTURES_PASS dropped rewritten appended wrapped_v1_rejected')
if __name__=='__main__':main()
