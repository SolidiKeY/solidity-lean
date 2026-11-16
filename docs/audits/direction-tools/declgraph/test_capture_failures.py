#!/usr/bin/env python3
"""Diagnostic categories, raw-LF units and protected-destination refusals."""
import argparse,pathlib,runpy,subprocess,sys,tempfile
HERE=pathlib.Path(__file__).resolve().parent;G=runpy.run_path(str(HERE/'capture_failures.py'))
def main():
 diagnose=G['diagnosis'];assert diagnose('','SNAPSHOT_ROOTS_UNSUPPORTED incomplete info context\n',False)=='explicit_unsupported_info_context'
 assert diagnose('','file:1:1: error: sol_close_nonlin: bounded search stopped; original goal retained\n',False)=='explicit_bounded_search_stop'
 assert diagnose('subprocess.TimeoutExpired: diagnostic','',False)=='driver_reported_subprocess_timeout'
 assert diagnose('','SNAPSHOT_ROOTS_UNSUPPORTED incomplete info context',True)=='unvalidated_native_receipt_present'
 assert diagnose('','unrelated failure',False)=='unclassified_failure'
 for text,expected in [('',0),('a',1),('a\n',1),('a\nb',2),('a\u2028b',1),('a\vb',1),('a\r\nb\r',2)]:assert G['raw_lf_lines'](text)==expected
 with tempfile.TemporaryDirectory() as directory:
  root=pathlib.Path(directory);source=root/'source';view=root/'view';captures=root/'captures';out=HERE/'capture-failures-prefix260.json';proof=root/'proof.json'
  def safe(**kw):
   values=dict(source=source,view=view,captures=captures,out=out,evidence=proof,limit=260);values.update(kw);G['safe_destinations'](**values)
  safe()
  sentinel=root/'sentinel';sentinel.write_bytes(b'protected fixture bytes')
  for change in [dict(out=sentinel),dict(evidence=source/'receipt.json'),dict(evidence=view/'receipt.json'),dict(evidence=captures/'x.status.json'),dict(evidence=HERE/'audit.py'),dict(evidence=out),dict(evidence=root),dict(evidence=sentinel)]:
   try:safe(**change)
   except AssertionError:pass
   else:raise AssertionError('Protected destination accepted')
  alias=root/'alias';alias.symlink_to(source/'receipt.json')
  try:safe(evidence=alias)
  except AssertionError:pass
  else:raise AssertionError('Protected alias accepted')
  proof.write_bytes(b'existing private receipt')
  try:safe()
  except AssertionError:pass
  else:raise AssertionError('Existing private receipt overwritten')
  safe(check=True);assert sentinel.read_bytes()==b'protected fixture bytes' and proof.read_bytes()==b'existing private receipt'
 result=subprocess.run([sys.executable,'-I','-B','-O',str(HERE/'capture_failures.py'),'--help'],capture_output=True,text=True)
 assert result.returncode and 'OPTIMIZED_PYTHON_UNSUPPORTED' in result.stderr
 print('CAPTURE_FAILURE_CONTROLS_PASS diagnostics_not_semantics raw_LF_unicode_controls designated_summary protected_aliases fresh_receipt read_only optimized_refusal')
if __name__=='__main__':main()
