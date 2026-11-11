#!/usr/bin/env python3
"""Reject corrupted capture accounting and preserve ambiguous display names."""
import copy,json,pathlib,runpy,tempfile
M=runpy.run_path(str(pathlib.Path(__file__).with_name('check_refs.py')))
def main():
 with tempfile.TemporaryDirectory() as d:
  raw=pathlib.Path(d)/'raw';log=pathlib.Path(d)/'log'
  rows=[dict(record='command',command=0,unresolved_info_holes=0,finished_diagnostic_snapshots=0),dict(record='command_info',command=0,check_kind='example')]
  for key in (['str','anonymous','a.1'],['num',['str','anonymous','a'],1]):rows.append(dict(record='identifier',command=0,check_kind='example',ident=dict(kind='const',name='a.1'),is_binder=False,name_key=key))
  log.write_text('RAW_REFS_CAPTURE_PASS 1 3 0\n')
  def write(data):raw.write_text(''.join(json.dumps(r)+'\n' for r in data))
  write(rows);result=M['measure'](raw,log);assert len(result['observed_constants'])==2 and result['check_reference_events']==2
  def rejected(data):
   write(data)
   try:M['measure'](raw,log)
   except AssertionError:return
   raise AssertionError('Corrupt capture accepted')
  rejected(rows+[dict(record='unknown')]);bad=copy.deepcopy(rows);bad[-1]['name_key']=None;rejected(bad)
  write(rows);log.write_text('RAW_REFS_CAPTURE_PASS 1 2 0\n');rejected(rows)
 print('CHECK_REFERENCE_ACCOUNTING_FIXTURES_PASS')
if __name__=='__main__':main()
