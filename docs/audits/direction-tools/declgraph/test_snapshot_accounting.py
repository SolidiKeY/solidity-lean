#!/usr/bin/env python3
"""Corruption and all-or-nothing table merge fixtures; no Lean required."""
import copy,json,pathlib,runpy,tempfile
M=runpy.run_path(str(pathlib.Path(__file__).with_name('run_snapshot_roots.py')))
def main():
 imported={'existing':('old',)};stage2={'conflict':['old']}
 try:M['merge_tables'](imported,stage2,{'fresh':('new',)},{'conflict':['different']})
 except AssertionError:pass
 else:raise AssertionError('Conflicting file accepted')
 assert imported=={'existing':('old',)} and stage2=={'conflict':['old']}
 n=['str','anonymous','root']
 rows=[dict(record='command',command=0,missing_parent_events=0,active_nodes_without_parent=0),dict(record='check_event',command=0,check_kind='example'),dict(record='root_event',command=0,snapshot=0,name_key=n,constant_kind='def'),dict(record='binding',command=0,snapshot=0,name='root',name_key=n,constant_kind='def',imported_pointer_modules=[],refs=[],in_stage2=True,own_range=None,is_root=True),dict(record='snapshot_summary',command=0,snapshot=0,root_names=[n],emitted_bindings=1,visited_names=1,missing_names=[],unresolved_import_origins=0)]
 with tempfile.TemporaryDirectory() as d:
  raw=pathlib.Path(d)/'raw';log=pathlib.Path(d)/'log';log.write_text('SNAPSHOT_ROOTS_PASS 1 1 1 1 1\n')
  def put(data):raw.write_text(''.join(json.dumps(x)+'\n' for x in data))
  put(rows);data,im,st=M['measure'](raw,log,'Fixture.lean');assert data['covered_check_commands']==1 and len(st)==1
  def reject(data):
   put(data)
   try:M['measure'](raw,log,'Fixture.lean')
   except AssertionError:return
   raise AssertionError('Corrupt snapshot accepted')
  bad=copy.deepcopy(rows);bad[3]['snapshot']=1;reject(bad)
  bad=copy.deepcopy(rows);bad[4]['root_names']=[['str','anonymous','wrong']];reject(bad)
  bad=copy.deepcopy(rows);bad[3]['is_root']=False;reject(bad)
  bad=copy.deepcopy(rows);bad[0]['missing_parent_events']=1;reject(bad)
 print('SNAPSHOT_ACCOUNTING_FIXTURES_PASS atomic_merge snapshot_references root_identity counters')
if __name__=='__main__':main()
