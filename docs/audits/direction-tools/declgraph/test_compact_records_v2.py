#!/usr/bin/env python3
"""Exact legacy tuple/rejection fixtures and optional complete-corpus outputs."""
import argparse,copy,json,pathlib,runpy,tempfile,time
HERE=pathlib.Path(__file__).resolve().parent;V=runpy.run_path(str(HERE/'compact_records_v2.py'));B=V['BASE']
def main():
 p=argparse.ArgumentParser();p.add_argument('--legacy-receipt',type=pathlib.Path);p.add_argument('--v2-receipt',type=pathlib.Path);p.add_argument('--capture',type=pathlib.Path);p.add_argument('--path');a=p.parse_args()
 assert bool(a.legacy_receipt)==bool(a.v2_receipt) and bool(a.capture)==bool(a.path)
 n=['str','anonymous','root'];ref=['str','anonymous','support']
 rows=[dict(record='command',command=0,missing_parent_events=0,active_nodes_without_parent=0),dict(record='check_event',command=0,check_kind='example'),dict(record='root_event',command=0,snapshot=0,name_key=n,constant_kind='def'),dict(record='definition',id=0,name='root',name_key=n,constant_kind='def',refs=[dict(name='support',name_key=ref),dict(name='support',name_key=copy.deepcopy(ref))]),dict(record='binding_ref',definition=0,command=0,snapshot=0,in_stage2=True,elaborating_module='Fixture',imported_pointer_modules=[],is_root=True,own_range=None),dict(record='snapshot_summary',command=0,snapshot=0,root_names=[n],emitted_bindings=1,visited_names=1,missing_names=[],unresolved_import_origins=0)]
 with tempfile.TemporaryDirectory() as directory:
  raw=pathlib.Path(directory)/'roots';log=pathlib.Path(directory)/'log';log.write_text('COMPACT_ROOTS_PASS 1 1 1 1 1 1\n')
  def put(data):raw.write_text(''.join(json.dumps(r)+'\n' for r in data))
  put(rows);assert B['measure'](raw,log,'Fixture.lean')==V['measure'](raw,log,'Fixture.lean')
  for edit in [lambda x:x[4].update(definition=999),lambda x:x.append(copy.deepcopy(x[3])),lambda x:x[3].update(name_key=None),lambda x:x[3]['refs'][0].update(name_key=None),lambda x:x[5].update(emitted_bindings=2),lambda x:x[4].update(snapshot=2),lambda x:x[5].update(root_names=[['str','anonymous','wrong']])]:
   data=copy.deepcopy(rows);edit(data);put(data)
   for implementation in (B,V):
    try:implementation['measure'](raw,log,'Fixture.lean')
    except AssertionError:pass
    else:raise AssertionError('Invalid data accepted')
  put(rows);log.write_text('COMPACT_ROOTS_PASS 1 1 1 1 2 1\n')
  for implementation in (B,V):
   try:implementation['measure'](raw,log,'Fixture.lean')
   except AssertionError:pass
   else:raise AssertionError('Wrong footer accepted')
  original=V['LEGACY']['measure'];clone=V['cloned_measure']();assert clone.__code__ is original.__code__ and clone.__defaults__==original.__defaults__ and clone.__kwdefaults__==original.__kwdefaults__ and clone.__closure__ is original.__closure__
  assert clone.__globals__ is not original.__globals__ and original.__globals__['keyhash'] is V['LEGACY']['keyhash']
  key=['str','anonymous','retained'];same=copy.deepcopy(key);cached=clone.__globals__['keyhash'];assert cached(key)==cached(key)==cached(same)==V['LEGACY']['keyhash'](key)
 if a.capture:
  values=[];seconds=[]
  for implementation in (B,V):
   start=time.monotonic();values.append(implementation['measure'](a.capture/'roots.jsonl',a.capture/'capture.log',a.path));seconds.append(time.monotonic()-start)
  assert values[0]==values[1];print('COMPACT_V2_REAL_TUPLE_PASS',json.dumps(seconds))
 if a.legacy_receipt:
  old=json.loads(a.legacy_receipt.read_text());new=json.loads(a.v2_receipt.read_text())
  assert old['base']==new['base'] and old['inputs']==new['inputs'] and old['outputs']==new['outputs'] and old['lean']==new['lean'] and old['queue_summary']==new['queue_summary']
  assert all(new['producers'][n]==h for n,h in old['producers'].items())
  assert set(new['producers'])-set(old['producers'])=={'replay_cached_checks_v2.py','compact_records_v2.py'}
  print('COMPACT_V2_FULL_OUTPUT_PASS',len(old['outputs']))
 print('COMPACT_V2_FIXTURES_PASS exact_tuple distinct_equal_keys retained_identity clone_isolation invalid_references null_keys snapshot_root_footer_rejections')
if __name__=='__main__':main()
