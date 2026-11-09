#!/usr/bin/env python3
"""Queue receipt field tampering and atomic status replacement fixtures."""
import copy,json,pathlib,runpy,tempfile
M=runpy.run_path(str(pathlib.Path(__file__).with_name('capture_cached_checks.py')));H=M['HERE']
def main():
 with tempfile.TemporaryDirectory() as d:
  root=pathlib.Path(d);capture=root/'capture';capture.mkdir();view=root/'view';(view/'Solidity').mkdir(parents=True);source=root/'Fixture.lean';source.write_text('example : True := True.intro\n');(view/'Solidity/Fixture.ilean').write_text('{"module":"Solidity.Fixture"}')
  for n in ('roots.jsonl','capture.log'):(capture/n).write_text('fixture\n')
  names=('CompactRoots.lean','compact_records.py','run_snapshot_roots.py','audit.py','modules.txt','capture_compact.py');producers={n:M['SHA'](H/n) for n in names};version='Lean (version 4.24.0, commit797c613)';graph='graph-receipt'
  cmd=['lean','--tstack=131072','-j1','-M10000','--run',str(H/'CompactRoots.lean'),str(source),'Solidity.Fixture',str(H/'modules.txt'),str(capture/'roots.jsonl')]
  meta=dict(producers=producers,command=cmd,lean=version,module='Solidity.Fixture',source_sha256=M['SHA'](source),view=str(view),graph_receipt_sha256=graph,exit_code=0,outputs={n:M['SHA'](capture/n) for n in ('roots.jsonl','capture.log')})
  def test(data):
   M['atomic_json'](capture/'receipt.json',data);return M['validate_capture'](capture,source,'Solidity/Fixture.lean',view,version,graph,producers)
  assert test(meta)==meta
  for field,value in [('lean','wrong'),('module','wrong'),('graph_receipt_sha256','wrong'),('command',cmd[:-1]),('source_sha256','wrong')]:
   bad=copy.deepcopy(meta);bad[field]=value
   try:test(bad)
   except AssertionError:pass
   else:raise AssertionError('Tampered receipt accepted: '+field)
  state=root/'status.json';M['atomic_json'](state,{'first':1});M['atomic_json'](state,{'second':2});assert json.loads(state.read_text())=={'second':2};assert not list(root.glob('status.json.tmp-*'))
 print('CACHED_QUEUE_FIXTURES_PASS native_recipe module version graph_receipt source atomic_replace')
if __name__=='__main__':main()
