#!/usr/bin/env python3
"""Range endpoint, overlap, unresolved-membership and path refusal controls."""
import argparse,copy,pathlib,runpy,subprocess,sys,tempfile
HERE=pathlib.Path(__file__).resolve().parent;G=runpy.run_path(str(HERE/'observed_ranges.py'))
def rejected(action):
 try:action()
 except AssertionError:return
 raise AssertionError('Invalid input accepted')
def main():
 lines=G['native_lines'];assert lines('',[0,0,0,0])==set() and lines('a\nb\n',[0,0,2,0])=={1,2}
 assert lines('a\nb\n',[0,0,1,0])=={1} and lines('a\nb\n',[2,0,2,0])==set()
 assert lines('α😀\nlast\n',[0,1,0,3])=={1} and lines('α\u2028β',[0,0,0,3])=={1}
 assert lines('a',None) is None
 for text,r in [('α😀\n',[0,2,0,3]),('a',[0,0,1,0]),('a\n',[0,0,1,1]),('a',[0,0,0,9]),('a',[1,0,0,0]),('a',[0,0,0,-1]),('a',[0,0,0,True])]:rejected(lambda:lines(text,r))
 assert G['footprint_counts']('a\nb\nc\n',{1},{1,2})==(1,1,1)
 assert G['footprint_counts']('a\nb\n',{1,2},{1,2})==(2,0,0)
 rejected(lambda:G['footprint_counts']('a\n',{2},set()))
 with tempfile.TemporaryDirectory() as directory:
  root=pathlib.Path(directory);sentinel=root/'sentinel';sentinel.write_bytes(b'protected bytes')
  base=dict(source_root=root/'source',view=root/'view',graph=root/'graph.jsonl',combined=root/'combined',combined_evidence=root/'combined-receipt.json',replay=root/'replay',replay_evidence=root/'replay-receipt.json',capture=root/'capture',out=HERE/'observed-ranges-prefix130',evidence=root/'evidence.json',prefix=130,check=False)
  def safe(**changes):
   values=dict(base);values.update(changes);G['safe_paths'](argparse.Namespace(**values))
  safe()
  for change in [dict(out=sentinel),dict(capture=base['source_root']/'new'),dict(capture=HERE/'new'),dict(evidence=base['view']/'record.json'),dict(evidence=base['replay_evidence']),dict(capture=base['combined_evidence']),dict(evidence=base['capture']/'receipt.json'),dict(evidence=sentinel),dict(capture=root),dict(out=base['replay'],replay=HERE/'observed-ranges-prefix130')]:rejected(lambda:safe(**change))
  alias=root/'alias';alias.symlink_to(base['source_root']/'new');rejected(lambda:safe(capture=alias))
  base['capture'].mkdir();base['evidence'].write_bytes(b'private receipt')
  rejected(safe);safe(check=True)
  assert sentinel.read_bytes()==b'protected bytes' and base['evidence'].read_bytes()==b'private receipt'
  chunk=root/'chunk';chunk.mkdir();body='[]\n'
  for name,content in [('query.json',body),('capture.log','fixture log'),('keys.jsonl','fixture keys')]: (chunk/name).write_text(content)
  fixed=dict(command=['fixture-only'],query_sha256=G['SHA'](chunk/'query.json'))
  meta=dict(fixed,exit_code=0,outputs={n:G['SHA'](chunk/n) for n in ('query.json','capture.log','keys.jsonl')})
  G['validate_chunk'](meta,fixed,chunk,body)
  for name in ('query.json','capture.log','keys.jsonl'):
   bad=copy.deepcopy(meta);bad['outputs'].pop(name);rejected(lambda:G['validate_chunk'](bad,fixed,chunk,body))
  bad=copy.deepcopy(meta);bad['outputs']['unexpected']='0'*64;rejected(lambda:G['validate_chunk'](bad,fixed,chunk,body))
  (chunk/'capture.log').write_text('modified log');rejected(lambda:G['validate_chunk'](meta,fixed,chunk,body));(chunk/'capture.log').write_text('fixture log')
  failed=copy.deepcopy(meta);failed['exit_code']=124;G['validate_chunk'](failed,fixed,chunk,body)
  (chunk/'keys.jsonl').unlink();failed['outputs'].pop('keys.jsonl');G['validate_chunk'](failed,fixed,chunk,body)
  failed['exit_code']=0;rejected(lambda:G['validate_chunk'](failed,fixed,chunk,body))
 result=subprocess.run([sys.executable,'-I','-B','-O',str(HERE/'observed_ranges.py'),'--help'],capture_output=True,text=True);assert result.returncode and 'OPTIMIZED_PYTHON_UNSUPPORTED' in result.stderr
 print('OBSERVED_RANGES_CONTROLS_PASS raw_LF_UTF16_endpoints exclusive_end EOF invalid_ranges facade_first_overlap protected_aliases fresh_evidence exact_chunk_output_sets changed_log_refused failed_partial_keys_sealed optimized_refusal no_Lean')
if __name__=='__main__':main()
