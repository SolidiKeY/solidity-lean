#!/usr/bin/env python3
"""Summarize explicit-source check syntax; diagnostics do not certify semantic roots.
Run with --source-root FROZEN --reference-view VIEW --commands INDEX
--compiler-edges INDEX.compiler.json --out RESULT_DIR. Raw parser data remains
outside Git. Skipped command effects, macro expansions and uncached consumers remain unmeasured.
"""
import argparse,collections,hashlib,json,pathlib,runpy
HERE=pathlib.Path(__file__).resolve().parent

def generate(source_root,view,commands,compiler):
 receipt=json.loads(pathlib.Path(str(commands)+'.receipt.json').read_text())
 assert receipt['producer_sha256']==hashlib.sha256((HERE/'Commands.lean').read_bytes()).hexdigest(),'Stale parser revision'
 assert receipt['index_sha256']==hashlib.sha256(commands.read_bytes()).hexdigest(),'Index receipt mismatch'
 assert receipt['compiler_sha256']==hashlib.sha256(compiler.read_bytes()).hexdigest(),'Compiler receipt mismatch'
 assert pathlib.Path(receipt['reference_view']).resolve()==view.resolve(),'Reference-view mismatch'
 api=runpy.run_path(str(HERE/'audit.py'));src=api['assert_sources'](source_root)
 expected={str(source_root.resolve()/p):p for p in src};seen=set();areas=collections.defaultdict(collections.Counter);failures=[];roots=[];provenance=collections.defaultdict(collections.Counter)
 for line in commands.open():
  r=json.loads(line);assert r['path'] in expected and r['path'] not in seen,'Unexpected/duplicate source path'
  seen.add(r['path']);p=expected[r['path']];area='/'.join(p.split('/')[:2]);c=areas[area]
  required=['complete','checks','parse_errors','scope_errors','missing_imports','unlocated_parser_groups','unsupported_registrations','unapplied_parser_groups']
  assert all(k in r for k in required),'Old/incomplete index schema'
  bad=any(r[k] for k in required[2:]);assert r['complete']==(not bad),(p,r)
  if not r['complete']:assert r['checks']==[],p
  pc=provenance[api['provenance'](p,src[p])];pc['files']+=1;pc['diagnostic_clear_files']+=int(r['complete']);pc['syntax_occurrences']+=len(r['checks'])
  c['files']+=1;c['commands']+=r['commands'];c['diagnostic_clear_files']+=int(r['complete'])
  ref=view/pathlib.Path(p.removeprefix('Bridge/').removeprefix('vendor/LeanTeX/')).with_suffix('.ilean')
  cached=ref.is_file();c['cached_files']+=int(cached);c['diagnostic_clear_cached_files']+=int(cached and r['complete'])
  for flag in required[2:]:
   if r[flag]:c[flag+'_files']+=1
  c['local_grammar_replays']+=r['local_grammar_replays']
  c['bookkeeping_kind_groups']+=r['bookkeeping_kind_groups']
  for check in r['checks']:
   assert check['kind'] in ('eval','example') and len(check['range'])==4
   lo=tuple(check['range'][:2]);hi=tuple(check['range'][2:]);assert lo<hi
   assert hi[0]<len(src[p].splitlines()),(p,check)
   c[check['kind']+'_syntax_occurrences']+=1
   roots.append(dict(path=p,kind=check['kind'],range=check['range'],cached=cached))
  if bad:
   failures.append(dict(path=p,cached=cached,flags={k:r[k] for k in required[2:] if r[k]}))
 assert seen==expected.keys(),'Missing source index rows'
 pairs=json.loads(compiler.read_text());assert all(isinstance(x,list) and len(x)==2 and all(isinstance(n,str) for n in x) for x in pairs)
 assert len({tuple(x) for x in pairs})==len(pairs),'Duplicate override edges'
 totals=collections.Counter()
 for c in areas.values():totals.update(c)
 summary=dict(base=api['BASE'],status='partial',method='Lean-native check syntax under reconstructed grammar; recognized top-level example/eval bodies are not replayed',
  provenance={k:dict(sorted(v.items())) for k,v in sorted(provenance.items())},counts=dict(sorted(totals.items())),areas={k:dict(sorted(v.items())) for k,v in sorted(areas.items())},
  producer_sha256=receipt['producer_sha256'],lean=receipt['lean'],compiler_override_edges=len(pairs),index_sha256=hashlib.sha256(commands.read_bytes()).hexdigest(),
  boundaries=['complete in the raw index means only that recorded diagnostic flags are clear; it does not certify actual parser context.',
   'Only builtin declaration, in, and guard_msgs ancestry is counted; unknown nested-check wrappers suppress the file.',
   'Skipped custom commands can install grammar and change later parsing. Semantic-root coverage is unverified.',
   'Missing native/reference consumers and separate parser registrations remain explicit gaps.',
   'Command-macro-generated checks remain unmeasured. Scope/grammar replay may invoke term elaborators.' ,
   'No new liveness classification or deletion safety follows from this syntax census.'])
 return summary,sorted(roots,key=lambda r:(r['path'],r['range'],r['kind'])),sorted(pairs),failures

def main():
 p=argparse.ArgumentParser();p.add_argument('--source-root',type=pathlib.Path,required=True);p.add_argument('--reference-view',type=pathlib.Path,required=True);p.add_argument('--commands',type=pathlib.Path,required=True);p.add_argument('--compiler-edges',type=pathlib.Path,required=True);p.add_argument('--out',type=pathlib.Path,required=True);p.add_argument('--check',action='store_true');a=p.parse_args()
 summary,roots,pairs,failures=generate(a.source_root,a.reference_view,a.commands,a.compiler_edges)
 a.out.mkdir(parents=True,exist_ok=True)
 data={'syntax-census.json':summary,'source-check-syntax.json':roots,'compiler-edges.json':pairs}
 for name,obj in data.items():
  body=(json.dumps(obj,sort_keys=True,separators=(',',':')) if name=='source-check-syntax.json' else json.dumps(obj,indent=2,sort_keys=True))+'\n';assert len(body.encode())<1_000_000,name
  target=a.out/name
  if a.check:assert target.read_text()==body,'STALE '+name
  else:target.write_text(body)
 # Full failure diagnostics remain off-branch with the raw parser index.
 print('SOURCE_SYNTAX_CENSUS_PASS',summary['counts'].get('files'),summary['counts'].get('diagnostic_clear_files'),len(roots),len(failures))
if __name__=='__main__':main()
