#!/usr/bin/env python3
"""Recover the exact earlier lexical candidate inventory, not lexical use edges.
Only instruments the historical build() return to expose its existing partitions.
Native dependency judgements must be made separately. No historical code edited.
"""
import ast,collections,csv,hashlib,json,pathlib,runpy,subprocess,types
HERE=pathlib.Path(__file__).resolve().parent
API=runpy.run_path(str(HERE/'audit.py'));ROOT=API['ROOT'];BASE=API['BASE']
REACH='docs/audits/direction-tools/reachability/reach.py'

def raw_span(text,start,end):
 assert 0<=start<end<=len(text)
 first=text.count('\n',0,start)+1
 last=text.count('\n',0,end)+(0 if text[end-1]=='\n' else 1)
 return first,last,last-first+1

def backend():
 source=subprocess.check_output(['git','show',BASE+':'+REACH],cwd=ROOT,text=True)
 tree=ast.parse(source)
 fn=next(n for n in tree.body if isinstance(n,ast.FunctionDef) and n.name=='build')
 captured=0
 for call in ast.walk(fn):
  if isinstance(call,ast.Call) and isinstance(call.func,ast.Name) and call.func.id=='dict' and {'module','name','kind','start','lines','text'}<= {k.arg for k in call.keywords}:
   call.keywords.extend(ast.parse('dict(source_start_char=match.start(),source_end_char=end)',mode='eval').body.keywords);captured+=1
 assert captured==2,'Historical producer shape changed'
 ret=fn.body[-1];assert isinstance(ret,ast.Return)
 ret.value=ast.Tuple(elts=[ret.value,ast.Name(id='gi',ctx=ast.Load()),ast.Name(id='ti',ctx=ast.Load())],ctx=ast.Load())
 ast.fix_missing_locations(tree)
 namespace={'__name__':'historical_inventory','__file__':str(ROOT/REACH)}
 exec(compile(tree,REACH,'exec'),namespace)
 return namespace,source

def recover():
 namespace,source=backend()
 result,goals,tests=namespace['build']()
 report,unreachable,nodes,modules,texts,generators,graph=result
 oldbase=report['base'];current=API['sources']();rows=[];cleaned={};totals=collections.defaultdict(collections.Counter)
 for i,n in enumerate(nodes):
  if i in goals or i in tests:continue
  path=modules[n['module']]['path'];directory=str(pathlib.PurePosixPath(path).parent)
  if directory+'/' not in API['FAMILIES']:continue
  assert n['kind']!='command','Historical candidate includes a command'
  before=texts[path];after=current.get(path)
  # Fail closed for any changed source file; no name/line remapping guessed.
  same=after is not None and before==after
  if path not in cleaned:
   cleaned[path]=namespace['clean'](before);assert len(cleaned[path])==len(before),'Cleaner changed character offsets'
  a,b=n['source_start_char'],n['source_end_char'];assert n['text']==cleaned[path][a:b],'Recovered slice mismatch'
  first,last,physical=raw_span(before,a,b)
  row=dict(path=path,name=n['name'],kind=n['kind'],source_start_char=a,source_end_char=b,first_line=first,last_line=last,physical_span_lines=physical,historical_masked_first_line=n['start'],historical_masked_span_lines=n['lines'],unchanged_at_base=same,old_source_sha256=hashlib.sha256(before.encode()).hexdigest())
  rows.append(row);c=totals[directory+'/'];c['declarations']+=1;c['historical_reported_lines']+=n['lines'];c['physical_span_lines']+=physical;c['shifted_coordinate_declarations']+=int(first!=n['start']);c['unchanged_declarations' if same else 'changed_file_declarations']+=1;c['unchanged_reported_lines' if same else 'changed_file_reported_lines']+=n['lines'];c['unchanged_physical_span_lines' if same else 'changed_file_physical_span_lines']+=physical
 original=json.loads(subprocess.check_output(['git','show',BASE+':docs/audits/direction-tools/reachability/summary.json'],cwd=ROOT,text=True))
 for family,c in totals.items():
  cluster=next(x for x in original['largest_30_clusters'] if x.get('directory')==family.rstrip('/'))
  assert c['declarations']==cluster['decls'] and c['historical_reported_lines']==cluster['lines'],family
 summary=dict(base=BASE,historical_base=oldbase,producer_sha256=hashlib.sha256(source.encode()).hexdigest(),families={k:dict(v) for k,v in sorted(totals.items())},boundary='Recovered lexical candidate identity and reported masked-line accounting, plus LF-based raw-source positions and physical spans. No lexical edge is used to infer native dependencies. Changed files are not remapped.')
 return sorted(rows,key=lambda r:(r['path'],r['first_line'])),summary

def main():
 import argparse
 p=argparse.ArgumentParser();p.add_argument('--out',type=pathlib.Path,required=True);p.add_argument('--check',action='store_true');a=p.parse_args();rows,summary=recover();a.out.mkdir(parents=True,exist_ok=True)
 for family in API['FAMILIES']:
  subset=[r for r in rows if str(pathlib.PurePosixPath(r['path']).parent)+'/'==family]
  body=json.dumps(subset,sort_keys=True,separators=(',',':'))+'\n';assert len(body.encode())<1000000
  target=a.out/(family.strip('/').replace('/','_')+'-historical.json')
  if a.check:assert target.read_text()==body,'STALE '+target.name
  else:target.write_text(body)
 body=json.dumps(summary,indent=2,sort_keys=True)+'\n'
 if a.check:assert (a.out/'historical-summary.json').read_text()==body,'STALE historical summary'
 else:(a.out/'historical-summary.json').write_text(body)
 print('HISTORICAL_INVENTORY_PASS',len(rows),sum(r['historical_masked_span_lines'] for r in rows),sum(r['physical_span_lines'] for r in rows))
if __name__=='__main__':main()
