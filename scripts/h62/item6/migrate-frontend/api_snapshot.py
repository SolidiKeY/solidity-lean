#!/usr/bin/env python3
"""Extract every imported Frontend ConstantInfo; writes bulk evidence off Git.

Structural types and transitive axiom sets are an environment census. Compiler
auxiliary/private names are included and can differ with compiler scheduling;
these hashes alone are not a proof of frozen public interface equivalence.
"""
import argparse
import fcntl
import hashlib
import importlib.util
import json
import os
from pathlib import Path
import subprocess

TEMPLATE = r'''
open Lean Elab Command
run_cmd do
  let env ← getEnv
  let some path ← liftIO (IO.getEnv "H62_API_OUTPUT") | throwError "H62_API_OUTPUT missing"
  let out ← liftIO (IO.FS.Handle.mk (System.FilePath.mk path) IO.FS.Mode.write)
  let mut count : Nat := 0
  for (name, info) in env.constants.toList do
    if let some idx := env.getModuleIdxFor? name then
      let owner := env.header.moduleNames[idx.toNat]!
      if owner.toString.startsWith "Solidity.Frontend." then
        let axioms ← Lean.collectAxioms name
        let kind := match info with
          | .axiomInfo _ => "axiom"
          | .defnInfo _ => "definition"
          | .thmInfo _ => "theorem"
          | .opaqueInfo _ => "opaque"
          | .quotInfo _ => "quotient"
          | .inductInfo _ => "inductive"
          | .ctorInfo _ => "constructor"
          | .recInfo _ => "recursor"
        let row := Json.mkObj [
          ("name", toJson name.toString), ("module", toJson owner.toString),
          ("kind", toJson kind), ("type_expr", toJson (reprStr info.type)),
          ("levels", toJson (info.levelParams.map Name.toString)),
          ("isUnsafe", toJson info.isUnsafe), ("isPartial", toJson info.isPartial),
          ("axioms", toJson (axioms.map Name.toString).toList)]
        liftIO (out.putStrLn row.compress)
        count := count + 1
  logInfo m!"Frontend API environment census: {count} declarations"
'''

def sha(path): return hashlib.sha256(path.read_bytes()).hexdigest()

def validate_inputs(meta,census,census_path,root):
    if meta['status']!='pass' or meta['targets']!=census['topological_closure']:
        raise SystemExit('Full passing clean lane build required')
    if meta['census_sha256']!=sha(census_path): raise SystemExit('Census provenance mismatch')
    cmd=meta['results'][0]['command']
    config=Path(cmd[cmd.index('--file')+1])
    if sha(config)!=meta['private_config_sha256']: raise SystemExit('Private configuration drift')
    if sha(root/'lakefile.toml')!=meta['tracked_lakefile_sha256']: raise SystemExit('Tracked configuration drift')
    for row in census['closure_sources']+census['scope_files']:
        if sha(root/row['path'])!=row['sha256']: raise SystemExit('Source drift '+row['path'])
    return str(config)

def main():
    ap=argparse.ArgumentParser()
    ap.add_argument('--measurement',type=Path,required=True)
    ap.add_argument('--census',type=Path,required=True)
    ap.add_argument('--out',type=Path,required=True)
    args=ap.parse_args()
    lock=Path('/tmp/solidity-lean-feature-groups-20261025/writer.lock').open('a')
    fcntl.flock(lock,fcntl.LOCK_EX|fcntl.LOCK_NB)
    meta=json.loads(args.measurement.read_text())
    census=json.loads(args.census.read_text())
    root=Path(meta['root'])
    config=validate_inputs(meta,census,args.census,root)
    out=args.out.resolve()
    if out.exists(): raise SystemExit('Refusing to overwrite existing API snapshot')
    out.mkdir(parents=True)
    imports='import Lean\n'+''.join('import '+m+'\n' for m in census['frontend_modules'])
    source=out/'ApiSnapshot.lean';source.write_text(imports+TEMPLATE)
    spec=importlib.util.spec_from_file_location('measure',Path(__file__).with_name('measure.py'))
    runner=importlib.util.module_from_spec(spec);spec.loader.exec_module(runner)
    basecmd=meta['results'][0]['command'];lake=basecmd[0]
    env=dict(os.environ,PATH=str(Path(lake).parent)+':'+os.environ['PATH'],LEAN_NUM_THREADS='1',H62_API_OUTPUT=str(out/'raw.jsonl'))
    os.sched_setaffinity(0,set(meta['settings']['cpu_affinity']))
    cmd=[lake,'--dir',str(root),'--file',config,'env','lean','--tstack=131072','-j1','-DElab.async=false',str(source)]
    result=runner.run(cmd,root,env,out/'lean.log')
    (out/'command.json').write_text(json.dumps(result,indent=2)+'\n')
    if result['exit']!=0 or result['stop'] is not None: raise SystemExit('API extraction failed; see lean.log')
    with (out/'raw.jsonl').open() as raw:
        rows=[json.loads(line) for line in raw]
    for row in rows: row['axioms']=sorted(row['axioms'])
    rows.sort(key=lambda r:(r['module'],r['name']))
    if len({row['name'] for row in rows})!=len(rows): raise SystemExit('Duplicate declarations')
    modules={m:[] for m in census['frontend_modules']}
    for row in rows: modules[row['module']].append(row)
    manifest=[]
    for mod,data in modules.items():
        canonical=json.dumps(data,sort_keys=True,separators=(',',':'),ensure_ascii=False)+'\n'
        path=out/(mod+'.json');path.write_text(canonical)
        manifest.append({'module':mod,'declarations':len(data),'sha256':sha(path)})
    (out/'module-interface-hashes.json').write_text(json.dumps(manifest,indent=2)+'\n')
    (out/'summary.json').write_text(json.dumps({'modules':len(modules),'declarations':len(rows),
        'axiom_declarations':[r['name'] for r in rows if r['kind']=='axiom'],
        'axioms_used':sorted({a for r in rows for a in r['axioms']}),
        'sorryAx_users':[r['name'] for r in rows if 'sorryAx' in r['axioms']],
        'structural_export_limits':'All imported Frontend constants, including private/generated declarations. Cross-version equivalence must distinguish frozen source declarations from compiler auxiliary names.',
        'measurement_sha256':sha(args.measurement),'census_sha256':sha(args.census)},indent=2)+'\n')
    print('API snapshot:',len(rows),'declarations across',len(modules),'modules')

if __name__=='__main__': main()
