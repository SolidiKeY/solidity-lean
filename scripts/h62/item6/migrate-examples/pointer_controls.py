#!/usr/bin/env python3
"""Generate/check native IO encoder controls; no model claims or proof budgets."""
import argparse
import json
import pathlib
import hashlib
from dag_support import codec, load

CONTROL = r"""
namespace H62PointerControl
open Lean
@[noinline] def freshExpr : IO Expr := do
  let raw ← IO.getEnv "H62_EXAMPLES_PTR_CONTROL"
  let value := (raw.getD "xxx").length
  pure (mkApp (mkConst ``Nat.succ) (toExpr value))
end H62PointerControl
open Lean H62Interface H62PointerControl in
run_elab do
  let some output ← IO.getEnv "H62_CONTROL_OUTPUT"
    | throwError "H62_CONTROL_OUTPUT required"
  let sink ← IO.FS.Handle.mk output IO.FS.Mode.write
  let (_, finalState) ← (show GraphM Unit from do
    let base ← freshExpr
    let a ← emit base
    let copy ← freshExpr
    let b ← emit copy
    let x ← emit (.lam `x (mkConst ``Nat) (.bvar 0) .default)
    let y ← emit (.lam `y (mkConst ``Nat) (.bvar 0) .default)
    let f ← emit (.letE `x (mkConst ``Nat) (toExpr (0 : Nat)) (.bvar 0) false)
    let t ← emit (.letE `x (mkConst ``Nat) (toExpr (0 : Nat)) (.bvar 0) true)
    sink.putStrLn ("H62-POINTER-ROOTS " ++ (Json.mkObj [
      ("base",toJson a),("copy",toJson b),("binder_x",toJson x),
      ("binder_y",toJson y),("let_false",toJson f),("let_true",toJson t)]).compress)
    ).run {owner := "control", sink := sink}
  sink.flush
  IO.println ("H62-POINTER-SEAL " ++ (Json.mkObj [
    ("lean_version",toJson Lean.versionString),("lean_commit",toJson Lean.githash),
    ("control_file",toJson ((System.FilePath.mk output).fileName.getD "")),
    ("nodes",toJson finalState.next)]).compress)
"""


def check(logs, compiler_results, negative_controls=True):
    results={}
    pinned={'old':('4.24.0','797c613eb9b6d4ec95db23e3e00af9ac6657f24b'),
            'new':('4.35.0','eb6cafb7290e8bd5f2937522d8d804f58f02bafc')}
    generator=load('scripts/h62/item6/migrate-examples/generate-dag-inventory.py')
    for label,path in logs.items():
        store=codec.DagStore(['control']);roots=None
        with path.open() as stream:
            for line in stream:
                if line.startswith('H62-NODE '):store.add(json.loads(line[len('H62-NODE '):]))
                if line.startswith('H62-POINTER-ROOTS '):
                    if roots is not None:raise ValueError('DUPLICATE_CONTROL_FOOTER')
                    roots=json.loads(line[len('H62-POINTER-ROOTS '):])
        if roots is None or roots['base']==roots['copy']:
            raise ValueError('INDEPENDENT_RUNTIME_NODES_NOT_EXERCISED')
        hashes={key:store.root('control',value) for key,value in roots.items()}
        if hashes['base']!=hashes['copy'] or hashes['binder_x']==hashes['binder_y'] or hashes['let_false']==hashes['let_true']:
            raise ValueError('STRUCTURAL_FINGERPRINT_CONTROL_FAILED')
        result_path=compiler_results[label]
        compiler=json.loads(result_path.read_text())
        command=compiler.get('command')
        if type(compiler.get('exit')) is not int or compiler['exit']!=0 or compiler.get('stop','missing') is not None or compiler.get('resource_violations')!=[]:
            raise ValueError('CONTROL_COMPILER_FAILED')
        if not isinstance(command,list) or len(command)!=6 or command[:5]!=['lake','env','lean','-j1','--tstack=131072']:
            raise ValueError('INVALID_CONTROL_COMMAND')
        compiler_log=result_path.with_suffix('.log').read_text().splitlines()
        seals=[json.loads(v[len('H62-POINTER-SEAL '):]) for v in compiler_log if v.startswith('H62-POINTER-SEAL ')]
        captures=[json.loads(v[len('H62-EXAMPLES-SEAL '):]) for v in compiler_log if v.startswith('H62-EXAMPLES-SEAL ')]
        version,commit=pinned[label]
        if len(seals)!=1 or seals[0]!={'lean_version':version,'lean_commit':commit,'control_file':path.name,'nodes':len(store.hashes['control'])}:
            raise ValueError('CONTROL_COMPILER_SEAL_MISMATCH')
        if len(captures)!=1 or captures[0].get('lean_version')!=version or captures[0].get('lean_commit')!=commit or any(captures[0].get(f)!=0 for f in ('modules','kernel','compiler_extra')):
            raise ValueError('CONTROL_CAPTURE_PROVENANCE_MISMATCH')
        capture=captures[0]
        expected=generator.generate([],source_commit=capture['source_commit'],toolchain_version=version)+CONTROL
        source=pathlib.Path(command[-1])
        if source.read_text()!=expected:
            raise ValueError('CONTROL_FIXTURE_CHANGED')
        results[label]={'runtime_root_ids':roots,'fingerprints':hashes,'lean_version':version,'lean_commit':commit,
                        'compiler_result_file':result_path.name,'compiler_result_sha256':hashlib.sha256(result_path.read_bytes()).hexdigest(),
                        'control_stream_sha256':hashlib.sha256(path.read_bytes()).hexdigest(),
                        'fixture_sha256':hashlib.sha256(expected.encode()).hexdigest()}
    if results['old']['fingerprints']!=results['new']['fingerprints']:
        raise ValueError('CONTROL_TOOLCHAIN_DIFFERENCE')
    refusals={}
    if negative_controls:
        for label,bad_logs,bad_results in [('old_stream_as_new',{'old':logs['old'],'new':logs['old']},compiler_results),
                                           ('old_result_as_new',logs,{'old':compiler_results['old'],'new':compiler_results['old']})]:
            try:check(bad_logs,bad_results,False)
            except ValueError as error:refusals[label]=str(error)
            else:raise ValueError('CONTROL_PROVENANCE_NEGATIVE_ACCEPTED')
    return {'status':'pass','provenance_negative_controls':refusals,'results':results,'boundary':'Native audit encoding controls, not model migration or semantic proof.'}


def main():
    p=argparse.ArgumentParser(description=__doc__)
    p.add_argument('--generate-version',choices=('4.24.0','4.35.0'))
    p.add_argument('--output',type=pathlib.Path,required=True)
    p.add_argument('--old-log',type=pathlib.Path)
    p.add_argument('--new-log',type=pathlib.Path)
    p.add_argument('--old-result',type=pathlib.Path)
    p.add_argument('--new-result',type=pathlib.Path)
    a=p.parse_args()
    if a.generate_version:
        generator=load('scripts/h62/item6/migrate-examples/generate-dag-inventory.py')
        a.output.write_text(generator.generate([],toolchain_version=a.generate_version)+CONTROL)
    else:
        if any(v is None for v in (a.old_log,a.new_log,a.old_result,a.new_result)):p.error('old/new streams and compiler results required')
        result=check({'old':a.old_log,'new':a.new_log},{'old':a.old_result,'new':a.new_result})
        a.output.write_text(json.dumps(result,indent=2)+'\n')
        print('POINTER-CONTROLS PASS: distinct runtime nodes; sharing-independent fingerprints; binder/let flags retained; both versions equal')


if __name__=='__main__':main()
