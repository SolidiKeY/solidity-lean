#!/usr/bin/env python3
"""Generate an exact-scope ModuleData inventory with shared structural Expr nodes.

The read-only encoder comes from the testsuite lane and is embedded in the
fixture. No model source, root, registration, statement or budget is changed.
Compiler-only names are retained with unresolved signatures, never excluded.
"""
import argparse
import hashlib
import json
import pathlib
import subprocess
from census import BASE
from dependencies import Tree, closure
from dag_support import ROOT, ENCODER, INPUTS, load, validate_scope


def generate(modules, source_commit=None, toolchain_version="4.24.0", capture_id="control"):
    if source_commit is None:
        source_commit = subprocess.check_output(["git", "rev-parse", "HEAD"], cwd=ROOT, text=True).strip()
    if len(modules) != len(set(modules)):
        raise ValueError('duplicate assigned module')
    pointer_module, pointer_name = {'4.24.0': ('Lean.Meta.Tactic.Grind.ExprPtr', 'Lean.Meta.Grind.ExprPtr'),
                                    '4.35.0': ('Lean.Meta.Sym.ExprPtr', 'Lean.Meta.Sym.ExprPtr')}[toolchain_version]
    header = 'import Lean\nimport ' + pointer_module + '\n' + ''.join('import ' + m + '\n' for m in sorted(modules))
    code = load(ENCODER).LEAN_CODE
    # Native IO traversal only: pointer keys retain strong Expr references.
    # Pointer addresses/IDs never enter the structural fingerprint. Equal but
    # unshared nodes may be emitted twice; the codec hashes identical content.
    if code.count('Std.HashMap ExprStructEq Nat') != 1 or code.count('ExprStructEq.mk e') != 2:
        raise ValueError('unexpected shared encoder memo shape')
    code = code.replace('Std.HashMap ExprStructEq Nat', 'Std.HashMap ' + pointer_name + ' Nat')
    code = code.replace('ExprStructEq.mk e', pointer_name + '.mk e')
    code = code.replace('  owner : String\n', '  owner : String\n  sink : IO.FS.Handle\n')
    code = code.replace('IO.println ("H62-NODE ', 'state.sink.putStrLn ("H62-NODE ')
    body = r'''
open Lean H62Interface in
run_elab do
  let env ← getEnv
  let some output ← IO.getEnv "H62_DAG_OUTPUT"
    | throwError "H62_DAG_OUTPUT required"
  let sink ← IO.FS.Handle.mk output IO.FS.Mode.write
  let progress? ← IO.getEnv "H62_DAG_PROGRESS"
  let requested : Array String := MODULES
  IO.println ("H62-EXAMPLES-HEADER " ++ (Json.mkObj [
    ("schema",toJson "h62-examples-dag-v1"),("base",toJson BASE),
    ("modules",toJson requested),("lean_version",toJson Lean.versionString),
    ("lean_commit",toJson Lean.githash),("source_commit",toJson SOURCE_COMMIT),
    ("capture_id",toJson CAPTURE_ID)]).compress)
  let mut total : Nat := 0
  let mut extras : Nat := 0
  for moduleName in requested do
    if let some progress := progress? then
      IO.FS.writeFile progress (moduleName ++ "\n")
    let some index := env.header.moduleNames.findIdx? (fun name => name.toString == moduleName)
      | throwError "missing original module {moduleName}"
    let data := env.header.moduleData[index]!
    unless data.constNames == data.constants.map (·.name) do
      throwError "kernel name/data mismatch in {moduleName}"
    let entries := data.constants.qsort (fun a b => (nameJson a.name).compress < (nameJson b.name).compress)
    let (_, finalState) ← (show GraphM Unit from do
      for info in entries do
        if info.type.hasMVar || info.type.hasFVar || info.type.hasLooseBVars then
          throw (IO.userError "open declaration type")
        let typeRoot ← emit info.type
        let kind := match info with
          | .axiomInfo _ => "axiom"
          | .defnInfo _ => "definition"
          | .thmInfo _ => "theorem"
          | .opaqueInfo _ => "opaque"
          | .quotInfo _ => "quotient"
          | .inductInfo _ => "inductive"
          | .ctorInfo _ => "constructor"
          | .recInfo _ => "recursor"
        IO.println ("H62-EXAMPLES-DECL " ++ (Json.mkObj [
          ("module",toJson moduleName),("name",toJson info.name.toString),
          ("name_parts",nameJson info.name),("kind",toJson kind),
          ("unsafe",toJson info.isUnsafe),("private_name",toJson (isPrivateName info.name)),
          ("protected_name",toJson (isProtected env info.name)),
          ("level_parameters",toJson (info.levelParams.map nameJson)),
          ("type_root",toJson typeRoot)]).compress)
      ).run {owner := moduleName, sink := sink}
    for name in data.extraConstNames do
      IO.println ("H62-EXAMPLES-EXTRA " ++ (Json.mkObj [
        ("module",toJson moduleName),("name",toJson name.toString),
        ("name_parts",nameJson name),("private_name",toJson (isPrivateName name)),
        ("internal",toJson name.isInternal)]).compress)
    IO.println ("H62-EXAMPLES-MODULE " ++ (Json.mkObj [
      ("module",toJson moduleName),("kernel",toJson entries.size),
      ("compiler_extra",toJson data.extraConstNames.size),
      ("nodes",toJson finalState.next)]).compress)
    total := total + entries.size
    extras := extras + data.extraConstNames.size
  IO.println ("H62-EXAMPLES-COMPLETE " ++ (Json.mkObj [
    ("modules",toJson requested.size),("kernel",toJson total),
    ("compiler_extra",toJson extras)]).compress)
'''
    body = body.replace('IO.println (', 'sink.putStrLn (')
    body += r'''
  sink.flush
  if let some progress := progress? then IO.FS.writeFile progress "complete\n"
  IO.println ("H62-EXAMPLES-SEAL " ++ (Json.mkObj [
    ("capture_id",toJson CAPTURE_ID),("source_commit",toJson SOURCE_COMMIT),
    ("lean_version",toJson Lean.versionString),("lean_commit",toJson Lean.githash),
    ("stream_file",toJson ((System.FilePath.mk output).fileName.getD "")),
    ("modules",toJson requested.size),("kernel",toJson total),
    ("compiler_extra",toJson extras)]).compress)
'''
    body = body.replace('toJson CAPTURE_ID', 'toJson ' + json.dumps(capture_id))
    body = body.replace('MODULES', '#[' + ','.join(json.dumps(m) for m in sorted(modules)) + ']')
    body = body.replace('toJson SOURCE_COMMIT', 'toJson ' + json.dumps(source_commit))
    body = body.replace('toJson BASE', 'toJson ' + json.dumps(BASE))
    return header + code + body


def main():
    p = argparse.ArgumentParser(description=__doc__)
    p.add_argument('--census', type=pathlib.Path, required=True)
    p.add_argument('--stdlib', type=pathlib.Path, required=True)
    p.add_argument('--toolchain-version', choices=('4.24.0','4.35.0'), default='4.24.0')
    p.add_argument('--output', type=pathlib.Path, required=True)
    p.add_argument('--manifest', type=pathlib.Path, required=True)
    a = p.parse_args()
    scope = json.loads(a.census.read_text())
    validate_scope(scope)
    report = closure(ROOT, 'HEAD', a.stdlib)
    modules = sorted(row['module'] for row in scope['modules'])
    actual = {row['module'] for row in report['modules'] if row['module'].startswith('Solidity.Examples.')}
    if actual != set(modules) or report['unresolved_imports']:
        raise ValueError('missing original, extra transitive example, or unresolved import')
    if a.output.resolve().is_relative_to(ROOT) or a.manifest.resolve().is_relative_to(ROOT) or a.output.resolve() == a.manifest.resolve():
        raise ValueError('distinct off-checkout output and manifest required')
    pinned = closure(ROOT, BASE, a.stdlib)
    def blobs(data):
        return sorted((r['module'], r['path'], r['source_sha256']) for r in data['modules'])
    if blobs(pinned) != blobs(report):
        raise ValueError('old inventory source closure differs from frozen base')
    source = generate(modules, report['source_commit'], a.toolchain_version, a.output.stem)
    a.output.write_text(source)
    inputs = INPUTS
    manifest = {'schema_version': 1, 'source_commit': report['source_commit'], 'base': BASE,
                'original_scope_modules': len(modules), 'modules': modules, 'local_closure': report['local_closure'],
                'pinned_closure_equal': True, 'toolchain_version': a.toolchain_version,
                'memo_strategy': 'pointer_identity_for_native_traversal_only; structural content fingerprints unchanged',
                'census_sha256': hashlib.sha256(a.census.read_bytes()).hexdigest(),
                'inputs': [{'repository_path': path, 'sha256': hashlib.sha256((ROOT/path).read_bytes()).hexdigest()} for path in inputs],
                'capture_id': a.output.stem, 'stream_file': a.output.stem + '.jsonl',
                'fixture_file': a.output.name, 'fixture_sha256': hashlib.sha256(source.encode()).hexdigest(),
                'boundary': 'ModuleData kernel declarations plus compiler-extra names. Extra signatures and export accessibility remain unresolved. No H78/new-toolchain compatibility claim.'}
    a.manifest.write_text(json.dumps(manifest, indent=2, sort_keys=True) + '\n')
    print(json.dumps({k:v for k,v in manifest.items() if k not in ('modules','inputs')}))


if __name__ == '__main__':
    main()
