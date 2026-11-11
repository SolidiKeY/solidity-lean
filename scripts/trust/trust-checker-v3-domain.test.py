#!/usr/bin/env python3
"""H537 additive metadata audit; never kernel replay or A04 acceptance.

Guards omitted/filtered declarations, wrong ordered-set comparisons, stale or
unlisted objects, changed native helpers and renewed one-shot allowances.
--materialize writes ONLY the adjacent isolated DomainControls module below.
--prepare snapshots fresh Lake-selected objects, sources and the full sysroot
object/IR inventory; this creates inputs, never comparison/validation credit.
--compare repeats every mandatory hash before and after import/comparison in
ONE TOTAL300s budget under the external serial/no-swap/memory/pidfd guard.
The fixed H537 admission marker in this lane Git common directory forbids
renewing the attempt through a different binding/output directory.
Frozen v1/v2/v3 bodies, Main and every kernel path remain untouched.
"""
if not __debug__:
    raise SystemExit('optimized Python refused')
import argparse
import hashlib
import importlib.util
import json
import os
from pathlib import Path
import subprocess
import sys
import time
import unittest
from unittest.mock import patch
import tempfile
import shutil

HERE = Path(__file__).resolve().parent
SOURCE_ROOT = HERE.parents[1].resolve()
SCRIPT = 'scripts/trust/trust-checker-v3-domain.test.py'
MODULE = 'Lean4Checker/FusedDepsV3DomainControls.lean'
BASE = 'da26eb05e9959402afcb9bd6dfe5dc4f700f70d6'
TOOLCHAIN = 'leanprover/lean4:v4.24.0'
REFERENCE_SHA = '623c5ca18746942891869f169b90a665ac66ba4f6dac1edcbe251fff7cc0d0b4'
FROZEN_PACKAGE = {
 'trust-checker-v3.patch': 'c5a848c591d1758a6bd86d9297fc20aa8356e7f87333d06f5affc31903f05fd8',
 'trust-recheck-v3.py': 'b32656f97fe645c3ae039069af7fa5e56ceff7df0978b4add4a3d14d85e77012',
 'trust-checker-v3.test.py': '43b3cf9772b211de8b1414308047cde3de25399998d61dc03dc427e7cd39b28f',
}
HELPER_OLEAN_SHA = '7b7d830dfd8580287d9b992cc9cb88525e53b5de2958f6f0fc833cd7511fbe64'
DOMAIN_SOURCE = r'''/-
Copyright (c) 2026. Released under Apache 2.0 license; see LICENSE.
-/
import Lean.Environment
import Lean.Util.Path
import Lean.Data.Json
import Lean4Checker.FusedDepsV3

namespace Lean.Environment.Replay'.FusedDepsV3DomainControls

/-- Guards array-order regressions: compare actual NameSet ForIn order. -/
def orderedNames (deps : NameSet) : Array Name := Id.run do
  let mut names := #[]
  for name in deps do names := names.push name
  return names

def kindIndex : ConstantInfo → Nat
  | .axiomInfo _ => 0 | .defnInfo _ => 1 | .thmInfo _ => 2 | .opaqueInfo _ => 3
  | .quotInfo _ => 4 | .inductInfo _ => 5 | .ctorInfo _ => 6 | .recInfo _ => 7

structure Counts where
  expected : Nat := 0
  compared : Nat := 0
  mismatches : Nat := 0
  keyMismatches : Nat := 0
  duplicateKeys : Nat := 0
  unsafeEntries : Nat := 0
  partialEntries : Nat := 0
  kinds : Array Nat := Array.replicate 8 0
  deriving Inhabited

def emit (fields : List (String × Json)) : IO Unit :=
  IO.println (Json.mkObj fields).compress

/-- Every entry is compared, including unsafe/partial/opaque and both SMap
stores. No kernel replay/filter/proof submission occurs. Mismatch records are
streamed without a sampling limit; a failed/incomplete run is never agreement. -/
def auditEntries (entries : List (Name × ConstantInfo)) : IO Counts := do
  let mut counts : Counts := { expected := entries.length }
  let mut seen : NameHashSet := {}
  for (key, ci) in entries do
    let original := orderedNames ci.getUsedConstantsAsSet
    let fused := orderedNames (getUsedConstantsFusedV3 ci)
    let same := original == fused
    counts := { counts with
      compared := counts.compared + 1
      mismatches := counts.mismatches + (if same then 0 else 1)
      keyMismatches := counts.keyMismatches + (if key == ci.name then 0 else 1)
      duplicateKeys := counts.duplicateKeys + (if seen.contains key then 1 else 0)
      unsafeEntries := counts.unsafeEntries + (if ci.isUnsafe then 1 else 0)
      partialEntries := counts.partialEntries + (if ci.isPartial then 1 else 0)
      kinds := counts.kinds.modify (kindIndex ci) (· + 1) }
    seen := seen.insert key
    unless same do
      emit [("event", toJson "mismatch"), ("name", toJson key.toString),
        ("kind", toJson (kindIndex ci)),
        ("original", toJson (original.map Name.toString)),
        ("v3", toJson (fused.map Name.toString))]
  return counts

def emitSummary (counts : Counts) : IO Unit :=
  emit [("event", toJson "summary"), ("expected", toJson counts.expected),
    ("compared", toJson counts.compared), ("mismatches", toJson counts.mismatches),
    ("keyMismatches", toJson counts.keyMismatches), ("duplicateKeys", toJson counts.duplicateKeys),
    ("unsafeEntries", toJson counts.unsafeEntries), ("partialEntries", toJson counts.partialEntries),
    ("kinds", toJson counts.kinds), ("kernelReplay", toJson false), ("a04Accepted", toJson false)]

/-- Guards missing rows/filters and logical-empty-fallback vacuity before any
public import: independently expect nonempty names for opaque, unsafe and
partial metadata. A bad map key is reported, not silently omitted. -/
def runSynthetic (announce : Bool := true) : IO Unit := do
  let type := Expr.const `independentType []
  let value := Expr.const `independentValue []
  let opaqueCi : ConstantInfo := .opaqueInfo { name := `opaqueFixture, levelParams := [], type := type, value := value, isUnsafe := true }
  let partialCi : ConstantInfo := .defnInfo { name := `partialFixture, levelParams := [], type := type, value := value, hints := .opaque, safety := .partial }
  let expected := orderedNames (NameSet.ofList [`independentType, `independentValue])
  for ci in [opaqueCi, partialCi] do
    unless orderedNames ci.getUsedConstantsAsSet == expected && orderedNames (getUsedConstantsFusedV3 ci) == expected do
      throw <| IO.userError "native nonempty oracle failed"
  let counts ← auditEntries [(opaqueCi.name, opaqueCi), (partialCi.name, partialCi)]
  unless counts.expected == 2 && counts.compared == 2 && counts.mismatches == 0 &&
      counts.unsafeEntries == 1 && counts.partialEntries == 1 && counts.keyMismatches == 0 do
    throw <| IO.userError "metadata denominator/filter control failed"
  let bad ← auditEntries [(`wrongKey, opaqueCi), (`wrongKey, partialCi)]
  unless bad.compared == 2 && bad.keyMismatches == 2 && bad.duplicateKeys == 1 do
    throw <| IO.userError "invalid-key/duplicate control failed"
  if announce then
    IO.println "H537_SYNTHETIC_PASS nonempty opaque/unsafe/partial; full denominator; bad keys reported; no public import or replay"

/-- Exactly one full root import in the admitted external TOTAL300s guard.
Matches the original checker's private-level, loadExts=false import, but does
not create an empty kernel or call any replay/addDecl/checker executable. -/
def comparePublic (rootsFile : System.FilePath) : IO UInt32 := do
  runSynthetic false
  emit [("event", toJson "native_oracle"), ("nonempty", toJson true), ("cases", toJson (2 : Nat))]
  initSearchPath (← findSysroot)
  let env ← Lean.importModules #[{ module := `Solidity.Theorems }] {} (loadExts := false)
  for moduleName in env.allImportedModuleNames do
    let object ← findOLean moduleName
    emit [("event", toJson "module"), ("name", toJson moduleName.toString),
      ("object", toJson object.toString)]
  let roots := (← IO.FS.readFile rootsFile).splitOn "\n" |>.filter (!·.isEmpty)
  unless !roots.isEmpty do throw <| IO.userError "nonempty public-root witnesses required"
  let missing := roots.filter fun root => !env.contains root.toName
  emit [("event", toJson "witnesses"), ("expected", toJson roots.length),
    ("missing", toJson missing)]
  let entries := env.constants.toList
  emit [("event", toJson "domain"), ("entries", toJson entries.length),
    ("stage1Entries", toJson env.constants.map₁.size),
    ("moduleCount", toJson env.allImportedModuleNames.size),
    ("root", toJson "Solidity.Theorems"), ("loadExts", toJson false)]
  let counts ← auditEntries entries
  emitSummary counts
  return if counts.expected > 0 && counts.expected == counts.compared &&
    counts.mismatches == 0 && counts.keyMismatches == 0 && counts.duplicateKeys == 0 && missing.isEmpty then 0 else 2

end Lean.Environment.Replay'.FusedDepsV3DomainControls

def main (args : List String) : IO UInt32 := do
  match args with
  | ["--synthetic"] => Lean.Environment.Replay'.FusedDepsV3DomainControls.runSynthetic; return 0
  | ["--compare", rootsFile] => Lean.Environment.Replay'.FusedDepsV3DomainControls.comparePublic rootsFile
  | _ => throw <| IO.userError "explicit --synthetic or reviewed --compare required; no replay mode"
'''


def raw_sha(path):
    return hashlib.sha256(Path(path).read_bytes()).hexdigest()


def load_module(name, path, expected):
    if raw_sha(path) != expected: raise ValueError('frozen utility changed: ' + str(path))
    spec = importlib.util.spec_from_file_location(name, path)
    module = importlib.util.module_from_spec(spec)
    sys.modules[name] = module
    spec.loader.exec_module(module)
    return module


V = load_module('h537_frozen_v3', HERE / 'trust-recheck-v3.py', FROZEN_PACKAGE['trust-recheck-v3.py'])
R = load_module('h537_reference_primitives', HERE.parent / 'trust-replay/recipe.py', REFERENCE_SHA)
# No R.run or checker invocation is used; only deadline/hash/JSON/process primitives.


def check_frozen(checker, deadline, added=True):
    checker = Path(checker).resolve()
    R.require(checker == (SOURCE_ROOT / '.lake/trust-checker-v3-va1-fused').resolve(), 'reserved generated checker path required')
    for name, expected in FROZEN_PACKAGE.items():
        R.require(R.digest(HERE / name, deadline) == expected, 'frozen v3 package changed')
    for name, expected in V.SOURCES.items():
        R.require(R.digest(checker / name, deadline) == expected, 'frozen checker body changed: ' + name)
    if added:
        R.require((checker / MODULE).read_bytes() == DOMAIN_SOURCE.encode(), 'audit source differs from committed generator')
        R.require(not R.small(['git', '--no-replace-objects', 'status', '--porcelain'], checker, deadline), 'dirty audit source checkout')
        changed = R.small(['git', '--no-replace-objects', 'diff', '--name-only', BASE, 'HEAD'], checker, deadline)
        R.require(set(changed.splitlines()) == set(V.SOURCES) | {MODULE}, 'unexpected checker source set')
        R.small(['git', '--no-replace-objects', 'merge-base', '--is-ancestor', BASE, 'HEAD'], checker, deadline)
    return R.small(['git', '--no-replace-objects', 'rev-parse', 'HEAD'], checker, deadline)


def materialize(checker):
    checker = Path(checker).resolve()
    check_frozen(checker, R.clock() + 30, added=False)
    target = checker / MODULE
    if target.exists():
        R.require(target.read_bytes() == DOMAIN_SOURCE.encode(), 'refusing to overwrite a different audit module')
    else:
        with target.open('x') as out: out.write(DOMAIN_SOURCE)
    print(target)


def object_files(root):
    """Inventory is a superset for sysroot; runtime module paths must be bound."""
    return sorted(p for p in Path(root).rglob('*') if p.is_file() and
                  (p.name.endswith(('.olean', '.olean.private', '.olean.server', '.ir'))))


def rows(paths, deadline):
    return [{'path': str(p.resolve()), 'bytes': p.stat().st_size,
             'sha256': R.digest(p, deadline)} for p in sorted(set(map(Path, paths)))]


def check_rows(items, deadline):
    R.require(isinstance(items, list) and items, 'nonempty hash inventory required')
    seen = set()
    for row in items:
        R.remaining(deadline)
        R.require(set(row) == {'path', 'bytes', 'sha256'} and isinstance(row['path'], str), 'invalid hash row')
        path = Path(row['path'])
        R.require(path.is_absolute() and str(path) not in seen and type(row['bytes']) is int and row['bytes'] >= 0,
                  'duplicate/invalid hash identity')
        seen.add(str(path))
        R.require(path.stat().st_size == row['bytes'] and R.digest(path, deadline) == row['sha256'], 'input hash mismatch: ' + str(path))
    return seen


def fresh_graph(source, deadline):
    js = "import {freshArtifactGraph} from './scripts/trust/trust-artifacts.mjs'; console.log(JSON.stringify(freshArtifactGraph('Solidity.Theorems')));"
    return json.loads(R.small(['node', '--input-type=module', '-e', js], source, deadline))


def helper_files(checker):
    paths = object_files(Path(checker) / '.lake/build/lib/lean')
    for path in paths:
        relative = path.relative_to(Path(checker) / '.lake/build/lib/lean').as_posix()
        R.require(relative.startswith(('Lean4Checker/', 'Lean4CheckerTests/')) or relative.startswith('Main.'),
                  'helper search path could shadow public/sysroot modules')
    return paths


def source_context(source, deadline):
    head = R.small(['git', '--no-replace-objects', 'rev-parse', 'HEAD'], source, deadline)
    R.require(not R.small(['git', '--no-replace-objects', 'status', '--porcelain'], source, deadline), 'dirty public source checkout')
    R.require((source / 'lean-toolchain').read_text().strip() == TOOLCHAIN, 'wrong source toolchain')
    return head, R.lake_context(source, head, deadline)


def authority_marker(source, deadline):
    source = Path(source).resolve()
    R.require(source == SOURCE_ROOT, 'H537 authority is fixed to the executing lane checkout')
    common = Path(R.small(['git', '--no-replace-objects', 'rev-parse', '--git-common-dir'], source, deadline))
    if not common.is_absolute(): common = source / common
    return common.resolve() / 'va1-trust-H537-metadata-attempt.json'


def selector_roles(sysroot):
    roles = {'python': str(Path(sys.executable).resolve())}
    for name in ('lean', 'lake', 'node', 'timeout'):
        selected = shutil.which(name)
        R.require(selected is not None, 'missing runtime selector: ' + name)
        roles[name] = str(Path(selected).resolve())
    for name in ('lean', 'lake'):
        R.require(roles[name] == str((Path(sysroot) / 'bin' / name).resolve()), 'tool selector differs from pinned prefix')
    return roles


def validate_selectors(data, sysroot, deadline):
    current = selector_roles(sysroot)
    R.require(current == data['selectors'], 'active Python/Lean/Lake/Node/timeout selector changed')
    bound = {row['path']: row['sha256'] for row in data['tool_files']}
    for path in current.values():
        R.require(path in bound and R.digest(Path(path), deadline) == bound[path], 'active tool is not bound')


def prepare(source, checker, sysroot, binding):
    """Produce the exact proposed inputs. All hashes are repeated in --compare."""
    source, checker, sysroot, binding = map(lambda p: Path(p).resolve(), (source, checker, sysroot, binding))
    R.require(os.environ.get('TRUST_H537_METADATA') == '1', 'H537 preparation opt-in required')
    deadline = R.clock() + 300
    marker = authority_marker(source, deadline)
    R.require(not binding.exists() and not marker.exists(), 'fresh binding/unused H537 authority required')
    head, context = source_context(source, deadline)
    revision = check_frozen(checker, deadline)
    R.require(R.digest(checker / '.lake/build/lib/lean/Lean4Checker/FusedDepsV3.olean', deadline) == HELPER_OLEAN_SHA, 'unreviewed compiled helper')
    graph = fresh_graph(source, deadline)
    binding.parent.mkdir(parents=True, exist_ok=True)
    # Use the existing committed staging implementation, not traces or fallback paths.
    js = "import {makeReplayInputs} from './scripts/trust/trust-replay-inputs.mjs'; const x=JSON.parse(process.argv[1]); console.log(JSON.stringify(makeReplayInputs(x)));"
    objects = source / '.lake/refactor-cache' / ('h537-inputs-' + str(time.time_ns()))
    config = dict(imports=graph['imports'], destination=str(objects), head=head,
                  provenance=dict(setupOrigin=graph['origin'], setupSha256=graph['querySha256'],
                                  rootSourceSha256=R.digest(source / 'Solidity/Theorems.lean', deadline)))
    manifest = json.loads(R.small(['node', '--input-type=module', '-e', js, json.dumps(config)], source, deadline))
    root_baseline = source / 'scripts/trust/trust-closure-baseline.json'
    roots = json.loads(root_baseline.read_text())['roots']
    R.require(isinstance(roots, list) and roots and len(roots) == len(set(roots)), 'invalid public witness roots')
    roots_file = binding.parent / 'public-roots.txt'
    R.require(not roots_file.exists(), 'fresh root witness input required')
    roots_file.write_text(''.join(name + '\n' for name in roots))
    project_sources = [source / (name.replace('.', '/') + '.lean') for name in graph['imports']]
    R.require(all(p.is_file() for p in project_sources), 'unresolved project source identity')
    source_files = project_sources + [source / SCRIPT, root_baseline, source / 'lean-toolchain',
        source / 'scripts/trust/trust-artifacts.mjs', source / 'scripts/trust/trust-replay-inputs.mjs',
        roots_file, *[HERE / name for name in FROZEN_PACKAGE], HERE.parent / 'trust-replay/recipe.py']
    sys_objects = object_files(sysroot / 'lib/lean')
    # Pin native runtime libraries as well as all serialized/IR toolchain inputs.
    libraries = sorted((sysroot / 'lib/lean').glob('*.so'))
    tool_files = [sysroot / 'bin/lean', sysroot / 'bin/lake', *libraries,
                  Path(sys.executable).resolve(), Path(shutil.which('node')).resolve(),
                  Path(shutil.which('timeout')).resolve()]
    for executable in (sysroot / 'bin/lean', sysroot / 'bin/lake', Path(sys.executable).resolve()):
        dependencies = R.small(['ldd', str(executable)], source, deadline)
        for token in dependencies.split():
            if token.startswith('/') and Path(token).is_file(): tool_files.append(Path(token).resolve())
    tool_sources = list((sysroot / 'src/lean').rglob('*.lean'))
    sources = [checker / name for name in V.SOURCES] + [checker / MODULE, checker / 'lean-toolchain']
    data = dict(schema=1, authority='H537', root='Solidity.Theorems', source=str(source), checker=str(checker),
        sysroot=str(sysroot), objects=str(objects), manifest_path=str(objects / 'MANIFEST.json'),
        manifest_sha256=R.digest(objects / 'MANIFEST.json', deadline), source_head=head, checker_head=revision,
        lake_context=context, selected_imports=graph['imports'], setup_sha256=graph['querySha256'],
        roots_file=str(roots_file), public_roots=roots, one_shot_path=str(marker), selectors=selector_roles(sysroot),
        source_files=rows(source_files, deadline), checker_sources=rows(sources, deadline),
        helper_objects=rows(helper_files(checker), deadline), sysroot_objects=rows(sys_objects, deadline),
        tool_files=rows(tool_files, deadline), tool_sources=rows(tool_sources, deadline),
        runner_sha256=R.digest(Path(__file__).resolve(), deadline),
        object_count=len(manifest['files']), object_bytes=sum(row['bytes'] for row in manifest['files']))
    binding.write_text(json.dumps(data, indent=2) + '\n')
    print(json.dumps({'binding': str(binding), 'sha256': raw_sha(binding), 'project_objects': data['object_count'],
                      'sysroot_objects_and_ir': len(sys_objects), 'boundary': 'prepared inputs only; no public import/comparison/validation credit'}))


def validate_binding(data, deadline):
    R.require(type(data['schema']) is int and data['schema'] == 1 and data['authority'] == 'H537' and
              data['root'] == 'Solidity.Theorems', 'wrong metadata authority/root/schema')
    source, checker, sysroot = (Path(data[k]) for k in ('source', 'checker', 'sysroot'))
    R.require(source_context(source, deadline) == (data['source_head'], data['lake_context']), 'source/Lake context drift')
    R.require(check_frozen(checker, deadline) == data['checker_head'], 'audit revision changed')
    R.require(R.digest(checker / '.lake/build/lib/lean/Lean4Checker/FusedDepsV3.olean', deadline) == HELPER_OLEAN_SHA, 'compiled v3 helper identity differs')
    R.require(R.digest(Path(__file__).resolve(), deadline) == data['runner_sha256'] ==
              R.digest(source / SCRIPT, deadline), 'executing runner identity differs')
    roots = json.loads((source / 'scripts/trust/trust-closure-baseline.json').read_text())['roots']
    R.require(roots == data['public_roots'] and roots and len(roots) == len(set(roots)) and
              Path(data['roots_file']).read_text() == ''.join(name + '\n' for name in roots), 'public witnesses changed')
    expected_sources = [source / (name.replace('.', '/') + '.lean') for name in data['selected_imports']]
    expected_sources += [source / SCRIPT, source / 'scripts/trust/trust-closure-baseline.json', source / 'lean-toolchain',
        source / 'scripts/trust/trust-artifacts.mjs', source / 'scripts/trust/trust-replay-inputs.mjs',
        Path(data['roots_file']), *[HERE / name for name in FROZEN_PACKAGE], HERE.parent / 'trust-replay/recipe.py']
    R.require({str(p.resolve()) for p in expected_sources} == {row['path'] for row in data['source_files']}, 'source identity inventory omitted/extended')
    expected_checker = [checker / name for name in V.SOURCES] + [checker / MODULE, checker / 'lean-toolchain']
    R.require({str(p.resolve()) for p in expected_checker} == {row['path'] for row in data['checker_sources']}, 'checker identity inventory omitted/extended')
    R.require(data['one_shot_path'] == str(authority_marker(source, deadline)), 'H537 authority marker moved')
    validate_selectors(data, sysroot, deadline)
    for name in ('source_files', 'checker_sources', 'helper_objects', 'sysroot_objects', 'tool_files', 'tool_sources'):
        check_rows(data[name], deadline)
    for key, current in [('helper_objects', helper_files(checker)), ('sysroot_objects', object_files(sysroot / 'lib/lean'))]:
        R.require({str(p.resolve()) for p in current} == {row['path'] for row in data[key]}, 'extra/omitted runtime object inventory')
    tool_paths = {row['path'] for row in data['tool_files']}
    for name, expected in V.TOOLS.items():
        R.require(R.digest(sysroot / 'bin' / name, deadline) == expected and
                  str((sysroot / 'bin' / name).resolve()) in tool_paths and
                  R.digest(Path(shutil.which(name)).resolve(), deadline) == expected, 'pinned tool selector/binary mismatch')
    R.require({str(p.resolve()) for p in (sysroot / 'src/lean').rglob('*.lean')} ==
              {row['path'] for row in data['tool_sources']}, 'toolchain source inventory omitted/extended')
    R.require(R.small([str(sysroot / 'bin/lean'), '--print-prefix'], source, deadline) == str(sysroot), 'active sysroot mismatch')
    graph = fresh_graph(source, deadline)
    R.require(graph['imports'] == data['selected_imports'], 'current selected import graph changed')
    manifest_path, objects = Path(data['manifest_path']), Path(data['objects'])
    manifest = R.load_json(manifest_path, data['manifest_sha256'], deadline)
    R.require(type(manifest['schema']) is int and manifest['schema'] == 1 and manifest['scope'] == R.SCOPE and
              manifest['head'] == data['source_head'] and manifest['root'] == data['root'] and
              manifest['provenance']['setupOrigin'] == graph['origin'] and
              manifest['provenance']['setupSha256'] == data['setup_sha256'], 'object manifest identity/scope mismatch')
    R.require(len(manifest['files']) == data['object_count'] and sum(row['bytes'] for row in manifest['files']) == data['object_bytes'], 'object denominator changed')
    selected_objects = {}
    for name, paths in graph['imports'].items():
        for original in paths:
            extension = next((ext for ext in ('.olean.private', '.olean.server', '.olean') if original.endswith(ext)), None)
            R.require(extension is not None, 'invalid selected artifact extension')
            key = name.replace('.', '/') + extension
            R.require(key not in selected_objects, 'duplicate selected object')
            selected_objects[key] = str(Path(original).resolve())
    R.require(set(selected_objects) == {row['path'] for row in manifest['files']}, 'selected object omitted/extended')
    expected = {str(manifest_path.resolve())}
    for row in manifest['files']:
        R.require(str(Path(row['source']).resolve()) == selected_objects[row['path']] and
                  R.digest(Path(row['source']), deadline) == row['sha256'], 'overlay differs from current selected artifact')
        path = objects / row['path']
        R.require(path.is_relative_to(objects) and '..' not in Path(row['path']).parts and not Path(row['path']).is_absolute(), 'unsafe object path')
        expected.add(str(path.resolve()))
        R.require(path.stat().st_size == row['bytes'] and R.digest(path, deadline) == row['sha256'], 'public object changed')
    actual = set()
    for path in objects.rglob('*'):
        R.remaining(deadline)
        R.require(not path.is_symlink(), 'symlink in public object tree')
        if path.is_file(): actual.add(str(path.resolve()))
        else: R.require(path.is_dir(), 'special public object node')
    R.require(actual == expected and len(expected) == len(manifest['files']) + 1, 'unlisted/duplicate/omitted public objects')
    return manifest


def evaluate_output(log, data, manifest):
    modules, domain, summary, witnesses, oracles = {}, [], [], [], []
    mismatch_rows = 0
    for line in Path(log).read_text().splitlines():
        row = json.loads(line, object_pairs_hook=R.unique_object)
        event = row.get('event')
        if event == 'native_oracle': oracles.append(row)
        elif event == 'module':
            R.require(row['name'] not in modules, 'duplicate module event')
            modules[row['name']] = str(Path(row['object']).resolve())
        elif event == 'domain': domain.append(row)
        elif event == 'summary': summary.append(row)
        elif event == 'witnesses': witnesses.append(row)
        elif event == 'mismatch': mismatch_rows += 1
        else: raise R.InvalidInput('unexpected audit output')
    R.require(len(domain) == len(summary) == len(witnesses) == len(oracles) == 1, 'incomplete/duplicate audit summary')
    R.require(oracles[0].get('nonempty') is True and oracles[0].get('cases') == 2, 'fresh nonempty native oracle absent')
    d, s, w = domain[0], summary[0], witnesses[0]
    for key in ('expected', 'compared', 'mismatches', 'keyMismatches', 'duplicateKeys', 'unsafeEntries', 'partialEntries'):
        R.require(type(s[key]) is int and s[key] >= 0, 'invalid audit count')
    R.require(s['expected'] > 0 and s['expected'] == s['compared'] == d['entries'] and
              len(s['kinds']) == 8 and all(type(n) is int and n >= 0 for n in s['kinds']) and
              sum(s['kinds']) == s['compared'], 'incomplete ConstantInfo denominator')
    R.require(d['root'] == data['root'] and d['moduleCount'] == len(modules) and d['loadExts'] is False and
              s['kernelReplay'] is False and s['a04Accepted'] is False, 'wrong import/control boundary')
    R.require(w['expected'] == len(data['public_roots']) and w['missing'] == [], 'public headline roots absent')
    bound = {row['path'] for row in data['sysroot_objects']}
    bound.update(str((Path(data['objects']) / row['path']).resolve()) for row in manifest['files'])
    R.require(set(modules.values()) <= bound and data['root'] in modules, 'unbound runtime imported object')
    R.require(set(modules) & set(data['selected_imports']) == set(data['selected_imports']), 'selected project module omitted')
    R.require(s['mismatches'] == mismatch_rows, 'mismatch output count differs')
    R.require(s['mismatches'] == s['keyMismatches'] == s['duplicateKeys'] == 0, 'metadata correspondence mismatch')
    return {'modules': len(modules), **s}


def admit(path, binding_sha):
    with Path(path).open('x') as out:
        json.dump({'authority': 'H537', 'binding_sha256': binding_sha, 'attempted': True,
                   'kernel_replay': False, 'admitted_at_boottime': R.clock()}, out)
        out.flush(); os.fsync(out.fileno())
    directory = os.open(Path(path).parent, os.O_RDONLY | os.O_DIRECTORY)
    try: os.fsync(directory)
    finally: os.close(directory)


def compare(binding, expected, review, review_sha, output):
    start = R.clock(); deadline = start + 300
    V.check_guards()
    R.require(os.environ.get('TRUST_H537_METADATA') == '1', 'H537 public metadata opt-in required')
    data = R.load_json(binding, expected, deadline)
    approved = R.load_json(review, review_sha, deadline)
    R.require(approved['authority'] == 'H537' and approved['binding_sha256'] == expected and
              all(approved[k] == 'PASS' for k in ('owner', 'finder', 'skeptic')), 'bound owner/finder/skeptic review required')
    marker = Path(data['one_shot_path'])
    R.require(marker == authority_marker(Path(data['source']), deadline), 'authority-wide one-shot marker location changed')
    output = Path(output).resolve()
    for protected in (Path(data['source']), Path(data['checker']), Path(data['sysroot']), Path(data['objects'])):
        R.require(not output.is_relative_to(protected) and not protected.is_relative_to(output), 'output overlaps inputs')
    R.require(not output.exists(), 'fresh private output required')
    # Admission consumes H537 even if validation, import or posthashing fails.
    admit(marker, expected)
    output.mkdir(parents=True)
    receipt = dict(authority='H537', binding_sha256=expected, source_head=data['source_head'],
                   checker_head=data['checker_head'], total_budget_seconds=300,
                   metadata_process_started=False, metadata_agreement_pass=False,
                   kernel_replay=False, checker_executed=False, a04_accepted=False)
    code = 2
    try:
        manifest = validate_binding(data, deadline)
        sysroot, checker = Path(data['sysroot']), Path(data['checker'])
        env = dict(os.environ, LEAN_NUM_THREADS='1', LEAN_SYSROOT=str(sysroot),
                   LEAN_PATH=str(checker / '.lake/build/lib/lean') + os.pathsep + data['objects'])
        env.pop('LEAN_SRC_PATH', None)
        command = [str(sysroot / 'bin/lean'), '-j1', '--run', str(checker / MODULE), '--compare', data['roots_file']]
        receipt['command'] = command; receipt['metadata_process_started'] = True
        with (output / 'audit.jsonl').open('wb') as log:
            code = R.process(command, Path(data['source']), env, deadline, log)
        receipt['metadata_exit_code'] = code
        if code == 0:
            receipt['comparison'] = evaluate_output(output / 'audit.jsonl', data, manifest)
            validate_binding(data, deadline)
            R.load_json(binding, expected, deadline); R.load_json(review, review_sha, deadline)
            R.remaining(deadline)
            receipt['metadata_agreement_pass'] = True
    except (R.Deadline, subprocess.TimeoutExpired) as error:
        code = 124; receipt['error'] = str(error)
    except (R.InvalidInput, OSError, ValueError, KeyError, TypeError) as error:
        code = 2; receipt['error'] = str(error)
    receipt.update(exit_code=code, elapsed_seconds=R.clock() - start)
    (output / 'receipt.json').write_text(json.dumps(receipt, indent=2) + '\n')
    return code


def synthetic(checker, sysroot):
    V.check_guards()
    deadline = R.clock() + 300
    check_frozen(checker, deadline)
    command = [str(sysroot / 'bin/lean'), '-j1', '--run', str(checker / MODULE), '--synthetic']
    env = dict(os.environ, LEAN_NUM_THREADS='1', LEAN_SYSROOT=str(sysroot),
               LEAN_PATH=str(checker / '.lake/build/lib/lean'))
    env.pop('LEAN_SRC_PATH', None)
    result = subprocess.run(command, cwd=checker, env=env, capture_output=True, text=True,
                            timeout=R.remaining(deadline))
    R.require(result.returncode == 0, 'synthetic metadata failed: ' + result.stdout[-2000:] + result.stderr[-2000:])
    R.remaining(deadline)
    print(result.stdout, end='')


class RefusalControls(unittest.TestCase):
    def test_one_authority_across_distinct_binding_directories(self):
        with tempfile.TemporaryDirectory() as directory:
            root = Path(directory).resolve(); common = root / 'common-git'; common.mkdir()
            first = root / 'packet-a'; second = root / 'packet-b'; first.mkdir(); second.mkdir()
            with patch.dict(globals(), SOURCE_ROOT=root), patch.object(R, 'small', return_value=str(common)):
                marker1 = authority_marker(root, R.clock()+5)
                marker2 = authority_marker(root, R.clock()+5)
                self.assertNotEqual(first,second); self.assertEqual(marker1,marker2)
                admit(marker1, 'a' * 64)
                with self.assertRaises(FileExistsError): admit(marker2, 'b' * 64)
                self.assertEqual(json.loads(marker1.read_text())['binding_sha256'], 'a' * 64)
                with self.assertRaises(R.InvalidInput): authority_marker(second, R.clock()+5)

    def test_active_tool_selectors_are_bound(self):
        with tempfile.TemporaryDirectory() as directory:
            target = Path(directory) / 'tool';target.write_bytes(b'tool')
            selected = {name:str(target) for name in ('python','node','timeout','lean','lake')}
            data={'selectors':selected, 'tool_files':rows([target],R.clock()+5)}
            with patch.object(sys.modules[__name__], 'selector_roles', return_value=selected):
                validate_selectors(data,Path(directory),R.clock()+5)
            for name in ('python','node','timeout','lean','lake'):
                moved=dict(selected,**{name:str(target)+'-unbound'})
                with self.subTest(name=name),patch.object(sys.modules[__name__],'selector_roles',return_value=moved):
                    with self.assertRaises(R.InvalidInput):validate_selectors(data,Path(directory),R.clock()+5)

    def test_synthetic_uses_only_helper_search_path(self):
        from types import SimpleNamespace
        with patch.object(V,'check_guards'),patch.object(sys.modules[__name__],'check_frozen'), \
             patch.object(subprocess,'run',return_value=SimpleNamespace(returncode=0,stdout='synthetic fixture\n',stderr='')) as run:
            synthetic(Path('/fixture/checker'),Path('/fixture/sysroot'))
            env=run.call_args.kwargs['env']
            self.assertEqual(env['LEAN_PATH'],'/fixture/checker/.lake/build/lib/lean')
            self.assertEqual(env['LEAN_SYSROOT'],'/fixture/sysroot')
            self.assertEqual(run.call_args.args[0][-1],'--synthetic')

    def test_changed_and_duplicate_hash_rows_are_refused(self):
        with tempfile.TemporaryDirectory() as directory:
            p = Path(directory) / 'input';p.write_bytes(b'fixture')
            items = rows([p], R.clock() + 5)
            check_rows(items, R.clock() + 5)
            with self.assertRaises(R.InvalidInput): check_rows(items + items, R.clock() + 5)
            p.write_bytes(b'changed')
            with self.assertRaises(R.InvalidInput): check_rows(items, R.clock() + 5)

    def test_duplicate_json_is_refused(self):
        with tempfile.TemporaryDirectory() as directory:
            p = Path(directory) / 'binding';p.write_text('{"schema":1,"schema":1}')
            with self.assertRaises(R.InvalidInput): R.load_json(p, raw_sha(p), R.clock() + 5)

    def test_denominator_and_boundary_refusals(self):
        with tempfile.TemporaryDirectory() as directory:
            root = Path(directory);obj=root/'Public.olean';obj.write_bytes(b'fixture')
            data=dict(root='Solidity.Theorems', public_roots=['witness'], selected_imports={'Solidity.Theorems': []},
                      sysroot_objects=[], objects=str(root))
            manifest={'files':[{'path':'Public.olean'}]}
            good=[dict(event='native_oracle',nonempty=True,cases=2),dict(event='module',name='Solidity.Theorems',object=str(obj)),
                  dict(event='witnesses',expected=1,missing=[]),
                  dict(event='domain',entries=2,moduleCount=1,root='Solidity.Theorems',loadExts=False),
                  dict(event='summary',expected=2,compared=2,mismatches=0,keyMismatches=0,duplicateKeys=0,
                       unsafeEntries=1,partialEntries=1,kinds=[0,1,0,1,0,0,0,0],kernelReplay=False,a04Accepted=False)]
            log=root/'log'
            def run(records):
                log.write_text('\n'.join(json.dumps(row) for row in records)+'\n')
                return evaluate_output(log,data,manifest)
            self.assertEqual(run(good)['compared'],2)
            from copy import deepcopy
            for key,value in [('compared',1),('mismatches',1),('kernelReplay',True),('a04Accepted',True),('kinds',[0]*8)]:
                broken=deepcopy(good);broken[-1][key]=value
                with self.subTest(key=key),self.assertRaises(R.InvalidInput):run(broken)
            for index,key,value in [(2,'missing',['witness']),(3,'moduleCount',2),(1,'object',str(root/'unlisted.olean')),(0,'nonempty',False)]:
                broken=deepcopy(good);broken[index][key]=value
                with self.subTest(key=key),self.assertRaises(R.InvalidInput):run(broken)
            with self.assertRaises(R.InvalidInput):run(good[:-1])
            with self.assertRaises(R.InvalidInput):run(good+[good[-1]])

    def test_generated_module_has_no_kernel_or_checker_path(self):
        for token in ('#eval', 'replay\'', 'addDeclCore', 'mkEmptyEnvironment', 'import Main', 'import Lean4Checker.Replay'):
            self.assertNotIn(token, DOMAIN_SOURCE)
        self.assertEqual(DOMAIN_SOURCE.count('Lean.importModules'),1)
        self.assertIn('env.constants.toList',DOMAIN_SOURCE)
        self.assertIn('loadExts := false',DOMAIN_SOURCE)


def main():
    p=argparse.ArgumentParser(description=__doc__)
    modes=p.add_mutually_exclusive_group(required=True)
    for name in ('unit','materialize','synthetic','prepare','compare'):modes.add_argument('--'+name,action='store_true')
    for name in ('source','checker','sysroot','binding','review','output'):p.add_argument('--'+name,type=Path)
    p.add_argument('--binding-sha256');p.add_argument('--review-sha256')
    args=p.parse_args()
    try:
        if args.unit:return 0 if unittest.TextTestRunner(verbosity=2).run(unittest.defaultTestLoader.loadTestsFromTestCase(RefusalControls)).wasSuccessful() else 1
        if args.materialize:materialize(args.checker);return 0
        if args.synthetic:synthetic(args.checker.resolve(),args.sysroot.resolve());return 0
        if args.prepare:prepare(args.source,args.checker,args.sysroot,args.binding);return 0
        return compare(args.binding.resolve(),args.binding_sha256,args.review.resolve(),args.review_sha256,args.output)
    except (R.InvalidInput,R.Deadline,OSError,ValueError,KeyError,TypeError,AttributeError,subprocess.SubprocessError) as error:
        print('H537 refused: '+str(error),file=sys.stderr);return 2


if __name__=='__main__':raise SystemExit(main())
