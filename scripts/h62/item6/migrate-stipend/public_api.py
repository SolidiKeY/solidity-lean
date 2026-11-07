#!/usr/bin/env python3
"""Generate/read a full module-name census; raw signatures are versioned evidence.
No private/generated exclusion. Missing compiler-only types remain unresolved.
This does not prove cross-version semantic or definitional equivalence.
"""
import argparse
import hashlib
import json
import re
from pathlib import Path

ROOT = Path(__file__).resolve().parents[4]
MODULE = 'Solidity.Stipend.Rule'
ARCHIVES = {'leanprover/lean4:v4.24.0': 'b14f5e5159219dd1a1956c3b806813319f5e94ccd5bdfd56f54520609a5bb5ec', 'leanprover/lean4:v4.35.0': '7289597a44543246c9227b8cae501767e095ce17f6d448b95fc4a8dc97268f6d'}
PREFIX = 'STIPEND_API '
KINDS = {'axiom', 'definition', 'theorem', 'opaque', 'inductive', 'constructor', 'recursor', 'quotient'}
BINDERS = {'Lean.BinderInfo.default', 'Lean.BinderInfo.implicit', 'Lean.BinderInfo.strictImplicit', 'Lean.BinderInfo.instImplicit'}
BODY = r'''import Lean
import Solidity.Stipend.Rule

/-! Read-only module-owned name/type introspection, including generated names.
No production API, compiler obligation or cross-version equivalence is proved. -/
namespace StipendMigrationInventory
open Lean

def nameJson : Name → Json
  | .anonymous => toJson (["anonymous"] : List String)
  | .str parent value => Json.arr #[toJson "str", nameJson parent, toJson value]
  | .num parent value => Json.arr #[toJson "num", nameJson parent, toJson (toString value)]

def telescope : Expr → List Json × Expr
  | .forallE name domain body kind =>
    let (rest, result) := telescope body
    (Json.mkObj [("name_parts", nameJson name), ("domain_repr", toJson (reprStr domain)),
      ("binder_kind", toJson (reprStr kind))] :: rest, result)
  | type => ([], type)

end StipendMigrationInventory

open Lean StipendMigrationInventory in
run_elab do
  let env ← getEnv
  let moduleName := "Solidity.Stipend.Rule"
  let some index := env.header.moduleNames.findIdx? (fun name => name.toString == moduleName)
    | throwError "missing imported module {moduleName}"
  let data := env.header.moduleData[index]!
  unless data.constNames == data.constants.map (·.name) do
    throwError "module constant name/data mismatch"
  let write := fun (value : Json) => IO.println ("STIPEND_API " ++ value.compress)
  write <| Json.mkObj [("record", toJson "header"), ("schema_version", toJson (1 : Nat)),
    ("module", toJson moduleName), ("kernel_count", toJson data.constants.size),
    ("compiler_extra_count", toJson data.extraConstNames.size)]
  let groups : List (String × Array Name) :=
    [("kernel", data.constNames), ("compiler_extra", data.extraConstNames)]
  for (category, names) in groups do
    for name in names.qsort (fun a b => a.toString < b.toString) do
      let signature ← match env.find? name with
        | none => pure Json.null
        | some info => do
          let kind : String := match info with
            | .axiomInfo _ => "axiom"
            | .defnInfo _ => "definition"
            | .thmInfo _ => "theorem"
            | .opaqueInfo _ => "opaque"
            | .inductInfo _ => "inductive"
            | .ctorInfo _ => "constructor"
            | .recInfo _ => "recursor"
            | .quotInfo _ => "quotient"
          let axioms ← Lean.collectAxioms name
          let (binders, result) := telescope info.type
          pure <| Json.mkObj [("kind", toJson kind), ("unsafe", toJson info.isUnsafe),
            ("level_params", toJson (info.levelParams.map nameJson)),
            ("type_repr", toJson (reprStr info.type)), ("binders", toJson binders),
            ("result_repr", toJson (reprStr result)),
            ("axioms", toJson ((axioms.qsort (fun a b => a.toString < b.toString)).map nameJson))]
      write <| Json.mkObj [("record", toJson "declaration"), ("module", toJson moduleName),
        ("category", toJson category), ("name", toJson name.toString),
        ("name_parts", nameJson name), ("private", toJson (isPrivateName name)),
        ("internal", toJson name.isInternal), ("signature", signature)]
  write <| Json.mkObj [("record", toJson "end"), ("module", toJson moduleName),
    ("count", toJson (data.constants.size + data.extraConstNames.size))]
'''

def canonical(value):
    return json.dumps(value, ensure_ascii=False, sort_keys=True, separators=(',', ':')).encode()

def name_ok(value):
    if value == ['anonymous']:
        return True
    if not isinstance(value, list) or len(value) != 3 or value[0] not in {'str', 'num'}:
        return False
    if not name_ok(value[1]) or not isinstance(value[2], str):
        return False
    return value[0] == 'str' or (value[2].isascii() and value[2].isdecimal() and str(int(value[2])) == value[2])

def validate_row(row):
    required = {'record', 'module', 'category', 'name', 'name_parts', 'private', 'internal', 'signature'}
    if set(row) != required or row['record'] != 'declaration' or row['module'] != MODULE:
        raise ValueError('invalid declaration identity/fields')
    if row['category'] not in {'kernel', 'compiler_extra'} or not name_ok(row['name_parts']):
        raise ValueError('invalid category/structural name')
    if not isinstance(row['name'], str) or not row['name'] or type(row['private']) is not bool or type(row['internal']) is not bool:
        raise ValueError('invalid declaration name/visibility markers')
    s = row['signature']
    if s is None:
        if row['category'] == 'kernel':
            raise ValueError('kernel signature missing')
        return
    if not isinstance(s, dict) or set(s) != {'kind', 'unsafe', 'level_params', 'type_repr', 'binders', 'result_repr', 'axioms'}:
        raise ValueError('invalid signature fields')
    if s['kind'] not in KINDS or type(s['unsafe']) is not bool:
        raise ValueError('invalid signature kind/safety')
    for field in ('level_params', 'axioms'):
        if not isinstance(s[field], list) or not all(name_ok(n) for n in s[field]) or len({canonical(n) for n in s[field]}) != len(s[field]):
            raise ValueError('invalid or duplicate universe/axiom names')
    if not all(isinstance(s[k], str) and s[k] for k in ('type_repr', 'result_repr')) or not isinstance(s['binders'], list):
        raise ValueError('invalid raw signature/telescope')
    for binder in s['binders']:
        if not isinstance(binder, dict) or set(binder) != {'name_parts', 'domain_repr', 'binder_kind'} or not name_ok(binder['name_parts']) or not isinstance(binder['domain_repr'], str) or not binder['domain_repr'] or binder['binder_kind'] not in BINDERS:
            raise ValueError('invalid binder')

def parse(text):
    header, trailer, rows, seen = None, None, [], set()
    for line in text.splitlines():
        if not line.startswith(PREFIX):
            continue
        value = json.loads(line[len(PREFIX):])
        if not isinstance(value, dict):
            raise ValueError('invalid record')
        kind = value.get('record')
        if kind == 'header':
            if header is not None or rows or trailer is not None:
                raise ValueError('duplicate/out-of-order header')
            if set(value) != {'record', 'schema_version', 'module', 'kernel_count', 'compiler_extra_count'} or type(value['schema_version']) is not int or value['schema_version'] != 1 or value['module'] != MODULE or any(type(value[k]) is not int or value[k] < 0 for k in ('kernel_count', 'compiler_extra_count')):
                raise ValueError('invalid header')
            header = value
        elif kind == 'declaration':
            if header is None or trailer is not None:
                raise ValueError('out-of-order declaration')
            validate_row(value)
            key = canonical(value['name_parts'])
            if key in seen:
                raise ValueError('duplicate structural name')
            seen.add(key); rows.append(value)
        elif kind == 'end':
            if header is None or trailer is not None or set(value) != {'record', 'module', 'count'} or value['module'] != MODULE or type(value['count']) is not int:
                raise ValueError('invalid/out-of-order trailer')
            trailer = value
        else:
            raise ValueError('unknown record')
    if header is None or trailer is None or not rows:
        raise ValueError('incomplete export')
    if trailer['count'] != len(rows) or any(sum(r['category'] == cat for r in rows) != header[k] for cat, k in [('kernel', 'kernel_count'), ('compiler_extra', 'compiler_extra_count')]):
        raise ValueError('module count mismatch')
    return {'header': header, 'rows': sorted(rows, key=lambda r: canonical(r['name_parts'])),
            'raw_export_sha256': hashlib.sha256(text.encode('utf-8')).hexdigest(),
            'provenance_boundary': 'Digest identifies supplied UTF-8 log; compiler invocation, toolchain/archive, source and fixture hashes must be supplied by the run receipt.'}

def compare(old, new):
    a = {canonical(r['name_parts']): r for r in old['rows']}
    b = {canonical(r['name_parts']): r for r in new['rows']}
    missing = [a[k] for k in sorted(a.keys() - b.keys())]
    added = [b[k] for k in sorted(b.keys() - a.keys())]
    changed = [{'name': a[k]['name'], 'old': a[k], 'new': b[k]} for k in sorted(a.keys() & b.keys()) if a[k] != b[k]]
    unresolved = [{'side': side, 'row': r} for side, data in [('old', old), ('new', new)] for r in data['rows'] if r['signature'] is None]
    return {'schema_version': 1, 'module': MODULE, 'old_export_sha256': old['raw_export_sha256'], 'new_export_sha256': new['raw_export_sha256'], 'old_count': len(a), 'new_count': len(b), 'missing': missing, 'added': added, 'changed': changed, 'unresolved': unresolved,
            'all_original_records_identical_and_resolved': not (missing or changed or unresolved),
            'added_declarations_require_audit': added, 'full_migration_gate_pass': False,
            'boundary': 'Exact versioned raw export records only. No semantic equivalence or export-accessibility proof; no private/internal/generated exemption.'}

def file_sha(path):
    with Path(path).open('rb') as f:
        return hashlib.file_digest(f, 'sha256').hexdigest()

def validate_receipt(receipt, data):
    """Bind supplied records to a saved successful-run receipt and local bytes.
    This consistency check cannot attest that an untrusted receipt is truthful.
    """
    if 'stop' not in receipt or receipt.get('module') != MODULE or type(receipt.get('exit_code')) is not int or receipt['exit_code'] != 0 or receipt.get('stop') is not None:
        raise ValueError('successful exporter process receipt required')
    toolchain = receipt.get('toolchain')
    if toolchain not in ARCHIVES or receipt.get('archive_sha256') != ARCHIVES[toolchain]:
        raise ValueError('unknown or mismatched official toolchain archive')
    version = toolchain.rsplit(':v', 1)[1]
    lean = re.fullmatch(r'Lean \(version ([0-9]+\.[0-9]+\.[0-9]+)(?:, [^\r\n]*)?\)', str(receipt.get('lean_version')))
    lake = re.fullmatch(r'Lake version [^()\r\n]+ \(Lean version ([0-9]+\.[0-9]+\.[0-9]+)\)', str(receipt.get('lake_version')))
    if lean is None or lake is None or lean[1] != version or lake[1] != version:
        raise ValueError('exact actual Lean/Lake version receipt required')
    if receipt.get('log_sha256') != data['raw_export_sha256']:
        raise ValueError('export log/receipt mismatch')
    for key, path in [('fixture_sha256', ROOT/'tests/h62/item6/migrate-stipend/PublicInventory.lean'),
                      ('module_source_sha256', ROOT/'Solidity/Stipend/Rule.lean')]:
        if receipt.get(key) != file_sha(path):
            raise ValueError('source/fixture receipt mismatch')
    artifact = receipt.get('olean_path')
    if not isinstance(artifact, str) or not Path(artifact).is_absolute() or receipt.get('olean_sha256') != file_sha(artifact):
        raise ValueError('imported module object receipt mismatch')
    command = receipt.get('command')
    if not isinstance(command, list) or not command or not all(isinstance(x, str) for x in command):
        raise ValueError('actual serial command receipt required')
    thread_options = [x for x in command[1:] if x.startswith('-j') or x.startswith('--threads')]
    if thread_options != ['-j1'] or Path(command[0]).name != 'lean' or command[-1] != str(ROOT/'tests/h62/item6/migrate-stipend/PublicInventory.lean'):
        raise ValueError('actual unambiguous serial exporter command receipt required')
    return {'supplied_receipt_fields_verified': True, 'receipt_sha256': hashlib.sha256(canonical(receipt)).hexdigest(),
            'boundary': 'Local byte/metadata consistency, not execution attestation or H81 approval. Visibility and final migration gates remain separate.'}


def validate_pair(old_receipt, new_receipt, old, new):
    if old_receipt.get('toolchain') != 'leanprover/lean4:v4.24.0' or new_receipt.get('toolchain') != 'leanprover/lean4:v4.35.0':
        raise ValueError('migration comparison requires old 4.24.0 and new 4.35.0 roles')
    return [validate_receipt(old_receipt, old), validate_receipt(new_receipt, new)]


def main():
    p = argparse.ArgumentParser(); sub = p.add_subparsers(dest='command', required=True)
    sub.add_parser('fixture')
    x = sub.add_parser('extract'); x.add_argument('log', type=Path); x.add_argument('output', type=Path); x.add_argument('--receipt', type=Path, required=True)
    x = sub.add_parser('compare'); x.add_argument('old_log', type=Path); x.add_argument('new_log', type=Path); x.add_argument('output', type=Path); x.add_argument('--old-receipt', type=Path, required=True); x.add_argument('--new-receipt', type=Path, required=True)
    a = p.parse_args()
    if a.command == 'fixture':
        print(BODY, end=''); return
    if a.command == 'extract':
        result = parse(a.log.read_text()); result['receipt_check'] = validate_receipt(json.loads(a.receipt.read_text()), result)
    else:
        old, new = parse(a.old_log.read_text()), parse(a.new_log.read_text())
        receipts = validate_pair(json.loads(a.old_receipt.read_text()), json.loads(a.new_receipt.read_text()), old, new)
        result = compare(old, new); result['receipt_checks'] = receipts
    # Exclusive creation preserves existing evidence and refuses symlink aliases.
    with a.output.open('x') as f:
        f.write(json.dumps(result, ensure_ascii=False, sort_keys=True, indent=2) + '\n')

if __name__ == '__main__':
    main()
