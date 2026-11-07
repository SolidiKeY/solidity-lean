#!/usr/bin/env python3
"""Account for extra compiler names retained by a verified old-kernel inventory.
No IR types, public visibility, semantics or cross-version equivalence are inferred.
"""
import argparse, hashlib, json, pathlib, sys
sys.dont_write_bytecode = True
import expr_dag

def sha(path):
    return hashlib.sha256(pathlib.Path(path).read_bytes()).hexdigest()

def key(name):
    expr_dag.name(name)
    return json.dumps(name, ensure_ascii=False, separators=(',', ':'))

def collect(inventory_path):
    inventory_path = pathlib.Path(inventory_path)
    inventory = json.loads(inventory_path.read_text())
    if (inventory.get('status') != 'pass' or inventory.get('migration_acceptance') is not False
            or inventory.get('scope') != 'pinned old persisted-kernel inventory integrity only'
            or inventory.get('base') != 'c6f550e281a7e5affa9a99bc2cdaed556dec00e4'):
        raise ValueError('requires completed pinned old-kernel inventory')
    rows = inventory['modules']
    if len(rows) != inventory['module_count'] or len(rows) != inventory['selected_for_verification']:
        raise ValueError('incomplete module inventory')
    if len({row['module'] for row in rows}) != len(rows):
        raise ValueError('duplicate module')
    modules, names = [], {}
    for row in rows:
        path = pathlib.Path(row['summary'])
        if sha(path) != row['summary_sha256']:
            raise ValueError('summary digest mismatch: ' + row['module'])
        snapshot = json.loads(path.read_text())
        if snapshot['module'] != row['module'] or snapshot['schema'] != row['schema']:
            raise ValueError('summary identity mismatch')
        header = snapshot['header']
        if header['extra_codegen_scope'] != 'IR-only names; not kernel ConstantInfo declarations':
            raise ValueError('unknown IR coverage scope')
        extra = header['extra_codegen_names']
        if type(header['extra_codegen_count']) is not int or header['extra_codegen_count'] != len(extra):
            raise ValueError('IR name count mismatch')
        kernel_names = {key(d['name']) for d in snapshot['declarations']}
        module_names = [key(n) for n in extra]
        if len(set(module_names)) != len(module_names):
            raise ValueError('duplicate extra compiler name')
        overlap = [n for n in extra if key(n) in kernel_names]
        modules.append(dict(module=row['module'], summary=str(path),
                            summary_sha256=row['summary_sha256'], schema=row['schema'],
                            extra_codegen_names=extra, compiler_name_records=len(extra),
                            also_kernel_records=len(overlap), also_kernel_names=overlap))
        for name in extra:
            encoded = key(name)
            if encoded not in names:
                names[encoded] = dict(name=name, modules=[], also_kernel_in=[], ir_type=None, public_visibility=None)
            names[encoded]['modules'].append(row['module'])
            if encoded in kernel_names:
                names[encoded]['also_kernel_in'].append(row['module'])
    return dict(schema_version=1, status='pass',
                scope='accounting of existing old snapshot extra compiler names, with unresolved IR types/visibility',
                base=inventory['base'], inventory=str(inventory_path.resolve()),
                inventory_sha256=sha(inventory_path), generator_sha256=sha(__file__),
                name_validator_sha256=sha(pathlib.Path(__file__).with_name('expr_dag.py')),
                module_count=len(modules), compiler_name_records=sum(m['compiler_name_records'] for m in modules),
                also_kernel_records=sum(m['also_kernel_records'] for m in modules),
                unique_compiler_names=len(names), modules=modules,
                names=[names[k] for k in sorted(names)], implemented_shims=[], migration_acceptance=False,
                legacy_header_label='IR-only names; not kernel ConstantInfo declarations',
                legacy_label_correction='extraConstNames can overlap constants; explicit per-module overlaps retained here. Immutable source-bound historical headers were not rewritten.',
                limitation='Names only. IR types, exact public visibility, attributes and old/new compatibility remain unverified. No extra compiler name is excluded or waived.')

if __name__ == '__main__':
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--inventory', type=pathlib.Path, required=True)
    parser.add_argument('--output', type=pathlib.Path, required=True)
    args = parser.parse_args()
    if args.output.exists():
        raise SystemExit('output must be fresh')
    result = collect(args.inventory)
    args.output.parent.mkdir(parents=True, exist_ok=True)
    args.output.write_text(json.dumps(result, indent=2, ensure_ascii=False) + '\n')
    print(json.dumps({k: result[k] for k in ['status', 'module_count', 'compiler_name_records', 'also_kernel_records', 'unique_compiler_names', 'migration_acceptance']}))
