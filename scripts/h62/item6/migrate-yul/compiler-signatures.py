#!/usr/bin/env python3
"""Validate source-bound extra compiler signatures; never public API acceptance."""
import argparse, json, pathlib, sys
sys.dont_write_bytecode = True
import interfaces
name = interfaces.expr_dag.name
canonical = interfaces.canonical

def ir_type(t):
    if not isinstance(t, list) or not t:
        raise ValueError('invalid IR type')
    if t[0] == 'repr' and len(t) == 2 and isinstance(t[1], str) and t[1]:
        return
    if len(t) == 3 and t[0] in ['struct', 'union'] and isinstance(t[2], list):
        if t[0] == 'union' or t[1] is not None:
            name(t[1])
        for child in t[2]:
            ir_type(child)
        return
    raise ValueError('invalid IR type tag/arity')

def inspect(raw, module):
    rows = [json.loads(line) for line in pathlib.Path(raw).read_text().splitlines()]
    expected = interfaces.module_name(module)
    if len(rows) < 2 or rows[0].get('record') != 'header' or rows[-1].get('record') != 'complete':
        raise ValueError('incomplete compiler snapshot')
    header, footer = rows[0], rows[-1]
    if type(header.get('schema')) is not int or header['schema'] != 1:
        raise ValueError('unknown schema')
    if any(row.get('module') != expected for row in rows):
        raise ValueError('module mismatch')
    for field in ['module_uses_module_system', 'inspector_header_is_module']:
        if type(header[field]) is not bool:
            raise ValueError('invalid module-system flag')
    names, found = set(), 0
    for row in rows[1:-1]:
        if row.get('record') != 'compiler_name':
            raise ValueError('unexpected record')
        name(row['name'])
        key = canonical(row['name'])
        if key in names:
            raise ValueError('duplicate compiler name')
        names.add(key)
        for field in ['private_name_marker', 'kernel_constant_available', 'compiler_is_decl_public']:
            if type(row[field]) is not bool:
                raise ValueError('invalid declaration flag')
        signature = row['signature']
        if row['ir_lookup'] == 'not_found' and signature is None:
            continue
        if row['ir_lookup'] != 'found' or not isinstance(signature, dict):
            raise ValueError('lookup/signature mismatch')
        found += 1
        if signature['name'] != row['name'] or type(signature['extern']) is not bool:
            raise ValueError('signature identity mismatch')
        if not isinstance(signature['parameters'], list):
            raise ValueError('invalid parameters')
        indices = []
        for param in signature['parameters']:
            index = param['variable_index']
            if type(index) is not int or index < 0 or index in indices or type(param['borrow']) is not bool:
                raise ValueError('invalid parameter')
            indices.append(index)
            ir_type(param['type'])
        ir_type(signature['result'])
    count = len(rows) - 2
    for value in [header['expected_names'], footer['count'], footer['ir_found'], footer['ir_missing']]:
        if type(value) is not int or value < 0:
            raise ValueError('invalid count')
    if count != header['expected_names'] or count != footer['count'] or found != footer['ir_found'] or count-found != footer['ir_missing']:
        raise ValueError('count mismatch')
    if footer.get('migration_acceptance') is not False:
        raise ValueError('unsupported acceptance claim')
    return dict(schema_version=1, module=module, header=header, footer=footer, declarations=rows[1:-1], migration_acceptance=False)

def seal(raw, probe_path, module):
    raw = pathlib.Path(raw).resolve()
    probe = interfaces.validate_probe(probe_path)
    cmd = probe['modules'][0]['command']
    pos = cmd.index('--run')
    repo = pathlib.Path(probe['repository'])
    helper = (repo / cmd[pos+1]).resolve()
    output = (repo / cmd[pos+3]).resolve()
    if len(probe['modules']) != 1 or len(cmd) != pos+4 or cmd[pos+2] != module or output != raw:
        raise ValueError('probe argument mismatch')
    if helper != (repo / 'tests/h62/item6/migrate-yul/ExportCompilerSignatures.lean').resolve() or str(helper) not in probe['probe_sources_before']:
        raise ValueError('unbound compiler exporter')
    bound = probe['probe_outputs_after'].get(str(raw))
    if probe.get('probe_output_freshness_required') is not True or not bound or bound['sha256'] != interfaces.digest(raw) or bound['bytes'] != raw.stat().st_size:
        raise ValueError('unbound compiler snapshot')
    result = inspect(raw, module)
    result.update(raw=str(raw), raw_sha256=interfaces.digest(raw), probe=str(pathlib.Path(probe_path).resolve()), probe_sha256=interfaces.digest(probe_path), lean=probe['lean'], lake=probe['lake'], collector_sha256=interfaces.digest(__file__), limitation='IR signatures only. Compiler visibility flags are observations, not verified public API classification; missing IR remains unresolved. No compatibility or semantic acceptance.')
    return result

if __name__ == '__main__':
    p = argparse.ArgumentParser(description=__doc__)
    for key in ['raw', 'probe', 'output']:
        p.add_argument('--'+key, type=pathlib.Path, required=True)
    p.add_argument('--module', required=True)
    a = p.parse_args()
    if a.output.exists():
        raise SystemExit('output must be fresh')
    result = seal(a.raw, a.probe, a.module)
    a.output.write_text(json.dumps(result, indent=2, ensure_ascii=False)+'\n')
    print(json.dumps(result['footer']))
