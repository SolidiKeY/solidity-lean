#!/usr/bin/env python3
"""Reproduce exact positive-control instances; guards missing/ambiguous headers.
This is lexical extraction, not a semantic parser or proof acceptance oracle.
The generated single test reuses the actual generic proof; it never edits originals.
"""
import argparse
import hashlib
import json
import re
from pathlib import Path
import census as c
from propose import TARGETS


def select(rows, path, short):
    matches = [r for r in rows if r['path'] == path and r['name'].endswith('.'+short)]
    if len(matches) != 1:
        raise ValueError('missing or ambiguous original: '+path+':'+short)
    row = matches[0]
    if c.sha(row['statement']) != row['statement_sha256']:
        raise ValueError('statement hash mismatch')
    return row


def verify_frozen(live, frozen):
    if live != frozen:
        raise ValueError('frozen source/statement drift')


def generate():
    helper = c.ROOT/'tests/h62/item4/generic-structuredflow/GenericMapped.lean'
    text = helper.read_text()
    imports = set(re.findall(r'^import .+$', text, re.M))
    rows, chunks = [], []
    inventory = c.census()
    frozen = c.census(c.BASE)
    selected_paths = {c.FAMILY+name+'.lean' for name in TARGETS}
    def selected(source):
        return {key: [row for row in source[key] if row['path'] in selected_paths]
                for key in ('files', 'declarations')}
    verify_frozen(selected(inventory), selected(frozen))
    frozen_hashes = {row['path']: row['sha256'] for row in frozen['files']}
    for basename, names in sorted(TARGETS.items()):
        path = c.FAMILY+basename+'.lean'
        raw = (c.ROOT/path).read_bytes()
        original = raw.decode()
        if hashlib.sha256(raw).hexdigest() != frozen_hashes[path]:
            raise ValueError('source changed after census')
        imports.update(re.findall(r'^import .+$', original, re.M))
        namespace = re.search(r'^namespace (.+)$', original, re.M)[1]
        part = ['namespace '+namespace, '\n'.join(re.findall(r'^open .+$', original, re.M))]
        for short in names:
            row = select(inventory['declarations'], path, short)
            statement = row['statement'].replace('theorem '+short, 'theorem '+short+'_generic_instance', 1)
            if statement == row['statement']:
                raise ValueError('unexpected declaration syntax')
            base = 128 if short == 'nonzero_frame' else 0
            part.append(statement+' := by\n  exact Solidity.Backend.StructuredFlow.GenericMapped.emitted_snapshot '+str(base)+' flag\n')
            part.append('#print axioms '+short+'_generic_instance')
            rows.append(dict(original=row['name'], statement_sha256=row['statement_sha256'],
                             source_sha256=hashlib.sha256(raw).hexdigest(), path=path))
        chunks.append('\n'.join(part+['end '+namespace]))
    body = '\n'.join(sorted(imports))+'\n'+re.sub(r'^import .+\n', '', text, flags=re.M)+'\n'+'\n'.join(chunks)
    return body, rows


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--output', required=True, type=Path)
    output = parser.parse_args().output.resolve()
    if output == c.ROOT or c.ROOT in output.parents:
        raise SystemExit('H44: generated bulk stays off Git')
    body, rows = generate()
    if (body, rows) != generate():
        raise ValueError('nondeterministic reproduction')
    output.mkdir(parents=True, exist_ok=False)
    (output/'ExactInstances.lean').write_text(body)
    (output/'bindings.json').write_text(json.dumps(rows, indent=2)+'\n')
    print(json.dumps(dict(instances=len(rows), source_acceptance_only=True,
                         lean_sha256=c.sha(body))))

if __name__ == '__main__':
    main()
