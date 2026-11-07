#!/usr/bin/env python3
"""Prepare every original module for selected old metadata queries; executes none.
Zero own declarations never establish absence of serialized registration effects.
"""
import argparse, hashlib, json, pathlib, sys
sys.dont_write_bytecode = True
import interfaces

BASE = 'c6f550e281a7e5affa9a99bc2cdaed556dec00e4'
CENSUS_SHA256 = 'fac7f44fac55ba732eeb9b6151a0f001ddc4dd6d0cf10558642ffd1c30b22902'
FAMILIES = ['declaration private/protected/class flags and active instance priority',
            'serialized classes and out parameters',
            'serialized global/scoped instances and priorities',
            'serialized default instances and priorities']


def make_plan(census, inventory, census_sha256, baseline):
    """Validate coverage and current inputs, without interpreting metadata absence."""
    baseline = baseline.resolve()
    selected = census['yul_modules']
    rows = inventory['modules']
    if (len(set(selected)) != len(selected) or
            [row['module'] for row in rows] != selected):
        raise ValueError('original ordered module coverage mismatch')
    if (inventory['base'] != BASE or inventory['status'] != 'pass' or
            inventory['migration_acceptance'] is not False or
            inventory['original_census_sha256'] != census_sha256 or
            type(inventory['module_count']) is not int or
            inventory['module_count'] != len(selected) or
            type(inventory['selected_for_verification']) is not int or
            inventory['selected_for_verification'] != len(selected)):
        raise ValueError('old inventory provenance/count mismatch')
    # Bind all original closure inputs, including dependencies outside this lane.
    for source in census['modules'].values():
        if interfaces.digest(baseline / source['path']) != source['sha256']:
            raise ValueError('original source drift: ' + source['path'])
    jobs = []
    for index, row in enumerate(rows):
        count = row['declarations']
        if type(count) is not int or count < 0:
            raise ValueError('invalid kernel declaration count')
        # Relative inventory paths belong to the preserved source view, not cwd.
        # Absolute evidence paths may legitimately be outside that worktree.
        summary_path = (baseline / row['summary']).resolve()
        summary_bytes = summary_path.read_bytes()
        if hashlib.sha256(summary_bytes).hexdigest() != row['summary_sha256']:
            raise ValueError('old kernel summary drift: ' + row['module'])
        snapshot = json.loads(summary_bytes)
        if (snapshot['module'] != row['module'] or
                len(snapshot['declarations']) != count or
                type(snapshot['header']['expected_constants']) is not int or
                snapshot['header']['expected_constants'] != count):
            raise ValueError('old kernel summary coverage mismatch')
        jobs.append(dict(index=index, module=row['module'],
            kernel_declarations=count, kernel_summary=str(summary_path),
            kernel_summary_sha256=row['summary_sha256'],
            query_required=True, query_performed=False,
            scope='one original module per bounded old-toolchain probe'))
    return dict(schema_version=1, status='plan_only', base=BASE,
        module_count=len(jobs), queries_required=len(jobs), queries_performed=0,
        zero_kernel_declaration_modules=sum(j['kernel_declarations'] == 0 for j in jobs),
        kernel_declaration_records=sum(j['kernel_declarations'] for j in jobs),
        selected_metadata_families=FAMILIES, modules=jobs,
        migration_acceptance=False,
        limitation='Planning integrity only. No Lean execution or metadata collection. '
        'All modules require queries, even empty kernel modules. Existing focused '
        'Allocation/fixture evidence remains separate. Not a generic attribute census, '
        'public classification, semantic proof, new API or performance acceptance.')


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    for key in ['census', 'inventory', 'baseline', 'output']:
        parser.add_argument('--' + key, type=pathlib.Path, required=True)
    args = parser.parse_args()
    census_bytes = args.census.read_bytes()
    inventory_bytes = args.inventory.read_bytes()
    census_sha256 = hashlib.sha256(census_bytes).hexdigest()
    inventory_sha256 = hashlib.sha256(inventory_bytes).hexdigest()
    generator_sha256 = interfaces.digest(__file__)
    if census_sha256 != CENSUS_SHA256:
        raise ValueError('requires exact original pinned census')
    census = json.loads(census_bytes)
    if len(census['yul_modules']) != 1774:
        raise ValueError('requires complete original assigned scope')
    report = make_plan(census, json.loads(inventory_bytes),
                       census_sha256, args.baseline.resolve())
    inputs = {args.census: census_sha256, args.inventory: inventory_sha256,
              pathlib.Path(__file__): generator_sha256}
    for source in census['modules'].values():
        inputs[args.baseline.resolve() / source['path']] = source['sha256']
    for job in report['modules']:
        inputs[pathlib.Path(job['kernel_summary'])] = job['kernel_summary_sha256']
    if any(interfaces.digest(path) != sha for path, sha in inputs.items()):
        raise ValueError('planning inputs changed before final binding')
    report.update(census=str(args.census.resolve()), census_sha256=census_sha256,
        inventory=str(args.inventory.resolve()),
        inventory_sha256=inventory_sha256,
        baseline=str(args.baseline.resolve()), generator_sha256=generator_sha256)
    with args.output.open('x') as dest:
        dest.write(json.dumps(report, indent=2) + '\n')
    print(json.dumps({key: report[key] for key in
        ['status', 'module_count', 'zero_kernel_declaration_modules', 'queries_performed']}))

if __name__ == '__main__':
    main()
