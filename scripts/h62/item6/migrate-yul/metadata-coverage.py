#!/usr/bin/env python3
"""Revalidate selected old metadata observations against every original module.
No Lean execution, generic attribute census, public API or migration acceptance.
"""
import argparse, hashlib, importlib.util, json, pathlib, subprocess, sys
sys.dont_write_bytecode = True

def sibling(name, filename):
    spec = importlib.util.spec_from_file_location(name, pathlib.Path(__file__).with_name(filename))
    module = importlib.util.module_from_spec(spec)
    spec.loader.exec_module(module)
    return module

planner = sibling('metadata_coverage_planner', 'plan-old-metadata.py')
metadata = sibling('metadata_coverage_observer', 'declaration-metadata.py')
sha = metadata.interfaces.digest


def read_bound(path, bindings):
    path = pathlib.Path(path).resolve()
    data = path.read_bytes()
    digest = hashlib.sha256(data).hexdigest()
    if path in bindings and bindings[path] != digest:
        raise ValueError('input changed during validation: ' + str(path))
    bindings[path] = digest
    return json.loads(data)


@metadata.validation_input_errors
def load_plan(path, bindings):
    plan = read_bound(path, bindings)
    census_path = pathlib.Path(plan['census']).resolve()
    census = read_bound(census_path, bindings)
    if bindings[census_path] != planner.CENSUS_SHA256 or plan['census_sha256'] != planner.CENSUS_SHA256:
        raise ValueError('requires exact original pinned census')
    inventory_path = pathlib.Path(plan['inventory']).resolve()
    inventory = read_bound(inventory_path, bindings)
    if bindings[inventory_path] != plan['inventory_sha256']:
        raise ValueError('plan inventory binding mismatch')
    baseline = pathlib.Path(plan['baseline']).resolve()
    if len(census['yul_modules']) != 1774:
        raise ValueError('requires all original assigned modules')
    if subprocess.check_output(['git', 'rev-parse', 'HEAD'], cwd=baseline, text=True).strip() != planner.BASE:
        raise ValueError('requires preserved original baseline')
    expected = planner.make_plan(census, inventory, planner.CENSUS_SHA256, baseline)
    if any(plan.get(key) != value for key, value in expected.items()):
        raise ValueError('plan content differs from rebuilt original plan')
    planner_path = pathlib.Path(planner.__file__).resolve()
    if sha(planner_path) != plan['generator_sha256']:
        raise ValueError('plan generator binding mismatch')
    bindings[planner_path] = plan['generator_sha256']
    for source in census['modules'].values():
        bindings[(baseline / source['path']).resolve()] = source['sha256']
    for job in plan['modules']:
        bindings[pathlib.Path(job['kernel_summary']).resolve()] = job['kernel_summary_sha256']
    return plan


@metadata.validation_input_errors
def seal_observation(path, job, plan, bindings):
    observed = read_bound(path, bindings)
    module = job['module']
    if observed['module'] != module:
        raise ValueError('observation module mismatch')
    probe_path = pathlib.Path(observed['probe']).resolve()
    probe = read_bound(probe_path, bindings)
    raw_path = pathlib.Path(observed['raw']).resolve()
    # seal revalidates the actual supervised raw output, not just its saved summary.
    sealed = metadata.seal(raw_path, probe_path, module)
    if set(observed) - set(sealed) - {'original_coverage'}:
        raise ValueError('unknown observation fields')
    if any(observed.get(key) != value for key, value in sealed.items()):
        raise ValueError('saved observation differs from raw reseal')
    if (probe['head'] != planner.BASE or
            pathlib.Path(probe['repository']).resolve() != pathlib.Path(plan['baseline']).resolve() or
            probe['census_sha256'] != planner.CENSUS_SHA256 or
            '797c613eb9b6d4ec95db23e3e00af9ac6657f24b' not in probe['lean']):
        raise ValueError('observation original source/toolchain mismatch')
    if 'original_coverage' in observed:
        previous = observed['original_coverage']
        summary = pathlib.Path(previous['kernel_summary']).resolve()
        if sha(summary) != previous['kernel_summary_sha256']:
            raise ValueError('saved coverage summary drift')
        if metadata.check_original_coverage(sealed, summary) != previous:
            raise ValueError('saved original coverage mismatch')
        bindings[summary] = previous['kernel_summary_sha256']
    coverage = metadata.check_original_coverage(sealed, job['kernel_summary'])
    if coverage['declarations'] != job['kernel_declarations']:
        raise ValueError('observed declaration count differs from original plan')
    bindings[raw_path] = sealed['raw_sha256']
    if bindings[probe_path] != sealed['probe_sha256']:
        raise ValueError('probe changed during reseal')
    for source, digest in probe['probe_sources_before'].items():
        source = pathlib.Path(source).resolve()
        if source in bindings and bindings[source] != digest:
            raise ValueError('conflicting observed input binding')
        bindings[source] = digest
    return dict(status='observed', observation=str(pathlib.Path(path).resolve()),
        observation_sha256=bindings[pathlib.Path(path).resolve()],
        raw_sha256=sealed['raw_sha256'], probe=str(probe_path),
        probe_sha256=sealed['probe_sha256'], original_coverage=coverage,
        counts={key: sealed['footer'][key] for key in
                ['declarations', 'classes', 'instances', 'defaults']})


@metadata.validation_input_errors
def make_ledger(plan, paths, bindings):
    jobs = {job['module']: job for job in plan['modules']}
    if len(jobs) != len(plan['modules']):
        raise ValueError('duplicate planned module')
    observed = {}
    for path in paths:
        summary = read_bound(path, bindings)
        module = summary['module']
        if module not in jobs:
            raise ValueError('observation outside original scope: ' + module)
        if module in observed:
            raise ValueError('duplicate observed module: ' + module)
        observed[module] = seal_observation(path, jobs[module], plan, bindings)
    rows = []
    for job in plan['modules']:
        row = dict(module=job['module'], kernel_declarations=job['kernel_declarations'])
        row.update(observed.get(job['module'], dict(status='pending', query_required=True)))
        rows.append(row)
    return dict(schema_version=1, status='partial' if len(observed) != len(rows) else 'complete',
        integrity_status='pass', base=planner.BASE, module_count=len(rows),
        observed_modules=len(observed), pending_modules=len(rows)-len(observed),
        selected_metadata_families=planner.FAMILIES, modules=rows,
        migration_acceptance=False,
        limitation='Selected old metadata observation coverage only. Pending modules '
        'remain explicit; fixtures outside the original corpus and duplicates are rejected. '
        'Not all attributes, public classification, semantic proofs, new API or '
        'performance acceptance. External initializer IO is outside model/proofs.')


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--plan', type=pathlib.Path, required=True)
    parser.add_argument('--observation', type=pathlib.Path, action='append', default=[])
    parser.add_argument('--output', type=pathlib.Path, required=True)
    args = parser.parse_args()
    bindings = {}
    for source in [__file__, metadata.__file__, metadata.interfaces.__file__,
                   metadata.interfaces.expr_dag.__file__]:
        bindings[pathlib.Path(source).resolve()] = sha(source)
    plan = load_plan(args.plan, bindings)
    report = make_ledger(plan, args.observation, bindings)
    if any(sha(path) != digest for path, digest in bindings.items()):
        raise ValueError('coverage inputs changed before final binding')
    if subprocess.check_output(['git', 'rev-parse', 'HEAD'], cwd=plan['baseline'], text=True).strip() != planner.BASE:
        raise ValueError('baseline changed before final binding')
    report.update(plan=str(args.plan.resolve()), plan_sha256=bindings[args.plan.resolve()],
        input_sources={str(path): digest for path, digest in sorted(bindings.items())})
    with args.output.open('x') as dest:
        dest.write(json.dumps(report, indent=2)+'\n')
    print(json.dumps({key: report[key] for key in
        ['status', 'integrity_status', 'module_count', 'observed_modules', 'pending_modules']}))

if __name__ == '__main__':
    main()
