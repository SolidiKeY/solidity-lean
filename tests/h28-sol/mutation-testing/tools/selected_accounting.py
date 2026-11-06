"""Replay the complete census and selection ledger; no full-gate waiver."""
import json
import candidate_inventory as census
import selection_ledger
import checked
from archive_io import require
from check_candidate_inventory import check_printed_census, CACHE_SHA


def verify(repo, read, run, manifest, members):
    require({n for n in members if n.startswith("census/") and n.endswith(".olean")} == {"census/InventoryAudit.olean"}, "unexpected or negative census object")
    require(bool(read("census/InventoryAudit.olean")), "empty positive census object")
    ledger = json.loads(read('ledger.json'))
    require(ledger['input_head'] == run['run_head'], 'ledger/run head mismatch')
    actual = selection_ledger.build(repo, repo / 'tests/h28-sol/mutation-testing/manifests/selected-suite.json')
    actual['input_head'] = run['run_head']
    require(ledger == actual, 'exhaustive ledger regeneration mismatch')
    require(ledger['counts'] == dict(declarations=290, units=308, fixtures=34, profiles=13, selected_ids=19), 'final accounting counts mismatch')
    require(len({c['mutant_sha256'] for c in manifest['cases'] if c['kind'] in {'mutant', 'negative-control'}}) == 15, 'distinct scored program count mismatch')
    require(all(f['selected_roles'] and f['theorems'] for f in ledger['fixtures']), 'fixture lacks selected theorem inventory')
    for fixture in ledger['fixtures']:
        qualified = set()
        for role in fixture['selected_roles']:
            record = next((r for r in run['records'] if r['id'] == role['case_id']), None)
            require(record is not None, 'fixture references missing case result')
            for phase, cert in record['validation'].items():
                if phase.endswith('-' + role['role']) and 'all_owned_axioms' in cert:
                    qualified |= {n.rsplit('.', 1)[-1] for n in cert['all_owned_axioms']}
        require(set(fixture['theorems']) <= qualified, 'fixture theorem missing from successful axiom inventory')
    catalog = json.loads(read('census/catalog.json')); result = json.loads(read('census/result.json'))
    require(result['gate_head'] == run['run_head'] and result['audit_complete'] and not result['scope_complete'] and result['score'] is None, 'census identity or boundary mismatch')
    require(result['cache_manifest_sha256'] == CACHE_SHA, 'normal census cache identity mismatch')
    require(set(result['checks']) == {'keysort', 'positive', 'known-bad-table'}, 'census phase inventory mismatch')
    current = census.build(repo)
    source, names = census.lean_source(current)
    negative_source, _ = census.lean_source(current, corrupt=True)
    require(read('census/InventoryAudit.lean').decode() == source and read('census/InventoryNegative.lean').decode() == negative_source, 'generated proof source mismatch')
    require(census.digest(read('census/InventoryAudit.olean')) == result['artifact_sha256'] and census.digest(source.encode()) == result['positive_source_sha256'], 'census proof object/source mismatch')
    positive_log = read('census/positive.log').decode()
    certificate = checked.success(result['checks']['positive'], positive_log, names)
    require(len(certificate['axioms']) == 294, 'census axiom count mismatch')
    current['kernel_constructor_inventories'] = check_printed_census(positive_log, current)
    current['helper_consumers'] = census.attach_kernel_references(current, certificate['signatures'])
    current['kernel_certificate'] = certificate; current['state'] = 'kernel-audited-source-census'
    require(current == catalog, 'source/kernel census regeneration mismatch')
    for label, filename in [('keysort', 'keysort.log'), ('positive', 'positive.log'), ('known-bad-table', 'negative.log')]:
        res = result['checks'][label]; log = read('census/' + filename).decode()
        require(census.digest(log.encode()) == res['log_sha256'], 'census log hash mismatch')
        require(res['kind'] == 'exit' and res['cleanup_confirmed'] and res['failure'] is None and not res['oom_killed'], 'census runtime failure')
        require(res['runtime_lean_sha256'] == manifest['runtime_lean_sha256'] and res['measurement_binary_sha256'] == manifest['measurement_binary_sha256'], 'census runtime identity mismatch')
        require(res['memory_limit'] in {2 * 1024**3, 4 * 1024**3, 6 * 1024**3} and res['swap_limit'] == 0 and res['reserved_before'] >= 4 * 1024**3 and '-j1' in res['lean_argv'] and '--network=none' in res['argv'], 'census resource bounds mismatch')
        require(res['lean_measurement']['signal'] == 0 and res['lean_measurement']['exit'] == res['exit'], 'census measurement mismatch')
        if label != 'known-bad-table':
            checked.success(res, log)
        else:
            errors = [m for m in checked.messages(log) if m['severity'] in {'error', 'warning'}]
            line = next(i for i, text in enumerate(negative_source.splitlines(), 1) if text.startswith('theorem accepts_all'))
            require(res['exit'] == 1 and len(errors) == 1 and errors[0]['severity'] == 'error' and errors[0]['fileName'] == 'InventoryNegative.lean' and errors[0]['pos']['line'] == line and errors[0]['data'].startswith('Tactic `rfl` failed'), 'independent negative census control mismatch')
    version_gate = result['versions']
    require(version_gate['failure'] is None and version_gate['container_memory_limit'] == 2 * 1024**3 and version_gate['swap_limit'] == 0 and version_gate['preflight']['reserved_before'] >= 4 * 1024**3 and '--network=none' in version_gate['command'], 'version gate resource bounds mismatch')
    versions = read('census/versions.log').decode()
    require(census.digest(versions.encode()) == result['versions']['log_sha256'] and result['versions']['exit'] == 0 and result['versions']['cleanup_confirmed'], 'version gate identity mismatch')
    require('Lean (version 4.24.0' in versions and 'Lake version 5.0.0-src+797c613' in versions, 'wrong Lean/Lake versions')
    return {'declarations': 290, 'units': 308, 'fixtures': 34, 'profiles': 13, 'selected_ids': 19,
            'kernel_exports': 294, 'boundary': 'Selected-suite and exhaustive accounting verified; full repository gates remain separately required.'}
