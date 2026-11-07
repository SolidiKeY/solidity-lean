#!/usr/bin/env python3
"""Guarded regression: resumed coverage must reject overlapping, input-only,
stopped/truncated or forged native artifacts. Mutations are negative controls,
not extra fixture passes; positive coverage uses only real captured runs.
"""
import hashlib
import gzip
import importlib.util
import json
import os
import shutil
import tempfile
import unittest
from pathlib import Path

REPO = Path(__file__).resolve().parents[4]
BULK = Path(os.environ['G52_BULK']).resolve()  # Missing corpus is an error, never a skip.
SPEC = importlib.util.spec_from_file_location('coverage', REPO/'scripts/h62/item3/g52-differential/engine_execution_coverage.py')
MODULE = importlib.util.module_from_spec(SPEC)
SPEC.loader.exec_module(MODULE)


class CoverageControls(unittest.TestCase):
    def test_real_disjoint_native_ranges(self):
        result = MODULE.coverage(REPO, BULK, ['review-fix-0-20', 'review-fix-20-40', 'review-fix-40-60', 'review-fix-60-80'])
        self.assertEqual(result['processed_unique_cases'], 80)
        self.assertEqual(result['counts'], {'payload_reference_match': 80})
        self.assertEqual(result['unprocessed_ranges'], [[80, 21124]])
        self.assertFalse(result['differential_complete'])
        self.assertEqual(result['source_matches'], 0)

    def test_duplicate_overlap_and_binding_only_rejected(self):
        for labels, error in [(['review-fix-0-20', 'review-fix-0-20'], 'duplicate'),
                              (['review-fix-0-20', 'review-fix-overlap'], 'overlapping'),
                              (['engine-x-bindings'], 'not a native')]:
            with self.subTest(labels=labels), self.assertRaisesRegex(ValueError, error):
                MODULE.coverage(REPO, BULK, labels)

    def test_corrupt_artifact_controls(self):
        # Only negative tests use this temporary copy. Large pinned inputs are
        # linked read-only; original sealed results and receipts are never edited.
        def other_allocation(summary, command, rows):
            entries = json.loads((BULK/'engine-x-allocations-index.json').read_text())
            current = rows[0]['allocation_binding']['pre_hash']
            key = next(key for key in entries if key != current)
            entry = entries[key]
            rows[0]['allocation_binding'].update(pre_hash=key, allocation_path=entry['path'],
                                                 allocation_source_sha256=entry['source_sha256'],
                                                 allocation_record_sha256=entry['record_sha256'])
        def fraction(field, block=False):
            def mutate(summary, command, rows):
                target = rows[0]['blocks'][0] if block else rows[0]['blocks'][0]['transactions'][0]
                target[field] = int(target[field]) + 0.5
            return mutate
        mutations = [
            ('string-log-list', lambda s,c,r:next(tx for row in r for block in row['blocks'] for tx in block['transactions'] if tx['execution_exception'] is None).update(logs='garbage'), 'malformed native logs'),
            ('malformed-log-data', lambda s,c,r:r[0]['blocks'][0]['transactions'][0].update(logs=[dict(address='0x'+'00'*20,topics=[],data='0x0')]), 'malformed native logs'),
            ('bool-row-index', lambda s,c,r:r[0].update(index=False), 'range identity'),
            ('float-selected', lambda s,c,r:s.update(selected=20.0), 'summary count'),
            ('float-status-count', lambda s,c,r:s['counts'].update(payload_reference_match=20.0), 'status count'),
            ('malformed-log-list', lambda s,c,r:r[0]['blocks'][0]['transactions'][0].update(logs={}), 'malformed native logs'),
            ('malformed-log-address', lambda s,c,r:r[0]['blocks'][0]['transactions'][0].update(logs=[dict(address='0x00',topics=[],data='0x')]), 'malformed native logs'),
            ('malformed-log-topic', lambda s,c,r:r[0]['blocks'][0]['transactions'][0].update(logs=[dict(address='0x'+'00'*20,topics=['0x00'],data='0x')]), 'malformed native logs'),
            ('fraction-block-number', fraction('number', True), 'integer observation'),
            ('fraction-block-gas', fraction('gas_used', True), 'integer observation'),
            ('fraction-gas-limit', fraction('gas_limit'), 'integer observation'),
            ('fraction-gas-spent', fraction('total_gas_spent'), 'integer observation'),
            ('fraction-cumulative-gas', fraction('receipt_cumulative_gas_used'), 'integer observation'),
            ('missing-external-guard', lambda s,c,r:c.pop('external_guard'), 'external resource guard'),
            ('weakened-timeout', lambda s,c,r:c['external_guard'].update(timeout_seconds=301), 'external timeout'),
            ('weakened-rss', lambda s,c,r:c['external_guard'].update(aggregate_rss_limit_bytes=13*1024**3), 'external resource guard settings'),
            ('weakened-address-space', lambda s,c,r:c['external_guard'].update(address_space_hard_bytes=13*1024**3), 'external resource guard settings'),
            ('weakened-reserve', lambda s,c,r:c['external_guard'].update(available_reserve_bytes=1024**3), 'external resource guard settings'),
            ('swap-enabled', lambda s,c,r:c['external_guard'].update(swap_total_bytes=4096), 'external resource guard settings'),
            ('missing-as-application', lambda s,c,r:c['external_guard'].update(rlimit_as_applied=False), 'external resource guard settings'),
            ('wrong-external-runner', lambda s,c,r:c['external_guard'].update(runner_sha256='0'*64), 'external timeout/runner'),
            ('bad-minimum-reserve', lambda s,c,r:c['external_guard'].update(minimum_available_bytes=1), 'external resource observations'),
            ('coordinated-input-result', lambda s,c,r:r[0]['blocks'][0].update(state_root='0x'+'00'*32), 'pinned archive'),
            ('missing-stop', lambda s, c, r: c.pop('stopped'), 'stopped/incomplete'),
            ('stopped-job', lambda s, c, r: c.update(stopped='resource guard'), 'stopped/incomplete'),
            ('wrong-validator', lambda s, c, r: s.update(native_worker_sha256='0'*64), 'changed validator'),
            ('wrong-wrapper', lambda s, c, r: s.update(adapter_sha256='0'*64), 'unbound wrapper'),
            ('truncated', lambda s, c, r: r.pop(), 'truncated native range'),
            ('wrong-exit', lambda s, c, r: c.update(exit=0), 'wrong native exit'),
            ('source-pass', lambda s, c, r: s.update(differential_complete=True), 'conflated'),
            ('bind-row', lambda s, c, r: r[0].update(status='allocation_bound_input'), 'non-native result'),
            ('wrong-index', lambda s, c, r: r[0].update(index=1), 'range identity'),
            ('account-map', lambda s, c, r: r[0]['allocation_binding'].update(final_account_map_present=True), 'allocation mismatch'),
            ('other-valid-allocation', other_allocation, 'pinned input'),
            ('wrong-input-tx-hash', lambda s, c, r: r[0]['blocks'][0]['transactions'][0].update(hash='0x'+'00'*32), 'pinned input'),
            ('wrong-input-tx-type', lambda s, c, r: r[0]['blocks'][0]['transactions'][0].update(type=99), 'pinned input'),
            ('wrong-input-tx-limit', lambda s, c, r: r[0]['blocks'][0]['transactions'][0].update(gas_limit='1'), 'pinned input'),
            ('negative-tx-spent', lambda s, c, r: r[0]['blocks'][0]['transactions'][0].update(total_gas_spent='-1'), 'integer observation'),
            ('overspent-tx', lambda s, c, r: r[0]['blocks'][0]['transactions'][0].update(total_gas_spent=str(int(r[0]['blocks'][0]['transactions'][0]['gas_limit'])+1)), 'pinned input limit'),
            ('empty-payload-evidence', lambda s, c, r: (r[0].update(blocks=[]), r[0]['binding'].update(payload_block_hashes=[])), 'pinned input'),
            ('wrong-input-payload-hash', lambda s, c, r: (r[0]['blocks'][0].update(hash='0x'+'00'*32), r[0]['binding'].update(payload_block_hashes=['0x'+'00'*32])), 'pinned input'),
            ('duplicated-input-block', lambda s, c, r: (r[0]['blocks'].append(r[0]['blocks'][0]), r[0]['binding']['payload_block_hashes'].append(r[0]['binding']['payload_block_hashes'][0])), 'pinned input'),
            ('empty-tx-zero-gas', lambda s, c, r: r[0]['blocks'][0].update(transactions=[], gas_used='0'), 'pinned input'),
            ('wrong-input-state-root', lambda s, c, r: r[0]['blocks'][0].update(state_root='0x'+'00'*32), 'pinned input'),
            ('wrong-input-block-number', lambda s, c, r: r[0]['blocks'][0].update(number='999999'), 'pinned input'),
        ]
        for name, mutate, error in mutations:
            with self.subTest(name=name), tempfile.TemporaryDirectory(prefix='range-control-', dir=BULK) as temporary:
                root = Path(temporary)
                (root/'evidence').mkdir()
                (root/'reference').mkdir()
                (root/'upstream').mkdir()
                for p in ['engine-x-inputs.jsonl.gz', 'archive-inventory.jsonl.gz', 'engine-x-allocations.jsonl', 'engine-x-allocations-index.json', 'reference/package-lock.json', 'reference/package.json', 'reference/node_modules', 'upstream/fixtures_develop-v5.3.0.tar.gz']:
                    (root/p).symlink_to(BULK/p)
                for p in ['engine-x-export.json', 'archive-census.json']:
                    shutil.copyfile(BULK/'evidence'/p, root/'evidence'/p)
                summary = json.loads((BULK/'evidence/review-fix-0-20-summary.json').read_text())
                command = json.loads((BULK/'evidence/review-fix-0-20-command.json').read_text())
                rows = [json.loads(line) for line in (BULK/'evidence/review-fix-0-20.jsonl').read_text().splitlines()]
                command['command'][3] = str(root)
                command['command'][5] = 'negative-control'
                mutate(summary, command, rows)
                if name == 'coordinated-input-result':
                    (root/'engine-x-inputs.jsonl.gz').unlink()
                    with gzip.open(BULK/'engine-x-inputs.jsonl.gz', 'rt') as source, (root/'engine-x-inputs.jsonl.gz').open('wb') as raw:
                        with gzip.GzipFile(filename='', fileobj=raw, mode='wb', mtime=0) as out:
                            for line in source:
                                record = json.loads(line)
                                if record['index'] == 0:
                                    record['fixture']['engineNewPayloads'][0]['params'][0]['stateRoot'] = rows[0]['blocks'][0]['state_root']
                                out.write((json.dumps(record, sort_keys=True, separators=(',', ':'))+'\n').encode())
                    receipt_path = root/'evidence/engine-x-export.json'
                    receipt = json.loads(receipt_path.read_text())
                    receipt['stream_sha256'] = MODULE.digest(root/'engine-x-inputs.jsonl.gz')
                    receipt_path.write_text(json.dumps(receipt))
                    summary['input_sha256'] = receipt['stream_sha256']
                    summary['export_sha256'] = MODULE.digest(receipt_path)
                data = ''.join(json.dumps(row)+'\n' for row in rows).encode()
                summary['results_sha256'] = hashlib.sha256(data).hexdigest()
                (root/'evidence/negative-control.jsonl').write_bytes(data)
                (root/'evidence/negative-control-summary.json').write_text(json.dumps(summary))
                (root/'evidence/negative-control-command.json').write_text(json.dumps(command))
                with self.assertRaisesRegex(ValueError, error):
                    MODULE.coverage(REPO, root, ['negative-control'])


if __name__ == '__main__':
    unittest.main()
