"""Guarded regression: receipt preflight refuses forged counts, code/command
identities and weak resource evidence. Synthetic receipts are controls only and
never native matches; archive validation is not mocked for the substitution test.
"""
import copy
import hashlib
import importlib.util
import json
from pathlib import Path
import sys
import tempfile
import unittest
from unittest.mock import patch

REPO = Path(__file__).resolve().parents[4]
SOURCE = REPO/'scripts/h62/item3/g52-differential/engine_rejection_preflight.py'
sys.path.insert(0, str(SOURCE.parent))
spec = importlib.util.spec_from_file_location('rejection_preflight', SOURCE)
m = importlib.util.module_from_spec(spec)
spec.loader.exec_module(m)


def sample(bulk=Path('/outside-bulk')):
    row = dict(index=7, path='p', case='c', status='payload_rejection_reference_match',
               coverage_admitted=False, engine_rpc_complete=False, forkchoice_executed=False,
               differential_complete=False, source_semantics='unsupported-adapter-pending', source_matches=0)
    raw = (json.dumps(row)+'\n').encode()
    summary = dict(schema=1, original_format='blockchain_test_engine_x', indices=[7], selected=1,
                   coverage_admitted=False, engine_rpc_complete=False, forkchoice_executed=False,
                   differential_complete=False, full_conformance=False, final_account_map_present=False,
                   source_matches=0, native_worker_calls=1, counts={'payload_rejection_reference_match': 1},
                   results_sha256=hashlib.sha256(raw).hexdigest(), peak_aggregate_rss=1000000,
                   reference_lock_sha256=m.digest(REPO/'tests/h62/item3/g52-differential/package-lock.json'),
                   validator_sha256={name:m.digest(SOURCE.parent/name) for name in m.MODULES}, archive_binding={})
    command = dict(command=['node','--max-old-space-size=4096',m.RUNNER,str(bulk),'sample','7'],
                   stopped=None, exit=2, seconds=1.0, peak_rss=1000000,
                   external_guard=dict(schema=1,timeout_seconds=300,aggregate_rss_limit_bytes=12*1024**3,
                     address_space_soft_bytes=12*1024**3,address_space_hard_bytes=12*1024**3,
                     available_reserve_bytes=4*1024**3,swap_total_bytes=0,sampling_interval_seconds=0.5,
                     termination_grace_seconds=10,process_group=True,rlimit_as_applied=True,
                     lean_num_threads='1',minimum_available_bytes=8*1024**3,
                     runner_sha256=m.digest(SOURCE.parent/'serial_semantics.py')))
    return summary,command,raw


class PreflightControls(unittest.TestCase):
    def check(self, summary, command, raw):
        return m.receipt_preflight(REPO,Path('/outside-bulk'),'sample',summary,command,raw)

    def test_preflight_is_explicitly_not_native_qualification(self):
        summary,command,raw=sample()
        rows=self.check(summary,command,raw)
        self.assertEqual(len(rows),1)
        self.assertNotIn('native',rows[0])  # No native-evidence claim from receipt-only checks.
        self.assertFalse(summary['coverage_admitted'])
        self.assertEqual(summary['source_matches'],0)

    def test_weakened_or_missing_resource_guards_fail(self):
        mutations=[lambda c:c.pop('external_guard'),lambda c:c['external_guard'].pop('timeout_seconds'),
                   lambda c:c['external_guard'].update(timeout_seconds=301),
                   lambda c:c['external_guard'].update(address_space_soft_bytes=24*1024**3),
                   lambda c:c['external_guard'].update(available_reserve_bytes=1),
                   lambda c:c['external_guard'].update(swap_total_bytes=1),
                   lambda c:c['external_guard'].update(process_group=False),
                   lambda c:c['external_guard'].update(runner_sha256='0'*64),
                   lambda c:c.update(stopped='resource/time guard')]
        for mutate in mutations:
            with self.subTest(mutation=mutate):
                summary,command,raw=sample();mutate(command)
                with self.assertRaises(ValueError):self.check(summary,command,raw)

    def test_selection_and_command_coercion_fail(self):
        for indices in [[],[7,7],[8,7],[True],[7.5],[2**53],[0,1,2,3,4]]:
            summary,command,raw=sample();summary['indices']=indices
            with self.subTest(indices=indices),self.assertRaises(ValueError):self.check(summary,command,raw)
        for index in ['07','7.0','+7']:
            summary,command,raw=sample();command['command'][-1]=index
            with self.assertRaises(ValueError):self.check(summary,command,raw)

    def test_changed_transitive_validator_or_false_flags_fail(self):
        for mutation in ['missing-observation','changed-worker','coverage','source','rpc']:
            summary,command,raw=sample()
            if mutation=='missing-observation':summary['validator_sha256'].pop('eest_observation.mjs')
            elif mutation=='changed-worker':summary['validator_sha256']['eest_reference.mjs']='0'*64
            elif mutation=='coverage':summary['coverage_admitted']=True
            elif mutation=='source':summary['source_matches']=1
            else:summary['engine_rpc_complete']=True
            with self.subTest(mutation=mutation),self.assertRaises(ValueError):self.check(summary,command,raw)

    def test_rehashed_empty_extra_reordered_and_miscounted_rows_fail(self):
        for mutation in ['empty','extra','wrong-index','count','fractional-count','wrong-exit']:
            summary,command,raw=sample();row=json.loads(raw)
            if mutation=='empty':raw=b''
            elif mutation=='extra':raw=raw+raw
            elif mutation=='wrong-index':row['index']=8;raw=(json.dumps(row)+'\n').encode()
            elif mutation=='count':summary['counts']={'unsupported':1}
            elif mutation=='fractional-count':summary['counts']={'payload_rejection_reference_match':1.5}
            else:command['exit']=0
            summary['results_sha256']=hashlib.sha256(raw).hexdigest()
            with self.subTest(mutation=mutation),self.assertRaises(ValueError):self.check(summary,command,raw)

    def test_worker_error_cannot_use_incomplete_exit_or_lose_retryable(self):
        summary,command,raw=sample();row=json.loads(raw);row['status']='engine_error'
        summary['counts']={'engine_error':1};raw=(json.dumps(row)+'\n').encode();summary['results_sha256']=hashlib.sha256(raw).hexdigest()
        with self.assertRaisesRegex(ValueError,'retryable'):self.check(summary,command,raw)
        row['retryable']=True;raw=(json.dumps(row)+'\n').encode();summary['results_sha256']=hashlib.sha256(raw).hexdigest()
        with self.assertRaisesRegex(ValueError,'exit'):self.check(summary,command,raw)
        command['exit']=1;self.assertEqual(self.check(summary,command,raw)[0]['status'],'engine_error')

    def test_native_calls_require_mismatches_and_exclude_unsupported(self):
        for status,calls,exit_code in [('payload_rejection_mismatch',0,1),('unsupported',1,2)]:
            summary,command,raw=sample();row=json.loads(raw);row['status']=status
            raw=(json.dumps(row)+'\n').encode();summary.update(counts={status:1},native_worker_calls=calls,results_sha256=hashlib.sha256(raw).hexdigest());command['exit']=exit_code
            with self.subTest(status=status),self.assertRaisesRegex(ValueError,'native call count'):
                self.check(summary,command,raw)
            summary['native_worker_calls']=1 if status=='payload_rejection_mismatch' else 0
            self.assertEqual(self.check(summary,command,raw)[0]['status'],status)

    def test_capture_hash_names_exact_inspected_bytes_despite_replacement(self):
        with tempfile.TemporaryDirectory() as root:
            path=Path(root)/'capture.json';original=b'{"value":"inspected"}';replacement=b'{"value":"replacement"}'
            path.write_bytes(original);read=Path.read_bytes
            def replace_after_read(value):
                raw=read(value)
                if value==path:value.write_bytes(replacement)
                return raw
            with patch.object(Path,'read_bytes',replace_after_read):
                buffers,pins=m.read_captures([path])
            self.assertEqual(buffers[str(path)],original)
            self.assertEqual(pins[str(path)],hashlib.sha256(original).hexdigest())
            self.assertNotEqual(m.digest(path),pins[str(path)])

    def test_coordinated_receipts_cannot_replace_archive(self):
        with tempfile.TemporaryDirectory() as root:
            bulk=Path(root);(bulk/'evidence').mkdir();(bulk/'upstream').mkdir()
            summary,command,raw=sample(bulk)
            (bulk/'evidence/sample-summary.json').write_text(json.dumps(summary))
            (bulk/'evidence/sample.jsonl').write_bytes(raw)
            command_path=bulk/'command.json';command_path.write_text(json.dumps(command))
            (bulk/'upstream/fixtures_develop-v5.3.0.tar.gz').write_bytes(b'substituted archive')
            with self.assertRaisesRegex(ValueError,'untrusted fixture archive'):
                m.audit(REPO,bulk,'sample',command_path)


if __name__=='__main__':unittest.main()
