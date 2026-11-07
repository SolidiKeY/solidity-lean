#!/usr/bin/env python3
"""Mutation controls for exact census identities and failed/stale Lean exports."""
import copy
import importlib.util
import json
from pathlib import Path
import tempfile
import unittest

spec = importlib.util.spec_from_file_location('exporter', Path(__file__).with_name('export_signatures.py'))
exporter = importlib.util.module_from_spec(spec)
spec.loader.exec_module(exporter)
EV = Path('/workspace/h62-audit-readonly-calls/continuation-h69/evidence')


class ExportAcceptance(unittest.TestCase):
    @classmethod
    def setUpClass(cls):
        cls.full = exporter.census.census()
        cls.expected = cls.full['declarations'][0]
        cls.dataset = {'declarations': [cls.expected]}
        exported = json.loads((EV/'elaborated-signatures.json').read_text())
        cls.entry = exported['declarations'][0]
        cls.receipt = json.loads((EV/'signature-query-typed.json').read_text())

    def log(self, item=None):
        return 'H62-SIGNATURE '+json.dumps(item or self.entry)+'\n'

    def test_positive_parser_and_real_gate(self):
        self.assertEqual(exporter.collect(self.log(), self.dataset)['declaration_count'], 1)
        exporter.verify_receipt(EV/'ExportSignatures.lean', EV/'signature-query-typed.log',
                                EV/'signature-query-typed.json', self.full)

    def test_missing_and_duplicate_records_rejected(self):
        with self.assertRaisesRegex(ValueError, 'uncovered'):
            exporter.collect('', self.dataset)
        with self.assertRaisesRegex(ValueError, 'duplicate'):
            exporter.collect(self.log()+self.log(), self.dataset)

    def test_wrong_kernel_identity_rejected(self):
        entry = copy.deepcopy(self.entry)
        entry['kernel_name'] = 'WRONG.NAME'
        with self.assertRaisesRegex(ValueError, 'kernel identity'):
            exporter.collect(self.log(entry), self.dataset)

    def test_private_kernel_identity_rejected(self):
        exported = json.loads((EV/'elaborated-signatures.json').read_text())
        entry = copy.deepcopy(next(r for r in exported['declarations'] if r['kernel_name'].startswith('_private.')))
        row = next(r for r in self.full['declarations'] if r['source_name'] == entry['source_name'])
        entry['kernel_name'] = entry['source_name']
        with self.assertRaisesRegex(ValueError, 'kernel identity'):
            exporter.collect(self.log(entry), {'declarations': [row]})

    def test_binder_metadata_tampering_rejected_on_ingestion(self):
        artifact = json.loads((EV/'elaborated-signatures.json').read_text())
        entry = next(r for r in artifact['declarations'] if r['forall_binders'])
        entry['forall_binders'] = []
        with self.assertRaisesRegex(ValueError, 'verified log'):
            exporter.census.attach_elaboration(copy.deepcopy(self.full), artifact)

    def test_syntactic_binder_free_does_not_discharge_witness(self):
        artifact = json.loads((EV/'elaborated-signatures.json').read_text())
        result = exporter.census.attach_elaboration(copy.deepcopy(self.full), artifact)
        empty = [r for r in result['declarations'] if not r['elaborated']['forall_binders']]
        self.assertEqual(len(empty), 339)
        self.assertTrue(all(r['witness_status'] == 'pending' for r in empty))

    def test_wrong_module_identity_rejected(self):
        entry = copy.deepcopy(self.entry)
        entry['module'] = 'Wrong.Module'
        with self.assertRaisesRegex(ValueError, 'module identity'):
            exporter.collect(self.log(entry), self.dataset)

    def test_complete_export_followed_by_error_rejected(self):
        with self.assertRaisesRegex(ValueError, 'Lean error'):
            exporter.collect(self.log()+'query.lean:999:0: error: later failure\n', self.dataset)

    def check_bad_receipt(self, change, reason):
        receipt = copy.deepcopy(self.receipt)
        change(receipt)
        with tempfile.TemporaryDirectory(prefix='h62-export-receipt-') as tmp:
            path = Path(tmp)/'receipt.json'
            path.write_text(json.dumps(receipt))
            with self.assertRaisesRegex(ValueError, reason):
                exporter.verify_receipt(EV/'ExportSignatures.lean', EV/'signature-query-typed.log', path, self.full)

    def test_failed_lean_gate_rejected(self):
        self.check_bad_receipt(lambda r: r.update(gate_exit=1, status='fail'), 'did not pass')

    def test_tampered_log_hash_rejected(self):
        self.check_bad_receipt(lambda r: r.update(log_sha256='0'*64), 'log hash')

    def test_tampered_query_hash_rejected(self):
        self.check_bad_receipt(lambda r: r['input_source_sha256'].update({str(EV/'ExportSignatures.lean'): '0'*64}), 'query hash')

    def test_wrong_tool_binary_rejected(self):
        self.check_bad_receipt(lambda r: r.update(lean_binary_sha256='0'*64), 'tool binary')


if __name__ == '__main__':
    unittest.main()
