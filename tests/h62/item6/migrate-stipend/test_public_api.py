"""External controls for evidence completeness; no Lean/proof claim."""
import copy
import importlib.util
import json
from pathlib import Path
import subprocess
import sys
import tempfile
import unittest
sys.dont_write_bytecode = True
ROOT = Path(__file__).resolve().parents[4]
SCRIPT = ROOT / 'scripts/h62/item6/migrate-stipend/public_api.py'
spec = importlib.util.spec_from_file_location('stipend_public_api', SCRIPT)
api = importlib.util.module_from_spec(spec)
spec.loader.exec_module(api)

def name(n):
    return ['str', ['anonymous'], n]

def row(n='CostModel.rec', category='kernel'):
    return {'record': 'declaration', 'module': api.MODULE, 'category': category,
            'name': n, 'name_parts': name(n), 'private': False, 'internal': False,
            'signature': {'kind': 'recursor', 'unsafe': False, 'level_params': [name('u')],
                          'type_repr': 'Lean.Expr.sort (Lean.Level.param `u)',
                          'binders': [], 'result_repr': 'Lean.Expr.sort (Lean.Level.param `u)', 'axioms': []}}

def log(rows):
    records = [{'record': 'header', 'schema_version': 1, 'module': api.MODULE,
                'kernel_count': sum(r['category'] == 'kernel' for r in rows),
                'compiler_extra_count': sum(r['category'] == 'compiler_extra' for r in rows)}]
    records += rows + [{'record': 'end', 'module': api.MODULE, 'count': len(rows)}]
    return '\n'.join(api.PREFIX + json.dumps(r) for r in records) + '\n'

def receipt(p, data):
    # Synthetic metadata for external negative controls, never actual Lean evidence.
    artifact = p/'synthetic.olean'; artifact.write_bytes(b'synthetic external-control object')
    return {'module': api.MODULE, 'exit_code': 0, 'stop': None,
            'toolchain': 'leanprover/lean4:v4.24.0',
            'archive_sha256': api.ARCHIVES['leanprover/lean4:v4.24.0'],
            'lean_version': 'Lean (version 4.24.0, synthetic external-control metadata)',
            'lake_version': 'Lake version synthetic-test (Lean version 4.24.0)',
            'log_sha256': data['raw_export_sha256'],
            'fixture_sha256': api.file_sha(ROOT/'tests/h62/item6/migrate-stipend/PublicInventory.lean'),
            'module_source_sha256': api.file_sha(ROOT/'Solidity/Stipend/Rule.lean'),
            'olean_path': str(artifact), 'olean_sha256': api.file_sha(artifact),
            'command': ['/synthetic/lean', '-j1', str(ROOT/'tests/h62/item6/migrate-stipend/PublicInventory.lean')]}

class PublicApiControls(unittest.TestCase):
    def test_generated_and_private_families_retained(self):
        names = ['Body.noConfusion', 'Body.recOn', 'Body.casesOn', 'stmtCost.match_1',
                 '_private.Rule.0.proof', 'CostModel.toCtorIdx']
        rows = [row(n) for n in names]; rows[-2]['private'] = True
        self.assertEqual(len(api.parse(log(rows))['rows']), len(names))

    def test_module_count_truncation_rejected(self):
        data = log([row()]).replace('"kernel_count": 1', '"kernel_count": 2')
        with self.assertRaises(ValueError): api.parse(data)

    def test_missing_compiler_extra_rejected(self):
        data = log([row()]).replace('"compiler_extra_count": 0', '"compiler_extra_count": 1')
        with self.assertRaises(ValueError): api.parse(data)

    def test_missing_trailer_rejected(self):
        with self.assertRaises(ValueError): api.parse('\n'.join(log([row()]).splitlines()[:-1]))

    def test_duplicate_structural_names_rejected(self):
        with self.assertRaises(ValueError): api.parse(log([row(), row()]))

    def test_wrong_module_rejected(self):
        r = row(); r['module'] = 'Solidity.Syntax.Raw'
        with self.assertRaises(ValueError): api.parse(log([r]))

    def test_kernel_type_required(self):
        r = row(); r['signature'] = None
        with self.assertRaises(ValueError): api.parse(log([r]))

    def test_unresolved_compiler_names_never_pass_even_when_identical(self):
        r = row('stmtCost._closed_1', 'compiler_extra'); r['signature'] = None
        data = api.parse(log([r])); result = api.compare(data, data)
        self.assertFalse(result['all_original_records_identical_and_resolved'])
        self.assertEqual(len(result['unresolved']), 2)

    def test_universe_order_is_part_of_signature(self):
        a = row(); a['signature']['level_params'] = [name('u'), name('v')]
        b = copy.deepcopy(a); b['signature']['level_params'].reverse()
        self.assertEqual(len(api.compare(api.parse(log([a])), api.parse(log([b])))['changed']), 1)

    def test_binder_kind_change_is_recorded(self):
        a = row(); a['signature']['binders'] = [{'name_parts': name('x'), 'domain_repr': 'Nat', 'binder_kind': 'Lean.BinderInfo.implicit'}]
        b = copy.deepcopy(a); b['signature']['binders'][0]['binder_kind'] = 'Lean.BinderInfo.default'
        self.assertFalse(api.compare(api.parse(log([a])), api.parse(log([b])))['all_original_records_identical_and_resolved'])

    def test_unknown_binder_and_duplicate_universe_rejected(self):
        a = row(); a['signature']['binders'] = [{'name_parts': name('x'), 'domain_repr': 'Nat', 'binder_kind': 'guess'}]
        with self.assertRaises(ValueError): api.parse(log([a]))
        a = row(); a['signature']['level_params'] *= 2
        with self.assertRaises(ValueError): api.parse(log([a]))

    def test_private_axiom_change_not_excluded(self):
        a = row('_private.Rule.0.proof'); a['private'] = True
        b = copy.deepcopy(a); b['signature']['axioms'] = [name('sorryAx')]
        result = api.compare(api.parse(log([a])), api.parse(log([b])))
        self.assertEqual(len(result['changed']), 1)
        self.assertFalse(result['all_original_records_identical_and_resolved'])

    def test_removal_and_addition_differ(self):
        result = api.compare(api.parse(log([row('Body.recOn')])), api.parse(log([row('Body.recOnNew')])))
        self.assertEqual(len(result['missing']), 1); self.assertEqual(len(result['added']), 1)

    def test_records_after_trailer_rejected(self):
        with self.assertRaises(ValueError): api.parse(log([row()]) + api.PREFIX + json.dumps(row('late')))

    def test_boolean_count_rejected(self):
        with self.assertRaises(ValueError): api.parse(log([row()]).replace('"kernel_count": 1', '"kernel_count": true'))

    def test_fixture_reproduction(self):
        expected = ROOT / 'tests/h62/item6/migrate-stipend/PublicInventory.lean'
        self.assertEqual(subprocess.check_output([sys.executable, str(SCRIPT), 'fixture']), expected.read_bytes())

    def test_cli_preserves_existing_evidence_and_symlink_targets(self):
        with tempfile.TemporaryDirectory() as tmp:
            p = Path(tmp); source = p/'input.log'; source.write_text(log([row()]))
            rfile = p/'receipt.json'; rfile.write_text(json.dumps(receipt(p, api.parse(source.read_text()))))
            existing = p/'existing'; existing.write_text('sentinel'); link = p/'link'; link.symlink_to(existing)
            for out in (existing, link):
                r = subprocess.run([sys.executable, str(SCRIPT), 'extract', str(source), str(out), '--receipt', str(rfile)], capture_output=True)
                self.assertNotEqual(r.returncode, 0)
                self.assertEqual(existing.read_text(), 'sentinel')

    def test_valid_receipt_metadata_binds_bytes(self):
        with tempfile.TemporaryDirectory() as tmp:
            data = api.parse(log([row()])); r = receipt(Path(tmp), data)
            self.assertTrue(api.validate_receipt(r, data)['supplied_receipt_fields_verified'])

    def test_bad_or_failed_run_receipts_rejected(self):
        with tempfile.TemporaryDirectory() as tmp:
            data = api.parse(log([row()])); original = receipt(Path(tmp), data)
            changes = [('exit_code', 1), ('exit_code', False), ('stop', 'RESOURCE_STOP'),
                       ('archive_sha256', '0'*64), ('lean_version', 'Lean 4.35.0'),
                       ('log_sha256', '0'*64), ('fixture_sha256', '0'*64),
                       ('module_source_sha256', '0'*64), ('olean_sha256', '0'*64),
                       ('command', ['/synthetic/lean']),
                       ('lean_version', 'Lean (version 4.24.01, synthetic)'),
                       ('lake_version', 'Lake version synthetic (Lean version 4.24.01)'),
                       ('command', ['/synthetic/lean', '-j1', '-j8', str(ROOT/'tests/h62/item6/migrate-stipend/PublicInventory.lean')]),
                       ('command', ['/synthetic/lean', '-j1', '--threads=8', str(ROOT/'tests/h62/item6/migrate-stipend/PublicInventory.lean')])]
            for key, value in changes:
                with self.subTest(field=key, value=value):
                    r = copy.deepcopy(original); r[key] = value
                    with self.assertRaises(ValueError): api.validate_receipt(r, data)
            r = copy.deepcopy(original); del r['stop']
            with self.assertRaises(ValueError): api.validate_receipt(r, data)

    def test_same_toolchain_receipts_cannot_fill_old_and_new_roles(self):
        with tempfile.TemporaryDirectory() as tmp:
            data = api.parse(log([row()])); r = receipt(Path(tmp), data)
            with self.assertRaises(ValueError): api.validate_pair(r, r, data, data)

    def test_additional_axiom_requires_separate_audit(self):
        added = row('newAxiom'); added['signature']['kind'] = 'axiom'
        result = api.compare(api.parse(log([row()])), api.parse(log([row(), added])))
        self.assertTrue(result['all_original_records_identical_and_resolved'])
        self.assertEqual(result['added_declarations_require_audit'][0]['name'], 'newAxiom')
        self.assertFalse(result['full_migration_gate_pass'])

    def test_log_digest_changes_with_diagnostic_noise(self):
        a = log([row()]); b = 'warning: synthetic control\n' + a
        self.assertNotEqual(api.parse(a)['raw_export_sha256'], api.parse(b)['raw_export_sha256'])

if __name__ == '__main__': unittest.main()
