"""Source-preservation checks for the additive overlay generator, not Lean."""
from pathlib import Path
import json
import sys
import tomllib
import unittest
import subprocess
import hashlib

ROOT = Path(__file__).resolve().parents[4]
sys.path.insert(0, str(ROOT/'scripts/h62/item4/generic-p10'))
import census
import make_candidate as G


class CandidateTests(unittest.TestCase):
    def setUp(self):
        self.original = subprocess.check_output(["git","-C",str(ROOT),"show",f"{census.BASE}:{G.SOURCE.as_posix()}"],text=True)

    def test_all_original_signatures_and_other_bodies_are_retained(self):
        candidate = G.candidate(self.original)
        old = {r['name']: r for r in census.declarations(self.original, 'old')}
        new = {r['name']: r for r in census.declarations(candidate, 'new')}
        self.assertEqual(set(new)-set(old), {'table_case'})
        for name, row in old.items():
            self.assertEqual(row['statement_sha256'], new[name]['statement_sha256'], name)
            if name not in set(G.CASES)|{'observed'}:
                self.assertEqual(row['declaration_sha256'], new[name]['declaration_sha256'], name)
        self.assertEqual(candidate.count('exact table_case .'), 9)

    def test_unknown_original_positive_proof_shape_is_refused(self):
        changed = self.original.replace('  apply observed\n  decide +kernel', '  exact other_proof', 1)
        with self.assertRaises(ValueError): G.candidate(changed)

    def test_h126_production_application_retains_original_contracts(self):
        import export_migration
        actual=(ROOT/G.SOURCE).read_text()
        receipt=json.loads((ROOT/'tests/h62/item4/generic-p10/owner-relay-request.json').read_text())
        self.assertEqual(hashlib.sha256(actual.encode()).hexdigest(),receipt['proposed_source_sha256'])
        old={r['name']:r for r in census.declarations(self.original,'old')}
        new={r['name']:r for r in census.declarations(actual,'production')}
        self.assertEqual(len(old),32)
        self.assertEqual(set(new)-set(old),export_migration.NEW_NAMES)
        for name,row in old.items():
            self.assertEqual(row['statement_sha256'],new[name]['statement_sha256'],name)
            if name not in set(G.CASES)|{'observed'}:
                self.assertEqual(row['declaration_sha256'],new[name]['declaration_sha256'],name)
        self.assertEqual(actual.count('exact table_case .'),9)

    def test_standalone_package_identity_and_remote_pins(self):
        package = ROOT/'tests/h62/item4/generic-p10'
        config = tomllib.loads((package/'lakefile.toml').read_text())
        manifest = json.loads((package/'lake-manifest.json').read_text())
        owner = json.loads((ROOT/'Bridge/lake-manifest.json').read_text())
        self.assertEqual(manifest['name'].strip('«»'), config['name'])
        self.assertEqual({p['name']:p['rev'] for p in manifest['packages'] if p['type']=='git'},
                         {p['name']:p['rev'] for p in owner['packages'] if p['type']=='git'})

if __name__ == '__main__': unittest.main()
