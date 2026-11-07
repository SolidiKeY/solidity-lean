"""Guarded regression: absent/overlapping scope evidence cannot silently confirm an owner."""
import sys,unittest,tempfile
from pathlib import Path
sys.path.insert(0,str(Path(__file__).resolve().parents[4]/'scripts/h62/item2/audit-calculus'))
from standing_owners import parse_scope,classify_files,load_scopes,match_live_scopes

class StandingOwnerControls(unittest.TestCase):
    file='Solidity/Calculus/Correct.lean'
    def scope(self,namespace='live',entries=None):
        return {'namespace':namespace,'entries':entries or [],'path':'scope.json'}
    def test_exact_live_match_remains_unresolved(self):
        self.assertEqual(match_live_scopes(self.file,[self.scope(entries=[self.file])]),['scope.json'])
    def test_glob_and_directory_overlaps_remain_unresolved(self):
        for pattern in ['Solidity/Calculus/**','Solidity/Calculus','Solidity/{Calculus,Backend}/Correct.lean']:
            entries=parse_scope({'write_namespace':'live','new_file_scope':[pattern]})['entries']
            self.assertEqual(match_live_scopes(self.file,[self.scope(entries=entries)]),['scope.json'])
    def test_migration_overlay_does_not_transfer_live_ownership(self):
        result=match_live_scopes(self.file,[self.scope('migration-overlay/v4.35',['Solidity/**'])])
        self.assertEqual(result,[])
    def test_missing_scope_inputs_refused(self):
        with self.assertRaises(ValueError):match_live_scopes(self.file,[])
    def test_unknown_namespace_refused(self):
        with self.assertRaises(ValueError):parse_scope({'write_namespace':'future'})
    def test_unknown_scope_field_refused(self):
        with self.assertRaises(ValueError):parse_scope({'write_namespace':'live','other_ownership':['Solidity/**']})
    def test_invalid_scope_paths_refused(self):
        for paths in [['../Solidity/Calculus'],['/Solidity'],[''],[None],'Solidity/**']:
            with self.subTest(paths=paths),self.assertRaises(ValueError):parse_scope({'write_namespace':'live','exclusive_files':paths})
    def test_other_areas_do_not_inherit_rule(self):
        with self.assertRaises(ValueError):match_live_scopes('Solidity/Backend/Creation/Artifact.lean',[self.scope()])
    def test_tampered_index_refused(self):
        with tempfile.TemporaryDirectory() as t:
            p=Path(t);(p/'SHA256SUMS').write_text('untrusted');(p/'manifest.json').write_text('{}')
            with self.assertRaisesRegex(ValueError,'unauthenticated'):load_scopes(p)

    def test_nonempty_partial_scope_list_cannot_confirm_ownership(self):
        with self.assertRaisesRegex(ValueError,'authenticated package'):
            classify_files([self.file],[self.scope('migration-overlay/v4.35',['Solidity/**'])])
