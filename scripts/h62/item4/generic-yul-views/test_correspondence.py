import unittest
import subprocess
import tempfile
from pathlib import Path
import census
from correspondence import compare, source_preservation, control_rows

class CorrespondenceControls(unittest.TestCase):
    original = "theorem byte_component : True := True.intro\ntheorem byte_component_decode : True := True.intro\n"
    candidate = "theorem original_byte_component : True := True.intro\ntheorem original_byte_component_decode : True := True.intro\n"
    def test_exact_instances(self):
        self.assertEqual(len(compare(self.original,self.candidate)),2)
    def test_changed_observation_refused(self):
        with self.assertRaises(ValueError): compare(self.original,self.candidate.replace(': True', ': False',1))
    def test_changed_string_literal_refused(self):
        original = self.original.replace('True', '"before" = "before"')
        candidate = self.candidate.replace('True', '"after!" = "after!"')
        with self.assertRaises(ValueError): compare(original, candidate)
    def test_changed_literal_whitespace_refused(self):
        original = self.original.replace(': True', ': "a b" = "a b"')
        candidate = self.candidate.replace(': True', ': "a  b" = "a  b"')
        with self.assertRaises(ValueError): compare(original, candidate)
    def test_literal_syntax_is_not_a_boundary(self):
        original = self.original.replace(': True', ': "x := where" = "x := where"')
        candidate = self.candidate.replace(': True', ': "x := where" = "x := where"')
        self.assertEqual(len(compare(original, candidate)), 2)
    def test_escaped_literal_whitespace_refused(self):
        original = self.original.replace(': True', r': "a\n  b" = "a\n  b"')
        candidate = self.candidate.replace(': True', r': "a\n b" = "a\n b"')
        with self.assertRaises(ValueError): compare(original, candidate)
    def test_raw_literal_refused(self):
        original = self.original.replace(': True', ': r#"a" b c"# = r#"a" b c"#')
        candidate = self.candidate.replace(': True', ': r#"a" b  c"# = r#"a" b c"#')
        with self.assertRaises(ValueError): compare(original, candidate)
    def test_character_literal_refused(self):
        original = self.original.replace(': True', ": (' ' : Char) = ' '")
        candidate = self.candidate.replace(': True', ": ('\t' : Char) = ' '")
        with self.assertRaises(ValueError): compare(original, candidate)
    def test_string_mutation_refused(self):
        a = self.original.replace('True', '"A" = "A"')
        b = self.candidate.replace('True', '"A" = "B"')
        with self.assertRaises(ValueError): compare(a,b)
    def test_string_whitespace_mutation_refused(self):
        a = self.original.replace('True', '"A B" = "A B"')
        b = self.candidate.replace('True', '"A  B" = "A B"')
        with self.assertRaises(ValueError): compare(a,b)
    def test_quoted_identifier_mutation_refused(self):
        a = self.original.replace('True', '«has where A» = «has where A»')
        b = self.candidate.replace('True', '«has where A» = «has where B»')
        with self.assertRaises(ValueError): compare(a,b)
    def test_dropped_instance_refused(self):
        with self.assertRaises(ValueError): compare(self.original,self.candidate.splitlines()[0])

class FrozenSourceControls(unittest.TestCase):
    def setUp(self):
        self.temp = tempfile.TemporaryDirectory()
        self.addCleanup(self.temp.cleanup)
        self.root = Path(self.temp.name)
        self.views = self.root / "Solidity/Yul/Views"
        self.views.mkdir(parents=True)
        self.path = self.views / "ReadControls.lean"
        self.original = CorrespondenceControls.original
        self.path.write_text(self.original)
        self.git("init", "-q")
        self.freeze()

    def git(self, *args):
        return subprocess.check_output(["git", "-c", "user.name=Fixture",
            "-c", "user.email=fixture@example.invalid", "-c", "commit.gpgsign=false",
            "-c", "core.hooksPath=/dev/null", *args], cwd=self.root, stderr=subprocess.PIPE)

    def freeze(self):
        self.git("add", "-A")
        self.git("commit", "-qm", "frozen fixture")
        self.base = self.git("rev-parse", "HEAD").decode().strip()

    def classify(self, inventory=None):
        inventory = census.scan(self.root) if inventory is None else inventory
        preservation = source_preservation(self.root, inventory["files"], base=self.base)
        return preservation, control_rows(inventory, preservation)

    def test_unchanged_has_verified_preservation(self):
        preservation, rows = self.classify()
        self.assertEqual(preservation["baseline_files"], 1)
        self.assertEqual(preservation["removed_files"], [])
        self.assertTrue(all(row["preservation_status"] == "unchanged" for row in rows))
        self.assertTrue(all(row["disposition"].startswith("preserved original source;") for row in rows))

    def test_matching_changed_pair_is_not_preserved(self):
        self.path.write_text(self.original.replace(": True", ": False"))
        candidate = CorrespondenceControls.candidate.replace(": True", ": False")
        self.assertEqual(len(compare(self.path.read_text(), candidate)), 2)
        _, rows = self.classify()
        self.assertTrue(all(row["preservation_status"] == "modified" for row in rows))
        self.assertTrue(all("preservation not established" in row["disposition"] for row in rows))

    def test_proof_only_change_is_not_blob_identity(self):
        self.path.write_text(self.original.replace("True.intro", "by exact True.intro"))
        self.assertEqual(len(compare(self.path.read_text(), CorrespondenceControls.candidate)), 2)
        _, rows = self.classify()
        self.assertTrue(all(row["preservation_status"] == "modified" for row in rows))

    def test_added_control_is_not_original(self):
        (self.views / "AddedControls.lean").write_text("theorem extra : True := True.intro\n")
        preservation, rows = self.classify()
        added = next(row for row in rows if row["name"] == "extra")
        self.assertEqual(added["preservation_status"], "added")
        self.assertNotIn("preserved original", added["disposition"])
        self.assertEqual(preservation["baseline_files"], 1)
        self.assertEqual(preservation["current_files"], 2)

    def test_other_readcontrols_is_not_a_selected_pair(self):
        nested = self.views / "Nested/ReadControls.lean"
        nested.parent.mkdir()
        nested.write_text(self.original)
        _, rows = self.classify()
        nested_rows = [row for row in rows if row["path"].endswith("Nested/ReadControls.lean")]
        self.assertEqual(len(nested_rows), 2)
        self.assertTrue(all("candidate correspondence available" not in row["disposition"]
            for row in nested_rows))

    def test_removed_file_is_reported(self):
        (self.views / "KeepControls.lean").write_text("theorem keep : True := True.intro\n")
        self.freeze()
        self.path.unlink()
        preservation, _ = self.classify()
        self.assertEqual(preservation["removed_files"], ["Solidity/Yul/Views/ReadControls.lean"])

    def test_stale_inventory_is_refused(self):
        inventory = census.scan(self.root)
        self.path.write_text(self.original + "-- changed after scan\n")
        with self.assertRaisesRegex(ValueError, "source changed after census"):
            self.classify(inventory)

    def test_file_added_after_census_is_refused(self):
        inventory = census.scan(self.root)
        (self.views / "AddedControls.lean").write_text("theorem extra : True := True.intro\n")
        with self.assertRaisesRegex(ValueError, "source universe changed"):
            self.classify(inventory)

    def test_file_removed_after_census_is_refused(self):
        inventory = census.scan(self.root)
        self.path.unlink()
        with self.assertRaisesRegex(ValueError, "source universe changed"):
            self.classify(inventory)

    def test_missing_baseline_is_refused(self):
        with self.assertRaisesRegex(ValueError, "cannot authenticate"):
            source_preservation(self.root, census.scan(self.root)["files"], base="0" * 40)

    def test_empty_baseline_is_refused(self):
        self.path.unlink()
        self.freeze()
        self.path.write_text(self.original)
        with self.assertRaisesRegex(ValueError, "empty frozen"):
            self.classify()

    def test_missing_file_provenance_is_refused(self):
        with self.assertRaisesRegex(ValueError, "missing source preservation"):
            control_rows(census.scan(self.root), {"files": {}})

    def test_scanner_alone_does_not_claim_preservation(self):
        rows = census.scan(self.root)["declarations"]
        self.assertTrue(all("preservation not checked" in row["disposition"] for row in rows))

if __name__ == "__main__": unittest.main()
