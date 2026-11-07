"""Guard the H78 regression where missing lanes, export pointers or failed controls falsely certify API fidelity.

Legacy-name linking must not grow a bucket while iterating it, and a metadata-only
index must not silently omit frozen production inputs.
Historical aliases removed by pinned-toolchain restoration must remain historical,
without aborting the inventory or claiming generated names are absent.
These static controls exercise the shared inventory helpers. They run no Lean,
regenerate no old export and never change producer source or axiom guards.
"""
import importlib.util
from pathlib import Path
import unittest
import os
import subprocess
import tempfile
import json
import tarfile
import io
ROOT = Path(__file__).resolve().parents[4]
spec = importlib.util.spec_from_file_location("public_inventory", ROOT/"scripts/h62/item6/migrate-root-gate/public-api-inventory.py")
inventory = importlib.util.module_from_spec(spec)
spec.loader.exec_module(inventory)

class InventoryControls(unittest.TestCase):
    def test_h44_archive_is_required_and_tampering_fails_closed(self):
        with tempfile.TemporaryDirectory() as directory:
            root = Path(directory)
            location = root/"scripts/h62/item6/migrate-root-gate"
            location.mkdir(parents=True)
            archive = root/"bulk.tar.gz"
            data = b'{"historical": true}'
            name = "tests/h62/item6/migrate-hash/receipt.json"
            with tarfile.open(archive, "w:gz") as stream:
                member = tarfile.TarInfo(name); member.size = len(data)
                stream.addfile(member, io.BytesIO(data))
            manifest = {"archive": str(archive), "size_bytes": archive.stat().st_size,
                        "sha256": inventory.sha(archive.read_bytes()), "file_count": 1,
                        "uncompressed_bytes": len(data)}
            (location/"bulk-manifest.json").write_text(json.dumps(manifest))
            self.assertEqual(inventory.archived_inputs(root), {name: data})
            archive.write_bytes(archive.read_bytes()+b"tampered")
            with self.assertRaisesRegex(ValueError, "size/SHA256 mismatch"):
                inventory.archived_inputs(root)
            archive.unlink()
            with self.assertRaises(FileNotFoundError):
                inventory.archived_inputs(root)

    def test_rebased_member_is_reported_without_claiming_current_ancestry(self):
        with tempfile.TemporaryDirectory() as directory:
            def git(*args, data=None):
                return subprocess.check_output(["git", *args], cwd=directory, input=data,
                    env=dict(os.environ, GIT_AUTHOR_NAME="Control", GIT_AUTHOR_EMAIL="control@example.invalid",
                             GIT_COMMITTER_NAME="Control", GIT_COMMITTER_EMAIL="control@example.invalid"),
                    stderr=subprocess.DEVNULL).decode().strip()
            git("init", "--bare")
            tree = git("mktree", data=b"")
            historical = git("commit-tree", tree, data=b"historical")
            rebased = git("commit-tree", tree, data=b"rebased independent root")
            descendant = git("commit-tree", tree, "-p", historical, data=b"descendant")
            self.assertFalse(inventory.member_ancestry(directory, historical, rebased)["historical_head_is_current_ancestor"])
            self.assertTrue(inventory.member_ancestry(directory, historical, descendant)["historical_head_is_current_ancestor"])
            with self.assertRaisesRegex(ValueError, "missing exact historical member commit"):
                inventory.member_ancestry(directory, "0"*40, rebased)

    def test_removed_alias_is_historical_not_a_missing_generated_API_verdict(self):
        record = {"name": "Solidity.TacletAnnotations.ReadDomain.toCtorIdx", "shim_signature": "ReadDomain → Nat"}
        rows = inventory.reconcile_source_shims([record], 'inductive ReadDomain where | a\n')
        self.assertFalse(rows[0]["explicit_source_alias_present"])
        self.assertEqual(rows[0]["historical_record"], record)
        self.assertIn("generated API availability unverified", rows[0]["status"])
        self.assertFalse(rows[0]["API_axiom_acceptance"])

    def test_explicit_alias_comments_cannot_claim_current_installation(self):
        record = {"name": "Solidity.TacletAnnotations.ReadDomain.toCtorIdx"}
        alias = "protected abbrev ReadDomain.toCtorIdx : type_of% ReadDomain.ctorIdx := ReadDomain.ctorIdx"
        self.assertTrue(inventory.reconcile_source_shims([record], alias)[0]["explicit_source_alias_present"])
        for text in ['/- '+alias+' -/', '-- '+alias, 'def note := "'+alias+'"']:
            self.assertFalse(inventory.reconcile_source_shims([record], text)[0]["explicit_source_alias_present"])

    def test_missing_or_duplicate_lane_cannot_certify_complete_inputs(self):
        rows = [{"lane": str(i), "integrated": True, "commit_available": True} for i in range(28)]
        self.assertEqual(len(inventory.validate_members({"members": rows})), 28)
        for bad in [rows[:-1], rows[:-1]+[rows[0]]]:
            with self.assertRaisesRegex(ValueError, "all28 unique"):
                inventory.validate_members({"members": bad})
        rows[0]["integrated"] = False
        with self.assertRaisesRegex(ValueError, "exact member inputs"):
            inventory.validate_members({"members": rows})

    def test_metadata_only_index_cannot_hide_missing_production_file(self):
        with self.assertRaisesRegex(ValueError, "missing assigned production input"):
            inventory.require_production_inputs(["Solidity/Syntax/Raw.lean"], ["tests/h62/item6/migrate-syntax/Api.lean"])
        inventory.require_production_inputs(["Solidity/Syntax/Raw.lean"], ["Solidity/Syntax/Raw.lean", "docs/notes.md"])

    def test_signature_pointer_is_not_promoted_to_literal_signature(self):
        pointer = {"file": "/workspace/missing/old-api.json", "key": "Solidity.X.match_1"}
        self.assertIn("no literal type", inventory.signature_kind(pointer))
        self.assertEqual(inventory.signature_kind(None), "not supplied")

    def test_private_proof_debug_and_matcher_names_are_retained(self):
        names = ["Solidity.X._proof_2", "Solidity.X.match_1", "_private.File.0.Solidity.X", "Solidity.X.debug"]
        rows = [{"name": n, "old_signature": None, "new_signature": None} for n in names]
        self.assertEqual({r[0] for r in inventory.records(rows)}, set(names))

    def test_default_arguments_and_literal_changes_stay_in_authored_headers(self):
        original = 'def x (n : Nat := 0) (s : String := "old") : Nat := 1\n'
        body_change = original.replace(':= 1', ':= 2')
        self.assertEqual(inventory.headers(original), inventory.headers(body_change))
        self.assertNotEqual(inventory.headers(original), inventory.headers(original.replace(':= 0', ':= 3')))
        self.assertNotEqual(inventory.headers(original), inventory.headers(original.replace('"old"', '"new"')))

    def test_unsupported_declaration_cannot_consume_a_later_body(self):
        with self.assertRaisesRegex(ValueError, "unsupported authored header"):
            inventory.headers('opaque noBody : Nat\ndef later : Nat := 0\n')

    def test_existing_legacy_bucket_does_not_grow_during_traversal(self):
        legacy = "Solidity.Source.Syn.noConfusion"
        candidate = {"lane": "migrate-source", "record": {"name": "H78Compat.Syn.noConfusion", "legacy_public_name": legacy}}
        existing = {"lane": "migrate-root-gate", "record": {"name": legacy, "old_signature": None}}
        catalog = {"H78Compat.Syn.noConfusion": [candidate], legacy: [existing]}
        inventory.link_legacy_names(catalog)
        self.assertEqual(len(catalog[legacy]), 2)
        self.assertEqual(catalog[legacy][1]["status"], "legacy name obligation; separate-namespace candidate is not an installed shim")
        self.assertEqual(len(catalog["H78Compat.Syn.noConfusion"]), 1)

    def test_added_private_headers_are_recorded_without_hiding_original_drift(self):
        before = inventory.headers('def x : Nat := 1\n')
        after = inventory.headers('private def helper : Nat := 0\ndef x : Nat := helper\n')
        delta = inventory.header_changes(before, after)
        self.assertTrue(delta["original_headers_preserved"])
        self.assertEqual(delta["added_headers"], ['private def helper : Nat'])
        self.assertFalse(delta["entire_header_list_equal"])
        changed = inventory.header_changes(before, inventory.headers('def x : Int := 1\n'))
        self.assertFalse(changed["original_headers_preserved"])

    def test_prose_failed_control_is_retained_with_line_number(self):
        rows = inventory.source_notes('Ordinary prose.\nold-role executable failed; new-role not run.\nH78 unresolved.\n')
        self.assertEqual(rows[0]["line"], 2)
        self.assertIn('failed', rows[0]["text"])

    def test_nested_comment_declarations_are_not_source_headers(self):
        text = '/- def fake := 1 /- theorem nested := 2 -/ -/\ndef real : String := "def text := 3"\n'
        self.assertEqual(inventory.headers(text), ['def real : String'])

    def test_failed_controls_and_holds_are_not_dropped(self):
        value = {"controls": {"status": "failed old-role codegen", "hold": "STOP retained", "passing_names": 3}}
        rows = list(inventory.notes(value))
        self.assertEqual({r["text"] for r in rows}, {"failed old-role codegen", "STOP retained"})

if __name__ == "__main__":
    unittest.main()
