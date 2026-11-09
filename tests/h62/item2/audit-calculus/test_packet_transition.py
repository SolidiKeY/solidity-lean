"""Guard regression: published transitions cannot revise old roles or owners."""
import copy
import sys
from pathlib import Path
import unittest
sys.path.insert(0, str(Path(__file__).resolve().parents[4] / "scripts/h62/item2/audit-calculus"))
from verify_packet_transition import compare, read_packet


class PacketTransitionControls(unittest.TestCase):
    def before(self):
        return {"scope": b"exact frozen scope", "dataset": {
            "base": "frozen base", "source_census_sha256": "frozen census",
            "semantic_owner_by_file": {"a": "confirmed owner"},
            "declarations": [{"id": "a", "conclusion": "exact statement role"}],
            "reviewed_files": ["a"]}}

    def test_addition_preserves_exact_prefix(self):
        a = self.before()
        b = copy.deepcopy(a)
        b["dataset"]["declarations"].append({"id": "b", "conclusion": "next role"})
        b["dataset"]["reviewed_files"].append("b")
        self.assertEqual(compare(a, b)["added"], 1)

    def test_edited_prior_role_refused(self):
        a = self.before()
        b = copy.deepcopy(a)
        b["dataset"]["declarations"][0]["conclusion"] = "weakened role"
        with self.assertRaisesRegex(ValueError, "prior classification"):
            compare(a, b)

    def test_owner_or_scope_change_refused(self):
        a = self.before()
        for field in ("scope", "owner"):
            with self.subTest(field=field):
                b = copy.deepcopy(a)
                if field == "scope":
                    b["scope"] = b"different scope"
                else:
                    b["dataset"]["semantic_owner_by_file"]["a"] = "guessed owner"
                with self.assertRaises(ValueError):
                    compare(a, b)

    def test_reserved_or_duplicate_output_names_refused(self):
        import json
        import hashlib
        from unittest.mock import patch
        payload = b"{}"
        row = {"bytes": len(payload), "sha256": hashlib.sha256(payload).hexdigest()}
        for names in (("bulk-inputs-manifest.json", "other.json"), ("same.json", "same.json")):
            with self.subTest(names=names):
                manifest = json.dumps({key: {**row, "path": name}
                    for key, name in zip(("frozen_scope", "lifetime_roles"), names)}).encode()
                def read(repo, revision, name):
                    return manifest if name.endswith("/bulk-inputs-manifest.json") else payload
                with patch("verify_packet_transition._git_bytes", side_effect=read):
                    with self.assertRaisesRegex(ValueError, "reserved or duplicate"):
                        read_packet(Path("/external-packet"), "a" * 40, "packet")

    def test_duplicate_identity_refused(self):
        a = self.before()
        b = copy.deepcopy(a)
        b["dataset"]["declarations"].append(copy.deepcopy(a["dataset"]["declarations"][0]))
        with self.assertRaisesRegex(ValueError, "duplicate classification"):
            compare(a, b)


if __name__ == "__main__":
    unittest.main()
