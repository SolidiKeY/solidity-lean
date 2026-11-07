#!/usr/bin/env python3
import contextlib
import importlib.util
import io
import json
from pathlib import Path
import tempfile
import unittest
from unittest.mock import patch

SCRIPT = Path(__file__).resolve().parents[4] / "scripts/h62/item1/pin-fragments/census.py"
spec = importlib.util.spec_from_file_location("census", SCRIPT)
census = importlib.util.module_from_spec(spec)
spec.loader.exec_module(census)

class CensusTests(unittest.TestCase):
    def run_fixture(self, fragment, inventory, untracked=b""):
        with tempfile.TemporaryDirectory() as tmp:
            root = Path(tmp)
            file = root / "scripts/g07-axiom-pins.d/Solidity/F.json"
            file.parent.mkdir(parents=True)
            file.write_text(fragment)
            (root / census.INVENTORY).write_text(inventory)
            tracked = b"scripts/g07-axiom-pins.d/Solidity/F.json\0"
            output = io.StringIO()
            with patch.object(census, "ROOT", root), patch.object(census.subprocess, "check_output", side_effect=[tracked, untracked]), contextlib.redirect_stdout(output):
                code = census.main()
            return code, json.loads(output.getvalue())

    def test_matching_and_duplicate_key(self):
        key = "Solidity/F.lean:x"
        good = json.dumps({key: []})
        code, result = self.run_fixture(good, good)
        self.assertEqual(code, 0)
        self.assertEqual(result["fragment_pins"], 1)
        duplicate = "{" + json.dumps(key) + ":[]," + json.dumps(key) + ":[\"propext\"]}"
        code, result = self.run_fixture(duplicate, json.dumps({key: ["propext"]}))
        self.assertEqual(code, 1)
        self.assertTrue(any("duplicate key" in e for e in result["errors"]))

    def test_mismatch_empty_name_and_untracked(self):
        code, result = self.run_fixture(json.dumps({"Solidity/F.lean:": []}), json.dumps({"Solidity/F.lean:x": []}), b"scripts/g07-axiom-pins.d/extra.json\0")
        self.assertEqual(code, 1)
        self.assertEqual(result["inventory_only_keys"], ["Solidity/F.lean:x"])
        self.assertEqual(result["fragments_only_keys"], ["Solidity/F.lean:"])
        self.assertEqual(len(result["untracked_fragments"]), 1)
        self.assertTrue(any("wrong fragment" in e for e in result["errors"]))

    def test_different_values_and_invalid_inventory(self):
        key = "Solidity/F.lean:x"
        code, result = self.run_fixture(json.dumps({key: []}), json.dumps({key: ["propext"]}))
        self.assertEqual(code, 1)
        self.assertEqual(result["different_value_keys"], [key])
        code, result = self.run_fixture(json.dumps({key: []}), "{")
        self.assertEqual(code, 1)
        self.assertIn("fatal", result)
        duplicate = "{" + json.dumps(key) + ":[]," + json.dumps(key) + ":[]}" 
        code, result = self.run_fixture(json.dumps({key: []}), duplicate)
        self.assertEqual(code, 1)
        self.assertTrue(any("duplicate inventory key" in e for e in result["errors"]))

if __name__ == "__main__": unittest.main()
