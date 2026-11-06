#!/usr/bin/env python3
"""Reconstruction and negative controls for exact-source census intervals."""
import hashlib
import importlib.util
import json
import pathlib
import subprocess
import sys
import unittest

ROOT = pathlib.Path(__file__).resolve().parents[4]
SCRIPT = ROOT / "scripts/h62/item1/binding-fixtures/source_intervals.py"
SPEC = importlib.util.spec_from_file_location("source_intervals", SCRIPT)
subject = importlib.util.module_from_spec(SPEC)
SPEC.loader.exec_module(subject)


class SourceIntervalControls(unittest.TestCase):
    def test_reconstruct_all_named_files(self):
        report = json.loads(subprocess.check_output([sys.executable, str(SCRIPT)], cwd=ROOT))
        self.assertEqual(len(report["files"]), 17)
        for row in report["files"]:
            original = (ROOT / row["path"]).read_bytes()
            reconstructed = (row["preamble"] + "".join(i["text"] for i in row["intervals"])).encode()
            self.assertEqual(reconstructed, original, row["path"])
            self.assertEqual(hashlib.sha256(original).hexdigest(), row["sha256"])
            matches = [i for i in row["intervals"] if i["name"] == "BindingRel"]
            self.assertEqual(len(matches), 1, row["path"])
            for interval in row["intervals"]:
                self.assertEqual(hashlib.sha256(interval["text"].encode()).hexdigest(), interval["sha256"])

    def test_no_markers_and_comment_marker(self):
        self.assertEqual(subject.split_source("no declaration\n"), ("no declaration\n", []))
        # Comment markers are ignored while original source remains intact.
        text = "/-\ndef phantom : Nat := 0\n-/\n"
        prefix, intervals = subject.split_source(text)
        self.assertEqual(intervals, [])
        self.assertEqual(prefix + "".join(i["text"] for i in intervals), text)


if __name__ == "__main__":
    unittest.main(verbosity=2)
