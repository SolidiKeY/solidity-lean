#!/usr/bin/env python3
"""Synthetic threshold/refusal tests; these are not benchmark results."""
import copy
import json
from pathlib import Path
import tempfile
import unittest
from measure import compare
from propose import TARGETS


class TimingAcceptance(unittest.TestCase):
    def setUp(self):
        self.temp = tempfile.TemporaryDirectory()
        self.addCleanup(self.temp.cleanup)
        self.before, self.after = [Path(self.temp.name)/n for n in ("before", "after")]
        self.modules = ["Solidity.Backend.StructuredFlow."+name for name in TARGETS]
        self.receipt = dict(exit=0, guard=None, conditions=dict(cache="fresh-private-output", threads=1, timing_unit="nanoseconds"),
                            head="same-frozen-tree", archive_sha256="same-pinned-toolchain", requested=self.modules, closure=["Fixture"]+self.modules,
                            source_sha256=dict(Fixture="same"), source_sha256_before=dict(Fixture="same"), git_status_before="", git_status_after="")
        self.suffix = "".join(m+" 0 0\n" for m in self.modules)
        for p in (self.before, self.after):
            p.mkdir()
            (p/"receipt.json").write_text(json.dumps(dict(self.receipt, command=[str(p)])))
            (p/"modules.tsv").write_text("Fixture 0 1000000000\n"+self.suffix)

    def test_exact_ten_percent_and_one_nanosecond_over(self):
        (self.after/"modules.tsv").write_text("Fixture 0 1100000000\n"+self.suffix)
        self.assertEqual(compare(self.before,self.after)["decision"], "WITHIN_TIMING_LIMIT")
        (self.after/"modules.tsv").write_text("Fixture 0 1100000001\n"+self.suffix)
        self.assertEqual(compare(self.before,self.after)["decision"], "STOP_SLOWDOWN")
        self.assertFalse(compare(self.before,self.after)["semantic_acceptance"])

    def test_failed_or_mixed_conditions_refused(self):
        for edit in (lambda r:r.update(exit=1), lambda r:r.update(guard="headroom"),
                     lambda r:r["conditions"].update(threads=4), lambda r:r.update(head="other-base"),
                     lambda r:r["source_sha256"].update(Fixture="changed")):
            changed = copy.deepcopy(self.receipt)
            changed["command"] = [str(self.after)]
            edit(changed)
            (self.after/"receipt.json").write_text(json.dumps(changed))
            with self.assertRaises(ValueError):
                compare(self.before,self.after)

    def test_incomplete_or_failed_module_inventory_refused(self):
        for text in ("", "Fixture 1 1000000000\n", "Other 0 1000000000\n"):
            (self.after/"modules.tsv").write_text(text)
            with self.assertRaises(ValueError):
                compare(self.before,self.after)


if __name__ == "__main__":
    unittest.main(verbosity=2)
