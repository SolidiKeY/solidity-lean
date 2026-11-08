"""Guard pinned H127 timing intake against cross-run, clock and coverage substitution.

Only synthetic observations are used; no worker or production measurement runs.
"""
import hashlib
import importlib.util
import json
from pathlib import Path
import tempfile
import unittest

spec = importlib.util.spec_from_file_location("offline_stage", Path(__file__).with_name("offline-stage.py"))
m = importlib.util.module_from_spec(spec)
spec.loader.exec_module(m)
BOOT = "11111111-1111-1111-1111-111111111111"


def sample(t):
    return {"bootId": BOOT, "monotonicBeforeNs": t, "boottimeNs": t, "monotonicAfterNs": t}


class IntakeControls(unittest.TestCase):
    def setUp(self):
        self.tmp = tempfile.TemporaryDirectory()
        self.addCleanup(self.tmp.cleanup)
        self.root = Path(self.tmp.name)
        store = self.root / "store"
        store.mkdir(mode=0o700)
        locator = m.offline.journal.provision(store)
        with m.offline.journal.Journal(store, locator) as j:
            j.reserve("a"*64, "sha256:"+"b"*64)
        self.journal = store / "active.json"
        self.journal_bytes = self.journal.read_bytes()
        self.journal_pin = hashlib.sha256(self.journal_bytes).hexdigest()
        lifecycle = json.loads(self.journal_bytes)
        self.boot = lifecycle["identity"]["bootId"]
        self.begin = lifecycle["events"][0]["monotonicNs"]
        def observation(offset):
            result = sample(self.begin + offset)
            result["bootId"] = self.boot
            return result
        self.observation = observation
        self.stage = self.root / "stage.json"
        self.record = {"journalSha256": self.journal_pin,
                       "identity": json.loads(self.journal_bytes)["identity"],
                       "timing": {"context": "lane-end", "checks": [
                           {"target": target, "start": observation(i*10), "end": observation(i*10+1),
                            "exitCode": 0, "cachedVerdict": False}
                           for i, target in enumerate(m.timing.TARGETS)]}}

    def write(self):
        data = m.offline.journal.encode(self.record)
        self.stage.write_bytes(data)
        return hashlib.sha256(data).hexdigest()

    def inspect(self):
        return m.inspect_files(self.stage, self.write(), self.journal, self.journal_pin)

    def test_pinned_positive_is_never_execution_or_recovery(self):
        result = self.inspect()
        self.assertTrue(result["timing"]["timingEligibleByDeclaredPolicy"])
        self.assertEqual(result["lastRecordedState"], "reserved")
        for field in ("recordedFactsVerified", "executionAccepted", "resourceAccepted", "measurementAccepted", "cleanupAccepted", "postCreateBarrierReleased"):
            self.assertIs(result[field], False)
        self.assertEqual(self.journal.read_bytes(), self.journal_bytes)

    def test_external_pins_and_cross_run_binding(self):
        pin = self.write()
        with self.assertRaises(ValueError):
            m.inspect_files(self.stage, "0"*64, self.journal, self.journal_pin)
        with self.assertRaises(ValueError):
            m.inspect_files(self.stage, pin, self.journal, "0"*64)
        self.record["journalSha256"] = "0"*64
        with self.assertRaisesRegex(ValueError, "another journal"):
            self.inspect()
        self.record["journalSha256"] = self.journal_pin
        self.record["identity"]["planSha256"] = "c"*64
        with self.assertRaisesRegex(ValueError, "identities differ"):
            self.inspect()

    def test_repinning_failed_observations_never_hides_failure(self):
        self.record["timing"]["checks"][0]["exitCode"] = 1
        self.assertFalse(self.inspect()["timing"]["timingEligibleByDeclaredPolicy"])
        self.record["timing"]["checks"][0]["exitCode"] = 0
        self.record["timing"]["checks"][-1]["end"] = self.observation(300_000_000_000)
        self.assertFalse(self.inspect()["timing"]["timingEligibleByDeclaredPolicy"])

    def test_missing_target_cached_verdict_and_unknown_context_refused(self):
        original = json.loads(json.dumps(self.record))
        for kind in ("missing", "cached", "context", "extra"):
            self.record = json.loads(json.dumps(original))
            if kind == "missing": self.record["timing"]["checks"].pop()
            elif kind == "cached": self.record["timing"]["checks"][0]["cachedVerdict"] = True
            elif kind == "context": self.record["timing"]["context"] = []
            else: self.record["acceptance"] = True
            with self.subTest(kind=kind), self.assertRaises(ValueError):
                self.inspect()

    def test_boot_and_reservation_time_must_match_journal(self):
        for check in self.record["timing"]["checks"]:
            for field in ("start", "end"):
                check[field]["bootId"] = BOOT
        with self.assertRaises(ValueError):
            self.inspect()
        for check in self.record["timing"]["checks"]:
            for field in ("start", "end"):
                check[field]["bootId"] = self.boot
                for key in ("monotonicBeforeNs", "boottimeNs", "monotonicAfterNs"):
                    check[field][key] -= self.begin
        with self.assertRaisesRegex(ValueError, "precedes journal reservation"):
            self.inspect()

    def test_noncanonical_and_symlink_inputs_refused(self):
        data = json.dumps(self.record).encode()
        self.stage.write_bytes(data)
        with self.assertRaises(ValueError):
            m.inspect_files(self.stage, hashlib.sha256(data).hexdigest(), self.journal, self.journal_pin)
        pin = self.write()
        link = self.root / "link"
        link.symlink_to(self.stage)
        with self.assertRaises(OSError):
            m.inspect_files(link, pin, self.journal, self.journal_pin)


if __name__ == "__main__":
    unittest.main()
