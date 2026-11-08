"""Guard offline lifecycle intake against pin, chain and filesystem substitution.

Fixtures are generated journals; these checks certify no live cleanup or runner.
"""
import hashlib
import importlib.util
import json
import os
from pathlib import Path
import tempfile
import unittest
from unittest import mock

spec = importlib.util.spec_from_file_location("offline", Path(__file__).with_name("offline-journal.py"))
m = importlib.util.module_from_spec(spec)
spec.loader.exec_module(m)


class OfflineControls(unittest.TestCase):
    def setUp(self):
        self.tmp = tempfile.TemporaryDirectory()
        self.addCleanup(self.tmp.cleanup)
        self.root = Path(self.tmp.name)
        store = self.root / "store"
        store.mkdir(mode=0o700)
        locator = m.journal.provision(store)
        with m.journal.Journal(store, locator) as j:
            j.reserve("a"*64, "sha256:"+"b"*64)
            j.advance("create-intent", {})
            j.advance("created", {"containerId": "c"*64})
            j.advance("drain-observed", {"cleanupAccepted": True, "measurementAccepted": True})
        self.path = store / "active.json"
        self.data = self.path.read_bytes()
        self.pin = hashlib.sha256(self.data).hexdigest()

    def check(self, data):
        return m.inspect_bytes(data, hashlib.sha256(data).hexdigest())

    def test_real_journal_structure_never_promotes_claimed_facts(self):
        before = self.path.stat()
        result = m.inspect_bytes(m.read_pinned(self.path, self.pin), self.pin)
        self.assertEqual(result["lastRecordedState"], "drain-observed")
        self.assertEqual(result["eventCount"], 4)
        for key in ("recordedFactsVerified", "liveLeaseAuthenticated", "cleanupAccepted", "resourceAccepted", "measurementAccepted", "postCreateBarrierReleased"):
            self.assertIs(result[key], False)
        self.assertEqual(self.path.read_bytes(), self.data)
        self.assertEqual(before.st_mtime_ns, self.path.stat().st_mtime_ns)
        self.assertTrue(self.path.exists())

    def test_external_pin_required_and_mismatch_refused(self):
        for pin in (None, "", "A"*64, "0"*64):
            with self.subTest(pin=pin), self.assertRaises(ValueError):
                m.inspect_bytes(self.data, pin)
        with self.assertRaises(ValueError):
            m.read_pinned(self.path, "0"*64)

    def test_canonical_json_and_duplicates(self):
        for data in (self.data[:-1], json.dumps(json.loads(self.data)).encode(), b'{"version":1,"version":1}\n', b'{"x":NaN}\n', b'[]\n', b'{'):
            with self.subTest(data=data[:30]), self.assertRaises((ValueError, m.journal.JournalError)):
                self.check(data)

    def test_chain_transition_and_clock_refused(self):
        for change in ("previous", "state", "monotonicNs", "sequence"):
            value = json.loads(self.data)
            value["events"][1][change] = {"previous": "0"*64, "state": "drain-observed", "monotonicNs": -1, "sequence": True}[change]
            with self.subTest(change=change), self.assertRaises(m.journal.JournalError):
                self.check(m.journal.encode(value))

    def test_symlink_ancestor_leaf_hardlink_and_fifo_refused(self):
        link = self.root / "link"
        link.symlink_to(self.path)
        ancestor = self.root / "ancestor"
        ancestor.symlink_to(self.path.parent, target_is_directory=True)
        fifo = self.root / "fifo"
        os.mkfifo(fifo)
        for path in (link, ancestor / self.path.name, fifo):
            with self.subTest(path=path), self.assertRaises((OSError, ValueError)):
                m.read_pinned(path, self.pin)
        os.link(self.path, self.root / "alias")
        with self.assertRaises(ValueError):
            m.read_pinned(self.path, self.pin)

    def test_oversize_and_path_traversal_refused(self):
        big = self.root / "big"
        big.write_bytes(b"x"*(m.LIMIT+1))
        for path in (big, "relative", str(self.root)+"/store/../store/active.json"):
            with self.subTest(path=path), self.assertRaises(ValueError):
                m.read_pinned(path, self.pin)
        with self.assertRaises(ValueError):
            self.check(big.read_bytes())

    def test_replacement_during_read_refused(self):
        original = os.read
        replaced = False
        def read(fd, count):
            nonlocal replaced
            data = original(fd, count)
            if not replaced:
                replaced = True
                sibling = self.path.with_name("sibling")
                sibling.write_bytes(self.data)
                os.replace(sibling, self.path)
            return data
        with mock.patch.object(m.os, "read", side_effect=read), self.assertRaises(ValueError):
            m.read_pinned(self.path, self.pin)


if __name__ == "__main__":
    unittest.main()
