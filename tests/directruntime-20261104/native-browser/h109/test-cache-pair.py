"""Guard matched cache initialization with inert owned fixtures, never Lean."""
import hashlib
import importlib.util
import json
import os
from pathlib import Path
import tempfile
import unittest
from unittest import mock

spec=importlib.util.spec_from_file_location("pair",Path(__file__).with_name("cache-pair.py"))
m=importlib.util.module_from_spec(spec);spec.loader.exec_module(m)


class PairControls(unittest.TestCase):
    def setUp(self):
        self.tmp=tempfile.TemporaryDirectory();self.addCleanup(self.tmp.cleanup)
        self.root=Path(self.tmp.name).resolve();self.source=self.root/"source";self.source.mkdir()
        (self.source/"artifact").write_bytes(b"inert initial cache bytes")
        self.receipt=self.root/"inventory.json"
        self.expected=m.copy.inventory.inventory(self.source)
        self.receipt.write_text(json.dumps(self.expected)+"\n")
        self.pin=hashlib.sha256(self.receipt.read_bytes()).hexdigest();self.envelope=self.root/"pair"

    def prepare(self):return m.prepare(self.source,self.receipt,self.pin,self.envelope)

    def test_matched_initial_metadata_and_independent_mutation(self):
        result=self.prepare();before=self.envelope/"before/cache";after=self.envelope/"after/cache"
        for arm in (before,after):
            actual=m.copy.inventory.inventory(arm)
            self.assertEqual(actual["contentMetadataSha256"],self.expected["contentMetadataSha256"])
        self.assertNotEqual((before/"artifact").stat().st_ino,(after/"artifact").stat().st_ino)
        (before/"artifact").write_bytes(b"changed only before")
        self.assertEqual((after/"artifact").read_bytes(),b"inert initial cache bytes")
        self.assertEqual(m.copy.inventory.inventory(self.source),self.expected)
        with self.assertRaises(FileExistsError):self.prepare()
        for flag in ("physicalCacheEquivalenceAuthenticated","writableCacheMounted","lifetimeSealed","workerExecutionAuthorized"):
            self.assertIs(result[flag],False)

    def test_no_reuse_after_success_or_second_arm_failure(self):
        real=m.copy.prepare;calls=0
        def fail_second(*args):
            nonlocal calls
            calls+=1
            if calls==2:raise ValueError("fixture second-arm failure")
            return real(*args)
        with mock.patch.object(m.copy,"prepare",side_effect=fail_second),self.assertRaisesRegex(ValueError,"second-arm"):
            self.prepare()
        self.assertTrue((self.envelope/"before/cache/artifact").exists())
        with self.assertRaises(FileExistsError):self.prepare()

    def test_first_arm_drift_during_second_copy_refused(self):
        real=m.copy.prepare
        def drift(*args):
            result=real(*args)
            if Path(args[-1])==self.envelope/"after/cache":
                (self.envelope/"before/cache/artifact").write_bytes(b"unexpected first-arm drift")
            return result
        with mock.patch.object(m.copy,"prepare",side_effect=drift),self.assertRaisesRegex(ValueError,"cache arm changed"):
            self.prepare()
        self.assertTrue(self.envelope.exists())

    def test_pin_and_source_drift_refused_before_envelope_creation(self):
        with self.assertRaisesRegex(ValueError,"receipt pin"):
            m.prepare(self.source,self.receipt,"0"*64,self.envelope)
        self.assertFalse(self.envelope.exists())
        (self.source/"artifact").write_bytes(b"changed")
        with self.assertRaisesRegex(ValueError,"source differs"):self.prepare()
        self.assertFalse(self.envelope.exists())

    def test_bind_alias_refused_before_source_mutation(self):
        real=m.copy.directory
        def alias(path,ancestry=None):
            if Path(path)==self.envelope.parent and ancestry is not None:
                fd=real(self.source);ancestry.append((os.fstat(fd).st_dev,os.fstat(fd).st_ino));return fd
            return real(path,ancestry)
        with mock.patch.object(m.copy,"directory",side_effect=alias),self.assertRaisesRegex(ValueError,"aliases source"):
            self.prepare()
        self.assertEqual(m.copy.inventory.inventory(self.source),self.expected)


if __name__=="__main__":unittest.main()
