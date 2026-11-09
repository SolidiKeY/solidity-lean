"""Guard pinned input materialization against metadata loss and source drift.

Small owned filesystem fixtures only; no production input, worker, mount, Lean
or container is prepared or qualified by these controls.
"""
import errno
import hashlib
import importlib.util
import json
import os
from pathlib import Path
import tempfile
import unittest
from unittest import mock

spec=importlib.util.spec_from_file_location("copy_inputs",Path(__file__).with_name("input-copy.py"))
m=importlib.util.module_from_spec(spec);spec.loader.exec_module(m)


class CopyControls(unittest.TestCase):
    def setUp(self):
        self.tmp=tempfile.TemporaryDirectory();self.addCleanup(self.tmp.cleanup)
        self.root=Path(self.tmp.name).resolve();self.source=self.root/"source";self.source.mkdir()
        (self.source/"dir").mkdir();(self.source/"dir/tool").write_bytes(b"\x00tool\xff\n")
        (self.source/"dir/tool").chmod(0o555)
        (self.source/"link").symlink_to("dir/tool")
        os.link(self.source/"dir/tool",self.source/"alias")
        self.dest=self.root/"copy";self.path=self.root/"inventory.json"
        self.pin_source()

    def pin_source(self):
        self.expected=m.inventory.inventory(self.source)
        self.path.write_text(json.dumps(self.expected,sort_keys=True)+"\n")
        self.pin=hashlib.sha256(self.path.read_bytes()).hexdigest()

    def prepare(self):return m.prepare(self.source,self.path,self.pin,self.dest)

    def test_complete_copy_metadata_internal_symlink_and_hardlink_flattening(self):
        result=self.prepare()
        actual=m.inventory.inventory(self.dest)
        self.assertEqual([r["contentMetadata"] for r in actual["records"]],[r["contentMetadata"] for r in self.expected["records"]])
        self.assertEqual(m.inventory.inventory(self.source),self.expected)
        self.assertEqual((self.dest/"link").readlink(),Path("dir/tool"))
        self.assertNotEqual((self.dest/"alias").stat().st_ino,(self.dest/"dir/tool").stat().st_ino)
        for field in ("readOnlyMountAuthenticated","lifetimeSealed","workerExecutionAuthorized","capacityEnforcementAuthenticated"):
            self.assertIs(result[field],False)

    def test_xattrs_and_nanosecond_mtime(self):
        (self.source/"dir/tool").chmod(0o755)
        try:os.setxattr(self.source/"dir/tool","user.h127",b"fixture")
        except OSError as e:
            if e.errno not in (errno.ENOTSUP,errno.ENOSYS):raise
            self.skipTest("user xattrs unsupported: "+str(e))
        (self.source/"dir/tool").chmod(0o555)
        os.utime(self.source/"dir/tool",ns=(1770000000000001,1770000000000003))
        self.pin_source();self.prepare()
        self.assertEqual(os.getxattr(self.dest/"dir/tool","user.h127"),b"fixture")
        self.assertEqual((self.dest/"dir/tool").stat().st_mtime_ns,1770000000000003)

    def test_bad_pin_and_changed_source_refused_before_destination(self):
        with self.assertRaisesRegex(ValueError,"receipt pin"):
            m.prepare(self.source,self.path,"0"*64,self.dest)
        self.assertFalse(self.dest.exists())
        (self.source/"dir/tool").chmod(0o755)
        (self.source/"dir/tool").write_bytes(b"changed")
        with self.assertRaisesRegex(ValueError,"source differs"):self.prepare()
        self.assertFalse(self.dest.exists())

    def test_external_hardlink_source_flattened_without_copy_aliases(self):
        os.link(self.source/"dir/tool",self.root/"external-alias")
        self.pin_source();self.assertTrue(self.expected["externalHardlinkAliases"])
        self.prepare()
        self.assertEqual((self.dest/"dir/tool").stat().st_nlink,1)
        self.assertNotEqual((self.dest/"dir/tool").stat().st_ino,(self.root/"external-alias").stat().st_ino)

    def test_existing_overlapping_and_symlink_destinations_refused(self):
        for dest in (self.source,self.source/"nested",self.root):
            with self.subTest(dest=dest),self.assertRaises(ValueError):
                m.prepare(self.source,self.path,self.pin,dest)
        self.dest.mkdir()
        with self.assertRaises(FileExistsError):self.prepare()
        self.dest.rmdir();self.dest.symlink_to(self.source,target_is_directory=True)
        with self.assertRaises(FileExistsError):self.prepare()

    def test_special_and_linked_receipts_refused(self):
        link=self.root/"receipt-link";link.symlink_to(self.path)
        fifo=self.root/"fifo";os.mkfifo(fifo)
        for path in (link,fifo):
            with self.subTest(path=path),self.assertRaises((OSError,ValueError)):
                m.prepare(self.source,path,self.pin,self.dest)
        self.assertFalse(self.dest.exists())
        os.link(self.path,self.root/"receipt-alias")
        with self.assertRaisesRegex(ValueError,"unaliased"):self.prepare()

    def test_capacity_failure_before_and_during_copy_leaves_no_success(self):
        with mock.patch.object(m,"RESERVE",10**40),self.assertRaisesRegex(ValueError,"reserve"):
            self.prepare()
        self.assertFalse(self.dest.exists())
        real=m.capacity;calls=0
        def fail_later(*args,**kwargs):
            nonlocal calls
            calls+=1
            if calls>2:raise ValueError("fixture reserve stop")
            return real(*args,**kwargs)
        with mock.patch.object(m,"capacity",side_effect=fail_later),self.assertRaisesRegex(ValueError,"reserve stop"):
            self.prepare()
        self.assertTrue(self.dest.exists())
        with self.assertRaises(FileExistsError):self.prepare()

    def test_second_parent_open_failure_closes_first_descriptor(self):
        real=m.relative_parent;calls=0
        def fail_second(*args):
            nonlocal calls
            calls+=1
            if calls==2:raise OSError(errno.EMFILE,"fixture destination parent open failure")
            return real(*args)
        before=len(os.listdir("/proc/self/fd"))
        with mock.patch.object(m,"relative_parent",side_effect=fail_second),self.assertRaisesRegex(OSError,"destination parent"):
            self.prepare()
        self.assertEqual(len(os.listdir("/proc/self/fd")),before)
        self.assertTrue(self.dest.exists())

    def test_destination_identity_alias_refused_before_source_mutation(self):
        # Emulate an ancestor reached through a bind alias without mounting.
        real=m.directory
        def alias(path,ancestry=None):
            if Path(path)==self.dest.parent and ancestry is not None:
                fd=real(self.source)
                if ancestry is not None:ancestry.append((os.fstat(fd).st_dev,os.fstat(fd).st_ino))
                return fd
            return real(path,ancestry)
        with mock.patch.object(m,"directory",side_effect=alias),self.assertRaisesRegex(ValueError,"aliases source"):
            self.prepare()
        self.assertFalse((self.source/self.dest.name).exists())
        self.assertEqual(m.inventory.inventory(self.source),self.expected)

    def test_source_mutation_during_write_refused(self):
        real=m.os.write;changed=False
        def drift(fd,data):
            nonlocal changed
            count=real(fd,data)
            if not changed:
                changed=True;(self.source/"dir/tool").chmod(0o755);(self.source/"dir/tool").write_bytes(b"changed")
            return count
        with mock.patch.object(m.os,"write",side_effect=drift),self.assertRaisesRegex(ValueError,"source changed"):
            self.prepare()
        self.assertTrue(self.dest.exists())


if __name__=="__main__":unittest.main()
