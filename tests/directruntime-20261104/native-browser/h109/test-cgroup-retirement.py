#!/usr/bin/env python3
"""Guard H127 drain observations against moved groups, ENOENT shortcuts and nlink.

Temporary regular-file fixtures emulate only the observer's decision inputs.
They are not actual kernel deactivation, Docker cleanup or release acceptance.
"""
import errno
import importlib.util
import os
from pathlib import Path
import tempfile
from types import SimpleNamespace
import unittest
from unittest.mock import patch

spec=importlib.util.spec_from_file_location('retire',Path(__file__).with_name('cgroup-retirement.py'))
m=importlib.util.module_from_spec(spec);spec.loader.exec_module(m)


class Controls(unittest.TestCase):
    def setUp(self):
        self.temp=tempfile.TemporaryDirectory();self.addCleanup(self.temp.cleanup)
        self.root=Path(self.temp.name);self.path=self.root/'group';self.path.mkdir()
        self.write('domain','populated 1\nfrozen 0','777')
        self.parent=os.open(self.root,os.O_RDONLY|os.O_DIRECTORY)
        self.group=os.open(self.path,os.O_RDONLY|os.O_DIRECTORY)
        self.addCleanup(os.close,self.parent);self.addCleanup(os.close,self.group)
        dev=self.root.stat().st_dev
        self.mount={'device':[os.major(dev),os.minor(dev)],'point':str(self.root),'mountId':1}
        self.boot='11111111-1111-1111-1111-111111111111'
        self.count=0
        def capture():
            self.count+=1
            return {'bootId':self.boot,'monotonicBeforeNs':self.count*3,'boottimeNs':self.count*3+1,'monotonicAfterNs':self.count*3+2}
        for manager in (patch.object(m.resources,'mount_record',side_effect=lambda _:dict(self.mount)),
                        patch.object(m.resources,'_clock_module',return_value=SimpleNamespace(capture=capture)),
                        patch.object(m.os,'readlink',return_value='mnt:[11]')):
            manager.start();self.addCleanup(manager.stop)
        self.pin=m.CgroupPin(self.parent,self.group,'group',777);self.addCleanup(self.pin.close)

    def write(self,domain,events,pids):
        for name,value in zip(m.FILES,(domain,events,pids)):(self.path/name).write_text(value+'\n' if value else '')

    def test_live_populated_is_not_drain(self):
        data=self.pin.observe()
        self.assertEqual(data['state'],'populated-domain');self.assertFalse(data['emptyOrDeactivatedObserved'])
        self.assertFalse(data['kernelBuildAuthenticated'])
        self.assertFalse(data['cleanupAccepted']);self.assertFalse(data['postCreateBarrierReleased'])

    def test_recursive_population_required_even_with_empty_direct_procs(self):
        self.write('domain','populated 1','')
        self.assertFalse(self.pin.observe()['emptyOrDeactivatedObserved'])
        self.write('domain','populated 0','')
        data=self.pin.observe();self.assertEqual(data['state'],'empty-live-domain');self.assertTrue(data['emptyOrDeactivatedObserved'])
        self.write('domain','populated 0','777')
        self.assertFalse(self.pin.observe()['emptyOrDeactivatedObserved'])

    def test_deactivated_fixture_does_not_require_zero_link_count(self):
        for p in self.path.iterdir():p.unlink()
        self.path.rmdir()
        real=m.os.fstat
        def links(fd):
            s=real(fd)
            return SimpleNamespace(st_mode=s.st_mode,st_dev=s.st_dev,st_ino=s.st_ino,st_nlink=2)
        with patch.object(m.os,'fstat',side_effect=links):data=self.pin.observe()
        self.assertEqual(data['state'],'deactivated-cgroup2-node');self.assertTrue(data['emptyOrDeactivatedObserved'])
        self.assertEqual(data['first']['linksInformationalOnly'],2)
        self.assertTrue(all(not f['available'] for f in data['first']['files'].values()))

    def test_renamed_active_or_empty_group_is_unknown(self):
        self.path.rename(self.root/'moved')
        data=self.pin.observe();self.assertEqual(data['state'],'unknown');self.assertFalse(data['emptyOrDeactivatedObserved'])
        (self.root/'moved/cgroup.events').write_text('populated 0\n');(self.root/'moved/cgroup.procs').write_text('')
        self.assertFalse(self.pin.observe()['emptyOrDeactivatedObserved'])

    def test_replacement_parent_entry_rejected(self):
        self.path.rename(self.root/'moved');self.path.mkdir()
        with self.assertRaisesRegex(m.RetirementError,'replaced'):self.pin.observe()

    def test_missing_files_with_live_parent_or_mixed_availability_unknown(self):
        (self.path/'cgroup.events').unlink()
        self.assertFalse(self.pin.observe()['emptyOrDeactivatedObserved'])
        for p in self.path.iterdir():p.unlink()
        self.assertFalse(self.pin.observe()['emptyOrDeactivatedObserved'])

    def test_non_enoent_kernel_errors_never_retire(self):
        for code in (errno.EACCES,errno.EIO,errno.ENODEV):
            with patch.object(m.resources,'_read',side_effect=OSError(code,'fixture')):
                with self.assertRaises(OSError):self.pin.observe()

    def test_symlink_and_fifo_controls_refused_without_blocking(self):
        (self.path/'cgroup.events').unlink();(self.path/'cgroup.events').symlink_to('/etc/passwd')
        with self.assertRaises(OSError):self.pin.observe()
        (self.path/'cgroup.events').unlink();os.mkfifo(self.path/'cgroup.events')
        with self.assertRaises(m.resources.ObservationError):self.pin.observe()

    def test_mount_boot_or_pinned_identity_drift_refused(self):
        self.mount['mountId']=2
        with self.assertRaisesRegex(m.RetirementError,'mount/namespace'):self.pin.observe()
        self.mount['mountId']=1;self.boot='22222222-2222-2222-2222-222222222222'
        with self.assertRaisesRegex(m.RetirementError,'boot'):self.pin.observe()

    def test_capture_requires_live_pid_and_failed_capture_closes_fds(self):
        before=len(list(Path('/proc/self/fd').iterdir()))
        for _ in range(5):
            with self.assertRaisesRegex(m.RetirementError,'live domain/PID'):m.CgroupPin(self.parent,self.group,'group',999)
        self.assertEqual(len(list(Path('/proc/self/fd').iterdir())),before)
        for name in ('','..','a/b','control\n'):
            with self.assertRaises(m.RetirementError):m.CgroupPin(self.parent,self.group,name,777)

    def test_invalid_population_membership_or_domain_never_empty_passes(self):
        self.write('domain','populated 2','')
        with self.assertRaisesRegex(m.RetirementError,'populated'):self.pin.observe()
        self.write('domain','populated 0','777\n777')
        with self.assertRaisesRegex(m.RetirementError,'membership'):self.pin.observe()
        self.write('threaded','populated 0','')
        self.assertFalse(self.pin.observe()['emptyOrDeactivatedObserved'])

    def test_closed_pin_cannot_be_reconstituted_from_birth_record(self):
        saved=self.pin.birth;self.pin.close()
        self.assertIn('pid',saved)
        with self.assertRaisesRegex(m.RetirementError,'closed'):self.pin.observe()


if __name__=='__main__':unittest.main()
