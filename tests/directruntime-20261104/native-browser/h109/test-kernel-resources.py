"""Guard kernel-resource parsing, PID mapping and bounded descriptor cleanup.

Synthetic filesystem cases are parser/mapping controls, not actual cgroup or
worker authentication. No Docker, Lean, cgroup modification or process kill.
"""
import importlib.util
import os
from pathlib import Path
import tempfile
import unittest
from unittest import mock
from types import SimpleNamespace

spec = importlib.util.spec_from_file_location('resources', Path(__file__).with_name('kernel-resources.py'))
m = importlib.util.module_from_spec(spec);spec.loader.exec_module(m)


class ResourceControls(unittest.TestCase):
    def setUp(self):
        self.temp = tempfile.TemporaryDirectory();self.addCleanup(self.temp.cleanup)
        self.root = Path(self.temp.name)
        self.group(self.root, [])
        self.fd = m._directory(self.root)
        self.addCleanup(os.close, self.fd)

    def group(self, path, members):
        path.mkdir(exist_ok=True)
        (path/'cgroup.type').write_text('domain\n')
        (path/'cgroup.procs').write_text(''.join(str(n)+'\n' for n in members))

    def close(self, chain):
        for _, fd in chain:os.close(fd)

    def test_unique_pid_mapping_ignores_namespace_root_guess(self):
        self.group(self.root/'init', [777])
        self.group(self.root/'docker', [])
        chain = m.locate(self.fd, 777)
        try:
            self.assertEqual([name for name,_ in chain], ['/', '/init'])
            self.assertEqual(os.fstat(chain[-1][1]).st_ino, (self.root/'init').stat().st_ino)
        finally:self.close(chain)
        with self.assertRaises(m.ObservationError):m.locate(self.fd, 999)

    def test_ambiguous_membership_and_search_bounds_refused(self):
        self.group(self.root/'a', [777]);self.group(self.root/'b', [777])
        with self.assertRaises(m.ObservationError):m.locate(self.fd, 777)
        (self.root/'b/cgroup.procs').write_text('')
        with self.assertRaises(m.ObservationError):m.locate(self.fd, 777, max_groups=1)
        with self.assertRaises(m.ObservationError):m.locate(self.fd, 777, max_depth=0)

    def test_failed_search_does_not_leak_group_descriptors(self):
        self.group(self.root/'a', [777]);self.group(self.root/'b', [777])
        before = len(list(Path('/proc/self/fd').iterdir()))
        for _ in range(20):
            with self.assertRaises(m.ObservationError):m.locate(self.fd, 777)
        self.assertEqual(len(list(Path('/proc/self/fd').iterdir())), before)

    def test_threaded_repeated_and_symlink_groups_refused(self):
        self.group(self.root/'child', [777])
        (self.root/'child/cgroup.type').write_text('threaded\n')
        with self.assertRaises(m.ObservationError):m.locate(self.fd, 777)
        (self.root/'child/cgroup.type').write_text('domain\n')
        (self.root/'child/cgroup.procs').write_text('777\n777\n')
        with self.assertRaises(m.ObservationError):m.locate(self.fd, 777)
        (self.root/'child/cgroup.procs').write_text('777\n')
        (self.root/'alias').symlink_to(self.root/'child', target_is_directory=True)
        with self.assertRaises(m.ObservationError):m.locate(self.fd, 777)

    def test_nonregular_oversized_and_nonascii_reads_refused(self):
        os.mkfifo(self.root/'pipe', 0o600)
        with self.assertRaises(m.ObservationError):m._read(self.fd, 'pipe')
        (self.root/'large').write_bytes(b'x'*11)
        with self.assertRaises(m.ObservationError):m._read(self.fd, 'large', maximum=10)
        (self.root/'bad').write_bytes(b'\xff')
        with self.assertRaises(UnicodeError):m._read(self.fd, 'bad')
        (self.root/'link').symlink_to(self.root/'large')
        with self.assertRaises(OSError):m._read(self.fd, 'link')

    def observation_fixture(self):
        (self.root/'cgroup.procs').write_text('777\n')
        values={'memory.max':'12884901888','memory.high':'max','memory.current':'1024',
                'memory.peak':'2048','memory.swap.max':'0','memory.swap.current':'0',
                'cpu.max':'100000 100000','cpu.max.burst':'0','cpu.weight':'100',
                'cpuset.cpus.effective':'0-4','memory.events':'oom 0\noom_kill 0',
                'cpu.stat':'usage_usec 1'}
        for key,value in values.items():(self.root/key).write_text(value+'\n')
        dev=self.root.stat().st_dev
        return {'point':str(self.root),'device':[os.major(dev),os.minor(dev)]}

    def hierarchy_root_fixture(self,cpuset=True):
        for p in self.root.iterdir():p.unlink()
        (self.root/'cgroup.procs').write_text('777\n')
        (self.root/'cgroup.controllers').write_text('cpu memory cpuset\n')
        (self.root/'cgroup.subtree_control').write_text('cpu memory\n')
        if cpuset:(self.root/'cpuset.cpus.effective').write_text('0-4\n')
        dev=self.root.stat().st_dev
        return {'point':str(self.root),'device':[os.major(dev),os.minor(dev)]}

    def test_actual_hierarchy_root_has_no_manufactured_controller_budgets(self):
        primary=self.hierarchy_root_fixture()
        clock=SimpleNamespace(capture=lambda:{'bootId':'fixture'},ClockError=RuntimeError)
        with mock.patch.object(m,'_directory',side_effect=lambda path:os.dup(self.fd)),mock.patch.object(m,'mount_record',return_value=primary),mock.patch.object(m,'_process',return_value={'pid':777,'affinity':[0]}),mock.patch.object(m,'_clock_module',return_value=clock):
            observed=m.observe(777)
        root=observed['ancestors'][0]
        self.assertTrue(root['constraints']['hierarchyRootProfile'])
        self.assertEqual(root['constraints']['cgroupType'],'hierarchy-root')
        for key in ('memoryCurrentBytes','memoryPeakBytes','swapCurrentBytes','memoryEvents','cpuStat'):
            self.assertIsNone(root[key])
        self.assertIsNone(root['constraints']['cpuWeight'])
        self.assertEqual(observed['visibleCpusetConcurrentCpuUpperBound'],5)
        self.assertIsNone(observed['visibleConfiguredSustainedQuotaRate'])

    def test_root_without_cpuset_is_unknown_not_zero_or_process_affinity(self):
        self.hierarchy_root_fixture(cpuset=False)
        row={'constraints':m.constraints(self.fd,root=True)}
        self.assertIsNone(row['constraints']['effectiveCpuIntervals'])
        self.assertIsNone(m.cpu_configuration([row])['visibleCpusetConcurrentCpuUpperBound'])
        with self.assertRaises(FileNotFoundError):m.constraints(self.fd)

    def test_nonroot_missing_controller_and_inconsistent_root_fail_closed(self):
        self.observation_fixture();(self.root/'memory.max').unlink()
        with self.assertRaises(FileNotFoundError):m.constraints(self.fd,root=True)
        self.hierarchy_root_fixture();(self.root/'memory.max').write_text('max\n')
        with self.assertRaisesRegex(m.ObservationError,'inconsistent hierarchy-root'):m.constraints(self.fd,root=True)

    def test_constraint_drift_rejected_without_descriptor_leak(self):
        primary=self.observation_fixture();identity={'pid':777,'affinity':[0]}
        clock=SimpleNamespace(capture=lambda:{'bootId':'fixture'},ClockError=RuntimeError)
        real=m.constraints;calls=[0]
        def drift(fd,**kwargs):
            data=real(fd,**kwargs);calls[0]+=1
            if calls[0]==2:data['swapMaxBytes']=1
            return data
        before=len(list(Path('/proc/self/fd').iterdir()))
        with mock.patch.object(m,'_directory',side_effect=lambda path:os.dup(self.fd)), mock.patch.object(m,'mount_record',return_value=primary), mock.patch.object(m,'_process',return_value=identity), mock.patch.object(m,'_clock_module',return_value=clock), mock.patch.object(m,'constraints',side_effect=drift):
            with self.assertRaisesRegex(m.ObservationError,'constraints changed'):m.observe(777)
        self.assertEqual(len(list(Path('/proc/self/fd').iterdir())),before)

    def test_process_identity_change_rejected(self):
        primary=self.observation_fixture()
        clock=SimpleNamespace(capture=lambda:{'bootId':'fixture'},ClockError=RuntimeError)
        with mock.patch.object(m,'_directory',side_effect=lambda path:os.dup(self.fd)), mock.patch.object(m,'mount_record',return_value=primary), mock.patch.object(m,'_process',side_effect=[{'pid':777,'affinity':[0]},{'pid':777,'affinity':[1]}]), mock.patch.object(m,'_clock_module',return_value=clock):
            with self.assertRaisesRegex(m.ObservationError,'identity changed'):m.observe(777)

    def test_cpu_quota_uses_exact_rationals_and_unbounded_is_not_zero(self):
        self.assertEqual(m.cpu_limit('50000 100000'), {'quota':50000,'period':100000})
        self.assertEqual(m.cpu_limit('max 100000'), {'quota':None,'period':100000})
        self.assertIsNone(m.limit('max'));self.assertEqual(m.limit('0'),0)
        for bad in ['0 100000','100000 0','-1 100000','1 2 3','NaN 100000']:
            with self.assertRaises(m.ObservationError):m.cpu_limit(bad)

    def test_cpuset_intervals_do_not_expand_or_double_count(self):
        self.assertEqual(m.cpu_set('0-4,7,9-11'), [[0,4],[7,7],[9,11]])
        self.assertEqual(m.cpu_set('0-1048575'), [[0,1048575]])
        for bad in ['', '1-0','0-4,4-5','2,1','1,,2','0-1048576','1-2-3']:
            with self.assertRaises(m.ObservationError):m.cpu_set(bad)

    def test_quota_configuration_is_not_concurrent_cpu_capacity(self):
        def row(quota, period, burst=0):
            return {'constraints': {'cpuMax': {'quota':quota,'period':period},
                    'cpuBurstMicroseconds':burst,'effectiveCpuIntervals':[[0,4]]}}
        result = m.cpu_configuration([row(None,100000),row(100000,100000)])
        self.assertEqual(result['visibleCpusetConcurrentCpuUpperBound'],5)
        self.assertEqual(result['visibleConfiguredSustainedQuotaRate'],{'numerator':1,'denominator':1})
        self.assertEqual(m.cpu_configuration([row(50000,100000,40000)])['visibleConfiguredSustainedQuotaRate'],{'numerator':1,'denominator':2})
        self.assertIsNone(m.cpu_configuration([row(None,100000)])['visibleConfiguredSustainedQuotaRate'])
        self.assertNotIn('visibleCpuCapacityUpperBound',result)

    def test_counter_missing_duplicate_malformed_and_negative_refused(self):
        self.assertEqual(m.counters('oom 0\noom_kill 2', ['oom','oom_kill']), {'oom':0,'oom_kill':2})
        for bad in ['oom 0','oom 0\noom 1','oom -1\noom_kill 0','oom 0 extra\noom_kill 0']:
            with self.assertRaises(m.ObservationError):m.counters(bad, ['oom','oom_kill'])

    def test_mount_root_parent_is_preserved_not_joined_into_paths(self):
        line = '92 91 0:24 /.. /sys/fs/cgroup ro master:8 - cgroup2 cgroup2 rw'
        result = m.mount_record(line)
        self.assertEqual(result['root'], '/..');self.assertEqual(result['device'],[0,24])
        with self.assertRaises(m.ObservationError):m.mount_record(line+'\n'+line)
        with self.assertRaises(m.ObservationError):m.mount_record(line.replace(' - cgroup2 ', ' - tmpfs '))
        with self.assertRaises(m.ObservationError):m.mount_record('malformed')


if __name__ == '__main__':unittest.main()
