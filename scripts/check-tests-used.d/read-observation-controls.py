"""Opt-in producer controls. No result here registers a census root or row."""
import copy
import hashlib
import importlib.util
import json
from pathlib import Path
import unittest


def load(name):
    path = Path(__file__).with_name('read-observation-' + name + '.py')
    spec = importlib.util.spec_from_file_location('observation_' + name, path)
    module = importlib.util.module_from_spec(spec)
    spec.loader.exec_module(module)
    return module


schema = load('schema')


def example(cli=False):
    digest = hashlib.sha256(b'abc').hexdigest()
    artifact = dict(path='/external/evidence', sha256='a' * 64, bytes=3)
    source = dict(path='tests/real-input', blob='b' * 40, sha256=digest, bytes=3, revision='c' * 40)
    tool = dict(path='/usr/bin/python3', sha256='d' * 64, version='test')
    frame = dict(source=source, line=1, qualname='main', code_sha256='e' * 64)
    outcome = dict(exit=1 if cli else 0, signal=None, timed_out=False, phase='main', log=artifact)
    obs = dict(invocation=dict(argv=['python3', '-B', 'runner.py'], cwd='/scratch', env=[], tools=[tool],
                              inputs=[source], external_inputs=[], external_outputs=['/external/output'], timeout_seconds=30),
               producer=dict(name='h145-host-observed-byte-reader-v1', adapter='python-audit-kernel',
                             source=artifact, binary=None, kernel='test', runtime_tools=[tool], config=artifact,
                             raw_events=artifact, trusted_host_statement=artifact),
               reader=source, read=dict(target=source, namespace='working-tree',
                                       process=dict(run_nonce='f' * 64, pid=1, start_identity='boot:1',
                                                    parent_start_identity=None, exec_sequence=0, executable=tool,
                                                    argv=['python3', '-B', 'runner.py']),
                                       fd_identity='generation1', open_event_sequence=1, close_event_sequence=3,
                                       intervals=[dict(offset=0, bytes=3, returned_bytes_sha256=digest, event_sequence=2)],
                                       complete_target_sha256=digest, frames=[frame], entered_branch_events=[artifact],
                                       mutation_audit=artifact, pre_identity=artifact, post_identity=artifact),
               outcome=outcome, ordinary_outcome=outcome, pre_manifest=artifact, post_manifest=artifact)
    result = dict(schema='h145.nonpassing-cli/1' if cli else 'h145.exact-byte-read/1',
                  availability='available', observation=obs)
    if cli:
        result['context'] = dict(reader=source, introducing_commit='c' * 40, reviewed_argv=obs['invocation']['argv'],
                                 observed_revision='c' * 40, failure_frame=frame, failure_event_sequence=4,
                                 diagnostic_fingerprint_sha256='a' * 64, read_event_sequences=[2],
                                 normal_and_traced_context_equivalence_review=artifact, historical=False,
                                 current_blob_equivalence_review=artifact)
    return copy.deepcopy(result)


class MetadataControls(unittest.TestCase):
    def test_exact_metadata_does_not_assert_evidence_authentication(self):
        for cli in (False, True):
            record = example(cli)
            self.assertEqual(schema.validate_receipt(schema.decode(json.dumps(record).encode())), record)

    def test_unavailable_has_no_observation(self):
        record = dict(schema='h145.exact-byte-read/1', availability='unavailable', missing=['producer'],
                      source_report=dict(path='/evidence/report', sha256='a' * 64, bytes=0))
        schema.validate_receipt(record)
        record['observation'] = example()['observation']
        with self.assertRaises(schema.Invalid):
            schema.validate_receipt(record)

    def test_duplicate_nonfinite_and_oversize(self):
        for data in (b'{"x":1,"x":2}', b'{"x":NaN}', b' ' * (schema.MAX_METADATA_BYTES + 1), b'\xff',
                     b'{\"x\":1e999}', b'{\"x\":0.5}', b'{\"x\":' + b'9' * 5000 + b'}',
                     b'{\"x\":18446744073709551616}'):
            with self.assertRaises(schema.Invalid):
                schema.decode(data)

    def test_false_identity_shape_and_byte_ranges(self):
        for change in ('boolean-count', 'extra-key', 'bad-sha', 'gap', 'overlap', 'partial', 'zero-noop', 'late-read'):
            record = example()
            read = record['observation']['read']
            if change == 'boolean-count': read['target']['bytes'] = True
            if change == 'extra-key': read['credit'] = 'pass'
            if change == 'bad-sha': read['target']['sha256'] = 'A' * 64
            if change == 'gap': read['intervals'][0]['offset'] = 1
            if change == 'overlap': read['intervals'].append(dict(read['intervals'][0], event_sequence=0))
            if change == 'partial': read['intervals'][0]['bytes'] = 2
            if change == 'zero-noop': read['intervals'][0]['bytes'] = 0
            if change == 'late-read': read['intervals'][0]['event_sequence'] = 3
            with self.subTest(change=change), self.assertRaises(schema.Invalid):
                schema.validate_receipt(record)

    def test_known_range_hashes_cannot_contradict_target(self):
        record = example()
        record['observation']['read']['intervals'][0]['returned_bytes_sha256'] = 'a' * 64
        with self.assertRaises(schema.Invalid):
            schema.validate_receipt(record)
        record = example()
        read = record['observation']['read']
        read['target']['bytes'] = 0
        read['intervals'][0].update(bytes=0, returned_bytes_sha256=hashlib.sha256(b'').hexdigest())
        with self.assertRaises(schema.Invalid):
            schema.validate_receipt(record)

    def test_context_failure_and_invocation_are_exact(self):
        for change in ('success', 'after-failure', 'wrong-argv', 'duplicate-env', 'termination', 'timeout', 'phase'):
            record = example(True)
            obs = record['observation']
            if change == 'success': obs['outcome']['exit'] = obs['ordinary_outcome']['exit'] = 0
            if change == 'after-failure': record['context']['failure_event_sequence'] = 2
            if change == 'wrong-argv': record['context']['reviewed_argv'] = ['other']
            if change == 'duplicate-env': obs['invocation']['env'] = [dict(name='X', value='1')] * 2
            if change == 'termination': obs['outcome']['signal'] = 9
            if change == 'timeout': obs['outcome']['timed_out'] = True
            if change == 'phase': obs['ordinary_outcome'] = dict(obs['outcome'], phase='bootstrap')
            with self.subTest(change=change), self.assertRaises(schema.Invalid):
                schema.validate_receipt(record)


class NativeLifecycleControls(unittest.TestCase):
    def test_real_exec_and_child_tree_are_observed(self):
        import os
        native = load('native')
        result = native.trace(['/bin/sh', '-c', '/bin/true & wait'], '/tmp', dict(os.environ),
                              timeout=5, max_events=6000, max_output_bytes=16384)
        self.assertEqual(result['status'], 'observed', result['reason'])
        self.assertTrue(result['cleanup_confirmed'])
        self.assertEqual(result['result'], dict(exit=0, signal=None))
        self.assertTrue(any(x['kind'] == 'child' for x in result['events']))
        self.assertTrue(any(x['kind'] == 'exec' for x in result['events']))
        self.assertEqual([x['sequence'] for x in result['events']], list(range(len(result['events']))))

    def test_timeout_and_event_loss_never_pass(self):
        import os
        native = load('native')
        for command, timeout, budget in [(['/bin/sleep', '2'], .1, 6000), (['/bin/true'], 5, 1)]:
            result = native.trace(command, '/tmp', dict(os.environ), timeout=timeout, max_events=budget, max_output_bytes=16384)
            self.assertEqual(result['status'], 'unavailable')
            self.assertTrue(result['cleanup_confirmed'])


class NativeRefusalControls(unittest.TestCase):
    def test_invalid_budgets_fail_before_fork(self):
        native = load('native')
        for timeout, events in [(float('inf'), 10), (float('nan'), 10), (1, float('nan')), (True, 1), (1, 1.5)]:
            with self.subTest(timeout=timeout, events=events), self.assertRaises(native.Unavailable):
                native.trace(['/bin/true'], '/tmp', {}, timeout=timeout, max_events=events, max_output_bytes=1024)

    def test_group_stop_is_not_swallowed(self):
        import os
        native = load('native')
        result = native.trace(['/bin/sh', '-c', 'kill -STOP $$; echo continued'], '/tmp', dict(os.environ),
                              timeout=2, max_events=6000, max_output_bytes=16384)
        self.assertEqual(result['status'], 'unavailable')
        self.assertNotIn(b'continued', result['stdout'])
        self.assertTrue(result['cleanup_confirmed'])

    def test_identity_failure_still_reaps_provisional_child(self):
        import os
        native = load('native')
        def broken(_): raise OSError('injected identity failure')
        native.process_identity = broken
        result = native.trace(['/bin/true'], '/tmp', dict(os.environ), timeout=2,
                              max_events=6000, max_output_bytes=16384)
        self.assertEqual(result['status'], 'unavailable')
        self.assertTrue(result['cleanup_confirmed'])
        self.assertFalse(native.traced_tasks())

    def test_tiny_deadline_reaps_child_before_ptrace_admission(self):
        import os
        native = load('native')
        result = native.trace(['/bin/sleep', '2'], '/tmp', dict(os.environ), timeout=1e-12,
                              max_events=50, max_output_bytes=1024)
        self.assertEqual(result['status'], 'unavailable')
        self.assertTrue(result['cleanup_confirmed'])
        self.assertFalse(native.traced_tasks())

    def test_exit_observer_failure_does_not_signal_reaped_root(self):
        import os
        native = load('native')
        original = native.os.kill
        reaped = set()
        def kill(pid, sig):
            self.assertNotIn(pid, reaped)
            return original(pid, sig)
        def observe(event, pid, _):
            if event['kind'] == 'exit':
                reaped.add(pid)
                raise native.Unavailable('injected exit observer failure')
        native.os.kill = kill
        try:
            result = native.trace(['/bin/true'], '/tmp', dict(os.environ), timeout=3,
                                  max_events=6000, max_output_bytes=1024, observer=observe)
        finally:
            native.os.kill = original
        self.assertEqual(result['status'], 'unavailable')
        self.assertTrue(result['cleanup_confirmed'])

    def test_large_output_is_bounded_and_unavailable(self):
        import os
        native = load('native')
        result = native.trace(['/bin/dd', 'if=/dev/zero', 'bs=65536', 'count=1'], '/tmp', dict(os.environ),
                              timeout=3, max_events=6000, max_output_bytes=1024)
        self.assertEqual(result['status'], 'unavailable')
        self.assertLessEqual(len(result['stdout']), 1024)
        self.assertTrue(result['cleanup_confirmed'])


class NativeByteControls(unittest.TestCase):
    def capture(self, payload, command=None, budget=4096):
        import os
        import tempfile
        native = load('native')
        with tempfile.TemporaryDirectory() as directory:
            path = Path(directory) / 'input'
            path.write_bytes(payload)
            observer = native.ByteCapture([str(path)], max_capture_bytes=budget)
            argv = command(str(path)) if command else ['/bin/dd', 'if=' + str(path), 'bs=4096', 'status=none']
            result = native.trace(argv, directory, dict(os.environ, LC_ALL='C'), timeout=5, max_events=12000,
                                  max_output_bytes=8192, observer=observer)
            return result, observer.finish(result)

    def test_real_returned_bytes_and_empty_eof_are_captured(self):
        import base64
        for data in (b'abc\x00def', b''):
            result, capture = self.capture(data)
            self.assertEqual(result['status'], 'observed', result['reason'])
            self.assertEqual(capture['status'], 'captured', capture['reasons'])
            chunks = [x for x in capture['records'] if x['bytes'] or not data]
            self.assertTrue(chunks)
            self.assertEqual(base64.b64decode(chunks[0]['data']), data)
            self.assertTrue(all(x['open_sequence'] < x['sequence'] < x['close_sequence'] for x in chunks))

    def test_readv_descriptors_are_snapshotted_before_they_are_overwritten(self):
        import os
        import subprocess
        import tempfile
        import base64
        native = load('native')
        code = """#include <fcntl.h>
#include <sys/uio.h>
#include <stdlib.h>
#include <sys/ioctl.h>
#include <unistd.h>
int main(int n, char **v) { struct iovec a[2]; char last;
a[0].iov_base=&a[1]; a[0].iov_len=sizeof(a[1]); a[1].iov_base=&last; a[1].iov_len=1;
if(n>3) { int f=atoi(v[3]); if(v[2][0]=='i') { int bytes; if(ioctl(f,FIONREAD,&bytes)!=0) return 4; }
else if(pwrite(f,"z",1,0)!=1 || pwrite(f,"\\0",1,0)!=1) return 3; }
if(n==3) { a[0].iov_base=&last; a[0].iov_len=1; }
int fd=open(v[1],O_RDONLY); return readv(fd,a,2)==sizeof(a[1])+1 ? 0 : 2; }
"""
        with tempfile.TemporaryDirectory() as d:
            root = Path(d)
            (root / 'read.c').write_text(code)
            subprocess.run(['/usr/bin/cc', str(root / 'read.c'), '-o', str(root / 'read')], check=True)
            payload = bytes(range(17))
            target = root / 'input'
            target.write_bytes(payload)
            capture = native.ByteCapture([str(target)], max_capture_bytes=4096)
            result = native.trace([str(root / 'read'), str(target)], d, dict(os.environ, LC_ALL='C'),
                                  timeout=5, max_events=12000, max_output_bytes=8192, observer=capture)
            raw = capture.finish(result)
            self.assertEqual(raw['status'], 'captured', raw['reasons'])
            self.assertEqual(base64.b64decode(raw['records'][0]['data']), payload)
            self.assertEqual(schema.replay_capture(raw, result['events'], max_capture_bytes=4096,
                                                  max_events=12000)['status'], 'replayed')
            capture = native.ByteCapture([str(target)], max_capture_bytes=4096)
            result = native.trace([str(root / 'read'), str(target), 'overlap'], d,
                                  dict(os.environ, LC_ALL='C'), timeout=5, max_events=12000,
                                  max_output_bytes=8192, observer=capture)
            self.assertEqual(result['status'], 'unavailable')
            self.assertIn('overlapping', result['reason'])
            self.assertTrue(result['cleanup_confirmed'])
            fd = os.open(target, os.O_RDWR)
            os.set_inheritable(fd, True)
            try:
                capture = native.ByteCapture([str(target)], max_capture_bytes=4096)
                result = native.trace([str(root / 'read'), str(target), 'mutate', str(fd)], d,
                                      dict(os.environ, LC_ALL='C'), timeout=5, max_events=12000,
                                      max_output_bytes=8192, observer=capture)
                raw = capture.finish(result)
            finally:
                os.close(fd)
            self.assertEqual(target.read_bytes(), payload)
            self.assertEqual(raw['status'], 'unavailable')
            self.assertTrue(any('pinned target' in x for x in raw['reasons']))
            fd = os.open(target, os.O_RDWR)
            os.set_inheritable(fd, True)
            try:
                capture = native.ByteCapture([str(target)], max_capture_bytes=4096)
                result = native.trace([str(root / 'read'), str(target), 'ioctl', str(fd)], d,
                                      dict(os.environ, LC_ALL='C'), timeout=5, max_events=12000,
                                      max_output_bytes=8192, observer=capture)
                raw = capture.finish(result)
            finally:
                os.close(fd)
            self.assertEqual(raw['status'], 'unavailable')
            self.assertTrue(any('pinned target' in x for x in raw['reasons']))

    def test_descendants_do_not_become_read_credit(self):
        _, capture = self.capture(b'abc', lambda p: ['/bin/sh', '-c', '/bin/cat "$1" & wait', 'sh', p])
        self.assertEqual(capture['status'], 'unavailable')
        self.assertTrue(any('descendants' in x for x in capture['reasons']))

    def test_budget_and_symlink_inputs_are_refused(self):
        import tempfile
        native = load('native')
        with tempfile.TemporaryDirectory() as directory:
            path = Path(directory) / 'input'
            path.write_bytes(b'abcd')
            link = Path(directory) / 'alias'
            link.symlink_to(path)
            for name, budget in [(str(path), 3), (str(link), 4096)]:
                with self.assertRaises(native.Unavailable):
                    native.ByteCapture([name], max_capture_bytes=budget)


class ReplayControls(unittest.TestCase):
    def test_real_payload_replay_grants_no_census_credit(self):
        for payload in (b'abc', b''):
            result, capture = NativeByteControls.capture(self, payload)
            replay = schema.replay_capture(capture, result['events'], max_capture_bytes=4096, max_events=12000)
            self.assertEqual(replay['status'], 'replayed')
            self.assertEqual(replay['credit'], 'none')
            self.assertEqual(replay['targets'][0]['sha256'], hashlib.sha256(payload).hexdigest())

    def test_fabricated_bytes_identity_and_event_links_are_refused(self):
        result, original = NativeByteControls.capture(self, b'abc')
        for fault in ('payload', 'inode', 'descriptor', 'generation', 'process', 'lifetime', 'sequence', 'entry', 'intervening-close', 'position', 'partial'):
            raw, events = copy.deepcopy(original), copy.deepcopy(result['events'])
            record = next(r for r in raw['records'] if r['bytes'])
            if fault == 'payload': record['data'] = 'eHl6'
            if fault == 'inode': record['inode'] += 1
            if fault == 'descriptor': record['fd'] += 100
            if fault == 'generation': record['fd_generation'] += 1
            if fault == 'process': record['task'] += ':wrong'
            if fault == 'lifetime': record['close_sequence'] = record['sequence']
            if fault == 'sequence': events[0]['sequence'] = True
            if fault == 'entry': events[record['sequence']]['enter_sequence'] = 0
            if fault in ('intervening-close', 'position'):
                close = next(e for e in events[record['open_sequence'] + 1:record['sequence']]
                             if e['kind'] == 'leave' and e.get('number') == 3)
                close['args'][0] = record['fd']
                events[close['enter_sequence']]['args'][0] = record['fd']
                if fault == 'position':
                    close['number'], close['result'] = 8, 1
                    close['args'] = [record['fd'], 1, 0, 0, 0, 0]
                    events[close['enter_sequence']].update(number=8, args=list(close['args']))
            if fault == 'partial': raw['records'].remove(record)
            with self.subTest(fault=fault):
                if fault == 'partial':
                    value = schema.replay_capture(raw, events, max_capture_bytes=4096, max_events=12000)
                    self.assertEqual(value['status'], 'unavailable')
                else:
                    with self.assertRaises(schema.Invalid):
                        schema.replay_capture(raw, events, max_capture_bytes=4096, max_events=12000)


class PythonAssociationControls(unittest.TestCase):
    def fixture(self, code):
        import subprocess
        import tempfile
        directory = tempfile.TemporaryDirectory()
        root = Path(directory.name) / 'repo'
        root.mkdir()
        (root / 'reader.py').write_text(code)
        (root / 'data').write_bytes(b'abc')
        subprocess.run(['git', 'init', '-q', str(root)], check=True)
        subprocess.run(['git', '-C', str(root), 'add', '.'], check=True)
        subprocess.run(['git', '-C', str(root), '-c', 'user.name=Control', '-c', 'user.email=control@example.invalid',
                        'commit', '-qm', 'fixture'], check=True)
        revision = subprocess.check_output(['git', '-C', str(root), 'rev-parse', 'HEAD'], text=True).strip()
        files = {}
        for name in ('reader.py', 'data'):
            blob = subprocess.check_output(['git', '-C', str(root), 'rev-parse', 'HEAD:' + name], text=True).strip()
            files[name] = dict(blob=blob, sha256=hashlib.sha256((root / name).read_bytes()).hexdigest())
        return directory, root, dict(measured_revision=revision, files=files)

    def test_real_measured_cli_read_is_only_a_candidate(self):
        import os
        import sys
        code = 'from pathlib import Path\ndef main():\n    Path("data").read_bytes()\nif __name__ == "__main__": main()\n'
        temporary, root, manifest = self.fixture(code)
        try:
            python, native = load('python'), load('native')
            env = dict(os.environ, LC_ALL='C', PYTHONUTF8='1', PYTHONCOERCECLOCALE='0')
            env.update(python.prepare(root, manifest, Path(temporary.name) / 'hook'))
            capture = native.ByteCapture([str(root / 'data')], max_capture_bytes=65536)
            hook = python.PythonEvents(capture, root, env['X1_READ_LOG'], max_hook_bytes=32768)
            result = native.trace([str(Path(sys.executable).resolve()), '-B', 'reader.py'], str(root), env,
                                  timeout=10, max_events=30000, max_output_bytes=32768, observer=hook)
            value = hook.candidates(result)
            self.assertEqual(result['result'], dict(exit=0, signal=None), result['stdout'])
            self.assertEqual(value['status'], 'candidates', (result['reason'], value['capture']['reasons']))
            self.assertEqual(value['credit'], 'none')
            frame = value['candidates'][0]['hook']['record']['frames'][-1]
            self.assertEqual(frame['path'], 'reader.py')
            self.assertEqual(frame['qualname'], 'main')
            self.assertEqual(frame['blob'], manifest['files']['reader.py']['blob'])
        finally:
            temporary.cleanup()


    def test_disabled_hook_and_synthetic_source_never_establish_frames(self):
        import os
        import sys
        for synthetic in (False, True):
            code = 'from pathlib import Path\nexec(compile(\'Path("data").read_bytes()\', "reader.py", "exec"))\n' if synthetic else 'from pathlib import Path\nPath("data").read_bytes()\n'
            temporary, root, manifest = self.fixture(code)
            try:
                python, native = load('python'), load('native')
                env = dict(os.environ, LC_ALL='C', PYTHONUTF8='1', PYTHONCOERCECLOCALE='0')
                env.update(python.prepare(root, manifest, Path(temporary.name) / 'hook'))
                if not synthetic:
                    env.pop('PYTHONPATH')
                capture = native.ByteCapture([str(root / 'data')], max_capture_bytes=65536)
                hook = python.PythonEvents(capture, root, env['X1_READ_LOG'], max_hook_bytes=32768)
                result = native.trace([str(Path(sys.executable).resolve()), '-B', 'reader.py'], str(root), env,
                                      timeout=10, max_events=30000, max_output_bytes=32768, observer=hook)
                self.assertEqual(hook.candidates(result)['status'], 'unavailable')
            finally:
                temporary.cleanup()


    def test_failed_python_opener_cannot_lend_frames_to_native_read(self):
        import os
        import sys
        code = 'import ctypes\nlib=ctypes.CDLL(None)\ndef decoy():\n    try: open("data", "rb", opener=lambda p,f: -1)\n    except ValueError: pass\ndef native():\n    fd=lib.open(b"data",0)\n    buffer=ctypes.create_string_buffer(3)\n    lib.read(fd,buffer,3)\n    lib.close(fd)\ndecoy()\nnative()\n'
        temporary, root, manifest = self.fixture(code)
        try:
            python, native = load('python'), load('native')
            env = dict(os.environ, LC_ALL='C', PYTHONUTF8='1', PYTHONCOERCECLOCALE='0')
            env.update(python.prepare(root, manifest, Path(temporary.name) / 'hook'))
            capture = native.ByteCapture([str(root / 'data')], max_capture_bytes=65536)
            hook = python.PythonEvents(capture, root, env['X1_READ_LOG'], max_hook_bytes=32768)
            result = native.trace([str(Path(sys.executable).resolve()), '-B', 'reader.py'], str(root), env,
                                  timeout=10, max_events=30000, max_output_bytes=32768, observer=hook)
            self.assertEqual(result['result'], dict(exit=0, signal=None), result['stdout'])
            self.assertEqual(hook.candidates(result)['status'], 'unavailable')
        finally:
            temporary.cleanup()


if __name__ == '__main__':
    unittest.main()
