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


if __name__ == '__main__':
    unittest.main()
