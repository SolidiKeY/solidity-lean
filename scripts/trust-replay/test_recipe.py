#!/usr/bin/env python3
"""Synthetic controls for omitted/corrupt/stale inputs and failure/deadline loss.
These bytes are NOT Lean objects and the fake process is NOT lean4checker.
No real-corpus replay, performance, fresh-kernel or A04 acceptance follows.
"""
import dataclasses
import hashlib
import importlib.util
import json
import os
import signal
from pathlib import Path
import subprocess
import sys
import tempfile
import time
from types import SimpleNamespace
import unittest
from unittest.mock import patch

SPEC = importlib.util.spec_from_file_location('trust_replay_recipe', Path(__file__).with_name('recipe.py'))
R = importlib.util.module_from_spec(SPEC)
sys.modules[SPEC.name] = R
SPEC.loader.exec_module(R)
SHA = lambda data: hashlib.sha256(data).hexdigest()


def git(root, *args):
    return subprocess.check_output(['git', '-C', str(root), *args], text=True, stderr=subprocess.DEVNULL).strip()


def repository(root, files):
    root.mkdir()
    git(root, 'init', '-q')
    git(root, 'config', 'user.name', 'synthetic-control')
    git(root, 'config', 'user.email', 'control@example.invalid')
    for path, body in files.items():
        target = root / path
        target.parent.mkdir(parents=True, exist_ok=True)
        target.write_text(body)
    git(root, 'add', '.')
    git(root, 'commit', '-qm', 'synthetic only')
    return git(root, 'rev-parse', 'HEAD')


def executable(path, body):
    path.parent.mkdir(parents=True, exist_ok=True)
    path.write_text('#!/usr/bin/env python3\n' + body)
    path.chmod(0o755)


class Controls(unittest.TestCase):
    def setUp(self):
        self.tmp = tempfile.TemporaryDirectory(prefix='synthetic-trust-replay-')
        self.addCleanup(self.tmp.cleanup)
        self.root = Path(self.tmp.name)
        self.source = self.root / 'source'
        self.head = repository(self.source, {'lean-toolchain': R.TOOLCHAIN + '\n',
                                             'lakefile.toml': 'name = "synthetic"\n',
                                             'Test/Public.lean': '-- synthetic, never elaborated\n'})
        self.checker_source = self.root / 'checker-source'
        self.revision = repository(self.checker_source, {'lean-toolchain': R.TOOLCHAIN + '\n'})
        self.objects = self.root / 'objects'
        self.objects.mkdir()
        self.files = []
        for name in ('Test/Helper.olean', 'Test/Public.olean'):
            data = ('NOT_A_LEAN_OBJECT:' + name).encode()
            target = self.objects / name
            target.parent.mkdir(parents=True, exist_ok=True)
            target.write_bytes(data)
            self.files.append(dict(path=name, source='/synthetic-cache/' + name, sha256=SHA(data), bytes=len(data)))
        self.manifest = dict(schema=1, head=self.head, root='Test.Public',
                             provenance=dict(setupOrigin='lake --no-build setup-file (import Test.Public)',
                                             setupSha256=SHA(b'synthetic setup'),
                                             rootSourceSha256=SHA((self.source / 'Test/Public.lean').read_bytes())),
                             scope=R.SCOPE, files=self.files)
        self.manifest_path = self.objects / 'MANIFEST.json'
        self.manifest_path.write_text(json.dumps(self.manifest) + '\n')
        self.sysroot = self.root / 'toolchain'
        executable(self.sysroot / 'bin/lean', "import sys,pathlib\nprint(pathlib.Path(__file__).parent.parent if sys.argv[1:]==['--print-prefix'] else 'Lean (version 4.24.0, synthetic control)')\n")
        # Simulate Lake changing the ambient search path, then applying inner env.
        executable(self.sysroot / 'bin/lake', '''import os,sys
if sys.argv[1:]==['--version']:
 print('Lake version 5.0.0 (Lean version 4.24.0)');raise SystemExit(0)
assert sys.argv[1:3]==['env','env']
env=dict(os.environ,LEAN_PATH='unlisted-lake-path')
args=sys.argv[3:]
while args and '=' in args[0]:
 k,v=args.pop(0).split('=',1);env[k]=v
os.execve(args[0],args,env)
''')
        self.checker = self.root / 'synthetic-checker'
        executable(self.checker, "import os,sys,json\nprint(json.dumps({'args':sys.argv[1:],'path':os.environ['LEAN_PATH'],'sysroot':os.environ['LEAN_SYSROOT'],'threads':os.environ['LEAN_NUM_THREADS']}))\n")
        self.packet_path = self.root / 'packet.json'
        self.configure()

    def configure(self):
        manifest_hash = SHA(self.manifest_path.read_bytes())
        checker_hash = SHA(self.checker.read_bytes())
        packet = dict(head=self.head, checker_revision=self.revision, checker_binary_sha256=checker_hash,
                      toolchain=R.TOOLCHAIN, manifest_sha256=manifest_hash, manifest_content=self.manifest)
        self.packet_path.write_text(json.dumps(packet) + '\n')
        self.profile = R.Profile(SHA(self.packet_path.read_bytes()), manifest_hash, checker_hash,
                                 self.revision, self.head, 2, sum(row['bytes'] for row in self.files),
                                 root='Test.Public', seconds=10, synthetic=True)
        self.config = SimpleNamespace(packet=self.packet_path, manifest=self.manifest_path, objects=self.objects,
                                      source_root=self.source, checker=self.checker,
                                      checker_source=self.checker_source, sysroot=self.sysroot,
                                      output=self.root / 'output')

    def run_recipe(self, expected):
        with patch.dict(os.environ, {'PATH': str(self.sysroot / 'bin') + os.pathsep + os.environ['PATH']}):
            self.assertEqual(R.run(self.profile, self.config), expected)
        result = json.loads((self.config.output / 'candidate-receipt.json').read_text())
        self.assertFalse(result['a04_accepted'])
        self.assertTrue(result['synthetic_control'])
        return result

    def test_success_keeps_one_fresh_root_and_inner_path_overrides(self):
        result = self.run_recipe(0)
        trace = json.loads((self.config.output / 'checker.log').read_text())
        self.assertEqual(trace, dict(args=['--fresh', 'Test.Public'], path=str(self.objects),
                                     sysroot=str(self.sysroot), threads='1'))
        self.assertEqual(result['object_count'], 2)
        self.assertIn('pending-va1', result['validation'])
        # Builtin path gets appended once, preserving first-match directories.
        old = [str(self.objects), str(self.sysroot / 'lib/lean'), str(self.sysroot / 'lib/lean')]
        new = [trace['path'], str(self.sysroot / 'lib/lean')]
        self.assertEqual(list(dict.fromkeys(old)), new)

    def test_omitted_object_is_refused_before_checker(self):
        (self.objects / 'Test/Helper.olean').unlink()
        self.assertFalse(self.run_recipe(2)['checker_started'])

    def test_corrupt_same_size_object_is_refused(self):
        target = self.objects / 'Test/Helper.olean'
        target.write_bytes(b'x' * target.stat().st_size)
        self.assertFalse(self.run_recipe(2)['checker_started'])

    def test_stale_manifest_bytes_and_omitted_row_are_refused(self):
        self.manifest['files'] = self.files[:1]
        self.manifest_path.write_text(json.dumps(self.manifest) + '\n')
        self.assertFalse(self.run_recipe(2)['checker_started'])

    def test_extra_object_is_refused(self):
        (self.objects / 'Test/Extra.olean').write_bytes(b'unlisted')
        self.assertFalse(self.run_recipe(2)['checker_started'])

    def test_symlink_object_is_refused(self):
        target = self.objects / 'Test/Helper.olean'
        data = target.read_bytes()
        target.unlink()
        outside = self.root / 'outside'
        outside.write_bytes(data)
        target.symlink_to(outside)
        self.assertFalse(self.run_recipe(2)['checker_started'])

    def test_stale_source_head_and_root_are_refused(self):
        (self.source / 'Test/Public.lean').write_text('-- changed root\n')
        self.assertFalse(self.run_recipe(2)['checker_started'])

    def test_stale_git_head_is_refused(self):
        (self.source / 'Other.txt').write_text('new source revision')
        git(self.source, 'add', '.')
        git(self.source, 'commit', '-qm', 'new synthetic source head')
        self.assertFalse(self.run_recipe(2)['checker_started'])

    def test_changed_checker_is_refused(self):
        self.checker.write_bytes(self.checker.read_bytes() + b'# changed\n')
        self.assertFalse(self.run_recipe(2)['checker_started'])

    def test_checker_failure_exit_propagates(self):
        executable(self.checker, 'raise SystemExit(7)\n')
        self.configure()
        result = self.run_recipe(7)
        self.assertEqual(result['checker_exit_code'], 7)

    def test_checker_signal_exit_propagates(self):
        executable(self.checker, 'import os,signal\nos.kill(os.getpid(),signal.SIGTERM)\n')
        self.configure()
        self.assertEqual(self.run_recipe(143)['checker_exit_code'], 143)

    def test_new_lake_context_is_detected_after_checker(self):
        executable(self.checker, "import pathlib\npathlib.Path('lakefile.lean').write_text('-- unexpected context')\n")
        self.configure()
        self.assertIn('untracked Lake context', self.run_recipe(2)['error'])

    def test_postcheck_catches_checker_corrupting_input(self):
        executable(self.checker, "import os,pathlib\np=pathlib.Path(os.environ['LEAN_PATH'])/'Test/Helper.olean'\np.write_bytes(b'x'*p.stat().st_size)\n")
        self.configure()
        result = self.run_recipe(2)
        self.assertEqual(result['checker_exit_code'], 0)
        self.assertIn('corrupt object', result['error'])

    def test_timeout_propagates_with_one_total_deadline(self):
        executable(self.checker, 'import time\ntime.sleep(5)\n')
        self.configure()
        self.profile = dataclasses.replace(self.profile, seconds=1)
        start = time.monotonic()
        self.assertTrue(self.run_recipe(124)['checker_started'])
        self.assertLess(time.monotonic() - start, 2)

    def test_setup_and_checker_share_budget(self):
        original = R.validate_inputs
        def delayed(*args):
            time.sleep(.15)
            return original(*args)
        self.profile = dataclasses.replace(self.profile, seconds=.1)
        with patch.object(R, 'validate_inputs', delayed):
            result = self.run_recipe(124)
        self.assertFalse(result['checker_started'])

    def test_dirty_committed_lake_context_refused(self):
        (self.source / 'lakefile.toml').write_text('name = "dirty"\n')
        self.assertFalse(self.run_recipe(2)['checker_started'])

    def test_untracked_lake_context_refused(self):
        (self.source / 'lakefile.lean').write_text('-- untracked')
        self.assertFalse(self.run_recipe(2)['checker_started'])

    def test_alternative_sysroot_refused(self):
        other = self.root / 'alternative'
        other.mkdir()
        self.config.sysroot = other
        self.assertIn('active reference Lean prefix', self.run_recipe(2)['error'])

    def test_special_companion_refused(self):
        os.mkfifo(self.objects / 'Test/Helper.olean.private')
        self.assertFalse(self.run_recipe(2)['checker_started'])

    def test_unlisted_private_companion_refused(self):
        (self.objects / 'Test/Helper.olean.private').write_bytes(b'not listed')
        self.assertFalse(self.run_recipe(2)['checker_started'])

    def test_unlisted_server_companion_refused(self):
        (self.objects / 'Test/Helper.olean.server').write_bytes(b'not listed')
        self.assertFalse(self.run_recipe(2)['checker_started'])

    def test_companion_created_during_checker_refused(self):
        executable(self.checker, "import os,pathlib\n(pathlib.Path(os.environ['LEAN_PATH'])/'Test/Helper.olean.private').write_bytes(b'not listed')\n")
        self.configure()
        self.assertIn('object companion', self.run_recipe(2)['error'])

    def cancellation(self, signum):
        # Exercise only owned synthetic processes. The GNU timer must survive
        # abrupt launcher loss; this is not a replacement for VA1's outer guard.
        marker = self.root / 'pid'
        child_script = self.root / 'cancel.py'
        child_script.write_text("import importlib.util,sys,os,pathlib\n"
            + "s=importlib.util.spec_from_file_location('recipe'," + repr(str(Path(R.__file__))) + ");r=importlib.util.module_from_spec(s);sys.modules[s.name]=r;s.loader.exec_module(r)\n"
            + "with open(os.devnull,'wb') as log: r.process([sys.executable,'-c',"
            + repr("import os,time,pathlib;pathlib.Path(" + repr(str(marker)) + ").write_text(str(os.getpid()));time.sleep(30)")
            + "],pathlib.Path('.'),dict(os.environ),r.clock()+1.5,log)\n")
        parent = subprocess.Popen([sys.executable, '-I', '-B', str(child_script)], start_new_session=True,
                                  stdout=subprocess.DEVNULL, stderr=subprocess.DEVNULL)
        try:
            end = time.monotonic()+3
            while not marker.exists() and time.monotonic()<end:
                time.sleep(.01)
            self.assertTrue(marker.exists())
            pid = int(marker.read_text())
            parent.send_signal(signum)
            parent.wait(timeout=4)
            end = time.monotonic()+3
            while time.monotonic()<end:
                status = Path('/proc') / str(pid) / 'stat'
                if not status.exists() or status.read_text().split()[2]=='Z':
                    break
                time.sleep(.02)
            else:
                self.fail('owned synthetic checker survived GNU timeout/cancellation')
        finally:
            if parent.poll() is None:
                parent.kill(); parent.wait()
            try:
                os.killpg(parent.pid, signal.SIGKILL)
            except ProcessLookupError:
                pass

    def test_term_cancellation_propagates(self):
        self.cancellation(signal.SIGTERM)

    def test_killed_launcher_retains_gnu_deadline(self):
        self.cancellation(signal.SIGKILL)

    def test_production_pins_and_optimized_refusal(self):
        self.assertEqual(R.REFERENCE.count, 267)
        self.assertEqual(R.REFERENCE.total_bytes, 638245176)
        self.assertEqual(R.REFERENCE.seconds, 300)
        self.assertFalse(R.REFERENCE.synthetic)
        result = subprocess.run([sys.executable, '-I', '-B', '-O', str(Path(R.__file__))], capture_output=True, text=True)
        self.assertNotEqual(result.returncode, 0)
        self.assertIn('optimized Python refused', result.stderr)


if __name__ == '__main__':
    unittest.main()
