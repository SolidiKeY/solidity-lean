import hashlib
import os
from pathlib import Path
import subprocess
import tempfile
import unittest

TOOL = Path(__file__).resolve().parents[3] / 'scripts/coord-tools/disk.sh'

class DiskCases(unittest.TestCase):
    def setUp(self):
        self.temp = tempfile.TemporaryDirectory()
        self.addCleanup(self.temp.cleanup)
        self.root = Path(self.temp.name)
        self.repo = self.root / 'repo'
        self.repo.mkdir()
        self.git('init', '-q')
        self.git('config', 'user.email', 'test@example.invalid')
        self.git('config', 'user.name', 'Fixture')
        (self.repo / 'tracked').write_text('base\n')
        self.git('add', 'tracked')
        self.git('commit', '-qm', 'base')
        self.base = self.git('rev-parse', 'HEAD').strip()
        (self.repo / 'tracked').write_text('next\n')
        self.git('commit', '-qam', 'next')
        self.evidence = self.root / 'evidence'
        self.evidence.mkdir()
        self.bin = self.root / 'bin'
        self.bin.mkdir()
        self.calls = self.root / 'calls'
        self.cg = self.root / 'cgroup'
        self.cg.mkdir()
        (self.cg / 'memory.current').write_text('123\n')
        (self.cg / 'memory.max').write_text('456\n')
        self.env = dict(os.environ, DISK_REPO=str(self.repo), DISK_CGROUP=str(self.cg),
                        DISK_EVIDENCE_ROOTS=str(self.evidence), DISK_MIN_FREE_BYTES='0',
                        PATH=str(self.bin) + os.pathsep + os.environ['PATH'], CALLS=str(self.calls))
        for name in ('docker', 'podman'):
            p = self.bin / name
            p.write_text('#!/bin/sh\nprintf "%s\\n" "' + name + ' $*" >> "$CALLS"\nif [ "$1" = ps ]; then printf "exited-1\\nexited-2\\n"; fi\n')
            p.chmod(0o755)

    def git(self, *args):
        return subprocess.check_output(['git', '-C', str(self.repo), *args], text=True, stderr=subprocess.PIPE)

    def worktree(self):
        wt = self.root / 'worktree'
        self.git('worktree', 'add', '-q', '--detach', str(wt))
        return wt

    def run_disk(self, *args):
        return subprocess.run([str(TOOL), *args], cwd=self.repo, env=self.env, text=True, capture_output=True)

    def seal(self, name, mtime):
        d = self.evidence / name
        d.mkdir()
        self.git('bundle', 'create', str(d / 'data.bundle'), self.base + '..HEAD')
        (d / 'manifest').write_text('manifest\n')
        names = ['data.bundle', 'manifest']
        (d / 'SHA256SUMS').write_text(''.join(hashlib.sha256((d / n).read_bytes()).hexdigest() + '  ' + n + '\n' for n in names))
        os.utime(d / 'SHA256SUMS', ns=(mtime, mtime))
        return d

    def snapshot(self, directory):
        # Preserve the full tree, including empty directories and file contents.
        return {p.relative_to(directory).as_posix():
                ('dir',) if p.is_dir() else ('file', p.read_bytes())
                for p in directory.rglob('*')}

    def rewrite_sums(self, directory):
        files = sorted(p for p in directory.iterdir() if p.is_file() and p.name != 'SHA256SUMS')
        (directory / 'SHA256SUMS').write_text(''.join(
            hashlib.sha256(p.read_bytes()).hexdigest() + '  ' + p.name + '\n' for p in files))
        os.utime(directory / 'SHA256SUMS', ns=(2, 2))

    def assert_clean_run(self, result):
        self.assertEqual(result.returncode, 0, result.stderr)
        self.assertIn('disk: path=', result.stdout)
        self.assertIn('ram: current=123 max=456', result.stdout)
        if self.calls.exists():
            self.assertEqual(self.calls.read_text().splitlines(), [
                'docker ps -aq --filter status=exited', 'docker rm exited-1', 'docker rm exited-2',
                'podman ps -aq --filter status=exited', 'podman rm exited-1', 'podman rm exited-2'])

    def test_report_only(self):
        wt = self.worktree()
        build = wt / '.lake/build'
        build.mkdir(parents=True)
        (build / 'keep').write_text('x')
        self.seal('old', 1)
        self.seal('new', 2)
        before_seals = self.snapshot(self.evidence)
        before_build = self.snapshot(build)
        r = self.run_disk()
        self.assert_clean_run(r)
        self.assertEqual(self.snapshot(build), before_build)
        self.assertEqual(self.snapshot(self.evidence), before_seals)
        self.assertFalse(self.calls.exists())
        self.assertNotIn('deleted:', r.stdout)

    def test_missing_cgroup(self):
        self.env['DISK_CGROUP'] = str(self.root / 'absent')
        r = self.run_disk()
        self.assertEqual(r.returncode, 0, r.stderr)
        self.assertIn('ram: current=unavailable max=unavailable', r.stdout)
        self.assertFalse(self.calls.exists())

    def test_real_worktree_build(self):
        wt = self.worktree()
        build = wt / '.lake/build'
        build.mkdir(parents=True)
        (build / 'artifact').write_text('x')
        r = self.run_disk('--free')
        self.assert_clean_run(r)
        self.assertFalse(build.exists())
        self.assertIn('deleted: ' + str(build), r.stdout)
        self.assertTrue((wt / '.git').is_file())

    def test_symlink_lake_preserved(self):
        wt = self.worktree()
        dest = self.root / 'external'
        (dest / 'build').mkdir(parents=True)
        (dest / 'build/keep').write_text('x')
        (wt / '.lake').symlink_to(dest, target_is_directory=True)
        before_link = os.readlink(wt / '.lake')
        self.assert_clean_run(self.run_disk('--free'))
        self.assertEqual(os.readlink(wt / '.lake'), before_link)
        self.assertEqual((dest / 'build/keep').read_text(), 'x')
        self.assertTrue((wt / '.lake').is_symlink())

    def test_symlink_build_preserved(self):
        wt = self.worktree()
        dest = self.root / 'external'
        dest.mkdir()
        (dest / 'keep').write_text('x')
        (wt / '.lake').mkdir()
        (wt / '.lake/build').symlink_to(dest, target_is_directory=True)
        before_link = os.readlink(wt / '.lake/build')
        self.assert_clean_run(self.run_disk('--free'))
        self.assertEqual(os.readlink(wt / '.lake/build'), before_link)
        self.assertEqual((dest / 'keep').read_text(), 'x')
        self.assertTrue((wt / '.lake/build').is_symlink())

    def test_main_build_preserved(self):
        build = self.repo / '.lake/build'
        build.mkdir(parents=True)
        (build / 'keep').write_text('x')
        self.worktree()
        self.assert_clean_run(self.run_disk('--free'))
        self.assertEqual((build / 'keep').read_text(), 'x')

    def test_extra_seal_file_preserved(self):
        old = self.seal('old', 1)
        (old / 'extra').write_text('unlisted')
        self.seal('new', 2)
        before = self.snapshot(old)
        self.assert_clean_run(self.run_disk('--free'))
        self.assertEqual(self.snapshot(old), before)
        self.assertEqual({p.name for p in old.iterdir()}, {'data.bundle', 'manifest', 'SHA256SUMS', 'extra'})
        self.assertEqual({p.name for p in self.evidence.iterdir()}, {'old', 'new'})

    def test_invalid_checksum_preserved(self):
        old = self.seal('tampered', 2)
        (old / 'manifest').write_text('tampered')
        missing = self.seal('missing-bundle', 2)
        (missing / 'data.bundle').unlink()
        self.rewrite_sums(missing)
        malformed = self.seal('malformed-bundle', 2)
        (malformed / 'data.bundle').write_bytes(b'not a git bundle\n')
        self.rewrite_sums(malformed)
        truncated = self.seal('truncated-pack', 2)
        bundle = truncated / 'data.bundle'
        bundle.write_bytes(bundle.read_bytes()[:-12])
        self.rewrite_sums(truncated)
        valid_old = self.seal('valid-old', 1)
        self.seal('new', 3)
        for d in (missing, malformed, truncated):
            check = subprocess.run(['sha256sum', '-c', '--strict', 'SHA256SUMS'], cwd=d, capture_output=True)
            self.assertEqual(check.returncode, 0, check.stderr)
        bad_verify = subprocess.run(['git', '-C', str(self.repo), 'bundle', 'verify', str(malformed / 'data.bundle')], capture_output=True)
        self.assertNotEqual(bad_verify.returncode, 0)
        verify = subprocess.run(['git', '-C', str(self.repo), 'bundle', 'verify', str(bundle)], capture_output=True)
        self.assertEqual(verify.returncode, 0, verify.stderr)
        unbundle = subprocess.run(['git', '-C', str(self.repo), 'bundle', 'unbundle', str(bundle)], capture_output=True)
        self.assertNotEqual(unbundle.returncode, 0)
        before = {d.name: self.snapshot(d) for d in (old, missing, malformed, truncated)}
        r = self.run_disk('--free')
        self.assert_clean_run(r)
        self.assertFalse(valid_old.exists())
        self.assertEqual({d.name: self.snapshot(d) for d in (old, missing, malformed, truncated)}, before)
        self.assertEqual({p.name for p in self.evidence.iterdir()}, set(before) | {'new'})

    def test_git_directory_preserved(self):
        old = self.seal('old', 1)
        (old / '.git').mkdir()
        self.seal('new', 2)
        before = self.snapshot(old)
        self.assertEqual(list((old / '.git').iterdir()), [])
        self.assert_clean_run(self.run_disk('--free'))
        self.assertEqual(self.snapshot(old), before)
        self.assertEqual({p.name for p in self.evidence.iterdir()}, {'old', 'new'})

    def test_newest_seal_preserved(self):
        old = self.seal('old', 1)
        new = self.seal('new', 2)
        before = {p.name: p.read_bytes() for p in new.iterdir()}
        r = self.run_disk('--free')
        self.assert_clean_run(r)
        self.assertFalse(old.exists())
        self.assertEqual({p.name: p.read_bytes() for p in new.iterdir()}, before)
        self.assertEqual({p.name for p in self.evidence.iterdir()}, {'new'})

    def test_older_valid_seal_removed(self):
        old = self.seal('old', 1)
        new = self.seal('new', 2)
        r = self.run_disk('--free')
        self.assert_clean_run(r)
        self.assertFalse(old.exists())
        self.assertEqual({p.name for p in new.iterdir()}, {'data.bundle', 'manifest', 'SHA256SUMS'})
        self.assertIn('deleted: ' + str(old), r.stdout)
        self.assertNotIn('deleted: ' + str(new), r.stdout)

    def test_exited_containers_only(self):
        r = self.run_disk('--free')
        self.assert_clean_run(r)
        self.assertEqual(self.calls.read_text().splitlines(), [
            'docker ps -aq --filter status=exited', 'docker rm exited-1', 'docker rm exited-2',
            'podman ps -aq --filter status=exited', 'podman rm exited-1', 'podman rm exited-2'])
        self.assertEqual([line for line in r.stdout.splitlines() if line.startswith('deleted:')],
                         ['deleted: docker:exited-1', 'deleted: docker:exited-2',
                          'deleted: podman:exited-1', 'deleted: podman:exited-2'])

    def test_invalid_usage(self):
        wt = self.worktree()
        build = wt / '.lake/build'
        build.mkdir(parents=True)
        (build / 'keep').write_bytes(b'build content')
        self.seal('old', 1)
        self.seal('new', 2)
        before_build = self.snapshot(build)
        before_seals = self.snapshot(self.evidence)
        for args in (('--bad',), ('--free', 'extra')):
            with self.subTest(args=args):
                r = self.run_disk(*args)
                self.assertNotEqual(r.returncode, 0)
                self.assertIn('usage: disk.sh [--free]', r.stderr)
                self.assertEqual(r.stdout, '')
                self.assertEqual(self.snapshot(build), before_build)
                self.assertEqual(self.snapshot(self.evidence), before_seals)
        self.assertFalse(self.calls.exists())
