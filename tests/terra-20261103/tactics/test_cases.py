"""Guard tactic runner backend selection, failure classification and scratch cleanup.

The pinned runner is real; Lake/MCP are recording substitutes for heavy Lean.
These fixtures establish process/protocol behavior, never tactic proof validity.
"""
import hashlib
import json
import os
from pathlib import Path
import re
import shutil
import subprocess
import sys
import tempfile
import unittest

ROOT = Path(__file__).resolve().parents[3]
TOOL = ROOT / 'scripts/coord-tools/try-tactics.sh'
STANDARD = ['rfl', 'decide', 'omega', 'simp only', 'sol_prove', 'sol_chain']
MOCK = r'''import json, os, pathlib, sys
cfg=json.loads(os.environ['TACTICS_CONFIG'])
args=sys.argv[1:]; kind=pathlib.Path(sys.argv[0]).name
if kind=='lake':
    file=pathlib.Path(args[-1]); text=file.read_text()
    candidate=text.split(':= by\n  ',1)[1].rstrip('\n')
else:
    file=pathlib.Path(args[1]) if args[0]=='try' else None
    text=file.read_text() if file else None
    candidate=args[-1] if file else None
row={'kind':kind,'args':args,'text':text,'candidate':candidate,
     'cwd':os.getcwd(),'home':os.environ['HOME']}
with open(os.environ['TACTICS_RECORD'],'a') as f: f.write(json.dumps(row)+'\n')
if kind!='lake' and args[0]=='status':
    print('status'); sys.exit(cfg.get('status',0))
print('recorded:'+str(candidate))
mode=cfg.get('mode','pass')
if mode=='sorry': print("warning: declaration uses 'sorry'")
rc=0 if mode in ('pass','sorry') else (2 if mode=='bridge_error' else 1)
if mode=='selected': rc=0 if candidate in cfg['successes'] else 1
sys.exit(rc)
'''


class Tactics(unittest.TestCase):
    def setUp(self):
        self.tmp = tempfile.TemporaryDirectory(prefix='tactics fixture ')
        self.addCleanup(self.tmp.cleanup)
        self.base = Path(self.tmp.name)
        self.repo = self.base / 'repo with spaces'
        self.repo.mkdir()
        subprocess.run(['git', 'init', '-q', str(self.repo)], check=True)
        self.tools = self.base / 'tools'; self.tools.mkdir()
        self.runner = self.tools / 'try-tactics.sh'
        self.runner.write_bytes(TOOL.read_bytes())
        self.assertEqual(hashlib.sha256(self.runner.read_bytes()).hexdigest(),
                         '75afcf2b39087397fc1a532af34757ec7aad53a3c26fb2afb39cdec9bd7dd821')
        self.bin = self.base / 'bin'; self.bin.mkdir()
        self.record = self.base / 'calls.jsonl'
        self.temp = self.base / 'scratch'; self.temp.mkdir()
        self.home = self.base / 'home'; self.home.mkdir()
        # Both heavy backends record calls and source text before the real runner
        # removes its scratch files. The actual MCP daemon is never started.
        self.bridge = self.tools / 'lean-mcp'
        self.bridge.write_text(MOCK)
        lake = self.bin / 'lake'
        lake.write_text('#!' + sys.executable + '\n' + MOCK)
        lake.chmod(0o755)
        self.env = {k: v for k, v in os.environ.items()
                    if not k.startswith(('GIT_', 'TRY_TACTICS_', 'LEAN_', 'LAKE_', 'ELAN_'))
                    and k not in ('BASH_ENV', 'ENV', 'CDPATH', 'PYTHONPATH', 'PYTHONHOME')}
        self.env.update(HOME=str(self.home), TMPDIR=str(self.temp),
                        PATH=str(self.bin) + os.pathsep + os.path.dirname(sys.executable)
                        + os.pathsep + '/usr/bin:/bin',
                        TACTICS_RECORD=str(self.record), PYTHONDONTWRITEBYTECODE='1')

    def run_tool(self, backend='lake', mode='pass', extra=(), goal=None, status=0):
        self.env['TRY_TACTICS_BACKEND'] = backend
        self.env['TACTICS_CONFIG'] = json.dumps({'mode': mode, 'status': status,
                                                'successes': ['omega', 'exact custom']})
        goal = goal or 'Demo.theorem'
        proc = subprocess.run(['bash', str(self.runner), 'Demo.Module', str(goal), *extra],
                              cwd=self.repo, env=self.env, capture_output=True,
                              text=True, timeout=20)
        calls = [json.loads(s) for s in self.record.read_text().splitlines()] if self.record.exists() else []
        return proc, calls

    def check_calls(self, proc, calls, backend, extra=(), proposition='type_of% Demo.theorem',
                    expected_status='PASS', rc=0, probes=0):
        self.assertEqual(proc.returncode, rc, proc.stderr + proc.stdout)
        candidates = STANDARD + list(extra)
        probe_rows = [r for r in calls if r['args'][0] == 'status']
        self.assertEqual(len(probe_rows), probes)
        attempts = [r for r in calls if r['args'][0] != 'status']
        self.assertEqual(calls, probe_rows + attempts)
        for row in probe_rows:
            self.assertEqual(row['kind'], 'lean-mcp')
            self.assertEqual(row['args'], ['status'])
            self.assertIsNone(row['text'])
            self.assertEqual(row['cwd'], str(self.repo))
            self.assertEqual(row['home'], str(self.home))
        self.assertEqual([r['candidate'] for r in attempts], candidates)
        lines = proc.stdout.splitlines()
        self.assertEqual(len(lines), len(candidates))
        logpaths = []
        for i, (candidate, row, line) in enumerate(zip(candidates, attempts, lines), 1):
            m = re.fullmatch(r'(PASS|FAIL) (.+) ([0-9]+)s (.+)', line)
            self.assertIsNotNone(m, line)
            status = expected_status(candidate) if callable(expected_status) else expected_status
            self.assertEqual((m[1], m[2]), (status, candidate))
            log = Path(m[4]); logpaths.append(log)
            self.assertEqual(log.name, str(i) + '.log')
            self.assertEqual(log.parent.parent, self.temp)
            self.assertIn('recorded:' + candidate, log.read_text())
            self.assertEqual(row['cwd'], str(self.repo))
            self.assertEqual(row['home'], str(self.home))
            self.assertEqual(row['kind'], 'lake' if backend == 'lake' else 'lean-mcp')
            if backend == 'lake':
                self.assertEqual(row['args'][:-1], ['env', 'lean', '--tstack=131072'])
                self.assertEqual(row['text'], 'import Demo.Module\n\nexample : ' + proposition + ' := by\n  ' + candidate + '\n')
                source = Path(row['args'][-1])
                self.assertEqual(source.name, 'candidate' + str(i) + '.lean')
                self.assertEqual(source.parent.parent, self.temp)
                self.assertTrue(source.parent.name.startswith('try-tactics-src.'))
            else:
                self.assertEqual(row['args'][0], 'try')
                self.assertEqual(row['args'][2:], [str(len(proposition.splitlines()) + 3), candidate])
                self.assertEqual(row['text'], 'import Demo.Module\n\nexample : ' + proposition + ' := by\n  sorry\n')
                source = Path(row['args'][1])
                self.assertEqual(source.parent, self.repo)
            self.assertFalse(source.exists(), str(source))
        self.assertEqual(len({p.parent for p in logpaths}), 1)
        self.assertEqual(set(logpaths[0].parent.iterdir()), set(logpaths))
        self.assertEqual(set(self.temp.iterdir()), {logpaths[0].parent})
        self.assertEqual(list(self.repo.glob('TerraTry*.lean')), [])
        return attempts

    def test_usage(self):
        proc = subprocess.run(['bash', str(self.runner)], cwd=self.repo, env=self.env,
                              capture_output=True, text=True, timeout=10)
        self.assertEqual(proc.returncode, 2)
        self.assertIn('usage:', proc.stderr)
        self.assertFalse(self.record.exists())
        self.assertEqual(list(self.temp.iterdir()), [])

    def test_lake_success(self):
        proc, calls = self.run_tool()
        self.check_calls(proc, calls, 'lake')
        # Guard the review regression: forced backends must reject extra probes.
        unexpected = dict(calls[0], kind='lean-mcp', args=['status'], text=None, candidate=None)
        with self.assertRaises(AssertionError):
            self.check_calls(proc, [unexpected] + calls, 'lake')

    def test_all_fail(self):
        self.check_calls(*self.run_tool(mode='fail'), 'lake', expected_status='FAIL', rc=1)

    def test_sorry_rejected(self):
        proc, calls = self.run_tool(mode='sorry')
        self.check_calls(proc, calls, 'lake', expected_status='FAIL', rc=1)
        for line in proc.stdout.splitlines():
            self.assertIn("declaration uses 'sorry'", Path(re.fullmatch(r'(PASS|FAIL) (.+) ([0-9]+)s (.+)', line)[4]).read_text())

    def test_standard_and_custom_candidates(self):
        extra = ['exact custom', 'fail custom']
        status = lambda c: 'PASS' if c in ('omega', 'exact custom') else 'FAIL'
        self.check_calls(*self.run_tool(mode='selected', extra=extra), 'lake',
                         extra=extra, expected_status=status)

    def test_multiline_goal_line(self):
        goal = self.base / 'multiline goal.txt'; goal.write_text('True ∧\n  True\n')
        self.check_calls(*self.run_tool(backend='mcp', goal=goal), 'mcp',
                         proposition='True ∧\n  True')

    def test_bridge_error_exit(self):
        proc, calls = self.run_tool(backend='mcp', mode='bridge_error')
        self.check_calls(proc, calls, 'mcp', expected_status='FAIL', rc=2)
        self.assertIn('bridge error', proc.stderr)

    def test_mcp_success(self):
        self.check_calls(*self.run_tool(backend='mcp'), 'mcp')

    def test_mcp_scratch_cleanup(self):
        self.check_calls(*self.run_tool(backend='mcp', mode='fail'), 'mcp',
                         expected_status='FAIL', rc=1)

    def test_lake_scratch_cleanup(self):
        self.check_calls(*self.run_tool(mode='fail'), 'lake', expected_status='FAIL', rc=1)

    def test_invalid_backend(self):
        proc, calls = self.run_tool(backend='wrong')
        self.assertEqual(proc.returncode, 2)
        self.assertIn('invalid TRY_TACTICS_BACKEND', proc.stderr)
        self.assertEqual(calls, [])
        self.assertEqual(list(self.repo.glob('TerraTry*.lean')), [])
        logs = list(self.temp.iterdir())
        self.assertEqual(len(logs), 1)
        self.assertTrue(logs[0].name.startswith('try-tactics.'))
        self.assertEqual(list(logs[0].iterdir()), [])

    def test_auto_backend(self):
        for status, backend in [(0, 'mcp'), (1, 'lake')]:
            with self.subTest(status=status):
                if self.record.exists(): self.record.unlink()
                for p in self.temp.iterdir(): shutil.rmtree(p)
                proc, calls = self.run_tool(backend='auto', status=status)
                self.assertEqual(calls[0]['kind'], 'lean-mcp')
                self.assertEqual(calls[0]['args'], ['status'])
                self.assertEqual(len([r for r in calls if r['args'][0] == 'status']), 1)
                self.check_calls(proc, calls, backend, probes=1)
