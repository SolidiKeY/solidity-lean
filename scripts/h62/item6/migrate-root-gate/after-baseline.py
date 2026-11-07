#!/usr/bin/env python3
"""One authorized serial diagnostic stage; never cut-over, edit source or merge."""
import fcntl
import hashlib
import json
import os
import signal
from pathlib import Path
import subprocess
import sys
import time

REPO = Path('/workspace/solidity-lean-migrate-root-gate')
EVIDENCE = Path('/workspace/h62-migrate-root-gate-evidence')
STATE = EVIDENCE/'queued-migration/state.json'
EXPECTED_HEAD = '39719c8cf7d51fdaa09e485e079eda6bee37a926'
BRANCH = 'codex/solidity-h62-6-20261106/migrate-root-gate'
FACADE = EVIDENCE/'serial-v4.35.0'
PIN = '7289597a44543246c9227b8cae501767e095ce17f6d448b95fc4a8dc97268f6d'
sys.dont_write_bytecode = True


def interrupted(signum, _frame):
    raise InterruptedError('driver signal '+str(signum))


signal.signal(signal.SIGTERM, interrupted)
signal.signal(signal.SIGINT, interrupted)


def state(status, **details):
    data = dict(status=status, observed_unix_seconds=time.time(), **details)
    pending = STATE.with_suffix('.tmp')
    pending.write_text(json.dumps(data, indent=2)+'\n')
    pending.replace(STATE)
    print(json.dumps(data), flush=True)


def git(*args):
    return subprocess.check_output(['git', *args], cwd=REPO, text=True).strip()


def main():
    if (EVIDENCE/'PERFORMANCE-HOLD.json').exists():
        state('blocked', blocker='PERFORMANCE_STOP_H70', hold=str(EVIDENCE/'PERFORMANCE-HOLD.json'))
        return 75
    state('waiting-baseline-writer-lock', expected_head=EXPECTED_HEAD)
    with open('/tmp/solidity-lean-feature-groups-20261025/writer.lock', 'a') as lock:
        fcntl.flock(lock, fcntl.LOCK_EX)
        if (EVIDENCE/'PERFORMANCE-HOLD.json').exists():
            state('blocked', blocker='PERFORMANCE_STOP_H70')
            return 75
        baseline_path = EVIDENCE/'clean-baseline-v4.24.0.json'
        if not baseline_path.exists():
            state('blocked', blocker='BASELINE_RESULT_MISSING')
            return 75
        baseline = json.loads(baseline_path.read_text())
        preflight = json.loads((EVIDENCE/'clean-baseline-preflight.json').read_text())
        if (baseline.get('cwd') != str(REPO) or baseline.get('command') != ['./run-lean.sh']
                or preflight.get('head') != EXPECTED_HEAD
                or not preflight.get('build_directory_absent')
                or not preflight.get('artifact_cache_absent')
                or not preflight.get('tracked_tree_clean')):
            state('blocked', blocker='BASELINE_IDENTITY_MISMATCH')
            return 75
        if baseline['exit'] != 0 or baseline.get('resource_stop'):
            state('blocked', blocker='BASELINE_GATE_FAILURE', baseline=baseline)
            return 75
        if git('rev-parse', 'HEAD') != EXPECTED_HEAD or git('branch', '--show-current') != BRANCH:
            state('blocked', blocker='CHECKOUT_IDENTITY_CHANGED')
            return 75
        if git('status', '--porcelain'):
            state('blocked', blocker='UNEXPECTED_LOCAL_WORK')
            return 75
        # Verify every frozen source byte after the writer lock, before timing.
        census = json.loads((EVIDENCE/'source-census-1.json').read_text())
        for name, entry in census['files'].items():
            if hashlib.sha256((REPO/name).read_bytes()).hexdigest() != entry['sha256']:
                state('blocked', blocker='FROZEN_SOURCE_CHANGED', path=name)
                return 75
        sys.path.insert(0, str(REPO/'scripts/h62/item6/migrate-root-gate'))
        from release_integrity import verify_release
        release = verify_release(EVIDENCE/'lean-4.35.0-linux.tar.zst', FACADE)
        (EVIDENCE/'queued-migration/release-sha256.json').write_text(json.dumps(release, sort_keys=True)+'\n')
        backup = EVIDENCE/'baseline-lake-final'
        cache = EVIDENCE/'migration-diagnostic-artifact-cache'
        output = EVIDENCE/'migration-diagnostic-v4.35.0.json'
        assert not backup.exists() and not cache.exists() and not output.exists()
        assert not output.with_suffix('.log').exists()
        assert (REPO/'.lake').is_dir() and not (REPO/'.lake').is_symlink()
        # Preserve every original baseline artifact; no reset/discard/clean.
        (REPO/'.lake').rename(backup)
        shim = EVIDENCE/'queued-migration/bin'
        shim.mkdir()
        lake = shim/'lake'
        lake.write_text('#!/usr/bin/env bash\nset -euo pipefail\n'
                        'if [[ "${1:-}" == build ]]; then\n'
                        '  exec /workspace/h62-migrate-root-gate-evidence/serial-v4.35.0/bin/lake --fail-fast "$@"\n'
                        'fi\nexec /workspace/h62-migrate-root-gate-evidence/serial-v4.35.0/bin/lake "$@"\n')
        lake.chmod(0o755)
        env = os.environ.copy()
        env.update(LEAN_SYSROOT=str(FACADE), LAKE_OVERRIDE_LEAN='true',
                   LEAN_NUM_THREADS='1', LAKE_CACHE_DIR=str(cache),
                   SOLKEY_RULES='/workspace/.setup/solkey/keyext.solidity.core/src/main/resources/org/key_project/solidity/proof/rules/solidityProgramRules.key',
                   PYTHONDONTWRITEBYTECODE='1')
        env['PATH'] = str(shim)+':'+str(FACADE/'bin')+':'+env['PATH']
        state('running-v4.35-diagnostic', head=EXPECTED_HEAD, archive_sha256=PIN,
              baseline_artifacts=str(backup), cache=str(cache), command='./run-lean.sh',
              note='fail-fast diagnostic; no source patches yet; no cut-over readiness')
        if (EVIDENCE/'PERFORMANCE-HOLD.json').exists():
            state('blocked', blocker='PERFORMANCE_STOP_H70')
            return 75
        child = subprocess.Popen([sys.executable,
                                  str(REPO/'scripts/h62/item6/migrate-root-gate/measure.py'),
                                  str(output), './run-lean.sh'], cwd=REPO, env=env,
                                 pass_fds=(lock.fileno(),))
        try:
            code = child.wait()
        except BaseException:
            signal.signal(signal.SIGTERM, signal.SIG_IGN)
            signal.signal(signal.SIGINT, signal.SIG_IGN)
            # Keep the writer lock until the supervisor has cleaned its Lean group.
            if child.poll() is None:
                child.send_signal(signal.SIGTERM)
                child.wait()
            raise
        result = json.loads(output.read_text()) if output.exists() else None
        if code != 0:
            state('diagnostic-failed', blocker='MIGRATION_DIAGNOSTICS_REQUIRE_OWNER_FIXES', result=result)
            return code
        delta = (result['wall_seconds']/baseline['wall_seconds']-1)*100
        (EVIDENCE/'queued-migration/comparison.json').write_text(json.dumps(
            dict(before=baseline, after=result, slowdown_percent=delta,
                 boundary='initial unmodified source diagnostic, not fleet overlay acceptance; cold artifact caches, OS page cache preparation unmatched'), indent=2)+'\n')
        if delta > 0:
            print('ESCALATE: H62 migration full-build slowdown: '+str(delta)+'%', flush=True)
        if delta > 10:
            state('stopped-slowdown', slowdown_percent=delta)
            return 75
        state('diagnostic-passed', slowdown_percent=delta,
              pending=['fleet-pin-receipts', 'directory-overlay-reconciliation',
                       'full acceptance reviews', 'production cache auth', 'coordinator cut-over'])
        return 0


if __name__ == '__main__':
    try:
        raise SystemExit(main())
    except Exception as exc:
        state('blocked', blocker='DRIVER_EXCEPTION', error=type(exc).__name__+': '+str(exc))
        raise
