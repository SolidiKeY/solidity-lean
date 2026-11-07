#!/usr/bin/env python3
"""Official Lake v4.35.0 HTTP get/put protocol fixture, never a master cache.

The loopback service tests transport/CAS behavior, not S3 authentication.
SHA256 sidecars bind exact source and every remote object. Real fleet service,
credentials, owner adoption and coordinator cut-over remain external gates.
"""
import argparse
from concurrent.futures import ThreadPoolExecutor
import hashlib
from http.server import BaseHTTPRequestHandler, ThreadingHTTPServer
import json
import os
from pathlib import Path
import shutil
import subprocess
import threading
import time
from release_integrity import verify_release
from urllib.parse import unquote, urlsplit

ROOT = Path(__file__).resolve().parents[4]
FIXTURE = ROOT/'tests/h62/item6/migrate-root-gate/cache-fixture'
PIN = '7289597a44543246c9227b8cae501767e095ce17f6d448b95fc4a8dc97268f6d'


def digest(path):
    return hashlib.sha256(path.read_bytes()).hexdigest()


def main():
    p = argparse.ArgumentParser()
    p.add_argument('output', type=Path)
    p.add_argument('facade', type=Path)
    p.add_argument('archive', type=Path)
    a = p.parse_args()
    release_manifest = verify_release(a.archive, a.facade.resolve())
    a.output.mkdir()  # refuse to overwrite evidence
    (a.output/'release-sha256.json').write_text(json.dumps(release_manifest, indent=2)+'\n')
    output = a.output.resolve()
    fixture = output/'fixture'
    shutil.copytree(FIXTURE, fixture)
    (fixture/'lean-toolchain').write_text('leanprover/lean4:v4.35.0\n')
    (fixture/'.gitignore').write_text('.lake/\nlake-manifest.json\n')
    env = os.environ.copy()
    env.update(LEAN_NUM_THREADS='1', LEAN_SYSROOT=str(a.facade.resolve()),
               LAKE_OVERRIDE_LEAN='true', LAKE_ARTIFACT_CACHE='true',
               LAKE_CACHE_KEY='h62-fixture-access:h62-fixture-secret')
    env['PATH'] = str(a.facade.resolve()/'bin')+os.pathsep+env['PATH']
    commands = []
    mutex = threading.Lock()

    def run(label, command, cache='producer-cache', expect=0):
        current = dict(env, LAKE_CACHE_DIR=str(output/cache))
        result = subprocess.run(command, cwd=fixture, env=current,
                                stdout=subprocess.PIPE, stderr=subprocess.STDOUT,
                                text=True, timeout=180)
        (output/(label+'.log')).write_text(result.stdout)
        with mutex:
            commands.append(dict(label=label, command=command, exit=result.returncode))
        assert expect is None or result.returncode == expect, (label, result.returncode, result.stdout[-2000:])
        return result.stdout

    run('git-init', ['git', 'init', '-q'])
    run('git-add', ['git', 'add', '.'])
    run('git-commit', ['git', '-c', 'user.name=H62 Fixture', '-c',
                       'user.email=h62-fixture@invalid', 'commit', '-qm', 'fixture'])
    revision = run('revision', ['git', 'rev-parse', 'HEAD']).strip()
    tree = run('tree', ['git', 'rev-parse', 'HEAD^{tree}']).strip()
    assert '4.35.0' in run('version', ['lake', '--version'])
    mappings = output/'mappings.jsonl'
    run('build', ['lake', 'build', '-o', str(mappings)])
    original = digest(fixture/'.lake/build/lib/lean/Fixture.olean')
    artifact_manifest = {f.name: digest(f) for f in (output/'producer-cache/artifacts').iterdir() if f.is_file()}

    def verify_received(cache, unpacked=False):
        actual = {f.name: digest(f) for f in (output/cache/'artifacts').glob('*') if f.is_file()}
        expected = artifact_manifest if unpacked else {k: v for k, v in artifact_manifest.items() if k.endswith('.ltar')}
        assert actual == expected, 'receiver SHA256 integrity mismatch'

    def identity_guard(actual_tree, actual_pin):
        assert actual_tree == tree, 'source tree identity mismatch'
        assert actual_pin == PIN, 'toolchain identity mismatch'
        assert not subprocess.check_output(['git', 'status', '--porcelain'], cwd=fixture).strip(), 'dirty source tree'

    identity_guard(tree, PIN)
    identity_controls = []
    for bad_tree, bad_pin in [('0'*40, PIN), (tree, '0'*64)]:
        try:
            identity_guard(bad_tree, bad_pin)
        except AssertionError:
            identity_controls.append(True)
        else:
            raise AssertionError('identity mismatch accepted')
    objects = output/'remote'
    objects.mkdir()
    server_lock = threading.Lock()
    requests = []
    overlap_enabled = False
    corrupt_download = False
    get_active = threading.Event()
    put_active = threading.Event()
    overlap_observed = []

    class Handler(BaseHTTPRequestHandler):
        def log_message(self, *_):
            pass

        def object_path(self):
            relative = unquote(urlsplit(self.path).path).lstrip('/')
            path = (objects/relative).resolve()
            if not path.is_relative_to(objects):
                raise ValueError('unsafe path')
            return path

        def do_PUT(self):
            data = self.rfile.read(int(self.headers['Content-Length']))
            path = self.object_path()
            if overlap_enabled and self.path.endswith('.art'):
                put_active.set()
                assert get_active.wait(30), 'no overlapping get'
                overlap_observed.append('put')
            with server_lock:
                status = 200
                if path.exists() and path.read_bytes() != data:
                    status = 409
                else:
                    path.parent.mkdir(parents=True, exist_ok=True)
                    path.write_bytes(data)
                requests.append(['PUT', self.path, status, time.monotonic()])
            self.send_response(status)
            self.send_header('Content-Length', '0')
            self.end_headers()

        def do_GET(self):
            path = self.object_path()
            if overlap_enabled and self.path.endswith('.art'):
                get_active.set()
                assert put_active.wait(30), 'no overlapping put'
                overlap_observed.append('get')
            with server_lock:
                status = 200 if path.is_file() else 404
                data = path.read_bytes() if status == 200 else b''
                requests.append(['GET', self.path, status, time.monotonic()])
                if corrupt_download and self.path.endswith('.art'):
                    data += b'corrupt'
            self.send_response(status)
            self.send_header('Content-Length', str(len(data)))
            self.end_headers()
            self.wfile.write(data)

    server = ThreadingHTTPServer(('127.0.0.1', 0), Handler)
    worker = threading.Thread(target=server.serve_forever, daemon=True)
    worker.start()
    endpoint = 'http://127.0.0.1:'+str(server.server_port)
    env.update(LAKE_CACHE_ARTIFACT_ENDPOINT=endpoint+'/artifacts',
               LAKE_CACHE_REVISION_ENDPOINT=endpoint+'/revisions')
    scope = 'h62-fixture/'+PIN+'/'+tree
    try:
        put = ['lake', 'cache', 'put', str(mappings), '--scope='+scope]
        get = ['lake', 'cache', 'get', '--scope='+scope, '--rev='+revision]
        run('put', put)
        manifest = {str(f.relative_to(objects)): digest(f) for f in objects.rglob('*') if f.is_file()}
        assert manifest and any(f.endswith('.art') for f in manifest)

        def verify_remote():
            actual = {str(f.relative_to(objects)): digest(f) for f in objects.rglob('*') if f.is_file()}
            assert actual == manifest, 'SHA256 remote artifact integrity mismatch'

        overlap_enabled = True
        with ThreadPoolExecutor(max_workers=3) as pool:
            futures = [pool.submit(run, 'get-concurrent-'+str(i), get, 'receiver-cache') for i in range(2)]
            futures.append(pool.submit(run, 'put-concurrent', put))
            for future in futures:
                future.result()
        overlap_enabled = False
        assert set(overlap_observed) == {'get', 'put'}
        verify_remote()
        verify_received('receiver-cache')
        identity_guard(tree, PIN)
        shutil.rmtree(fixture/'.lake/build')
        run('restore', ['lake', 'build'], 'receiver-cache')
        verify_received('receiver-cache', unpacked=True)
        assert digest(fixture/'.lake/build/lib/lean/Fixture.olean') == original
        # Enforce the trusted SHA manifest on a real corrupt download before restore.
        corrupt_download = True
        run('corrupt-get', get, 'corrupt-receiver', expect=None)
        try:
            verify_received('corrupt-receiver')
        except AssertionError:
            corruption_rejected = True
        else:
            raise AssertionError('corrupt download accepted')
        corrupt_download = False
        verify_remote()
        assert not run('clean-source', ['git', 'status', '--porcelain']).strip()
        summary = dict(status='fixture-pass', toolchain='leanprover/lean4:v4.35.0',
                       archive_sha256=PIN, source_revision=revision, source_tree=tree,
                       olean_sha256=original, remote_sha256=manifest,
                       corruption_rejected=corruption_rejected, identity_controls=identity_controls,
                       executed_release_manifest_sha256=digest(output/'release-sha256.json'),
                       receiver_artifact_sha256=artifact_manifest, overlap_observed=overlap_observed,
                       concurrency='two gets sharing one empty receiver cache plus simultaneous put',
                       boundary='loopback transport; no S3 auth or fleet adoption proof', commands=commands)
        (output/'result.json').write_text(json.dumps(summary, indent=2)+'\n')
    finally:
        server.shutdown()
        server.server_close()
        worker.join()
        (output/'requests.json').write_text(json.dumps(requests, indent=2)+'\n')
    print(output/'result.json')


if __name__ == '__main__':
    main()
