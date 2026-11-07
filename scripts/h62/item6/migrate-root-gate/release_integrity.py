"""Bind an extracted toolchain and its serial facade to the pinned archive."""
import hashlib
import os
from pathlib import Path
import subprocess
import tarfile

PIN = '7289597a44543246c9227b8cae501767e095ce17f6d448b95fc4a8dc97268f6d'


def digest(path):
    with path.open('rb') as stream:
        return hashlib.file_digest(stream, 'sha256').hexdigest()


def verify_release(archive, facade):
    assert digest(archive) == PIN, 'official release archive mismatch'
    release = (facade/'bin/lake').resolve().parents[1]
    manifest = {}
    proc = subprocess.Popen(['zstd', '-dc', str(archive)], stdout=subprocess.PIPE)
    try:
        with tarfile.open(fileobj=proc.stdout, mode='r|') as tar:
            for member in tar:
                parts = Path(member.name).parts
                assert parts[0] == 'lean-4.35.0-linux' and '..' not in parts
                relative = Path(*parts[1:])
                path = release/relative
                if member.isfile():
                    expected = hashlib.file_digest(tar.extractfile(member), 'sha256').hexdigest()
                    assert digest(path) == expected, 'release content mismatch: '+str(relative)
                    manifest[str(relative)] = expected
                elif member.issym():
                    assert path.is_symlink() and os.readlink(path) == member.linkname
        assert proc.wait() == 0, 'archive decompression failed'
    finally:
        if proc.poll() is None:
            proc.kill()
            proc.wait()
        proc.stdout.close()
    for entry in release.iterdir():
        if entry.name != 'bin':
            assert (facade/entry.name).resolve() == entry.resolve(), 'facade library mismatch'
    for entry in (release/'bin').iterdir():
        if entry.name != 'lean':
            assert (facade/'bin'/entry.name).resolve() == entry.resolve(), 'facade executable mismatch'
    # The only executable adapter is checked byte-for-byte against its generator.
    import shlex
    expected = ('#!/usr/bin/env bash\nset -euo pipefail\nexec 8>'+shlex.quote(str(facade/'lean-process.lock'))+
                '\nflock 8\nexport LEAN_NUM_THREADS=1\nexec '+
                shlex.quote(str(release/'bin/lean'))+' -j1 "$@"\n')
    assert (facade/'bin/lean').read_text() == expected, 'unexpected Lean adapter'
    return manifest
