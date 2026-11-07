#!/usr/bin/env python3
"""Verify portable repository-relative inputs and archive-relative evidence.

Repository-only checking explicitly does not verify unavailable VM artifacts.
All hashes stream from disk; no Lean or other process is launched.
"""
import argparse
import hashlib
import json
import pathlib
import re
ROOT = pathlib.Path(__file__).resolve().parents[4]


def verify_files(root, rows):
    root = root.resolve()
    seen = set()
    for row in rows:
        if not isinstance(row, dict) or set(row) != {'path', 'bytes', 'sha256'}:
            raise ValueError('INVALID_FILE_RECORD')
        relative = pathlib.PurePosixPath(row['path'])
        if relative.is_absolute() or '..' in relative.parts or not relative.parts or str(relative) in seen:
            raise ValueError('UNSAFE_OR_DUPLICATE_PATH')
        seen.add(str(relative))
        if type(row['bytes']) is not int or row['bytes'] < 0 or not isinstance(row['sha256'], str) or not re.fullmatch('[0-9a-f]{64}', row['sha256']):
            raise ValueError('INVALID_FILE_IDENTITY')
        path = root / relative
        if not path.resolve().is_relative_to(root) or not path.is_file():
            raise ValueError('MISSING_OR_ESCAPING_FILE: ' + str(relative))
        with path.open('rb') as stream:
            actual = hashlib.file_digest(stream, 'sha256').hexdigest()
        if path.stat().st_size != row['bytes'] or actual != row['sha256']:
            raise ValueError('FILE_IDENTITY_MISMATCH: ' + str(relative))
    return len(seen)


def verify(manifest, repository_root, artifact_root=None):
    if manifest.get('schema_version') != 1 or not isinstance(manifest.get('repository_inputs'), list) or not isinstance(manifest.get('artifact_files'), list):
        raise ValueError('INVALID_MANIFEST')
    inputs = verify_files(repository_root, manifest['repository_inputs'])
    artifacts = verify_files(artifact_root, manifest['artifact_files']) if artifact_root is not None else None
    return {'status': 'all_manifested_files_verified' if artifacts is not None else 'repository_inputs_verified_external_artifacts_pending',
            'repository_inputs_verified': inputs, 'artifact_files_verified': artifacts,
            'artifact_files_pending': len(manifest['artifact_files']) if artifacts is None else 0,
            'boundary': 'File identities only; not compiler, proof, semantic or API compatibility acceptance.'}


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--manifest', type=pathlib.Path, required=True)
    parser.add_argument('--artifact-root', type=pathlib.Path)
    parser.add_argument('--repository-only', action='store_true')
    args = parser.parse_args()
    if args.repository_only and args.artifact_root is not None:
        parser.error('choose repository-only or an artifact root')
    result = verify(json.loads(args.manifest.read_text()), ROOT, args.artifact_root)
    print(json.dumps(result))
    return 0 if args.repository_only or args.artifact_root is not None else 2


if __name__ == '__main__':
    raise SystemExit(main())
