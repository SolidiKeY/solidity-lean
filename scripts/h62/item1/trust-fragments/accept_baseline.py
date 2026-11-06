#!/usr/bin/env python3
"""Compare every byte against the published, hash-pinned audit at the task base.

This checks baseline reproduction, not coverage of future project declarations.
"""
import hashlib
import subprocess
import sys

import collect

BASE = 'c6f550e281a7e5affa9a99bc2cdaed556dec00e4'
SHA256 = 'ece2e6cebbee95d82fec246892993662e81dcfd895831981583d2b0867a37482'


def accept(original, reconstructed, checked_in):
    if hashlib.sha256(original).hexdigest() != SHA256:
        raise ValueError('base audit does not match pinned digest')
    if reconstructed != original:
        raise ValueError('fragments do not reproduce pinned audit')
    if checked_in != original:
        raise ValueError('checkout audit differs from pinned audit')


def main():
    try:
        original = subprocess.check_output(['git', 'show', f'{BASE}:TrustAudit.lean'], cwd=collect.ROOT)
        rebuilt = collect.collect(collect.FRAGMENTS)
        accept(original, rebuilt, collect.AUDIT.read_bytes())
    except (OSError, ValueError, subprocess.CalledProcessError) as exc:
        print(f'baseline acceptance failed: {exc}', file=sys.stderr)
        return 1
    print(f'baseline acceptance passed: {len(original)} bytes sha256={SHA256}')
    return 0


if __name__ == '__main__':
    raise SystemExit(main())
