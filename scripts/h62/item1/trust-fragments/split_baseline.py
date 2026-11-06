#!/usr/bin/env python3
"""Bootstrap ordered byte slices from a specified original TrustAudit file.

Each split starts at a top-level documentation comment immediately followed by
run_cmd. The first slice also preserves imports, the first audit and print pins.
The resulting fragments concatenate exactly; no Lean syntax is rewritten.
"""
import argparse
import pathlib
import re


def main():
    p = argparse.ArgumentParser()
    p.add_argument('source', type=pathlib.Path)
    p.add_argument('destination', type=pathlib.Path)
    args = p.parse_args()
    source = args.source.read_bytes()
    boundary = re.compile(rb'(?m)^(?:/\-! (?:(?!-/)[\s\S])*?-/\n|(?:-- [^\n]*\n)+)run_cmd do\n')
    starts = [m.start() for m in boundary.finditer(source) if m.start() > source.index(b'run_cmd do\n')]
    # Commands without a preceding comment still get their own fragment.
    for match in re.finditer(rb'(?m)^run_cmd do\n', source):
        if match.start() > source.index(b'run_cmd do\n') and not any(0 < match.start() - x < 512 and b'run_cmd do\n' not in source[x:match.start()] for x in starts):
            starts.append(match.start())
    starts.sort()
    parts = [source[a:b] for a, b in zip([0] + starts, starts + [len(source)])]
    args.destination.mkdir(parents=True, exist_ok=False)
    for index, part in enumerate(parts):
        (args.destination / f'{index:03d}-audit.leanfrag').write_bytes(part)
    print(f'{len(parts)} fragments, {len(source)} bytes')


if __name__ == '__main__':
    main()
