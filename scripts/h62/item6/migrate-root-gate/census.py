#!/usr/bin/env python3
"""Deterministic complete frozen Lean-source inventory, kept off git (H44).

Hashes every original Lean source byte, including tests/vendor files. This is a
source census, not an elaborated declaration or proof-coverage claim. Root files
are identified separately to review exact migration scope and missing overlays.
"""
import argparse
from collections import Counter
import hashlib
import json
from pathlib import Path
import subprocess
import tarfile

BASE = 'c6f550e281a7e5affa9a99bc2cdaed556dec00e4'
OWNED = '''SolCases.lean SolidityLean.lean SolkeyCheck.lean SolkeyTestSuite.lean TrustAudit.lean
lakefile.toml lean-toolchain Solidity/AST.lean Solidity/ERC7201.lean Solidity/Eqns.lean
Solidity/FreshNames.lean Solidity/Hashes.lean Solidity/Keccak.lean Solidity/KeySort.lean
Solidity/RevertBytes.lean Solidity/Scope.lean Solidity/Secp256k1.lean Solidity/Semantics.lean
Solidity/Signature.lean Solidity/SpecSyntax.lean Solidity/Syntax.lean Solidity/Theorems.lean
Solidity/TypeGraph.lean Solidity/Update.lean Solidity/Yul.lean'''.split()


def main():
    p = argparse.ArgumentParser()
    p.add_argument('output', type=Path)
    a = p.parse_args()
    subprocess.run(['git', 'merge-base', '--is-ancestor', BASE, 'HEAD'], check=True)
    tree = subprocess.check_output(['git', 'rev-parse', BASE+'^{tree}'], text=True).strip()
    files = {}
    counts = Counter()
    proc = subprocess.Popen(['git', 'archive', BASE], stdout=subprocess.PIPE)
    try:
        with tarfile.open(fileobj=proc.stdout, mode='r|') as archive:
            for entry in archive:
                if entry.isfile() and (entry.name.endswith('.lean') or entry.name in OWNED):
                    data = archive.extractfile(entry).read()
                    files[entry.name] = dict(sha256=hashlib.sha256(data).hexdigest(), bytes=len(data),
                                            root_lane=entry.name in OWNED)
                    counts[str(Path(entry.name).parent)] += 1
        assert proc.wait() == 0
    finally:
        if proc.poll() is None:
            proc.kill()
            proc.wait()
        proc.stdout.close()
    assert set(OWNED) <= files.keys()
    result = dict(base=BASE, tree=tree, file_count=len(files), root_lane_count=len(OWNED),
                  files=dict(sorted(files.items())), directories=dict(sorted(counts.items())),
                  boundary='source bytes only; no elaborated declaration/proof census')
    with a.output.open('x') as stream:
        json.dump(result, stream, indent=2, sort_keys=True)
        stream.write('\n')
    print(f'{len(files)} frozen files; {len(OWNED)} assigned originals; {tree}')


if __name__ == '__main__':
    main()
