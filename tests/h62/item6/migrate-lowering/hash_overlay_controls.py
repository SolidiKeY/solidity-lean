#!/usr/bin/env python3
"""Reject corrupt context/counts rather than accepting a misleading overlay candidate."""
import sys
from pathlib import Path
sys.path.insert(0,str(Path(__file__).resolve().parents[4]/"scripts/h62/item6/migrate-lowering"))
from inspect_hash_overlay import patched_bytes,blob
old=b"first\nold\nlast\n";patch=b"@@ -1,3 +1,3 @@\n first\n-old\n+new\n last\n"
new,n=patched_bytes(old,patch);assert new==b"first\nnew\nlast\n" and n==1
for bad in (patch.replace(b" old",b" nope").replace(b"-old",b"-nope"),patch.replace(b"-1,3",b"-1,4"),b"not a patch\n"):
    try:patched_bytes(old,bad)
    except ValueError:pass
    else:raise AssertionError("corrupt/empty patch accepted")
assert blob(b"")=="e69de29bb2d1d6434b8b29ae775ad8c2e48c5391"
print("PASS: exact patch replay, corrupt context/count rejection, empty patch rejection and Git blob identity")
