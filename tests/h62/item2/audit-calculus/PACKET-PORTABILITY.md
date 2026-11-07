# Relocating the historical static packet inputs

Guarded regression: moving byte-identical historical evidence must not force manifest rewrites or permit changed/missing artifacts to pass.

Run verify.py from any working directory. Its repository is derived from the script location. The historical evidence-manifest.json remains unchanged. Without arguments the checker reads recorded paths. To relocate artifacts, repeat the explicit option for each old root:

```sh
python3 tests/h28-sol/automation-benchmark/h82-static-handoff-v1/verify.py --path-map /old/checkout /new/checkout --path-map /old/toolchain /new/toolchain
```

Roots must be absolute and existing target directories. Matching uses path components and the most specific prefix; duplicate historical roots, parent traversal and symlink escapes are refused. A missing mapped file fails UNVERIFIABLE; it never falls back to a present original. All20 original size/SHA checks, live ContextControls/Context/toolchain comparisons against HEAD, historical reconciliation refusals and git apply --check remain required. Integrity checks also run under optimized Python. The proposal is never applied and Lean is never executed.

The receipt's audit-calculus-unmerged flag describes that historical snapshot, not the current integrated lane. A static PASS means only identical source/receipt bytes, clean live-source comparisons and a patch dry-run. It supplies no theorem replay, option-proof acceptance, axiom-delta disposition, runtime gate, performance or whole-goal completion.

Validation uses eight synthetic checksum/path controls plus a copy of all20 actual original entries: relocation passes, same-size tampering under optimized Python fails, missing mapped bytes fail while originals remain, and restoration passes. The manifest/state/patch bytes are unchanged. These external-tool controls are not formal proof fixtures.
