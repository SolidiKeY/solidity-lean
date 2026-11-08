# Optional Lean bridges

`Bridge/` is a separate Lake package; the core has no external dependencies.
Use the same `lean-toolchain` for both packages. Dependency pins and vendored
licenses are in `Bridge/lake-manifest.json` and `Bridge/vendor/`.

```sh
./scripts/check-bridge.sh
# Include the optional package in final verification:
./run-lean.sh --bridge
```

The declarations in [Bridge/SolidityBridge](../Bridge/SolidityBridge/) are the
authority for each correspondence and its premises. Independent-library tests
do not establish whole-source or executable-EVM agreement. Property sampling
never installs a theorem; see [rule-repair.md](rule-repair.md).

## Discrepancies

Keep the chosen halt policy from [correctness.md](correctness.md). In particular,
panic freedom is a separate obligation; the Loom adapter supplies neither
unconditional box/diamond duality nor a general `NoFailure` instance.
Pinned reference-machine agreement is conditional on the state, resource and
profile premises of the actual bridge theorem.
