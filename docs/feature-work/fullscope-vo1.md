# Optimizer obligation

[Authoritative source](../../Solidity/Optimizer).

The full-scope decision requires observational correctness, including failures and divergent/resource-limited behavior, for the actual optimization pipeline. Local constant-folding or pass-composition theorems do not provide that producer. Retain the H38 owner-review hold and D6 contract; target-only fixtures or a smaller partial relation cannot replace the required source/target semantics.

## Immediate unused-group pruning: handoff boundary

`Optimizer/UnusedFunctions.lean` adds a total intrinsically typed Yul pass over the existing syntax. It removes only an immediate function group whose continuation is `skip`, retaining every unsupported AST exactly. `prune_run` preserves the full Tier-A OpenRun state/flow outcome at horizons ≥2; `prune_completion` preserves each exact eventual completion with independently chosen horizons. The original policy is transported, not introduced as a new source admission condition. These runner theorems do not close D6, source/target correctness, physical effects, gas or general unused-function reachability.

The controls contain a nonempty body returning seven, nonzero caller locals/raw cells, a live invocation that retains its group, and a horizon-one difference. All new source theorems and controls have kernel axiom inventories. Finder and skeptic independently reviewed source/controls without Lean/server: PASS. Their helper findings (escaping destinations, unenforced config hashes and absolute-path ambiguity) were fixed: fresh resolved owned destination, semantic TOML equality preserving existing arguments, relative-path guard and enforced before/after hash equality.

Handoff commands and raw bounded receipts are sealed through the H44 archive manifest below. Reproduce source/controls with `bash scripts/coord-tools/gate.sh touched`. Touched compilation and per-file kernel gates pass; exact outcomes/versions/wall/RSS are in the sealed receipt. Full gate remains incomplete: generated root/orphan registration belongs to COORD, and corpus compilation hit the unchanged group cap. The missing setup SolKey pin was restored verbatim from the published repository pin only after its snapshot hash matched; all274 entries verified, TestSuite then passed. No RUNTIME_GATE_PASS or cache freshness/delivery receipt is inferred.

Registration record (done): `tests/fullscope-20261104/vo1/unused-functions-registration.md`. Cache packs remain on this VM, coordinator-pending under H41. Full O01 public/compiler/D6 composition and physical size/gas benchmarks remain open; O02/O03 integrated passes are partial delivery, with general unused-function pruning and full coverage still open. Revalidate after producer and registry integration. The active goal remains incomplete.

### H44 archive manifest

Bulk remains on this VM. The explicit H44 exception retains only archive identities in this owned feature document; no evidence dump is committed. These seals precede the final documentation-only manifest placement; Lean source identities are unchanged.

```text
# H44: bulk stays on this VM. Cache delivery coordinator-pending (H41).
# bytes=8344068
b4f1e72f8485cd79b9a5c281719c8871d7e7b255b98ff2f9b2ca5a24836f4d9d  /workspace/solidity-lean/tests/fullscope-20261104/vo1/delivery/idle-prune-20261108/evidence.tar.zst
# bytes=95469112
7db383fdb1098e393fd9079b2981d3654fd7ef9d677eb3e26b7ce285a156bd4b  /workspace/solidity-lean/tests/fullscope-20261104/vo1/delivery/cache-idle-prune-20261108/cache-packet.tar.zst
# bytes=408975
80229685d729161dc0cad699babb96897d4e2cbee3ca5658a15b7a235e33c790  /workspace/solidity-lean/tests/fullscope-20261104/vo1/delivery/idle-prune-20261108/original.patch
# bytes=16162
10540198909a2f56b45ccbbbe25cbe7749e39f6d46f66f489f2255787d91b92e  /workspace/solidity-lean/tests/fullscope-20261104/vo1/delivery/idle-prune-20261108/source.patch
# bytes=25694
4aab5de5b4ebf724dcfc027834826104921c5faeb64c48fe5abf4c4282e1fee3  /workspace/solidity-lean/tests/fullscope-20261104/vo1/delivery/idle-prune-20261108/evidence-files.json
# bytes=133667
9dbeaa313e63be36753d68cd2a93d237b24e936feb3b3ff3347e80a8b63b0dca  /workspace/solidity-lean/tests/fullscope-20261104/vo1/delivery/cache-idle-prune-20261108/cache-manifest.json
```
