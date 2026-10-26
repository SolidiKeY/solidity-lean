# Recursive types: guarded storage foundation

`recursiveTypes` remains **missing in the ordinary source/interpreter/calculus
pipeline**. This milestone supplies a checked, standalone type graph and
storage API. It does not make `solc_import`, `Stmt`, `State`, `Spec`, terms,
the heap or existing taclets accept recursive structs.

## Representation and laws

`Solidity.TypeGraph.Schema n` identifies nodes by `Fin n` and compilation
origin/declaration IDs. Ordered fields have typed positions. Its rank follows
struct and fixed-array edges and stops at mapping/dynamic-array boundaries.
`Schema.no_inline_cycle` rules out every nonempty inline cycle; direct and
fixed recursion cannot receive this certificate. Mapping-freedom must follow
all graph edges instead; this layout rank is not a mapping-freedom decision.

`Value G T` and `Slot G T` are strictly positive, well-founded inductives.
Fields are dependent functions, array slots functions on bounded positions,
and mapping slots functions on the existing bounded primitive key sorts.
There is no erased value/state or untyped fallback. Missing slots generate
the type's default only when read; fields are lazy too. A stored value cannot
contain a pointer cycle, while finite paths may follow a recursive mapping
edge arbitrarily many times. `defaultBelow` uses a proved layout bound;
`clear` recurses on existing value children, never on `sizeOf`.

Arrays distinguish live `Fin (2^256)` length from retained `Fin (2^256+1)`
extent. Logical reads and saves fail beyond extent. Live reads also check the
live length. Fixed indices are word-sized and checked against fixed size.
Deletion clears the former live prefix, preserves old shadows and extent,
and stops at the first mapping, preserving that whole subtree. Empty push
retains reference elements but resets the newly live primitive slot, matching
the existing `pushSlot`; pop clears its former last live slot.

Generic kernel proofs cover typed field/slot writes, read-after-save,
read/append composition, no inline cycle, deletion idempotence, deletion of
defaults, mapping preservation, old-tail preservation, push length/extent
and retained-slot preservation under its explicit primitive/index condition,
and pop length/extent. The headline axiom output uses only standard
`propext`/`Quot.sound`; the inline-cycle theorem has no axioms. No new axiom,
`sorry`, native proof, `unsafe`, `implemented_by`, external dependency or
heartbeat override was added.

`Value.ObsEq` observes failed reads, primitive values, live lengths and
retained extents. It is only a defined relation: congruence of save, deletion
and push/pop is not yet proved. Raw equality distinguishes an absent child
from an explicitly stored default. There is no structural mapping get-put
claim, path-level divergent-path frame law or save-composition theorem.

## Validation and review

Per-file MCP diagnostics pass for every new Lean module. Kernel examples
cover every depth of a self-mapping default path (including depth 64),
recursive saves, independent leaves, populated recursive tree deletion,
mutual-array reads/writes, mapping-bearing fixed elements, allocated-zero
versus absent reads, live versus retained bounds, dirty reference reuse,
primitive reset on push, old primitive shadows and nested shadow lengths.

Final `./run-lean.sh` passed: 595 library jobs, 243 TestSuite jobs and the
frozen SolKey sort gate (377 taclets, 131 read-bearing annotations, zero
mismatches). Frozen corpus parity passed with 774 obligations. The TestSuite
audit reports 552 derived, 11 refuted and zero pending; the automatic gate
reports 491 automatic and 61 with a step budget. Feature generation is
current. Layering passes with 133 core modules and no elaborator reach.
`git diff --check` passes. The existing 33 Scratch orphans and 13 missing
vendor/external documentation references remain. The global trust inventory
reports 25 existing findings; excluding all eight new graph Lean files gives
the identical findings, and no trust inventory was refreshed.

The independent reference script is:

```
node scripts/check-recursive-types.mjs SOLJSON_FILE NODE_MODULES_DIRECTORY
```

It verifies the exact 0.8.38+commit.1835d247 compiler SHA-256, compiles the
fixture under both legacy and via-IR pipelines, and checks 12 EVM vectors.
Five negative cases reject direct, fixed and mutual-inline recursion,
recursive external ABI arguments, and mapping-bearing memory parameters.
These reference observations and the Lean regressions are separate checks;
there is no compiler/Lean correspondence theorem. In particular, the legal
memory-alias cycle is a reference-only test and is outside this storage API.

The read-only finder found that the initial push reused arbitrary primitive
shadows, unlike the existing model. The implementation now resets that slot;
the frame theorem has an explicit preservation condition, and a kernel
regression distinguishes primitive reset from retained reference reuse.
The skeptic confirmed the primitive correction, bounds and deletion behavior and identified
the unproved observational/whole-pipeline interfaces above. Both reviewers
ran no Lean and made no edits. Their requested populated-tree and mutual
path fixtures were added and checked. The skeptic also corrected an obsolete
sparse-map compatibility claim: functional slots can encode arbitrary legacy
mapping defaults, though that bridge has not been proved.

## Cost and integration boundary

The warning and history review preceded representation edits. Commits
`323951dd`, `3929cbc2` and `01dd890d` explain the encoded-name/table choice;
`d0c13aba` and `2f41a68a` retain recursor/match optimizations motivated by
indexed-match checking cost. This milestone leaves that existing
representation and those optimizations intact. Carrying a graph through
the ordinary signatures will require a broad rebuild and may increase
elaboration cost; this isolated implementation is not evidence otherwise.

Functional slots do not give efficient support enumeration, whole-value
printing or executable equality. Updates/deletes retain closures and lookup
can grow with operation history. Measurements time the complete example module
(0.88 s) and an unchanged existing struct example (11.49 s before, 10.51 s
after). These single observations include ordinary run-to-run variation and
are not a speedup, history-scaling or whole-interpreter performance claim.

Remaining work includes extracting shared type foundations to avoid an
AST/graph import cycle, admitting compiler declaration graphs, migrating the
existing storage/heap/state/signature/terms and all relevant folds, proving
the observational laws and copy laws, and connecting typing, source notation,
printers, rules and soundness. A default allocator can recurse on guarded
layout rank, while copies of present storage children use value induction.
Copying synthesized defaults requires that separate argument. Recursive
memory-to-storage copying must additionally handle legal heap cycles through
an explicit exhaustion/divergence policy; the old decreasing `tyRank` proof
does not justify it. There is no acyclic compatibility bridge yet;
compatibility with arbitrary legacy mapping defaults remains unproved.

Validation logs and timing JSON live under
`/tmp/solidity-lean-feature-groups-20261025/recursive-*`; final results are in
`recursive-types.status.json`. Source changes are intentionally uncommitted
under the shared-checkout protocol.
