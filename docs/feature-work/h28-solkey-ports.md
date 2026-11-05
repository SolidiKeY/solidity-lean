# H28 SolKey freshness ports

Scope: only `memoryRules.key:newFromWrite` and
`structMemoryRules.key:newFromCopySt` at
`473da8944ca7329e6b76819863591407db26e7ec`, over the exact published Lean base
`6f3eedf0788ee1f8a3bcf230558c712ecdca04d5`.

The pinned copy taclet has a syntactic equality. The Lean contribution is an
additive typed reading over actual allocating `SVal.copyStToM`: freshness
transports backwards across copying, while newly allocated identities refute
the forward converse. It is not complete program-taclet parity. Successful
writes preserve the entire typing and therefore freshness in both directions.
There is no `new` term added to the existing model.

| Selected clause | Full source SHA256 | Exact body SHA256 |
|---|---|---|
| newFromWrite | 35536aea3e2fa70519147614d9b50bdf13a0e3a005be4b1a03ec88ba7847260e | 8fd78f93f974861fc5f1e337d3a3611e9b160c9ab767c4bca97565d88fca5336 |
| newFromCopySt | b771b1573578ad9eb9d5317d7127db905767cb39f714e55bda2543fe476fc048 | 7861ce0ccb1f74e707b24ffa3c6ecf20fd23200d7cfb482e6365ee6b067cac77 |

Exact bodies, source line numbers, snapshot identity, and read-only rule-map
rows 648–650 are in `tests/h28-sol/solkey-ports/pin.json` and the two `.key`
fixtures. Row 648 is context for the threshold, not an additional port.
No other rule, snapshot, sort diagnosis, or pending-taclet inventory is in scope.

## Reuse and independent consequences

Published `Tm.onSpineAny_grows`, `Tm.onSpine_grows`, `LTm.onSpine_grows`,
`LTm.stripW_sameH`, and `LTm.stripW_eval` already cover expression spines,
including arbitrary writes. Existing semantics is present and unchanged.
`SVal.mirrors_copyStToM` already handles all nested map-free values; the local
`copy_mirror` declaration explicitly reuses it.

The new module exposes the exact threshold certificate
`H.length ≤ id ↔ ∀ R (r : HRef H R), r.id ≠ id`. The reverse proof constructs
an in-range typed reference, rather than assuming separation. `Writes` uses
actual successful `Grown.writeT` steps at arbitrary `MAddrT` slot types;
induction closes finite composition, deriving exact typing preservation,
freshness equivalence and old/fresh separation. `Operations` composes actual
`Heap.writeAddr` and `SVal.copyStToM` steps. Its prefix is proved from its
constructors, without assuming growth or separation.

`copy_then_witness` supplies unchanged root identity, freshness relative to the
original heap, final allocation, and separation from every preexisting typed
reference after an arbitrary mixed suffix. `copies_ordered` orders two copy
roots across any intervening actual sequence. The universal copy laws include
primitive, struct, dynamic-array and fixed-array values recursively; map-free
is exactly the existing producer premise. There is no global identity
injectivity premise, untyped shape layer, or alternate memory implementation.
The mirror certifies copy-time contents; writes may change those contents.

## Selected acceptance and registration

The exact 46 inhabited and negative controls are enumerated in
`tests/h28-sol/solkey-ports/coverage.json`, including both address constructors,
primitive/reference writes, dynamic/fixed arrays, every primitive sort,
empty/nonempty/multiple sequences, nested structs/arrays, multiple allocations,
nonempty reference shadows, negative sequence relations, map refusal, and the
invalid copy converse. Computed nested root/child identities and an actual
write/copy suffix supplement universal proofs. Unknown non-map-free structs
are refused; empty field lists are checked directly without inventing an
admissible unknown struct.

`declarations.json` preserves exact declaration source bytes and hashes.
`trust-ledger.json` records all 61 compiler-printed theorem statements, separate
statement hashes, declaration hashes, actual axiom sets, and compiler-log hashes.
`Ledger.lean` and the control file ask the compiler for actual signatures and
transitive axiom sets. Checked results use only `propext` and `Quot.sound`
(or no axioms); runtime evaluation is an external runtime gate, not a proof.
The KeySort runtime output is `KeySort runtime: PASS (existing lattice,
identity/memory boundary)` on Lean 4.24.0 / Lake 5.0.0-src+797c613.

| Module | Local integration registration |
|---|---|
| `Solidity.Calculus.SolkeyAgreementH28.Freshness` | `tests/h28-sol/solkey-ports/registration.json` |

The assigned freeze forbids generated-root and central module-map edits.
The local manifest is the integration handoff. Orphan checking uses the
repository's supported `--allow` option for exactly this registered module;
a local root audit checks that it is the only pending generated-root import.
Full build targets include the module explicitly, alongside all frozen default
and TestSuite targets. This applies the assignment's local-registration policy
without modifying shared registries.

## Checks and review status

All final acceptance Lean runs use explicit `-j1`, `LEAN_NUM_THREADS=1`, a writer lock, and the
owned container `h28-solkey-check` with measured `memory.max=12884901888` and
`memory.swap.max=0`. The parent VM limit is 16 GiB, retaining 4 GiB headroom;
the VM has no swap. The initial MCP setup attempt was stopped for lacking explicit `-j1`; it is
not a passing gate. Direct use of cached imports proved inconsistent, so
selected dependencies were rebuilt cleanly in the lane-local runtime build
directory. Missing artifacts were then seeded from the preserved original
cache for the final broad build; normal Lake input-trace checks validate reuse,
without `--old` or any bypass. Freshly rebuilt artifacts were preserved. The
pinned official toolchain is outside source. No heartbeat budget was raised.

Finder and skeptic findings, fixes, final selected verdicts, and resource audits
are recorded in `tests/h28-sol/solkey-ports/reviews.md`. All selected kernel,
trust, layer, orphan, documentation, axiom-pin, TestSuite, strict automation,
full build, corpus and pinned sort-conformance checks passed. Full build checked
3673 jobs in 19128.660 seconds, with 9089776 KiB maximum child RSS. Cgroup peak
was 12884901888 bytes; memory pressure caused 1448 cap/reclaim events, with no
OOM or OOM kill and zero swap. No interrupted or failed setup attempt is counted
as a passing gate.

`RUNTIME_GATE_PASS`: actual Lean 4.24.0 and Lake 5.0.0-src+797c613 versions and
passing KeySort runtime output are recorded in `evidence/versions.log` and
`evidence/keysort-runtime-final.log`. Pinned conformance parsed 377 taclets,
131 read-bearing, with table coverage 131; annotations match. This required
existing conformance check adds no new sort-diagnostic inventory.

Queue accounting: both exact pins, exact intrinsic threshold, bidirectional
write transport, arbitrary write composition, arbitrary map-free copy transport,
arbitrary mixed suffix/root ordering, constructive nested witnesses, negative
controls and complete local trust ledger are implemented and checked. No proof
or selected clause is left open. Final exact-head receipts and sealed handoff
are generated under the ignored lane-local `artifacts/` directory; immutable
manifest records the final base/head/branch and all hashes.

## Published interface and coordinator reconciliation

Consumers can reuse the complete interface at
`Solidity/Calculus/SolkeyAgreementH28/Freshness.lean@96780494a943f45035d3d8164321bff6c30d3be7`.
The actual compiler signature ledger is committed at the same checkpoint; there
are no stubs. Statements/types were preserved after the independent reviews.
H30 file ownership agrees with this lane's original exclusive scope. Generated
roots, Scoped syntax, module maps and central trust inventory remain untouched.

The coordinator's published master was fetched and verified at
`b419c3cf4f642ae519b66bebc26cdf2f7cf93574`; it contains the frozen task base.
The task branch/base were not moved or merged. No newly published producer API
is needed for this exact pair, and no producer implementation was duplicated.

## Published-master adoption, 2026-11-05

Published `8495f1deb0a95dd6b9301822d8649ab76b217681` was adopted into the same
owned branch by merge `19a9a54195f34c24a72ef0d2413f2efdc3f7d284`, preserving the
sealed `a316c453` checkpoint and its history. All four owned Lean files and all
five frozen inputs remain byte-identical. The published master already contains
the exact freshness module and central registration, so the acceptance script
now requires the published registration to be complete; it retains the original
exact-one-pending-import check for the historical frozen checkpoint. Lane scope
is checked relative to this explicitly approved upstream integration after
adoption, while original rule/source pins and all proof/trust checks remain
unchanged. No theorem, type, premise, exclusion or budget was altered.

H35 validation and cache observations for the adopted head are kept in a
separate supplemental artifact directory. Existing seals are not rewritten.
Observed cache mappings and file hashes establish only the specifically checked
owned outputs; neither the coordinator notice nor directory presence is a
claim of whole-cache freshness or successful worker shipment.

The follow-on published `f77cf60d3cea8f7f1db8db29cc027532b0cd3fce`, which
contains the previous packet, was subsequently adopted on the same branch.
Acceptance selects only an explicitly approved publication that is an ancestor
of the current head; it does not follow an arbitrary moving remote ref. All
owned Lean statements and frozen inputs remain unchanged. Its existing-producer
helpers and retained holds are not treated as whole-lane completion. Separate
VM gate and cache-route receipts are recorded for this follow-on checkpoint.

Published `9584f9e7df09f638d9e0cb8930501d1660aa4b2f` was then adopted on the
same branch, preserving all earlier work. The fixed approved-publication list
was extended without changing proof, trust or historical registration checks.
All four owned Lean files and five frozen inputs remain unchanged. Under H41,
workers must not run `ship-cache.sh`: this lane leaves byte-verified native
cache packs with absolute paths and SHA-256 for coordinator pull. The previous
worker-shipment blocker is historical; no actual coordinator pull or global
cache freshness is asserted without its separate receipt.

Published `e6849d3bdf516099d20c33d3581d523449764018` was adopted by rebase
as explicitly requested. The original completed snapshot is preserved at
`codex/solidity-h28-sol-20261104/solkey-ports-pre-e6849d3b`
(`dd07c7efb30c3cfdfa24b7cb2e40a254b485703a`) and in the existing sealed bundles.
The publication pruned private evidence; this branch retains those fixtures,
receipts and ignore files. All owned Lean files remain byte-identical.
Acceptance adds only this fixed approved ancestor; H41 remains in force.

The rebase metadata passed independent read-only finder and skeptic reviews.
The owned build, actual axiom ledger, controls, selected acceptance and KeySort
runtime pass on the VM; exact final-head commands, exits, timings/RSS, resource
bounds, sealed handoff and H41 pull pack are in
`tests/h28-sol/solkey-ports/artifacts/rebase-e6849d3b/`. Coordinator import
remains separate; no new whole-tree/Bridge gate is asserted.

Published `70845978ab616a63b13d0dee8b31b28893ccf591` contains the prior
reviewed head and was adopted by rebase without owned content changes. The
fixed approved-publication list adds that exact ancestor. Initial selected
acceptance rejected upstream files against the older scope base; that failed
receipt is retained separately. No proof/trust/scope condition was weakened.
Final VM receipts and H41 handoff are in `artifacts/rebase-70845978/`.
