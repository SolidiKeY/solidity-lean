# E4 hash-mode bridge (H112)

Base: `a0a9ca15ba35fd6e8d9a9be10e4b6b45dbf45d3e`.
Owner: `solidity-plan-e4-hash-bridge-20261107/e4-hash-bridge`.
The symbolic ideal machine remains the true mode. No existing declaration,
premise, observation, generated registry or core representation is changed.

## Checkpoint 1: inventory and statements

Locations below are at the pinned base. The inventory distinguishes the
storage model from the byte hash: symbolic constructor injectivity does not
supply an injective finite-word encoding of all slots.

| Boundary | Declarations and base locations | Mode and bridge use |
|---|---|---|
| Symbolic slots | `Solidity/Evm/Machine.lean:99` `Slot` (`root`, `hash`, `data`); :106 `Slot.add`; :111 `Slot.toStr`; :167 `Word.slot`; :194 `Instr.keccakMap`, :195 `Instr.keccakArr` | Ideal constructors; printing is descriptive, not byte hashing. Keep unchanged. |
| Symbolic storage | `Solidity/Evm/Machine.lean:266` `WordStore`; :272 `WordStore.read`; :280 `ofFn`; :287 `write`; :290–311 read/write laws | Storage cells indexed by symbolic slots, with structural equality. No concrete hash premise is read. |
| Symbolic execution | `Solidity/Evm/Machine.lean:485` `Instr.step` (:555–560 keccak cases); :615 `exec`; :623 `run` | Keccak cases construct slots; no numerical keccak is computed. The bridge does not assert a new machine simulation. |
| Slot/layout correspondence | `Solidity/Storage/HashedLayoutEvm.lean:23` `ofSlot`; :28 `ofSlot_injective`; :45 `ofSlot_add`; :49 `KeysBelow`; :54 `keysBelow_ofSlot`; :60 `exists_ofSlot`; :70 `lmax_eq_Lmax`; :74 `slot_word_inj` | First seven describe symbolic correspondence; last requires bounded terms, word-valued hash and the per-run region premise. Cite this boundary, never infer global word injectivity. |
| Concrete slot interpretation | `Solidity/Storage/HashedLayout.lean:47` `Pre`; :53 `Loc`; :77 `Loc.word`; :83 `Loc.pres`; :96 `Loc.Bounded`; :117 `word_data_alias`; :126 `hashed_ne_root`; :134 `hashed_ne_hashed`; :143 `word_inj`; :220 `nodup_map_word`; :399 `located_word_inj` | Hash-parametric, bounded per-run separation; `word_data_alias` explains why bounds matter. Remaining `STy`/`Placed`/`locate` declarations in this module are layout arithmetic, not additional assumptions about the hash. |
| Byte encoding | `Solidity/Storage/HashedKeccak.lean:41` `bytesBE`; :62 `bytesBE_inj`; :72 `encode`; :77 `Pre.Words`; :81 `encode_inj`; :102 `keccakH`; :137 `keccak256_bytes`; :150 `keccakH_lt`; :162 `keccakH_eq_iff` | Encoding injectivity on word preimages is not hash injectivity. |
| Byte premise correspondence | `Solidity/Storage/HashedKeccak.lean:170` `collisionFree_keccakH_iff`; :184 `regionsDisjoint_keccakH_iff`; :205 `keccak_word_inj` | Cite these existing concrete-byte separation theorems; do not reprove or modify them. |
| Run premises | `Solidity/Hash/CollisionBound.lean:59` `CollisionFree`; :75–95 membership/prefix/append closure; :167 `Near`; :172 `Covers`; :216 `RegionsDisjoint`; :225–238 empty/prefix/collision closure | Bridge uses definitions and closure. Injectivity on a run is precisely collision freedom; region clearance is an additional requirement even for sane parameters. |
| Nonadaptive counts | `Solidity/Hash/CollisionBound.lean:272` `tuples`; :282 `collisions`; :516 `oracleOf`; :539 `dedup`; :589 `keccak_premise_fails_prob_le`; :604 dedup variant; :843 `keccak_region_premise_fails_prob_le`; :873 dedup variant | Existing fixed-input bounds; adaptive bridge must use Adaptive instead. |
| Adaptive model | `Solidity/Hash/CollisionBound.lean:928` `eagerQueries`; :939 `EagerAdaptiveBound`; `Solidity/Hash/Adaptive.lean:263` `eagerCollides`; :320 `eagerRegionsFail` | Every strategy-produced query lies in finite `dom`; repetitions retain the same answer. |
| Adaptive counts | `Solidity/Hash/Adaptive.lean:493` `two_mul_eagerCollides_le`; :542 `two_mul_eager_stopped_le`; :567 `keccak_eager_collision_prob_le`; :577 `two_mul_eagerRegionsFail_le`; :642 `keccak_eager_region_prob_le`; :653 `eagerAdaptiveBound` | Cite these counts for the combined union bound, stopped collision corollary and 256-bit reading. |
| Fixed concrete hash | `Solidity/Roadmap/Contracts.lean:472` `Fixed`; :479 `Fixed.hash`; :490 `Fixed.Sane`; :499 `HashPremise`; :505 `HashPremise.nil`; :509 `HashPremise.of_prefix`; :896 `Fixed.Keccak` | Byte hash wraps `F.evm.keccak` with its range proof. `Fixed.Keccak` is the real-keccak specialization, not an assumption imposed on a sampled random oracle. |
| Language guards | `Solidity/Roadmap/Contracts.lean:814–829` intrinsic hash fields/guard; :853–873 `EvmSpec`, `hashed`, `slotHashed`, `guard_iff` | General guarded transfer uses EVM `guard_iff`. No arbitrary symbolic theorem is automatically hash-parametric. |
| Compiler contract | `Solidity/Roadmap/Contracts.lean:937` `PublicCorrectness`; :958 `hashes_source`; :964 `refines`; :970 `decode_reach`; :976 `decode_commutes`; :1016 `PublicCorrectness.transfer` | Compiler result retains allowed/admissible environments, complete observations and the source forward/guard conditions. Target premise yields backward prefix refinement and decode reach. |
| Refinement meaning | `Solidity/Roadmap/Contracts.lean:179` `RefinesUnder`; :213 `completes`; :224 `sound`; :249 `safety` | Do not turn target guard alone into unguarded two-sided refinement. |
| Separate calculus premise | `Solidity/Calculus/HashPremise.lean:31–87` hash-input collectors/`Fml.HashFree`; :91 `holdsS`; :113 `holdsH`; :117 `ValidH`; :245–276 equivalences | Scope/formula guard, not definitionally Roadmap.HashPremise. No equivalence or calculus rework is claimed. |

Exact planned statements (before Lean edits):

1. For `F`, lists `xs, ys`, run injectivity
   `∀ a ∈ xs, ∀ b ∈ xs, F.hash a = F.hash b → a = b`
   and the two explicit region-clearance clauses imply `HashPremise F xs ys`.
   This is an iff once collision freedom is supplied. `F.Sane` alone, even
   together with collision freedom, does not imply region clearance.
   A root-free unit-length region is a useful special case under bounded
   outputs and run injectivity. Never assume global injectivity of keccak.
2. For every proposition `P`, `V.lang.Guard p e r → P` transfers to `P`
   under `HashPremise V.fixed (V.hashed p e r) (V.slotHashed p e r)` using
   `V.guard_iff`. Any two prefix sublists inherit the premise by
   `HashPremise.of_prefix`; the guard for another run follows only when its
   actual query lists are those prefixes. A colliding distinct pair in
   `xs` negates the premise. `HashPremise.nil` supplies the empty instance.
3. Set `Q g = eagerQueries s (oracleOf dom g) q`. Count oracles failing
   `CollisionFree (oracleOf dom g) (Q g) ∧
   RegionsDisjoint N L (oracleOf dom g) roots (Q g)`.
   For `∀ t, s t ∈ dom` and roots below `N`, prove
   `2*N*bad ≤ (q*(q-1) + q*(q-1)*(2*L-1) +
   2*q*roots.length*L) * N^dom.length` by a union of the existing counts.
   For `N=2^256`, the left factor is `2^(256+1)`.
   A contract specialization replaces `F.evm.keccak` by this oracle on
   tuples whose entries are below `N`, with an explicit range proof,
   and connects the run's actual preimage lists to this strategy (or its
   sublists). No bound covers unaccounted queries.
4. Given the existing `PublicCorrectness` for each hash-parameterized
   instance, every admissible target run meeting its premise has an
   admissible source prefix above the bytes' entire observed prefix.
   Forward completion retains source `Forward` and source `Guard`.
   Failure of that target-prefix refinement implies failure of its
   premise; with the strategy correspondence from item 3 its oracle count
   is bounded by item 3. The empty-list instance uses `HashPremise.nil`.

What q counts: all oracle queries of the adaptive strategy, including
attacker offline/grinding queries and system queries. A system-only count
cannot replace this total. The finite domain contains every preimage the
strategy can produce on every answer history, not only one sampled run.

## Scope question E4-Q1 (resolved: coordinator #168, option A)

Source tags: assignment checkpoint 3; `Solidity/Hash/CollisionBound.lean:172,216`;
`Solidity/Hash/Adaptive.lean:577–581`.
The requested universal q=1 zero-bad-oracles control for the combined
premise is false. For `N=2`, `L=1`, `roots=[0]`, one preimage, a single
query answered 0 covers root 0: `Covers 2 1 0 0`. Collision freedom holds
on the singleton but region disjointness fails. The region numerator at
q=1 is `2*roots.length*L`, which is positive here.

Options sent through coord-ask:

- A: q=0 combined zero, q=1 collision-only zero, and positive q=1 root-hit
  control; leave the full combined bound unchanged.
- B: q=1 combined zero only in an explicitly root-free control; leave the
  full combined bound unchanged.
- C: keep the literal universal combined-zero requirement; checkpoint 3
  remains blocked by this counterexample.

Coordinator answered A: replace the erroneous control with q=0 combined
zero, q=1 collision-only zero, and a positive q=1 root-hit control. The
combined bound and its premises are unchanged. The counterexample above is
the reason for this assignment correction.
Relay: `coord-q/codex/solidity-plan-e4-hash-bridge-20261107/e4-hash-bridge/20261107T162119Z`.

## Reviews

Checkpoint 1 finder (independent read-only thread, no Lean server):
confirmed the root-hit counterexample and required preservation of the
separate source forward/guard premises. Both findings are reflected above.
Checkpoint 2 independent finder and skeptic found no proof defects. Finder
requested a concrete collision witness beyond the generic obstruction;
`constantHash_collision` now supplies byte preimages `[]` and `[0]` under a
constant replacement hash. No semantic execution is manufactured from the
abstract EvmSpec. Both reviewers required recording actual axiom sets and
updating stale checkpoint status. Checkpoint 3–4 reviews remain pending.

## Registration fragment (coordinator only)

Intended imports (Bridge implemented, CollisionBridge pending; not registered):

```lean
import Solidity.Hash.Bridge
import Solidity.Hash.CollisionBridge
```

CORE entries and axiom-pin keys will be supplied after declarations are
checked. Module-map rows and generated roots remain coordinator-owned as
required by the exact sole-write-scope assignment. No register.sh mutation
is authorized for this worker.

## Gates and handoff status

Setup: clean original `work` branch at `f5038bc02bc52ea08f5a3cec7de292aef424e7c8`;
pinned base initially absent. Authorized fetch succeeded; origin/master
resolved exactly to the pinned base, ancestry check passed. Assigned branch
created at that exact base with writer lock; original branch preserved.
Repository: `/workspace/solidity-lean`.
Lean: 4.24.0, commit `797c613eb9b6d4ec95db23e3e00af9ac6657f24b`.
Lake: 5.0.0-src+797c613 (Lean 4.24.0).
VM: 17 GiB RAM, 16 GiB available at setup, no swap, 30 GiB disk free.
No runtime gate pass is claimed; KeySort and Lean build gates are pending.
The active tool catalog exposes stop_goal but no get_goal; no new goal was
created or reset.

Checkpoint 1 committed as `b782c5968`; doc paths exit 0 (143 ambiguous
references, all resolving). Checkpoint 2 Bridge implemented: MCP `diag`
reports 0 errors; `lake lean Solidity/Hash/Bridge.lean -- -j1
--tstack=131072` exits 0. Cold import build: CollisionBound 3.9 s, Adaptive
1.0 s, Roadmap.Evm 1.0 s, Contracts 2.0 s (6 jobs, success). Initial
`lake build -j1` was rejected because Lake 5 has no such option; corrected
to LEAN_NUM_THREADS=1 for dependency build and explicit Lean -j1 for files.
Module timing via Python monotonic/resource (no /usr/bin/time installed):
Bridge 0.513 s wall, 230516 KiB child max RSS. No existing module changed;
whole-library timing comparison remains pending. Actual pinned axioms:
unit-root-free theorem `[propext, Quot.sound]`; prefix transfer `[]`.
These are strictly below the requested standard triple, not artificially
inflated to introduce Classical.choice. Negative controls include explicit
constant-hash byte collision and generic root hit. Checkpoint gate evidence: `/tmp/e4-checkpoint2/gates.tsv`: layers PASS
(904 core, 0 elaborator reach, 0 parser reach, 0 new edges); touched build
PASS; trust PASS (6696 sources, 289 inventoried sites, 0 findings); fragments
PASS; doc paths PASS (143 resolving ambiguities). Orphans FAIL (6678
reachable, Bridge is the sole orphan); roots FAIL (missing Bridge import);
axiom pins FAIL (new unregistered pins), all expected coordinator-owned
registration deltas. Library gate was interrupted by this worker after
116 s while awaiting the E4-Q1 decision; it is NOT a pass. Coordinator then
answered A; the full library gate must be rerun. Registration fragment
completion, checkpoint 3–4, lane-end gates and handoff remain pending. No new axioms, sorry, trust shortcuts or frozen statements.

## Checkpoint 3: implemented probability bridge

`Solidity/Hash/CollisionBridge.lean` adds `eagerPremiseFails`,
`combined_count_le`, `two_mul_combined_le`, `pow_two_combined_le`,
`keccak_combined_le`, `stopped_collision_le`, `oracleFixed`,
`oracleFixed_hash_val`, `oracleFixed_premise_iff`, `premise_of_transcript`,
`runPremiseFails`, and `run_premise_le`.
The numerator is exactly
`q*(q-1) + (q*(q-1)*(2*L-1) + 2*q*R*L)`.
The denominator reading is `2^(256+1)` times the count versus the numerator
times `(2^256)^dom.length`.

`oracleFixed` changes only evm.keccak and its range proof; the total family
uses reduction modulo the word size on arbitrary tuples. On every sampled
tuple, `oracleFixed_hash_val` proves equality with oracleOf on ALL bytes,
including the default-zero points outside dom. Thus no sampled distribution
is changed. Both actual query lists must be contained in the full strategy
transcript for every sampled oracle. They may repeat or stop early. No
unproved EVM strategy-adequacy fact is inferred from EvmSpec.

Coordinator-approved controls: `zero_queries`, `one_query_collision`, and
`one_query_root_hit`. The last is kernel `decide` only on the tiny N=2,
one-point, one-query model: exactly one of two oracles fails. No native
computation shortcut is used.

MCP diagnostics: 0 errors. Single-threaded lake lean: exit 0, no warnings.
Measured headline axioms (`two_mul_combined_le`, `run_premise_le`,
`stopped_collision_le`): `[propext, Classical.choice, Quot.sound]`.
Each has a #guard_msgs pin. Independent checkpoint 3 finder and skeptic found no proof defect and no
weakened premise. They requested checked axiom pins (now present) and a
direct region-only positive control; `one_query_region_hit` now states
exactly one failing region oracle in the same tiny model. Full gates and
measured module timing remain pending.

## Checkpoint 4: compiler bridge and inhabited execution

`Solidity/Hash/CollisionBridgeCompiler.lean` adds `Compiler.refines`,
`prefix_refines`, `decode_reach`, `prefix_empty`, and `failure_le`.
The full refinement theorem keeps the source Forward restriction and both
hash guards; backward prefix refinement preserves the original complete
Prefix.Le observation. The probability event is failure of that full
backward prefix property on the chosen admissible run. It does not claim
that a fixed-hash correctness proof holds for replacement hashes, nor that
the existing compiler contracts have been implemented by this bridge.

The oracle-indexed source/intrinsic/EVM/compiler/export/environment/run
family has PublicCorrectness and the ordinary admission/compilation/allowed/
admissible conditions on sampled tuples, with V.fixed exactly oracleFixed.
The two actual query lists are included in all q strategy queries, including
offline attacker work. These are the explicit probabilistic model
instantiation relations; no extra semantic correctness premise is added.
The semantic failure classifier is classical/noncomputable; it is not an
external test or executable compiler-correctness decision procedure.

`Solidity/Hash/CollisionBridgeControls.lean` instantiates the existing
`toy_publicCorrectness` on the admitted compiled input `[3,1]`, a quiet
program that actually returns `[1]` with no hash queries. The three theorems
`quiet_compiler_prefix`, `quiet_success`, `quiet_premise` demonstrate an
inhabited admissible successful compiler run; its premise is HashPremise.nil.
No claim rests merely on an abstract inhabited premise.

Both independent checkpoint 4 finder and skeptic found no proof defect,
new semantic premise, or weakened observation. Both requested checked
compiler axiom pins instead of raw prints; these have been added. Actual
axioms: Compiler.refines `[]`, Compiler.failure_le the standard triple.
MCP diagnostics and Lean per-file checks for compiler and controls passed;
library/full gates and registration remain outstanding.

## Final registration fragment (supersedes the reserved fragment above)

Only the coordinator may apply these entries. No generated registry or
module-map file was modified by this worker.

Solidity root import lines, to be generated with register.sh:

```lean
import Solidity.Hash.Bridge
import Solidity.Hash.CollisionBridge
import Solidity.Hash.CollisionBridgeCompiler
import Solidity.Hash.CollisionBridgeControls
```

CORE entry:

```javascript
/^Solidity\.Hash\.(Bridge|CollisionBridge|CollisionBridgeCompiler|CollisionBridgeControls)$/,
```

Suggested language-area module-map fragment rows:

| Module (Solidity prefix omitted) | Contents |
|---|---|
| `Hash/Bridge.lean` | Run-local ideal special case, exact region clearance, guard/prefix transfer, concrete collision control. |
| `Hash/CollisionBridge.lean` | Combined adaptive oracle count, exact Fixed replacement, actual-query inclusion, corrected q=0/q=1 controls. |
| `Hash/CollisionBridgeCompiler.lean` | PublicCorrectness guarded refinement, decoded reachability and hash-indexed compiler failure bound. |
| `Hash/CollisionBridgeControls.lean` | Concrete admitted, compiled quiet success using HashPremise.nil. |

Axiom-pin entries (all new, no existing pin changes):

```json
{
  "Solidity/Hash/Bridge.lean:Solidity.Hash.Bridge.premise_unit_rootFree": [
    "Quot.sound",
    "propext"
  ],
  "Solidity/Hash/Bridge.lean:Solidity.Hash.Bridge.transfer_prefix": [],
  "Solidity/Hash/CollisionBridge.lean:Solidity.Hash.CollisionBridge.two_mul_combined_le": [
    "Classical.choice",
    "Quot.sound",
    "propext"
  ],
  "Solidity/Hash/CollisionBridge.lean:Solidity.Hash.CollisionBridge.run_premise_le": [
    "Classical.choice",
    "Quot.sound",
    "propext"
  ],
  "Solidity/Hash/CollisionBridge.lean:Solidity.Hash.CollisionBridge.stopped_collision_le": [
    "Classical.choice",
    "Quot.sound",
    "propext"
  ],
  "Solidity/Hash/CollisionBridgeCompiler.lean:Solidity.Hash.CollisionBridge.Compiler.refines": [],
  "Solidity/Hash/CollisionBridgeCompiler.lean:Solidity.Hash.CollisionBridge.Compiler.failure_le": [
    "Classical.choice",
    "Quot.sound",
    "propext"
  ]
}
```

## Final validation and handoff (goal NOT complete)

Saved proof head before final documentation: `7a092e0f0f4d6e1ba02ce18b9d6560707c468e0e`.
The final full committed head is in the sealed manifest, avoiding a
self-referential documentation commit hash.

All new Lean modules pass per-file MCP diagnostics (0 errors), per-file
Lean -j1 checks, and their own #guard_msgs pins. Final serial timings:
Bridge 0.515 s; CollisionBridge 0.965 s; compiler 0.765 s; controls 0.407 s.
KeySort passes: `lake lean Solidity/KeySort.lean -- -j1 --tstack=131072`,
exit 0, 1.327 s. Lean 4.24.0 and Lake 5.0.0-src+797c613 were used.
No RUNTIME_GATE_PASS is claimed. No existing Lean source or import graph
was modified, so these times measure added leaf costs, not a demonstrated
whole-library slowdown percentage. Full build timing delta is unmeasured;
the >10% requirement is not asserted satisfied.

Evidence: `/tmp/e4-evidence/per-file.json` and per-module logs;
`/tmp/e4-evidence/full/gates.tsv`; earlier checkpoint evidence at
`/tmp/e4-checkpoint2/gates.tsv`.

| Command/check | Outcome and decisive output |
|---|---|
| node scripts/check-layers.mjs | PASS: 904 core, zero elaborator/parser reach, zero new core edges. Same registered base count. |
| In-memory prospective CORE registration check | PASS: 908 core, zero elaborator/parser reach, zero new edges. Read-only registry preserved. |
| bash scripts/check-trust.sh | PASS: 6699 sources, 289 inventoried sites, zero findings. Base: 6695 sources, same 289 sites, zero findings. |
| node scripts/check-orphans.mjs | FAIL: exactly the four new modules are unregistered orphans; 6678 reachable. Base graph with the four additive files removed: 6678 reachable, zero orphans. |
| bash scripts/check-doc-paths.sh | PASS: 143 ambiguities, all references resolving; same count as initial inventory check. |
| register.sh --check | FAIL: exactly four missing root imports listed in the fragment above. |
| fragments.sh --check | PASS; no coordinator-owned fragment changed. |
| node scripts/check-axiom-pins.mjs | FAIL: zero policy errors, seven new unregistered changes. 17181 pins versus base 17174; no removed or enlarged pin. |
| gate.sh full / bash run-lean.sh | FAIL: runner stops at read-only generated-root registration, before its library build. |
| gate.sh checkpoint / lake build Solidity | INCOMPLETE: worker interrupted cold library build after 116 s while E4-Q1 awaited a decision; not a pass. |
| check-testsuite.sh (initial activation) | Setup-path failure: external copied snapshot lacked adjacent pin. |
| check-testsuite.sh with repository-pinned SOLKEY_EXAMPLES | PASS: 54 modules trust clean; 564 functions = 552 derived + 11 refuted + 0 pending + 0 divergent + 1 excluded; 2 skip. Snapshot-path recovery changes no source. |
| check-corpus.sh | INCOMPLETE: worker interrupted its cold Basic build after the full runner hit the read-only registration blocker; no corpus pass claimed. |
| node scripts/check-automatic.mjs --strict | PASS. |

The compiler probability event is a logical count over all sampled
functions, not an empirical cryptographic-security experiment. The only
kernel finite enumeration added is on tiny N=2 controls. No external test
is used as a substitute for any proof. The toy compiler witnesses the
corollary; no new concrete production compiler correctness proof is claimed.

Finder/skeptic checkpoints 2, 3, 4 are recorded above. All proof findings
were resolved; no premise/observation was weakened. Checkpoint 1 finder
also confirmed the corrected statement boundaries. Frozen statements
touched: none. New axioms/sorry/native_decide/implemented_by/maxHeartbeats:
zero. Sole changed repository paths are these four additive Hash modules
and this document. No push/merge/PR; the only remote write was the expressly
required E4-Q1 coord-ask question relay, resolved by coordinator #168.

Typed remaining blockers:

- REGISTRATION_OWNER: generated roots, CORE, axiom pins and module maps are
  outside this worker's exact write scope. The coordinator must apply the
  fragment and regenerate its registries before the full runner can pass.
- REQUIRED_GATES_PENDING: clean checkpoint library build, corpus audit/build,
  full runner and whole-build timing comparison remain unpassed. The goal
  must stay incomplete; a local leaf proof pass is not completion.

No scope question remains open. E4-Q1 is resolved as option A, and the
combined bound/premises were kept unchanged. Handoff patch, bundle,
evidence archive and SHA256SUMS will be sealed under `/tmp/e4-handoff`.
The manifest records exact base, branch, final head and artifact hashes.

## H82 continuation: local statement-preserving registration

The coordinator's H82 continuation explicitly authorizes statement-preserving
edits to any file without owner agreement. Under that newer authorization,
this worker applied the already reviewed registration fragment locally:
register.sh generated four root imports; the language-area fragment adds four
module rows; CORE registers these four modules; the generated axiom inventory
and three new per-file pin fragments record the seven measured pins.
No existing theorem statement, premise, observation or proof budget changed.
The pin writer also reordered seven unrelated P9 fragment objects; their JSON
values were verified equal and those incidental formatting changes removed.

The earlier REGISTRATION_OWNER wait is therefore cleared by H82. Library,
corpus, full-runner and timing validation are being resumed rather than
stopping at registration or discarding any saved proof work. The immutable
previous handoff remains at /tmp/e4-handoff; continuation evidence and a new
sealed handoff will use distinct directories.
