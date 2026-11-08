# E4 hash-mode bridge (H112)

Base: `a0a9ca15ba35fd6e8d9a9be10e4b6b45dbf45d3e`.
Owner: `solidity-plan-e4-hash-bridge-20261107/e4-hash-bridge`.
The symbolic ideal machine is unchanged. The bridge is additive: no existing
declaration, premise, observation or core representation changes. H82
authorizes the statement-preserving registration described below.

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

The independent read-only checkpoint 1 finder confirmed that collision
freedom does not remove the root-hit obstruction and that source
Forward/Guard restrictions must remain. Checkpoint 2 finder and skeptic
found no proof defect; the requested concrete distinct-byte collision
witness is `constantHash_collision`. Checkpoint 3 finder and skeptic found
no weakened premise; requested checked axiom pins and a direct region-only
positive control are present. Checkpoint 4 finder and skeptic confirmed the
full original observation, the hash-indexed correctness family, and the
inhabited quiet compiler execution. Requested compiler pins are checked.
Independent finder and skeptic also reviewed the dedup/repeat and separate
collision/region backfill: no findings, no existing definition or premise
changed, and the full root-hit term is retained. None used a Lean server.
Detailed review records belong to the private evidence archive below.

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
exactly one failing region oracle in the same tiny model. These controls retain the complete region contribution, including root hits
with one query.

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
The concrete witness retains the original admission and observation contracts.

## Backfill statements

The additional backfill lemmas preserve the existing declarations:
HashPremise depends only on membership of each actual query list; deduplication
and repeating either whole list therefore preserve the premise exactly.
The sampled-oracle failure classifier is unchanged by deduplicating the two
actual lists. Collision-only run failures have the existing q(q-1) numerator;
region-only run failures have q(q-1)(2L-1)+2qRL. Their bounds use the same
finite-domain strategy and actual-list inclusion relations as the combined
bound, dropping only the unrelated event from the conclusion. No existing
premise, observation or definition is weakened.

## Registration fragment and H82 application

The original assignment reserved registry writes for the coordinator. The
later H82 authorization permits statement-preserving edits to any file.
Accordingly, these reviewed entries have been applied: register.sh generated
the root imports, the language-area fragment generated the module-map rows,
and CORE and axiom inventories register the four additive modules. No
existing theorem or pin was removed or enlarged.

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

Axiom-pin entries (ten new; no existing pin changes):

```json
{
  "Solidity/Hash/Bridge.lean:Solidity.Hash.Bridge.premise_dedup": [
    "propext"
  ],
  "Solidity/Hash/Bridge.lean:Solidity.Hash.Bridge.premise_unit_rootFree": [
    "Quot.sound",
    "propext"
  ],
  "Solidity/Hash/Bridge.lean:Solidity.Hash.Bridge.transfer_prefix": [],
  "Solidity/Hash/CollisionBridge.lean:Solidity.Hash.CollisionBridge.run_collision_le": [
    "Classical.choice",
    "Quot.sound",
    "propext"
  ],
  "Solidity/Hash/CollisionBridge.lean:Solidity.Hash.CollisionBridge.run_premise_le": [
    "Classical.choice",
    "Quot.sound",
    "propext"
  ],
  "Solidity/Hash/CollisionBridge.lean:Solidity.Hash.CollisionBridge.run_regions_le": [
    "Classical.choice",
    "Quot.sound",
    "propext"
  ],
  "Solidity/Hash/CollisionBridge.lean:Solidity.Hash.CollisionBridge.stopped_collision_le": [
    "Classical.choice",
    "Quot.sound",
    "propext"
  ],
  "Solidity/Hash/CollisionBridge.lean:Solidity.Hash.CollisionBridge.two_mul_combined_le": [
    "Classical.choice",
    "Quot.sound",
    "propext"
  ],
  "Solidity/Hash/CollisionBridgeCompiler.lean:Solidity.Hash.CollisionBridge.Compiler.failure_le": [
    "Classical.choice",
    "Quot.sound",
    "propext"
  ],
  "Solidity/Hash/CollisionBridgeCompiler.lean:Solidity.Hash.CollisionBridge.Compiler.refines": []
}
```

## Validation boundaries and handoff

The registered library checkpoint and full runner pass, including corpus,
TestSuite, trust, layer, orphan, generated-root/fragment, documentation,
axiom-pin and strict automatic checks. All four new modules have clean
per-file diagnostics and checked axiom pins. No new sorry, axiom,
native_decide, implemented_by or raised maxHeartbeats is introduced.
Existing frozen theorem statements and semantic definitions are untouched.
The final committed head and exact-head gate receipts are recorded in the
private handoff rather than a self-referential source document.

Checking-time comparison uses balanced paired fresh Lean checks of the
pinned-base root and generated root with the same already-built imports.
The measured root change is below the 10% stop threshold. New module times
are measured separately. This does not establish a cold whole-repository
build-time ratio; the cold library/full passes include cache population and
unrelated existing examples. The existing resource limits and proof budgets
were preserved. Only one heavy Lean job runs at a time.

The probability theorems are kernel proofs of logical counts over sampled
functions. Corpus and runtime checks are external validation, not substitutes
for those proofs. No distributional assumption about actual keccak is proved.
No arbitrary symbolic-machine theorem is automatically transferred: callers
supply a guarded hash-parametric contract and the actual query/strategy
relations. No production compiler correctness instance is constructed;
the existing proved toy compiler supplies the concrete non-vacuity witness.
The source Forward/Guard restrictions and complete target-prefix observation
remain unchanged.

Under H145, detailed receipts, logs, timings, provenance, resource records,
handoffs and checksum manifests are kept outside the code branch in the
private repository `SolidiKeY/solidity-lean-coord`, under
`evidence/solidity-plan-e4-hash-bridge-20261107/e4-hash-bridge/`.
Earlier records are available at private evidence commits
`fa3c994dcc064d17970dfe8f0be75b7685bf7d54` and
`77932fbea1aa3040ce1ccade5755afa5be86583a`; the final handoff identifies the
subsequent archive commit and seals the patch/bundle/checksum manifest.
No evidence files were added under tests/ or Bridge/tests/. The later H145
whole-tree scripts report inherited evidence/private-path violations at the
pinned base; the lane adds none. These inherited failures are documented,
not treated as passing whole-tree gates. They do not authorize deleting
historical baseline files or fixtures.

E4-Q1 is resolved as option A. Acceptance of the inherited H145 whole-tree
failures is tracked as E4-Q2 in the private handoff; no option changes a
theorem or premise. Registration and backfill preserve the original combined bound,
its premises, exclusions and observations. Code changes are committed only
on the assigned branch; no code push, merge or PR is authorized. The only
remote writes are the explicitly requested question relay and private
H145 evidence archive.
