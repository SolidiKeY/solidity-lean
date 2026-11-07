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
| Language guards | `Solidity/Roadmap/Contracts.lean:820–829` intrinsic hash fields/guard; :850–873 `EvmSpec`, `hashed`, `slotHashed`, `guard_iff` | General guarded transfer uses EVM `guard_iff`. No arbitrary symbolic theorem is automatically hash-parametric. |
| Compiler contract | `Solidity/Roadmap/Contracts.lean:937` `PublicCorrectness`; :960 `hashes_source`; :967 `refines`; :974 `decode_reach`; :982 `decode_commutes`; :1016 `PublicCorrectness.transfer` | Compiler result retains allowed/admissible environments, complete observations and the source forward/guard conditions. Target premise yields backward prefix refinement and decode reach. |
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

## Scope question E4-Q1 (open)

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

No answer is assumed; no theorem or premise has been weakened.
Relay: `coord-q/codex/solidity-plan-e4-hash-bridge-20261107/e4-hash-bridge/20261107T162119Z`.

## Reviews

Checkpoint 1 finder (independent read-only thread, no Lean server):
confirmed the root-hit counterexample and required preservation of the
separate source forward/guard premises. Both findings are reflected above.
Further finder/skeptic reviews after checkpoints 2–4 are pending.

## Registration fragment (coordinator only)

Reserved intended imports (not yet implemented or registered):

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

Checkpoint 1 is inventory/statements only; no Lean edits. Checkpoints 2–4,
axiom pins, negative controls, module timing, full gates and final handoff
remain pending. No new axioms, sorry, trust shortcuts or frozen-statement
changes. No proof checking has yet been claimed.
