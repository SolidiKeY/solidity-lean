# Hash collision bound: the per-run premise and the random-oracle bound

Base revision: `caf52ecd4dde5d37cbc0098d47de1a01aa218285`. Module:
`Solidity/Hash/CollisionBound.lean` (namespace `Solidity.Hash`, imports
nothing, registered in `Solidity.lean`).

## The decision this implements

[solidity-scope.md](../solidity-scope.md#user-decisions-2026-10-29), row
"G01 Q3 / G04 Q1 — hash collisions": the public theorem carries a per-run
premise that the preimages hashed by the execution prefix do not collide,
plus a random-oracle lemma bounding the probability of a collision (about
q²/2²⁵⁷ for q hashes). Global injectivity stays forbidden;
`Solidity.Evm.External.no_injective_slot_encoding`
(`Bridge/SolidityBridge/ExternalEvm/Obstructions.lean`) proves that no
injective numeric encoding of the symbolic `Slot`s exists.

This module proves no correspondence and changes no theorem. It supplies the
premise's shape, its algebra and the probability lemma that justifies it.

## The per-run premise

```lean
def CollisionFree {α β : Type _} (f : α → β) (xs : List α) : Prop :=
  ∀ x ∈ xs, ∀ y ∈ xs, f x = f y → x = y
```

This is the shape the batch assigns to the sibling G01 contract revision
(no file at this module's base uses it yet). It is decidable
when `α` and `β` have decidable equality (an `instance` beside it). Lemmas, none
with a premise beyond the hypotheses shown:

| Name | Statement |
|---|---|
| `CollisionFree.nil`, `CollisionFree.singleton` | `[]` and `[x]` are collision-free. |
| `CollisionFree.mono` | from `CollisionFree f ys` and `∀ x ∈ xs, x ∈ ys`. |
| `CollisionFree.sublist`, `.of_prefix`, `.of_suffix` | sublists, prefixes (`<+:`) and suffixes (`<:+`) inherit it. |
| `CollisionFree.append_left`, `.append_right` | both halves of `xs ++ ys` inherit it. |
| `collisionFree_append` | `xs ++ ys` iff both halves and no cross collision. |
| `collisionFree_cons` | `x :: xs` iff `xs` and `x` collides with no element of `xs`. |
| `collisionFree_congr` | equal membership gives equal collision freedom. |
| `dedup`, `mem_dedup`, `nodup_dedup`, `length_dedup_le`, `collisionFree_dedup` | `CollisionFree f (dedup xs) ↔ CollisionFree f xs`: repetitions do not matter. |
| `collisionFree_iff_nodup_map` | for `xs.Nodup`: `CollisionFree f xs ↔ (xs.map f).Nodup`. |

The prefix lemma is the one executions need: a premise about a run's whole
preimage list gives the premise for every prefix of the run.

## The birthday bound, by counting

Model (as the assignment fixes it): a uniformly random function into `N`
values, restricted to `q` distinct inputs, is modelled as one of the `N^q`
output tuples, each equally likely. That a uniform function on a larger
domain gives the same bound is the non-adaptive instance of the eager
theorems below (a strategy that ignores its answers), proved in
`Solidity/Hash/Adaptive.lean`. Tuples are lists:

- `tuples N q : List (List Nat)` — all length-`q` lists with entries below
  `N`, enumerated explicitly (`length_tuples : (tuples N q).length = N ^ q`,
  `length_of_mem_tuples`).
- `hasDup : List Nat → Bool` — the tuple repeats a value
  (`hasDup_eq_false_iff : hasDup t = false ↔ t.Nodup`).
- `collisions N q := (tuples N q).countP hasDup`.

The proof is a union bound over pairs, taken one index at a time. A tuple
`a :: t` collides if `t` already collides (a pair among the old indices) or
if `a` equals one of the `q` entries of `t` (the `q` pairs with the new
index). Summing over `a < N` and swapping the double sum (`sumOver_swap`)
gives

- `collisions_succ_le : collisions N (q+1) ≤ N * collisions N q + q * N ^ q`,

and induction gives the bound. Probabilities are cross-multiplied over `Nat`
(`2 * N * bad ≤ q * (q - 1) * N ^ q` reads `bad / N^q ≤ q(q-1)/(2N)`):

| Name | Statement | Reading |
|---|---|---|
| `two_mul_collisions_le` | `2 * N * collisions N q ≤ q * (q - 1) * N ^ q` | |
| `collisions_le` | `2 * collisions N q ≤ q * (q - 1) * N ^ (q - 1)` | at most q(q-1)/2 · N^(q-1) colliding tuples |
| `collision_prob_le` | `2 * N * collisions N q ≤ q * (q - 1) * (tuples N q).length` | probability ≤ q(q-1)/(2N) |
| `collision_prob_le_sq` | `2 * N * collisions N q ≤ q ^ 2 * (tuples N q).length` | probability ≤ q²/(2N) |
| `pow_two_collision_prob_le` | `2 ^ (k + 1) * collisions (2 ^ k) q ≤ q ^ 2 * 2 ^ (k * q)` | k-bit hash: ≤ q²/2^(k+1) |
| `keccak_collision_prob_le` | `2 ^ (256 + 1) * collisions (2 ^ 256) q ≤ q ^ 2 * 2 ^ (256 * q)` | keccak: ≤ q²/2²⁵⁷ |

`2 ^ (256 + 1)` is written so because the elaborator warns before evaluating
the literal `2 ^ 257` (its exponentiation threshold is 256).

### The oracle reading

`oracleOf xs t : α → Nat` answers the `i`-th input of `xs` with the `i`-th
entry of `t` (and `0` elsewhere; `DecidableEq α`). Then:

- `map_oracleOf : xs.Nodup → t.length = xs.length → xs.map (oracleOf xs t) = t`;
- `oracle_collides_iff : xs.Nodup → t.length = xs.length →
  (¬ CollisionFree (oracleOf xs t) xs ↔ hasDup t = true)`;
- `keccak_premise_fails_prob_le (hxs : xs.Nodup)`: the 256-bit oracles under
  which the per-run premise fails on `xs` number `bad`, and
  `2 ^ (256 + 1) * bad ≤ xs.length ^ 2 * 2 ^ (256 * xs.length)`;
- `keccak_premise_fails_prob_le_dedup (xs : List α)`: the same for a preimage
  list with repetitions, with `q = (dedup xs).length ≤ xs.length` and the
  oracle drawn on `dedup xs`.

`#guard_msgs` pins the axioms of `keccak_premise_fails_prob_le`,
`keccak_premise_fails_prob_le_dedup`, `adaptive_lazy_collision_prob_le` and
`collisions_le`, `keccak_region_premise_fails_prob_le` and its `_dedup`
variant, `near_of_overlap`, and in `Solidity/Hash/Adaptive.lean`
`keccak_eager_collision_prob_le`, `keccak_eager_region_prob_le`,
`two_mul_eager_stopped_le` and `eagerAdaptiveBound` to
`[propext, Classical.choice, Quot.sound]`. Neither module has a `sorry`, new
axiom, `native_decide`, `decide` tactic, `implemented_by` or `maxHeartbeats`
option.

## Adaptive queries

The bound above fixes the `q` inputs before the oracle is sampled. A
random-oracle game lets the `i`-th query depend on the answers to the
earlier ones. What is proved and what is not:

- **Proved, lazy sampling.** `lazyQueries s t` is the query list of an
  adaptive strategy `s : List Nat → α` when the answers are `t` (query `i` is
  `s (t.take i)`). `adaptive_lazy_collision_prob_le` bounds, over all `N^q`
  answer sequences, those whose queries are distinct yet collide:
  `2 * N * bad ≤ q * (q - 1) * N ^ q`. Under lazy sampling each answer is a
  fresh uniform value, so once the queries are distinct the event is
  `hasDup t`, independent of `s`: the theorem is the non-adaptive count read
  on an adaptive query list and carries no adaptive content of its own. Its
  model gives a repeated query a fresh answer, which a real oracle does not,
  so it covers only strategies that never repeat a query.
- **Proved, eager sampling** (`Solidity/Hash/Adaptive.lean`, lane-hashing
  checkpoint 1). `eagerAdaptiveBound : EagerAdaptiveBound`: the oracle is a
  uniformly random function on a finite domain `dom`, fixed before the game
  (`oracleOf dom g`, `g` one of the `N^|dom|` tuples), and queried by
  `eagerQueries s g q`. The proof needs no eager/lazy equivalence: it is a
  union bound over the first query that goes wrong, counted over functions.
  For step `k + 1` at point `x`, the functions that agree off `x` form groups
  of `N` (`upd dom h x b`, `b < N`); redefining a function at a new point
  `x` keeps the first `k` answers, hence the first `k + 1` queries
  (`eagerQueries_upd`), so at most `k` members of a group repeat an earlier
  answer (`eager_step_le`, double counting with `sumOver_swap`).
- **Proved, repeats and stopping.** `two_mul_eagerCollides_le` counts every
  function under which the first `q` queries collide, with repeated queries
  allowed (a repeat gets the same answer, so it is no collision, and the
  step event asks only that the new point be fresh):
  `2 * N * bad ≤ q * (q - 1) * N ^ |dom|`. `two_mul_eager_stopped_le` covers
  runs that stop after `τ g ≤ q` queries, `τ` any function of the oracle
  (a stopped run's queries are a prefix of the first `q`).
  `keccak_eager_collision_prob_le` is the 2²⁵⁶ reading, `q(q-1)/2²⁵⁷`.
- **Proved, regions.** `two_mul_eagerRegionsFail_le` and
  `keccak_eager_region_prob_le`: the same union bound with a bad value being
  one whose region is `Near` an earlier answer's or `Covers` a root word
  (`regionBadValue`, at most `k(2L-1) + |roots| L` bad values,
  `countP_regionBadValue_le`), giving the non-adaptive region bound
  `2N · bad ≤ (q(q-1)(2L-1) + 2q·|roots|·L) · N^|dom|` for adaptive runs.

The step event `stepHit` does not ask the earlier steps to be clean: the
union bound needs only that every failing run has some bad step. `dom` may
contain duplicates: `oracleOf` and `upd` read and write the first
occurrence, so each function on the distinct points has the same number of
tuples behind it and the counted ratio is still the uniform probability
(`EagerAdaptiveBound` keeps its `dom.Nodup` premise; the proof does not use
it).

**What `q` counts.** The strategy `s` is the whole adversary together with
the run: everything that chooses a preimage (calldata, keys, the
environment) must be a function of earlier oracle answers only, and `q` must
bound every oracle query that influenced the run, including those an
attacker made offline before choosing its inputs, not only the run's own
`KECCAK256` steps. `q` is a worst-case bound, not an expected count.

What remains between these theorems and a real run is the modelling step
that keccak behaves as a uniformly random function on the (finite) set of
byte strings a run can hash: `dom` is any finite list containing every
preimage the strategy can produce (`hs : ∀ t, s t ∈ dom`); gas and memory
bound a preimage's length, so such a finite set exists. Read as a
probability (count / `N^|dom|`), the bound does not depend on `|dom|`. That keccak is not a random function is the reason the
public theorem stays conditional on the premise.

A repeated query is not a collision (`CollisionFree` relates equal images of
*different* preimages). For a fixed preimage list, repetitions are removed by
`collisionFree_dedup` and `keccak_premise_fails_prob_le_dedup`, so `q` counts
distinct preimages; for adaptive runs `two_mul_eagerCollides_le` takes `q` to
be the number of queries, repeats included.

## How G27.05 and G46.05 will use it

No file under `Solidity/Evm/**` is edited here. The plan for the owners:

1. **Record the preimages.** G46.05's EVM-side execution relation is to expose,
   for each execution prefix, the list `pre : List (List UInt8)` of
   `KECCAK256` inputs in the order hashed (EVM memory bytes). The list grows
   along the prefix order (`Prefix.Le` in `Solidity/Roadmap/Contracts.lean`),
   so a premise on a longer prefix gives one on every shorter prefix
   (`CollisionFree.of_prefix`).
2. **The premise.** `PublicCorrectness` (revised by G01) assumes, per run
   prefix, `CollisionFree keccak pre`, with `keccak` the fixed parameter
   that the "Readings" follow-up of the decision names. It is not
   `Function.Injective keccak`, which is false for a function from unbounded
   byte strings to 256-bit words.
3. **Symbolic slots.** G27.05 interprets each symbolic `Slot` reached by the
   prefix as a word: `hash k s off ↦ keccak(k ‖ ⟦s⟧) + off` and
   `data s off ↦ keccak(⟦s⟧) + off`. Under the premise, two reached
   `hash`/`data` terms with different preimages have different *bases*
   (`collisionFree_iff_nodup_map` turns the premise into distinct images of
   distinct preimages). Distinct bases still do not give distinct slots, and
   distinct slot terms need not give distinct preimages. The second-round
   region premise `RegionsDisjoint` (below) separates the regions, provided
   every reached offset stays below the region length.
4. **Justification.** `keccak_premise_fails_prob_le_dedup` bounds the
   probability that the premise fails for a random oracle by q²/2²⁵⁷, q the
   number of distinct preimages, when the preimages are fixed in advance.
   Real runs choose preimages adaptively (attacker-controlled keys; nested
   mappings hash earlier hash outputs); `keccak_eager_collision_prob_le` and
   `keccak_eager_region_prob_le` (`Solidity/Hash/Adaptive.lean`) cover them
   in the random-oracle model, with `q` counting every oracle query of the
   run *and* of whoever chose its inputs (see "What `q` counts"). Either way
   it is a statement about a random oracle, not about keccak: the public
   theorem stays conditional on the premise.

### Offsets and the region premise

`Slot.hash k s off` denotes `keccak(k ‖ s) + off` and `Slot.data s off`
denotes `keccak(s) + off` (`Solidity/Evm/Machine.lean`). Two slots with
different preimages a ≠ b collide numerically if
`keccak(a) + i = keccak(b) + j (mod 2^256)` for offsets `i ≠ j`. Preimage
collision freedom does not exclude that: it speaks about preimages whose
hashes are equal, not about hashes that are close. Nor does it exclude
**root overlap** (`keccak(a) + i ≡ j` for a `root j` slot). G04's R34 lists
this wrap-around and overlap as part of the same structural assumption.

**Second-round decision.** As relayed by the batch coordinator during this
task, the user extended the per-run premise to hashed regions: no two
regions of length at most `L` based at hashed slots overlap, and none
overlaps a root slot. This comes with a probability lemma of about
q²·L/2²⁵⁶ plus a q·R·L/2²⁵⁶ root term. The coordinator records it in
`docs/solidity-scope.md`, section "Second round (2026-10-29)". That section
is not at this task's base revision, so this document cites it by name only.

Proved here, in the same style as the preimage bound:

| Name | Statement |
|---|---|
| `Near N L a b` | `(a < b + L ∧ b < a + L) ∨ a + N < b + L ∨ b + N < a + L`: the regions `[a, a+L)` and `[b, b+L)` mod `N` are within reach. |
| `Covers N L a r` | `(a ≤ r ∧ r < a + L) ∨ r + N < a + L`: the region at `a` covers word `r`. |
| `near_of_overlap` | `a < N → b < N → L ≤ N → i < L → j < L → (a + i) % N = (b + j) % N → Near N L a b`. |
| `covers_of_hit` | `a < N → L ≤ N → i < L → (a + i) % N = r → Covers N L a r`. |
| `RegionsDisjoint N L f roots xs` | `(∀ x ∈ xs, ∀ y ∈ xs, x ≠ y → ¬ Near N L (f x) (f y)) ∧ ∀ x ∈ xs, ∀ r ∈ roots, ¬ Covers N L (f x) r`. |
| `RegionsDisjoint.nil`, `.mono`, `.of_prefix`, `regionsDisjoint_cons` | The same algebra as `CollisionFree`. |
| `regionsDisjoint_congr`, `regionsDisjoint_dedup` | Membership only; `RegionsDisjoint … (dedup xs) ↔ RegionsDisjoint … xs`. |
| `RegionsDisjoint.collisionFree` | `0 < L → RegionsDisjoint N L f roots xs → CollisionFree f xs`. |
| `regionBad`, `regionCollisions N L roots q` | The bad tuples and their count. |
| `countP_near_le`, `countP_covers_le` | For `b, r < N`, at most `2L - 1` (resp. `L`) bases `a < N` are near `b` (resp. cover `r`). |
| `regionCollisions_succ_le` | `(∀ r ∈ roots, r < N) →` `B(q+1) ≤ N · B(q) + (q(2L-1) + \|roots\| L) · N^q`. |
| `two_mul_regionCollisions_le` | `2 * N * regionCollisions N L roots q ≤ (q * (q - 1) * (2 * L - 1) + 2 * q * roots.length * L) * N ^ q`. |
| `pow_two_region_prob_le`, `keccak_region_prob_le` | The same at `N = 2^k` and `N = 2^256`, with `2 ^ (256 + 1)` on the left. |
| `regionsDisjoint_iff_regionBad` | `xs.Nodup → (RegionsDisjoint N L f roots xs ↔ regionBad N L roots (xs.map f) = false)`. |
| `keccak_region_premise_fails_prob_le` | For `xs.Nodup` and roots below `2^256`: `2 ^ (256 + 1) * bad ≤ (q(q-1)(2L-1) + 2q·\|roots\|·L) · 2^(256 q)` with `q = xs.length`. |
| `keccak_region_premise_fails_prob_le_dedup` | The same for a list with repetitions, `q = (dedup xs).length`. |

Read as a probability, the bound is
`q(q-1)(2L-1)/2²⁵⁷ + q·|roots|·L/2²⁵⁶ ≤ (q²·L + q·R·L)/2²⁵⁶`, which is the
decided figure. `L` can reach `Lmax` (2⁶⁴, `Solidity/Evm/Machine.lean`), so
for large arrays the bound is much weaker than q²/2²⁵⁷: with `L ≤ 2⁶⁴` it is
at most (q² + q·R)/2¹⁹². `R = roots.length` counts root *words*: a root
struct or static array is covered only if each of its words is listed in
`roots`. One `L` serves every region; a shorter region lies inside the
length-`L` one, so taking the largest region length is sound.

Left to the users of the premise (G27.05):

- **Offsets below `L`.** The premise reads each slot as base plus an offset
  `i < L`. Offsets in `Slot` are unbounded `Nat`s, so distinct terms such as
  `data s 0` and `data s 2^256` denote one word. A nested `hash`/`data` term
  over them then gives equal preimages from distinct slot terms. G27.05 must
  show that every reached offset is below the region length it assumes (for
  arrays, by `Lmax`).
- **Words below `N`.** `near_of_overlap` reads hashes as words below `N`,
  and both it and `covers_of_hit` need `L ≤ N`. The hypothesis that roots are
  below `2^256` belongs to the counting lemmas.
- **Adaptive and repeated preimages.** Proved (lane-hashing checkpoint 1):
  `regionsDisjoint_congr`, `regionsDisjoint_dedup`,
  `keccak_region_premise_fails_prob_le_dedup` for repeats in a fixed list,
  and `keccak_eager_region_prob_le` for adaptive runs.

## Checking cost

The module's diagnostics are clean. Profiled with `set_option profiler true`
(removed afterwards) on the final file, with the language server's parallel
elaboration on a 4-core VM: the slowest single tactic runs took 1.0–1.9 s
(`simp only` in `nodup_dedup` and `length_dedup_le`, `omega` in
`countP_near_le`); everything else was below about 1 s. The `#print axioms`
block at the end took 3.7 s. Before the region section was added, only two
steps passed the 100 ms threshold (378 ms and 548 ms). The later figures
include time spent waiting on parallel tasks ("blocked"), so they are upper
bounds.
No proof uses the `decide` tactic or evaluates a large `Fin` or `Nat` value; the 2²⁵⁶
corollaries instantiate the general `k`-bit theorem.

## Remaining child obligations

- bounded offsets are proved for `STy.locate` terms (`STy.locate_bounded`); their tie to compiled code (G27.05) is open.
- The G46.05 preimage list per prefix and the G01 `PublicCorrectness`
  premise (owners: G46.05 and the G01 revision).

(`EagerAdaptiveBound`, the repeat reduction, the region `dedup` lemma and the
region adaptive bound were closed in lane-hashing checkpoint 1; see
"Adaptive queries" and "Handoff — lane-hashing checkpoint 1" below.)

## Handoff and gates

Base `caf52ecd4dde5d37cbc0098d47de1a01aa218285`; Lean checked at commit
`4eb6d3a`. This section records that first task; lane-hashing checkpoint 1
changed the module afterwards (its own handoff is below).

- `lean_diagnostic_messages` on `Solidity/Hash/CollisionBound.lean`: no
  messages. No `sorry`, new axiom, `native_decide`, `implemented_by` or
  `maxHeartbeats`; `#guard_msgs` pins the standard three axioms.
- `node scripts/check-layers.mjs`: 156 core modules, 0 reach the elaborator.
  `node scripts/check-orphans.mjs`: 734 reachable, 0 orphaned.
  `bash scripts/check-trust.sh`: 0 findings.
  `bash scripts/check-doc-paths.sh`: 46 missing references, the base count.
- `./run-lean.sh` (23 min 17 s wall, 39 min 39 s user; peak memory not
  measured, since `/usr/bin/time` is absent): `lake build` passed (719 jobs;
  `Solidity.Hash.CollisionBound` built in 6.1 s). `lake build SolkeyTestSuite`
  failed: Lean was killed with exit code 137 (out of memory) on
  `Solidity/TestSuite/Derived17.lean`. That file is not touched here and does
  not import this module; its repair belongs to the memory-loops lane. The
  step therefore stopped before `check-solkey.sh`. Run on its own,
  `check-solkey.sh` reports `37 mismatch(es)`, the base count.

## Registration

`Solidity.lean` imports the module. It only states and proves, so following
[parallelism.md](../parallelism.md) it is in `CORE` in
`scripts/check-layers.mjs` (one added line).

## Review

A read-only finder and a separate skeptic reviewed commit `3a041d5`, without
the Lean server. Confirmed findings, all fixed in the following commit:

| Finding | Fix |
|---|---|
| The doc claimed a repeated hash "adds nothing to `q`", but every theorem required distinct preimages (finder 1, skeptic 1). | `collisionFree_congr`, `dedup` and its lemmas, `collisionFree_dedup`, `keccak_premise_fails_prob_le_dedup`; the adaptive repeat case is a named child obligation. |
| `adaptive_lazy_collision_prob_le` was called the adaptive birthday bound; it has no adaptive content, and its model gives repeated queries fresh answers (skeptic 2). | The doc, the module docstring and the coverage-plan status line now say so. |
| The doc cited the lazy bound for adaptively chosen keys (skeptic 4). | "Justification" now says the bound reaches real runs only through the open obligations. |
| The module docstring stated the tuple model as fact and said adaptive queries were "not covered", which contradicted the lazy theorem (skeptic 1, finder 2). | Docstring rewritten. |
| Offsets: root overlap and offset aliasing (`data s 0` versus `data s 2^256`) were missing, and the doc wrongly said distinct slots give distinct preimages (skeptic 3). | Added to the offsets section (now "Offsets and the region premise"); step 3 corrected. |
| The doc stated as fact that the G01 contracts use the `CollisionFree` shape and that G46.05 "exposes" preimages (finder 4). | Reworded as an assignment and a plan. |
| Two descriptions of the `2 ^ (256 + 1)` spelling disagreed (finder 5). | Aligned. |
| The module was not in `CORE` (finder 7). | Added. |
| Several `have`s had no explicit type (finder 8). | All typed. |
| `EagerAdaptiveBound` fixed `β : Type` (finder 3). | Universe-polymorphic. |
| A second skeptic review of the region commit `4eb6d3a` found the arithmetic and `Near`/`Covers` correct, plus four doc issues: the "below q²/2¹⁹²" figure dropped the root term, `R` counting root words was unstated, a stale section name, and a misattributed `r < N` hypothesis. | All four reworded. |
| The offsets question (skeptic 3) needed a user decision. | Decided in the second round (relayed by the coordinator); `RegionsDisjoint` and its bound added after the review, see "Offsets and the region premise". |

Not changed: `grind` in `two_mul_collisions_le` (one ring identity; `grind`
is used 55 times elsewhere in `Solidity/`), noted by both reviewers as a
doubt only.

## Handoff — lane-hashing checkpoint 1

Batch `roadmap-l1-20261029`, lane `lane-hashing`, branch
`cloud/roadmap-l1-20261029/lane-hashing`, base `ceb0d54`; this document and
`Solidity/Hash/CollisionBound.lean` were merged in from
`cloud/roadmap-w1-20261029/hash-collision-bound` and are owned by the lane.
Work queue item 1 ("Region premise and bound"):

- The region predicate and its counting bound were already in the merged
  module (above). Added: `regionsDisjoint_congr`, `regionsDisjoint_dedup`,
  `keccak_region_premise_fails_prob_le_dedup` (the dedup lemmas the reviews
  asked for; `collisionFree_dedup` already existed).
- The eager/lazy adaptive step is **closed**, not just stated: the new
  module `Solidity/Hash/Adaptive.lean` proves `eagerAdaptiveBound :
  EagerAdaptiveBound`, the repeat reduction (`two_mul_eagerCollides_le`
  allows repeated queries), early stopping (`two_mul_eager_stopped_le`) and
  the region counterpart (`two_mul_eagerRegionsFail_le`,
  `keccak_eager_region_prob_le`). The modelling gap that remains is stated
  in "Adaptive queries" ("What `q` counts").

Gates (on the checkpoint's final commit):

- `lean_diagnostic_messages`: no messages on `Solidity/Hash/CollisionBound.lean`
  and `Solidity/Hash/Adaptive.lean`; the `#guard_msgs` pins listed above
  hold. Both files elaborate in a few seconds in the language server; no
  step was slow enough to profile.
- `node scripts/check-layers.mjs`: 157 core modules, 0 reach the elaborator
  (`Solidity.Hash.Adaptive` added to `CORE`).
  `node scripts/check-orphans.mjs`: 735 reachable, 0 orphaned.
  `bash scripts/check-trust.sh`: 0 findings.
  `bash scripts/check-doc-paths.sh`: 46 missing references, the base count.
- `./run-lean.sh` runs once at the end of the lane (recorded in
  `docs/feature-work/storage-hashed-layout.md`).

### Review (checkpoint 1)

A read-only finder and a separate skeptic reviewed commit `668f1f9` without
the Lean server. Neither found a false or vacuous statement. Confirmed
findings, fixed in the following commit:

| Finding | Fix |
|---|---|
| The doc said the eager theorems cover real runs "with `q` the number of hash queries"; an attacker who hashes offline is modelled only if those queries are part of `s` (finder 1, skeptic 6). | "What `q` counts" added; step 4 of "How G27.05 and G46.05 will use it" and the coverage-plan line reworded. |
| Stale "not proved" sentences on restricting a larger-domain function to tuples, in this document and the module docstring (finder 2, skeptic 7). | Now point to `eagerAdaptiveBound`. |
| The previous handoff claimed later commits changed only this document; no checkpoint handoff existed (finder 3). | This section; the old handoff is scoped to its task. |
| The pin list and the "no `sorry`" claim covered only the first module (finder 4). | Extended to both modules. |
| The adaptive region bound was written without its `2N ·` factor (finder 5). | Fixed. |
| Ten `have`s without explicit types (finder 6). | All typed. |
| A new `grind` for a ring identity (finder 7). | Replaced by `simp only [Nat.mul_assoc, Nat.add_mul, …]` and `omega`. |
| `firstHit` is not the first bad step (finder, naming nit). | Renamed `stepHit`; docs say any bad step. |
| Duplicates in `dom` were undocumented (skeptic 2). | Documented in "Adaptive queries"; `EagerAdaptiveBound` keeps its unused `Nodup` premise. |
