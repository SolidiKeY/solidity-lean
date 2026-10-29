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

This is the shape the sibling G01 contract revision uses. It is decidable
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
| `collisionFree_iff_nodup_map` | for `xs.Nodup`: `CollisionFree f xs ↔ (xs.map f).Nodup`. |

The prefix lemma is the one executions need: a premise about a run's whole
preimage list gives the premise for every prefix of the run.

## The birthday bound, by counting

Model (as the assignment fixes it): a uniformly random function into `N`
values, restricted to `q` distinct inputs, is one of the `N^q` output tuples,
each equally likely. Tuples are lists:

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
  `2 ^ (256 + 1) * bad ≤ xs.length ^ 2 * 2 ^ (256 * xs.length)`.

`#guard_msgs` pins the axioms of `keccak_premise_fails_prob_le`,
`adaptive_lazy_collision_prob_le` and `collisions_le` to
`[propext, Classical.choice, Quot.sound]`. There is no `sorry`, new axiom,
`native_decide`, `decide` tactic, `implemented_by` or `maxHeartbeats` option.

## Adaptive queries

The bound above fixes the `q` inputs before the oracle is sampled. A
random-oracle game lets the `i`-th query depend on the answers to the
earlier ones. What is proved and what is not:

- **Proved, lazy sampling.** `lazyQueries s t` is the query list of an
  adaptive strategy `s : List Nat → α` when the answers are `t` (query `i` is
  `s (t.take i)`). `adaptive_lazy_collision_prob_le` bounds, over all `N^q`
  answer sequences, those whose queries are distinct yet collide:
  `2 * N * bad ≤ q * (q - 1) * N ^ q`. Under lazy sampling each answer is a
  fresh uniform value, so this is the adaptive birthday bound with distinct
  queries.
- **Not proved, child obligation `EagerAdaptiveBound`.** The same bound when
  the oracle is a uniformly random function on a finite domain `dom`, fixed
  before the game (`oracleOf dom g`, `g` one of the `N^|dom|` tuples) and
  queried by `eagerQueries s g q`. It follows from the lazy bound once eager
  and lazy sampling are shown to agree: the answers to distinct adaptive
  queries of a uniform function are uniform and independent. That
  equivalence, a bijection between functions on `dom` and (answers to the
  queries, values elsewhere), is the missing step. The non-adaptive bound has
  the same gap in eager form: it counts output tuples, not functions on a
  larger domain; `EagerAdaptiveBound` with a strategy that ignores the answers
  (query `i` is the `i`-th element of a fixed list) covers it.

A repeated query is not a collision (`CollisionFree` relates equal images of
*different* preimages), so the bounds count only distinct queries; an
execution hashing the same preimage twice adds nothing to `q` beyond its
first hash.

## How G27.05 and G46.05 will use it

No file under `Solidity/Evm/**` is edited here. The plan for the owners:

1. **Record the preimages.** G46.05's EVM-side execution relation exposes,
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
   distinct preimages). Distinct bases still do not give distinct slots: see
   the open question below on offsets.
4. **Justification.** `keccak_premise_fails_prob_le` (and
   `adaptive_lazy_collision_prob_le` for preimages chosen adaptively, as
   attacker-controlled keys are) bounds the probability that the premise fails
   for a random oracle by q²/2²⁵⁷, q the number of distinct preimages. This is
   a statement about a random oracle, not about keccak: the public theorem
   stays conditional on the premise.

### Open: offsets and region overlap

`Slot.hash k s off` denotes `keccak(k ‖ s) + off` and `Slot.data s off`
denotes `keccak(s) + off` (`Solidity/Evm/Machine.lean`). Two slots with
different preimages a ≠ b collide numerically if
`keccak(a) + i = keccak(b) + j (mod 2^256)` for offsets `i ≠ j`, which the
approved premise does not exclude: it speaks about preimages whose hashes are
equal, not about hashes that are close. G04's R34 lists this wrap-around and
overlap as part of the same structural assumption. With the premise as
stated, G27.05 can separate the bases but not the regions (array elements,
struct members) above them. Under a random oracle, the probability that `q`
regions of length at most `L` overlap is about q²·L/2²⁵⁶, the same counting
with "equal" replaced by "within distance L". The question is under
`questions:` in the handoff.

## Checking cost

The module's diagnostics are clean. With `set_option profiler true` (removed
afterwards) only two steps exceed the profiler's 100 ms threshold: a `simp`
in `map_oracleOf` (378 ms) and the axiom check at the end of the file (548 ms).
No proof uses the `decide` tactic or evaluates a large `Fin` or `Nat` value; the 2²⁵⁶
corollaries instantiate the general `k`-bit theorem.

## Remaining child obligations

- `EagerAdaptiveBound`: eager/lazy sampling equivalence (above).
- Region overlap with offsets, which depends on the open question above.
- The G46.05 preimage list per prefix and the G01 `PublicCorrectness`
  premise (owners: G46.05 and the G01 revision).

## Review

<!-- filled in after the finder and skeptic reviews -->
