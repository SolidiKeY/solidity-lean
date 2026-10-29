# Storage: the hashed layout and its separation

Lane `lane-hashing` of batch `roadmap-l1-20261029` (branch
`cloud/roadmap-l1-20261029/lane-hashing`, base `ceb0d54`). Preparation for
G27.05 (storage layout through hashes) and G46.05 (the hash premise on EVM
runs). The premise and its probability bounds are in
[hash-collision-bound.md](hash-collision-bound.md).

Decisions in force ([solidity-scope.md](../solidity-scope.md), "User
decisions (2026-10-29)" and "Second round (2026-10-29)"): the per-run premise
that hashed preimages do not collide; the region premise (no region of
length at most `L` based at a hashed slot overlaps another or a root word);
the physical layout is unobservable, so the compiler may choose its layout;
global injectivity is forbidden (`no_injective_slot_encoding`).

## Checkpoint 2 — the hashed layout model

Module `Solidity/Storage/HashedLayout.lean` (namespace `Solidity.Storage`,
imports only `Solidity.Hash.CollisionBound`, in `CORE`).

### Slot terms and words

```lean
inductive Pre | entry (k w : Nat) | data (w : Nat)
inductive Loc | root (off : Nat) | hash (k : Nat) (s : Loc) (off : Nat)
              | data (s : Loc) (off : Nat)
def Loc.word (N : Nat) (H : Pre → Nat) : Loc → Nat
  | root o => o % N
  | hash k s o => (H (.entry k (word s)) + o) % N
  | data s o => (H (.data (word s)) + o) % N
```

`Loc` has the shapes of `Solidity.Evm.Slot` (`Solidity/Evm/Machine.lean`):
a root word, a mapping entry `keccak(k ‖ ⟦s⟧) + off`, a dynamic array's data
`keccak(⟦s⟧) + off`. A preimage holds the *word* of the inner term, as the EVM
hashes it, so `Loc.pres N H l` (the preimages a term hashes) depends on `H`.
The hash parameter `H` is arbitrary; the theorems assume only `H p < N` and
the run's premise.

`Loc.Bounded L R l`: every root offset in `l` is below `R` (the root words)
and every hashed offset below `L` (the region length).

### Separation

| Name | Statement |
|---|---|
| `Loc.off_eq_of_mod_eq` | `a < N → i < N → j < N → (a + i) % N = (a + j) % N → i = j` (one region). |
| `Loc.hashed_ne_root` | Under `RegionsDisjoint N L H (List.range R) P`, `(H p + o) % N ≠ r % N` for `p ∈ P`, `o < L`, `r < R ≤ N` (a hashed word never lands on a root word; `Covers`). |
| `Loc.hashed_ne_hashed` | Different preimages in `P`, offsets below `L ≤ N`: different words, also across the wrap-around (`Near`). |
| `Loc.word_inj` | Two `Bounded L R` terms whose preimages lie in `P` have the same word only if they are equal. |
| `Loc.nodup_map_word` | A run's distinct bounded terms denote distinct words. |
| `Loc.word_data_alias` | Without the bound, `data s 0 ≠ data s N` have one word: the offset bound is needed. |

The proof of `word_inj` is by induction on both terms. Root/root: offsets
below `R ≤ N` are their own words. Root/hashed: `Loc.hashed_ne_root`. Hashed at
different preimages (including `entry` against `data`): `Loc.hashed_ne_hashed`.
Hashed at the same preimage: the preimage's parts are equal, so the inner
words are equal and the induction hypothesis gives equal inner terms; then
`Loc.off_eq_of_mod_eq` gives equal offsets. Only the region premise is used;
for `L > 0` it implies the point premise `CollisionFree`
(`RegionsDisjoint.collisionFree`).

These are the root and region cases the hash-bound reviews named:
wrap-around (`Near` reads distance around the circle), root overlap
(`Covers`) and offset aliasing (`Bounded`, `Loc.word_data_alias`).

### Types, paths and bounded offsets

`STy` is a storage type at word granularity: `word`, `strct fs`, `sarr e n`,
`darr e`, `map v`. `STy.size` follows solc without packing: a struct is the
sum of its members, a static array `n · size e`, a dynamic array and a
mapping one word. `STy.locate t l p` follows an access path (`Step.field i`,
`.index i`, `.key k`): member `i` at `l + sizes (take i fs)`, static element
`i < n` at `l + i · size e`, dynamic element `i < lmax` at
`data l (i · size e)`, mapping value at `hash k l 0`. `lmax = 2^64` is the EVM
model's `Lmax`. A dynamic index is bounded by `lmax`, the most an array's
length can be; the actual length check belongs to the semantics.

`STy.Fits L t`: every hashed region inside `t` fits in `L` words (a mapping's
value type, and `lmax · size e` for a dynamic array). `Placed L R t l`: every
in-place word of a value of type `t` at `l` is `Bounded`.

| Name | Statement |
|---|---|
| `STy.locate_bounded` | `t.Fits L → Placed L R t l → t.locate l p = some (t', l') → t'.Fits L ∧ Placed L R t' l'`. |
| `placed_root` | `t.size ≤ R → Placed L R t (.root 0)`. |
| `located_word_inj` | For the state type `t` (`t.Fits L`, `t.size ≤ R`), two words `l₁ + j₁`, `l₂ + j₂` reached by paths (`j < size`), whose preimages lie in `P`, are equal words only if they are equal terms, under `RegionsDisjoint N L H (List.range R) P`, `L, R ≤ N`. |

`locate_bounded` is the "offsets below `L`" obligation that
[hash-collision-bound.md](hash-collision-bound.md) left to G27.05, for the
terms this model reaches. With `lmax = 2^64`, `L` is at least
`2^64 · size e` for a dynamic array of `e`; the decided bound is then about
`(q² + q·R)·L/2²⁵⁶`.

### Correspondence with the EVM model

`Solidity/Storage/HashedLayoutEvm.lean` (imports `Solidity.Evm.Machine`;
not in `CORE`, like `Evm/**`; `Machine.lean` is not edited):

| Name | Statement |
|---|---|
| `ofSlot` | `Slot → Loc`, the key's word as its `Nat`. |
| `ofSlot_injective`, `ofSlot_add` | Injective; `ofSlot (s.add i) = (ofSlot s).add i`. |
| `keysBelow_ofSlot`, `exists_ofSlot` | The image is exactly the terms whose keys are below `W` (`KeysBelow W`). |
| `lmax_eq_Lmax` | `lmax = Lmax`, by `rfl`. |
| `slot_word_inj` | `Loc.word_inj` moved along `ofSlot`: `Loc.word W H (ofSlot s) = Loc.word W H (ofSlot t) → s = t` for bounded slots with preimages in `P`. |

The EVM model's store is symbolic (`WordStore.cells : Slot → Fin W`) and
never computes a slot's word, so `slot_word_inj` does not refine the machine;
it is what a word-addressed refinement of the store would need.

### Limitations (checkpoint 2)

- **Word keys only.** `Pre.entry` takes the key as one word, which covers
  value-type keys (`uint`, `int`, `address`, `bool`, `bytesN`). `string` and
  `bytes` keys hash their unpadded bytes (`keccak(bytes(k) ‖ p)`); the key
  `""` then gives the same bytes as a dynamic array's data at `p`, so such
  keys need another preimage shape and are not modelled. Nor are `bytes` and
  `string` storage values (their long form is data at `keccak(p)`).
- **One region length.** `L` must cover every hashed region of the type
  (`STy.Fits`), so the bound degrades with the largest one; a type with a
  region of `2^192` words or more cannot satisfy `L ≤ N` usefully. The
  premise is satisfiable only when `(q² + q·R)·L ≪ N` (for `L = N` and two
  preimages every pair is `Near`).

- **No packing.** solc packs value types smaller than a word into one slot
  (and `bytes`/`string` use a short in-place encoding). The model is word
  granular, as `Solidity/Evm/Layout.lean` is; packing changes offsets inside
  a word, not which slot terms exist. A packed layout is a G27 refinement.
- **The layout is not the compiler's yet.** `STy.locate` is a model of solc's
  formula; relating it to `Solidity/Evm/Layout.lean`'s `size`/`offset` (which
  read the AST's struct table) and to the compiled code is G27.05 proper.
  Since the physical layout is unobservable, a compiler may choose another
  layout; these theorems then apply to whatever terms it reaches.
- **Distinct paths to distinct terms** (symbolic separation, as in
  `Layout.lean`'s `occ_*_disjoint`) is not restated here; item 4 of the work
  queue takes it up.
- **`P` must contain the preimages.** The theorems take the run's preimage
  list as a hypothesis; G46.05 is to expose it per execution prefix.

### Handoff — checkpoint 2

Work queue item 2 is done: the layout model, bounded offsets for every
access path, separation (including the root and wrap-around cases) and the
read-only `Evm.Slot` correspondence. `Solidity/Evm/Machine.lean` is not
edited.

Gates on the checkpoint's final commit:

- `lean_diagnostic_messages`: no messages on `Solidity/Storage/HashedLayout.lean`
  and `Solidity/Storage/HashedLayoutEvm.lean`. `#guard_msgs` pins:
  `Loc.word_inj`, `located_word_inj`, `Loc.nodup_map_word` and
  `slot_word_inj` at `[propext, Classical.choice, Quot.sound]`,
  `STy.locate_bounded` at `[propext, Quot.sound]`. No `sorry`, new axiom,
  `native_decide`, `decide` tactic, `grind`, `implemented_by` or
  `maxHeartbeats`.
- `HashedLayout.lean` elaborates in a few seconds; `HashedLayoutEvm.lean`'s
  cost is that of loading `Solidity.Evm.Machine` (about a minute in a cold
  language server), its own declarations are immediate.
- `node scripts/check-layers.mjs`: 158 core modules, 0 reach the elaborator
  (`Solidity.Storage.HashedLayout` in `CORE`; the `Evm` correspondence stays
  outside, as `Evm/**` does). `node scripts/check-orphans.mjs`: 737
  reachable, 0 orphaned. `bash scripts/check-trust.sh`: 0 findings.
  `bash scripts/check-doc-paths.sh`: 46, the base count.

### Review (checkpoint 2)

A read-only finder and a separate skeptic reviewed commit `110f306` without
the Lean server. Both found the formal content sound: the layout matches
solc at word granularity (and `Evm/Layout.lean`'s sizes), the bounds have no
off-by-one, the induction in `word_inj` is sound, and the hypotheses are
satisfiable for realistic parameters. Confirmed findings, fixed in the
following commit:

| Finding | Fix |
|---|---|
| The module docstring, this document's title and the README row named a keccak module that did not exist yet (finder 1, skeptic 5). | Reworded as work queue item 3 (it lands in checkpoint 3). |
| `string`/`bytes` keys and values were not in the limitations; for keys the empty string makes an `entry` preimage's bytes equal a `data` one's (finder, skeptic 6). | "Word keys only" limitation. |
| The bound's dependence on the largest region and when the premise is satisfiable were unstated (skeptic 1, 3). | "One region length" limitation. |
| "Region premise implies point premise" omitted `L > 0` (skeptic 4). | Added. |
| The `Evm.Slot` reading suggested a refinement of the machine, whose store is symbolic (skeptic 7). | Reworded here and in the module docstring. |
| `no_injective_slot_encoding` cited without its `Bridge/` location; `Loc.` names cited bare (finder 2, 3). | Location added; names qualified. |
| `STy.locate_bounded` and `Loc.nodup_map_word` had no axiom pins (finder 4). | Pinned. |
