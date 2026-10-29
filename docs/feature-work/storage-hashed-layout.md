# Storage: the hashed layout, its separation and the keccak instantiation

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
| `off_eq_of_mod_eq` | `a < N → i < N → j < N → (a + i) % N = (a + j) % N → i = j` (one region). |
| `hashed_ne_root` | Under `RegionsDisjoint N L H (List.range R) P`, `(H p + o) % N ≠ r % N` for `p ∈ P`, `o < L`, `r < R ≤ N` (a hashed word never lands on a root word; `Covers`). |
| `hashed_ne_hashed` | Different preimages in `P`, offsets below `L ≤ N`: different words, also across the wrap-around (`Near`). |
| `Loc.word_inj` | Two `Bounded L R` terms whose preimages lie in `P` have the same word only if they are equal. |
| `nodup_map_word` | A run's distinct bounded terms denote distinct words. |
| `word_data_alias` | Without the bound, `data s 0 ≠ data s N` have one word: the offset bound is needed. |

The proof of `word_inj` is by induction on both terms. Root/root: offsets
below `R ≤ N` are their own words. Root/hashed: `hashed_ne_root`. Hashed at
different preimages (including `entry` against `data`): `hashed_ne_hashed`.
Hashed at the same preimage: the preimage's parts are equal, so the inner
words are equal and the induction hypothesis gives equal inner terms; then
`off_eq_of_mod_eq` gives equal offsets. Only the region premise is used; it
implies the point premise `CollisionFree` (`RegionsDisjoint.collisionFree`).

These are the root and region cases the hash-bound reviews named:
wrap-around (`Near` reads distance around the circle), root overlap
(`Covers`) and offset aliasing (`Bounded`, `word_data_alias`).

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
| `slot_word_inj` | `Loc.word_inj` read on slots: `Loc.word W H (ofSlot s) = Loc.word W H (ofSlot t) → s = t` for bounded slots with preimages in `P`. |

### Limitations (checkpoint 2)

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
