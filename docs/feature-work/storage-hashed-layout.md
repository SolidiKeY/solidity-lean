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
  value-type keys (`uint`, `int`, `address`, `bool`, `bytesN`), each as its
  ABI word: `int` sign-extended, `bytesN` left-aligned (`v · 256^(32-N)`). `string` and
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

## Checkpoint 3 — the keccak instantiation

Module `Solidity/Storage/HashedKeccak.lean` (imports `Solidity.Keccak` and
`Solidity.Storage.HashedLayout`, in `CORE`).

| Name | Statement |
|---|---|
| `bytesBE`, `ofBytes_bytesBE`, `bytesBE_inj` | The `m` low bytes big-endian; `ofBytes (bytesBE m n) = n % 256^m`; injective on words for `m = 32`. |
| `encode` | `entry k w ↦ bytesBE 32 k ++ bytesBE 32 w` (`abi.encode(k, w)`, 64 bytes), `data w ↦ bytesBE 32 w` (32 bytes). |
| `encode_inj` | Injective on preimages whose parts are words (`Pre.Words`); `entry` and `data` differ in length. |
| `keccakH` | `keccak256Nat ∘ encode`, the hash parameter. |
| `keccak256_bytes`, `keccakH_lt` | The digest has at most 32 bytes, each below 256, so `keccakH p < 2^256` (the `hH` hypothesis of `Loc.word_inj`). |
| `keccakH_eq_iff` | On word preimages, `keccakH` collides iff keccak-256 collides on the encoded inputs. |
| `collisionFree_keccakH_iff`, `regionsDisjoint_keccakH_iff` | `CollisionFree keccakH ps ↔ CollisionFree keccak256Nat (ps.map encode)`, and the same for `RegionsDisjoint`: the layout's premise is the premise on the layout's own byte-string `KECCAK256` inputs. A run's premise on all its inputs `X` gives it by `RegionsDisjoint.mono` once `P.map encode ⊆ X` (not proved here: it needs the compiled code to hash exactly these cleaned words). |
| `keccak_word_inj` | `Loc.word_inj` at `N = 2^256`, `H = keccakH`, with keys below `2^256` (`Pre.Words`; `bytesBE` truncates, so `k` and `k + 2^256` would alias) and the region premise stated on `P.map encode`. |

`#guard` vectors check `Loc.word (2^256) keccakH` against solc's formula
(`keccak256(abi.encode(k, p))` for a mapping entry, `keccak256(abi.encode(p))
+ i·s` for an array element): `uint256[]` at slots 0 and 1, a two-word struct
array element, `uint`/`bool` keys, a negative `int` key (two's complement),
an `address` key (left-padded), a nested mapping, an array inside a mapping,
`bytes32` and left-aligned `bytes4` keys, and one vector through
`STy.locate` against a literal digest. The digests were computed
independently with pycryptodome's keccak-256, installed with
`pip install --target <scratch> pycryptodome`:

```python
from Crypto.Hash import keccak
def k(b): h = keccak.new(digest_bits=256); h.update(b); return int.from_bytes(h.digest(), 'big')
w = lambda n: (n % 2**256).to_bytes(32, 'big')
k(w(0))                 # uint256[] at slot 0: 0x290dec…e563
k(w(9) + w(k(w(7) + w(2))))   # n[7][9], n at slot 2
```

The checkpoint-3 finder re-checked every literal with a separate pure-Python
Keccak-f[1600]. `keccak256(uint256(0))`, `keccak256(1)`, `keccak256(2)` and
`keccak256(0 ‖ 0)` are constants common tooling quotes. `#guard` evaluates;
no proof depends on it, and the vectors are the only check that `keccakH`
matches solc's byte order.

Limitations:

- Keys are value types (one word, below `2^256`); `string`/`bytes` keys
  hash their unpadded bytes and are outside `Pre` (see checkpoint 2).
- **Other hashed slots.** Slots user code or assembly computes from its own
  hashes (`abi.encodePacked`, inline `keccak256`) are not `Loc`s, so
  `keccak_word_inj` does not separate them from layout regions.
- **The probability bound.** The premise is about keccak's actual outputs; it
  is not implied by anything proved here. The bounds of
  [hash-collision-bound.md](hash-collision-bound.md) are about a uniformly
  random function on a finite domain; they apply with the domain `Pre` (or
  the encoded byte strings, `encode` being injective on words), not to
  `keccak256Nat`. No theorem restates them through `encode`
  (e.g. `(dedup (P.map encode)).length = (dedup P).length`).
- G46.05 records preimages as bytes; a `UInt8.toNat` map relates them to the
  `List Nat` inputs here.

### Handoff — checkpoint 3

Work queue item 3 is done: `keccakH`, the injective encoding, the premises
read on bytes, `keccak_word_inj`, and 13 `#guard` vectors.

Gates on the checkpoint's final commit: `lean_diagnostic_messages` clean on
`Solidity/Storage/HashedKeccak.lean` (the vectors evaluate keccak-256 in the
language server in a few seconds); pins `keccakH_lt` at `[propext,
Quot.sound]`, `encode_inj`, `collisionFree_keccakH_iff`,
`regionsDisjoint_keccakH_iff`, `keccak_word_inj` at `[propext,
Classical.choice, Quot.sound]`; no `sorry`, new axiom, `native_decide`,
`decide` tactic, `grind`, `implemented_by` or `maxHeartbeats`.
`check-layers`: 159 core modules, 0 reach the elaborator
(`Solidity.Storage.HashedKeccak` in `CORE`); `check-orphans`: 738 reachable,
0 orphaned; `check-trust`: 0 findings; `check-doc-paths`: 46, the base count.

### Review (checkpoint 3)

A read-only finder and a separate skeptic reviewed commit `b335a9d` without
the Lean server. No proof bug; the finder re-checked all digests with its own
Keccak implementation. Confirmed findings, fixed in the following commit:

| Finding | Fix |
|---|---|
| "The premise on the run's `KECCAK256` inputs is exactly what the layout needs" overstated: a run hashes more, and `P.map encode ⊆ X` is not proved (skeptic 1). | Reworded (module docstring, table); `mono` route stated; other hashed slots listed as a limitation. |
| Keys must be below `2^256` (truncation aliases) and this was unstated (skeptic 2, finder 2). | Stated in the docstring and the `keccak_word_inj` row. |
| No theorem carries the random-oracle bound through `encode` (skeptic 3). | Limitation "The probability bound". |
| The vectors' generation was unrecorded and "solc's documentation" was inaccurate (skeptic 5). | The pycryptodome call is recorded above; wording now "common tooling". |
| `bytesN` keys are left-aligned, not the value (finder 1a); no `bytes32` vector (finder 1b). | Stated; `bytes32` and `bytes4` vectors added. |
| The `STy.locate` vector compared two computed words and pinned no digest (finder 3). | Compared with the literal digest. |
| `encode_inj` and `regionsDisjoint_keccakH_iff` had no axiom pins (finder 4). | Pinned. |

## Checkpoint 4 — G27.01–G27.03 separation

Module `Solidity/Storage/HashedSeparation.lean` (imports
`Solidity.Storage.HashedLayout`, in `CORE`). `Occ t l x`: the slot term `x`
belongs to a value of type `t` at `l` (a word's slot; a struct member's
terms; a static or dynamic array element's terms, the dynamic index below
`lmax`; a dynamic array's length slot; every mapping entry's terms). The
argument follows `Solidity/Evm/Layout.lean`'s for `Evm.Slot`: `occ_reach`
(every occupied term is reached by hashing from one in-place word `l + j`,
`j < size`) and `reach_unique` (one ancestor per hash depth).

| Name | Statement |
|---|---|
| `occ_fields_disjoint` (G27.01) | Members `i ≠ i'` of a struct occupy disjoint slot terms. |
| `occ_keys_disjoint` (G27.02) | Entries at keys `k ≠ k'` (any word, any value types, nested paths below) occupy disjoint slot terms. |
| `occ_map_slot_entry` | A mapping's own slot is no entry's. |
| `occ_sarr_disjoint`, `occ_darr_disjoint` (G27.03) | Elements at indices `i ≠ i'` occupy disjoint slot terms. |
| `occ_darr_len_elem` (G27.03) | A dynamic array's length slot is no element's. |
| `occ_bounded` | `t.Fits L → Placed L R t l → Occ t l x → Loc.Bounded L R x`. |
| `occ_word_ne` | Under the region premise, distinct occupied terms (with preimages in `P`) have distinct words. |
| `keys_word_ne` | G27.02 on words: entries at different keys of a placed mapping have different words. |

The symbolic statements use no hash premise and no `Classical.choice`
(pins `[propext, Quot.sound]`); the word-level ones add the region premise
through `Loc.word_inj`.

Limitations (checkpoint 4): these are separation statements only. The
*representation* half of G27.01–G27.03 (a source value's reading agrees
with the words of its occupied terms, and a write to one member, entry or
element preserves the others' readings) needs the source and EVM store
semantics, which this dependency-free model does not have; `occ_word_ne` is
the frame fact such a proof would use. Widths and packing (G27.01 "widths")
are not modelled. G27.04 (recursive paths) and G27.05 (composition with the
compiler) remain.
