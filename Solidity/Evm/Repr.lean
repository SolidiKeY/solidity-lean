import Solidity.Evm.Layout
import Solidity.Evm.StorageLemmas

/-!
# The machine's storage represents the typed storage

`ReprAt st L T s v`: the typed storage value `v : SVal T` is laid out in the
machine storage `st` from slot `s` — every `uint`, `int` (its two's
complement word) and `bool` at its slot, every array's length at its own
slot (below `L`) and its live elements at theirs, every entry of a
`uint`-keyed mapping at its hashed slot.  `ReprStore` says it of every state
variable.  This is mini-solkey's `Sim.store` read by type rather than by
path, which is what makes `delete` and `pop` (writes of a whole subtree) the
same lemma as `alice.age = 1;` (a write of one slot).  The value's type says
the rest: a struct has every member, a fixed-size array its length
(`Semantics/Storage.lean`).

A typed path is laid out by `PathAt` (`PathSlot` from a state variable): a
member at its offset, a key at its hash, an element at its place; a `free`
path indexes no array.  The two lemmas the compiler proof needs:

* `find_repr`: a typed reference reads, live, a value its slot represents —
  or, if it indexes an array, `none` out of bounds;
* `save_repr`: the typed save of a subtree at a reference it can read is the
  machine's write of the slots that subtree occupies (`Occ`), and leaves
  every other slot as it was.  The step with content is the layout's
  injectivity (`occ_members_disjoint` and its siblings, `Evm/Layout.lean`).

A fixed-size array is laid out inline, as solc lays it out: its elements one
after the other from its own slot, no length slot, its length its type's.

What `ReprAt` does not constrain, it does not need to: an array's popped
slots (the typed value's `shadow`), a mapping keyed by other than `uint`.
The compiler rejects every read of those: a `push()` of a struct (which
revives a popped slot as it is) and an alias bound through an index after a
`pop` or a `delete` (which may point past the end).

Beyond the two lemmas: a static value is copied by copying its leaves
(`move_repr`, `overlay_repr`), a `push` grows the array by one element
(`push_repr`), and no slot is both a primitive's and an array's length
(`OccAt.kind_unique`), so a path in bounds stays in bounds while no length
shrinks (`live_mono`).
-/

namespace Solidity
namespace Evm

open Semantics (structDef lookupBy setBy tyRank)
open Semantics (lookupBy_setBy_self lookupBy_setBy_ne lookupBy_eq_some_mem)

variable {L : Nat}

/-! ## The representation -/

/-- A stack word represents a value of primitive type `p`: a `uint` as
itself (below `2^256` by its type), a `bool` as `1` or `0`, an `int` as its
two's complement word (the word's signed reading, `sgn`, is the value). -/
def ReprV : (p : PrimTy) → p.Denote → Word → Prop
  | .uint, v, w => w = .val v.1.toNat
  | .bool, b, w => w = .val (bword b)
  | .int, v, w => ∃ a, w = .val a ∧ a < W ∧ v.1 = sgn a

/-- An index found in a list is below its length. -/
theorem lt_of_getElem? {α : Type} {l : List α} {i : Nat} {x : α} (h : l[i]? = some x) :
    i < l.length :=
  (List.getElem?_eq_some_iff.1 h).1

/-- `ReprAt st L T s v`: the storage value `v` of type `T` is laid out in `st`
from slot `s`, and every dynamic array in it holds fewer than `L` elements
(`L` at most solc's `2^64`: what a `push` needs to agree with solc's). -/
inductive ReprAt (st : WordStore) (L : Nat) : (T : Ty) → Slot → SVal T → Prop
  | prim {p : PrimTy} {s : Slot} {v : p.Denote} :
      ReprV p v (.val (st s)) → ReprAt st L (.prim p) s (.prim v)
  | struct {n : Name} {s : Slot} {fs : SFields (structDef n)} :
      (∀ f T (h : lookupBy f (structDef n) = some T),
        ReprAt st L T (s.add (offset n f)) (fs.get h)) →
      ReprAt st L (.ref (.struct n)) s (.struct fs)
  | array {E : Ty} {k : Nat} {s : Slot} {e : SVec E k} {sh : SList E} {hk : k < 2 ^ 256} :
      st s = k → k < L →
      (∀ i x, e.toList[i]? = some x → ReprAt st L E (.data s (i * size E)) x) →
      ReprAt st L (.ref (.array E)) s (.array e sh hk)
  | fixed {E : Ty} {k : Nat} {s : Slot} {e : SVec E k} :
      (∀ i x, e.toList[i]? = some x → ReprAt st L E (s.add (i * size E)) x) →
      ReprAt st L (.ref (.fixed E k)) s (.fixed e)
  | map {K : PrimTy} {V : Ty} {s : Slot} {m : SMap K V} {d : SVal V} :
      (K = .uint → ∀ k : Nat, k < W →
        ReprAt st L V (.hash k s 0) ((lookupBy (k : Int) m.hashed).getD d)) →
      ReprAt st L (.ref (.mapping K V)) s (.map m d)

/-- A representation looks only at the slots the value occupies.

Example: `bob` is represented in slots `[14, 17)`; a write to `alice.age`
(slot `13`) keeps it represented. -/
theorem ReprAt.frame {st st' : WordStore} {T : Ty} {s : Slot} {v : SVal T}
    (h : ReprAt st L T s v) (hf : ∀ x, Occ T s x → st' x = st x) : ReprAt st' L T s v := by
  induction h with
  | prim h => exact .prim (by rw [hf _ .prim]; exact h)
  | struct _ ih => exact .struct fun f T hT => ih f T hT fun x hx => hf x (.field hT hx)
  | array hl hW _ ih =>
    exact .array (by rw [hf _ .len, hl]) hW fun i x hx => ih i x hx fun y hy => hf y (.elem i hy)
  | @fixed E k s e _ ih =>
    exact .fixed fun i x hx => ih i x hx fun y hy =>
      hf y (.felem i (by have := lt_of_getElem? hx; rwa [SVec.length_toList] at this) hy)
  | map _ ih => exact .map fun hK k hk => ih hK k hk fun y hy => hf y (.entry k hy)

/-- A looser bound on the arrays keeps a representation: after a `push`, the
bound is one more. -/
theorem ReprAt.mono {st : WordStore} {L' : Nat} {T : Ty} {s : Slot} {v : SVal T}
    (h : ReprAt st L T s v) (hL : L ≤ L') : ReprAt st L' T s v := by
  induction h with
  | prim h => exact .prim h
  | struct _ ih => exact .struct ih
  | array hl hW _ ih => exact .array hl (by omega) ih
  | fixed _ ih => exact .fixed ih
  | map _ ih => exact .map ih

/-- Every state variable is represented at its slot. -/
def ReprStore (C : Contract) (L : Nat) (st : WordStore) (stor : Solidity.Storage C) : Prop :=
  ∀ r T (h : C.rootType r = some T), ReprAt st L T (rootSlot C r) (stor.get h)

/-- `ReprAt.mono` for every state variable. -/
theorem ReprStore.mono {C : Contract} {st : WordStore} {stor : Solidity.Storage C} {L' : Nat}
    (h : ReprStore C L st stor) (hL : L ≤ L') : ReprStore C L' st stor :=
  fun r T hr => (h r T hr).mono hL

/-- A state variable's slot is an offset from slot `0`: `alice` is `0 + 11`. -/
theorem rootSlot_eq (C : Contract) (r : Name) :
    rootSlot C r = (Slot.root 0).add (offsetIn C.vars r) := by
  simp only [rootSlot, Slot.add, Nat.zero_add]

/-! ## Paths through the storage tree -/

/-- `PathAt a p s s'`: the typed path `p`, from a value laid out at `s`,
reaches slot `s'`.  `free` paths (`a = true`) index no array. -/
inductive PathAt : Bool → {T U : Ty} → Path T U → Slot → Slot → Prop
  | nil {a : Bool} {T : Ty} {s : Slot} : PathAt a (Path.nil (T := T)) s s
  | field {a : Bool} {n f : Name} {T U : Ty} {h : lookupBy f (structDef n) = some T}
      {p : Path T U} {s s' : Slot} :
      PathAt a p (s.add (offset n f)) s' → PathAt a (Path.field h p) s s'
  | key {a : Bool} {V U : Ty} {k : PrimTy.uint.Denote} {p : Path V U} {s s' : Slot} :
      0 ≤ k.1 → k.1 < W → PathAt a p (.hash k.1.toNat s 0) s' →
      PathAt a (Path.key (K := .uint) k p) s s'
  | elem {E U : Ty} {i : PrimTy.uint.Denote} {p : Path E U} {s s' : Slot} :
      0 ≤ i.1 → i.1 < W → PathAt false p (.data s (i.1.toNat * size E)) s' →
      PathAt false (Path.at i p) s s'
  | felem {E U : Ty} {n : Nat} {i : PrimTy.uint.Denote} {p : Path E U} {s s' : Slot} :
      0 ≤ i.1 → i.1 < n → PathAt false p (s.add (i.1.toNat * size E)) s' →
      PathAt false (Path.atF (n := n) i p) s s'

/-- `PathSlot C a r s`: the storage reference `r` has slot `s`. -/
def PathSlot (C : Contract) (a : Bool) {U : Ty} (r : SRef C U) (s : Slot) : Prop :=
  PathAt a r.path (rootSlot C r.root) s

/-- A path that indexes no array is a path: `folks[7].age`. -/
theorem PathAt.weaken {a : Bool} {T U : Ty} {p : Path T U} {s s' : Slot} (h : PathAt a p s s') :
    PathAt false p s s' := by
  induction h with
  | nil => exact .nil
  | field _ ih => exact .field ih
  | key h0 h1 _ ih => exact .key h0 h1 ih
  | elem h0 h1 _ ih => exact .elem h0 h1 ih
  | felem h0 h1 _ ih => exact .felem h0 h1 ih

/-- A path followed by another. -/
theorem PathAt.trans {a : Bool} {T U W : Ty} {p : Path T U} {q : Path U W} {s s' s'' : Slot}
    (h : PathAt a p s s') (hq : PathAt a q s' s'') : PathAt a (p.append q) s s'' := by
  induction h with
  | nil => rw [Path.append_nil]; exact hq
  | field _ ih => rw [Path.append_field]; exact .field (ih hq)
  | key h0 h1 _ ih => rw [Path.append_key]; exact .key h0 h1 (ih hq)
  | elem h0 h1 _ ih => rw [Path.append_at]; exact .elem h0 h1 (ih hq)
  | felem h0 h1 _ ih => rw [Path.append_atF]; exact .felem h0 h1 (ih hq)

namespace PathSlot

variable {C : Contract}

theorem weaken {a : Bool} {U : Ty} {r : SRef C U} {s : Slot} (h : PathSlot C a r s) :
    PathSlot C false r s :=
  PathAt.weaken h

/-- A path that indexes no array may be used where any path may: `folks[7]`
as an alias target and as a read. -/
theorem ofTrue {U : Ty} {r : SRef C U} {s : Slot} (h : PathSlot C true r s) :
    ∀ free, PathSlot C free r s
  | true => h
  | false => h.weaken

/-- A state variable's slot. -/
theorem root {r : Name} {T : Ty} (h : C.rootType r = some T) {a : Bool} :
    PathSlot C a (SRef.ofRoot r h) (rootSlot C r) :=
  PathAt.nil

/-- `b.f` is at `f`'s offset from `b`'s slot. -/
theorem field {a : Bool} {n f : Name} {T : Ty} {r : SRef C (.ref (.struct n))} {s : Slot}
    (hp : PathSlot C a r s) (h : C.fieldType n f = some T) :
    PathSlot C a (r.field h) (s.add (offset n f)) :=
  PathAt.trans hp (.field .nil)

/-- `b[k]` of a `uint`-keyed mapping is at `keccak(k, b)`. -/
theorem key {a : Bool} {V : Ty} {r : SRef C (.ref (.mapping .uint V))} {s : Slot}
    (hp : PathSlot C a r s) {k : PrimTy.uint.Denote} (h0 : 0 ≤ k.1) (h1 : k.1 < W) :
    PathSlot C a (r.index .map k) (.hash k.1.toNat s 0) := by
  unfold PathSlot SRef.index SRef.append
  rw [Path.index_map]
  exact PathAt.trans hp (.key h0 h1 .nil)

/-- `b[i]` of a dynamic array is at `keccak(b) + i·size`. -/
theorem elem {E : Ty} {r : SRef C (.ref (.array E))} {s : Slot}
    (hp : PathSlot C false r s) {i : PrimTy.uint.Denote} (h0 : 0 ≤ i.1) (h1 : i.1 < W) :
    PathSlot C false (r.index (.arr .dyn) i) (.data s (i.1.toNat * size E)) := by
  unfold PathSlot SRef.index SRef.append
  rw [Path.index_dyn]
  exact PathAt.trans hp (.elem h0 h1 .nil)

/-- `b[i]` of a fixed-size array is at `b + i·size`. -/
theorem felem {E : Ty} {n : Nat} {r : SRef C (.ref (.fixed E n))} {s : Slot}
    (hp : PathSlot C false r s) {i : PrimTy.uint.Denote} (h0 : 0 ≤ i.1) (h1 : i.1 < n) :
    PathSlot C false (r.index (.arr .fixed) i) (s.add (i.1.toNat * size E)) := by
  unfold PathSlot SRef.index SRef.append
  rw [Path.index_fixed]
  exact PathAt.trans hp (.felem h0 h1 .nil)

end PathSlot

/-- What a path reaches, the value it starts from occupies. -/
theorem PathAt.occ {a : Bool} {T U : Ty} {p : Path T U} {s s' : Slot} (hp : PathAt a p s s')
    {x : Slot} (h : Occ U s' x) : Occ T s x := by
  induction hp with
  | nil => exact h
  | @field _ _ _ _ _ hf _ _ _ _ ih => exact .field hf (ih h)
  | key _ _ _ ih => exact .entry _ (ih h)
  | elem _ _ _ ih => exact .elem _ (ih h)
  | felem _ h1 _ ih => exact .felem _ (by omega) (ih h)

/-! ## Reading -/

/-- A mapping's entry, live: the entry written, or the mapping's default. -/
theorem findLiveM_key {K : PrimTy} {V U : Ty} (m : SMap K V) (d : SVal V) (k : K.Denote)
    (p : Path V U) :
    (SVal.map (K := K) m d).findLiveM (.key k p) =
      ((lookupBy k m.toList).getD d).findLiveM p := by
  simp only [SVal.findLiveM]
  cases lookupBy k m.toList <;> rfl

/-- A typed path reads, live, a value its slot represents, or (if it indexes
an array) `none` out of bounds. -/
theorem ReprAt.findLive {st : WordStore} {a : Bool} {T U : Ty} {p : Path T U} {s s' : Slot}
    (hp : PathAt a p s s') :
    ∀ {v : SVal T}, ReprAt st L T s v →
      (∃ w, v.findLiveM p = some w ∧ ReprAt st L U s' w) ∨ (a = false ∧ v.findLiveM p = none) := by
  induction hp with
  | nil => intro v hv; exact .inl ⟨v, by cases v <;> rfl, hv⟩
  | @field a n f T U h p s s' _ ih =>
    intro v hv
    cases hv with
    | struct hall =>
      simp only [SVal.findLiveM]
      exact ih (hall f T h)
  | @key a V U k p s s' h0 h1 _ ih =>
    intro v hv
    cases hv with
    | @map _ _ _ m d hall =>
      rw [findLiveM_key]
      have := hall rfl k.1.toNat (by omega)
      rw [Int.toNat_of_nonneg h0, show (k.1 : Int) = PrimTy.key k from rfl,
        SMap.lookupBy_hashed] at this
      exact ih this
  | @elem E U i p s s' h0 h1 _ ih =>
    intro v hv
    cases hv with
    | array hl hW hall =>
      simp only [SVal.findLiveM, if_pos h0, true_and]
      split
      · rename_i x hx
        exact (ih (hall _ x hx)).imp id (·.2)
      · exact .inr rfl
  | @felem E U n i p s s' h0 h1 _ ih =>
    intro v hv
    cases hv with
    | @fixed _ _ _ e hall =>
      simp only [SVal.findLiveM, if_pos h0, true_and]
      split
      · rename_i x hx
        exact (ih (hall _ x hx)).imp id (·.2)
      · rename_i hx
        rw [List.getElem?_eq_none_iff, SVec.length_toList] at hx
        omega

/-- A typed reference reads, live, a value its slot represents, or (if it
indexes an array) `none` out of bounds.

Example: `folks[7].age` reads what slot `keccak(7, 7) + 2` holds; with three
`persons`, `persons[5].age` is `none`. -/
theorem find_repr {C : Contract} {st : WordStore} {stor : Solidity.Storage C}
    (hs : ReprStore C L st stor) {a : Bool} {U : Ty} {r : SRef C U} {s : Slot}
    (hp : PathSlot C a r s) :
    (∃ w, stor.findLive r = some w ∧ ReprAt st L U s w) ∨ (a = false ∧ stor.findLive r = none) := by
  rw [Sto.findLive_eq]
  exact ReprAt.findLive hp (hs r.root r.ty r.hroot)

/-! ## Writing -/

/-- The live slots of an array with one live slot replaced. -/
theorem take_set_append {α : Type} (l₁ l₂ : List α) {i : Nat} (hi : i < l₁.length) (x : α) :
    ((l₁ ++ l₂).set i x).take l₁.length = l₁.set i x := by
  rw [List.set_append_left _ _ hi,
    List.take_append_of_le_length (by rw [List.length_set]; exact Nat.le_refl _),
    List.take_of_length_le (by rw [List.length_set]; exact Nat.le_refl _)]

/-- A typed save at a path is the machine's write of the slots the path's
value occupies (the value-level `save_repr`). -/
theorem ReprAt.save {st st' : WordStore} {a : Bool} {T U : Ty} {p : Path T U} {s s' : Slot}
    (hp : PathAt a p s s') :
    ∀ {v : SVal T} {new : SVal U}, ReprAt st L T s v → (∃ old, v.findLiveM p = some old) →
      ReprAt st' L U s' new → (∀ x, ¬ Occ U s' x → st' x = st x) →
      ∃ v', v.saveM p new = some v' ∧ ReprAt st' L T s v' := by
  induction hp with
  | nil =>
    intro v new _ _ hnew _
    exact ⟨new, by cases v <;> rfl, hnew⟩
  | @field a n f T U h p s s' hp ih =>
    intro v new hv hfind hnew hout
    cases hv with
    | @struct _ _ fs hall =>
      obtain ⟨old, hold⟩ := hfind
      simp only [SVal.findLiveM] at hold
      obtain ⟨x', hx', hrep⟩ := ih (hall f T h) ⟨old, hold⟩ hnew hout
      refine ⟨.struct (fs.set h x'), by simp only [SVal.saveM, hx']; rfl, .struct fun g Tg hg => ?_⟩
      by_cases hgf : g = f
      · subst hgf
        obtain rfl : Tg = T := Option.some.inj (hg.symm.trans h)
        rw [SFields.get_set_same]
        exact hrep
      · rw [SFields.get_set_ne _ h hg (Ne.symm hgf)]
        exact (hall g Tg hg).frame fun y hy => hout y fun hy' =>
          occ_members_disjoint hg h hgf hy (hp.occ hy')
  | @key a V U k p s s' h0 h1 hp ih =>
    intro v new hv hfind hnew hout
    cases hv with
    | @map _ _ _ m d hall =>
      obtain ⟨old, hold⟩ := hfind
      rw [findLiveM_key] at hold
      have hcur := hall rfl k.1.toNat (by omega)
      rw [Int.toNat_of_nonneg h0, show (k.1 : Int) = PrimTy.key k from rfl,
        SMap.lookupBy_hashed] at hcur
      obtain ⟨x', hx', hrep⟩ := ih hcur ⟨old, hold⟩ hnew hout
      refine ⟨.map (.ofList (setBy k x' m.toList)) d, ?_, .map fun _ k' hk' => ?_⟩
      · simp only [SVal.saveM]
        cases hl : lookupBy k m.toList <;> rw [hl] at hx' <;> simp only [Option.getD] at hx' <;>
          simp only [hx'] <;> rfl
      · rw [SMap.hashed_ofList_setBy, SMap.ofList_toList]
        by_cases hkk : (k' : Int) = PrimTy.key k
        · have : k' = k.1.toNat := by
            have : (k' : Int) = k.1 := hkk
            omega
          subst this
          rw [hkk, lookupBy_setBy_self]
          exact hrep
        · have hkk' : (k' : Int) ≠ k.1 := hkk
          rw [lookupBy_setBy_ne hkk]
          exact (hall rfl k' hk').frame fun y hy => hout y fun hy' =>
            occ_entries_disjoint (by omega) hy (hp.occ hy')
  | @elem E U i p s s' h0 h1 hp ih =>
    intro v new hv hfind hnew hout
    cases hv with
    | @array _ k _ e sh hk hl hW hall =>
      obtain ⟨old, hold⟩ := hfind
      simp only [SVal.findLiveM, if_pos h0] at hold
      split at hold
      · rename_i x hx
        obtain ⟨x', hx', hrep⟩ := ih (hall _ x hx) ⟨old, hold⟩ hnew hout
        have hi : i.1.toNat < e.toList.length := lt_of_getElem? hx
        have hx2 : (e.toList ++ sh.toList)[i.1.toNat]? = some x := by
          rw [List.getElem?_append_left hi]; exact hx
        have hlen : e.toList.length = k := SVec.length_toList e
        refine ⟨_, by simp only [SVal.saveM, if_pos h0, hx2, hx']; rfl, ?_⟩
        have htake : ((e.toList ++ sh.toList).set i.1.toNat x').take k = e.toList.set i.1.toNat x' := by
          have := take_set_append e.toList sh.toList hi x'
          rwa [hlen] at this
        refine .array ?_ ?_ fun j y hy => ?_
        · rw [hout s fun ho => occ_len_elem (hp.occ ho), hl, htake, List.length_set, hlen]
        · rw [htake, List.length_set, hlen]; exact hW
        · rw [SVec.toList_ofList, htake, List.getElem?_set] at hy
          by_cases hji : i.1.toNat = j
          · subst hji
            rw [if_pos rfl, if_pos hi] at hy
            cases hy
            exact hrep
          · rw [if_neg hji] at hy
            exact (hall j y hy).frame fun z hz => hout z fun hz' =>
              occ_elems_disjoint hji (hp.occ hz') hz
      · cases hold
  | @felem E U n i p s s' h0 h1 hp ih =>
    intro v new hv hfind hnew hout
    cases hv with
    | @fixed _ _ _ e hall =>
      obtain ⟨old, hold⟩ := hfind
      simp only [SVal.findLiveM, if_pos h0] at hold
      split at hold
      · rename_i x hx
        obtain ⟨x', hx', hrep⟩ := ih (hall _ x hx) ⟨old, hold⟩ hnew hout
        refine ⟨.fixed (e.set i.1.toNat x'), by simp only [SVal.saveM, if_pos h0, hx, hx']; rfl,
          .fixed fun j y hy => ?_⟩
        rw [SVec.toList_set, List.getElem?_set] at hy
        by_cases hji : i.1.toNat = j
        · subst hji
          rw [if_pos rfl, if_pos (lt_of_getElem? hx)] at hy
          cases hy
          exact hrep
        · rw [if_neg hji] at hy
          exact (hall j y hy).frame fun z hz => hout z fun hz' =>
            occ_felems_disjoint hji (hp.occ hz') hz
      · cases hold

/-- **A write is represented by the slots it occupies.**  If the typed run
writes the subtree `new` at a reference it can read, and the machine storage
`st'` represents `new` at the reference's slot and agrees with `st` on every
slot the reference's value does not occupy, then the save succeeds and `st'`
represents the whole storage after it.

Example: `alice.age = 5;` stores `5` in slot `13` and nothing else: slot `11`
(`alice.account.balance`) and slots `[14, 17)` (`bob`) keep their words, and
the typed `alice.account` and `bob` do not change either.  `delete alice;`
is the same lemma with `new` the default `Person` and `st'` zero at three
slots. -/
theorem save_repr {C : Contract} {st : WordStore} {stor : Solidity.Storage C}
    (hs : ReprStore C L st stor) {a : Bool} {U : Ty} {r : SRef C U} {s : Slot}
    (hp : PathSlot C a r s) {st' : WordStore} {new : SVal U}
    (hfind : ∃ old, stor.findLive r = some old) (hnew : ReprAt st' L U s new)
    (hout : ∀ x, ¬ Occ U s x → st' x = st x) :
    ∃ stor', stor.save r new = some stor' ∧ ReprStore C L st' stor' := by
  rw [Sto.findLive_eq] at hfind
  obtain ⟨v', hv', hrep⟩ := ReprAt.save hp (hs r.root r.ty r.hroot) hfind hnew hout
  refine ⟨stor.set r.hroot v', by rw [Sto.save_eq, hv']; rfl, fun r' T' h' => ?_⟩
  by_cases hr : r' = r.root
  · subst hr
    obtain rfl : T' = r.ty := Option.some.inj (h'.symm.trans r.hroot)
    rw [SFields.get_set_same]
    exact hrep
  · rw [SFields.get_set_ne _ r.hroot h' (Ne.symm hr)]
    refine (hs r' T' h').frame fun x hx => hout x fun hx' => ?_
    have o := PathAt.occ hp hx'
    rw [rootSlot_eq] at hx o
    exact occ_members_disjoint h' r.hroot hr hx o

/-! ## `delete` and `pop` -/

/-- `st` with `0` written at `s + o` for each `o`, in order. -/
def zeroAt (st : WordStore) (s : Slot) : List Nat → WordStore
  | [] => st
  | o :: os => zeroAt (WordStore.write st (s.add o) 0) s os

/-- Zeroing some slots leaves the others: `delete alice;` leaves `bob.age`. -/
theorem zeroAt_other {st : WordStore} {s x : Slot} :
    ∀ {os : List Nat}, (∀ o ∈ os, x ≠ s.add o) → zeroAt st s os x = st x
  | [], _ => rfl
  | o :: os, h => by
    simp only [zeroAt]
    rw [zeroAt_other fun o' ho' => h o' (List.mem_cons_of_mem _ ho')]
    exact WordStore.write_other _ _ (h o List.mem_cons_self)

/-- Every zeroed slot holds `0`: `delete alice;` zeroes `alice.age`. -/
theorem zeroAt_zero {s x : Slot} :
    ∀ {st : WordStore} {os : List Nat}, (∃ o ∈ os, x = s.add o) → zeroAt st s os x = 0
  | _, [], ⟨_, ho, _⟩ => by cases ho
  | st, o :: os, h => by
    simp only [zeroAt]
    by_cases h' : ∃ o' ∈ os, x = s.add o'
    · exact zeroAt_zero h'
    · obtain ⟨o', ho', hx⟩ := h
      rcases List.mem_cons.1 ho' with rfl | ho'
      · rw [zeroAt_other fun o'' ho'' hx' => h' ⟨o'', ho'', hx'⟩, hx, WordStore.write_same, Nat.zero_mod]
      · exact absurd ⟨o', ho', hx⟩ h'

/-- The default of a primitive type is the word `0`. -/
theorem ReprV.dflt_zero (p : PrimTy) : ReprV p (PrimTy.dflt p) (.val 0) := by
  cases p with
  | uint => rfl
  | bool => rfl
  | int => exact ⟨0, rfl, W_pos, by decide⟩

/-- The first leaf of a primitive is its own slot. -/
theorem mem_leavesF_prim (fuel : Nat) (p : PrimTy) : 0 ∈ leavesF fuel (.prim p) := by
  simp only [leavesF, List.mem_singleton]

/-- **`delete` is represented by zeroing its leaves.**  If `st'` is zero at
every slot `delete` writes (`leavesF`) and agrees with `st` on the rest of what
the value occupies, it represents the value's default (`SVal.defaultOf`).

Example: `delete wallet;` zeroes `wallet.owner`'s slot and leaves
`wallet.stash`'s entries where they are, and `SVal.defaultOf` keeps the
mapping's entries too. -/
theorem zero_repr {st st' : WordStore} {T : Ty} {s : Slot} {v : SVal T} (h : ReprAt st L T s v) :
    ∀ fuel, tyRank T < fuel → (∀ o ∈ leavesF fuel T, st' (s.add o) = 0) →
      (∀ x, Occ T s x → (∀ o ∈ leavesF fuel T, x ≠ s.add o) → st' x = st x) →
      ReprAt st' L T s v.defaultOf := by
  induction h with
  | @prim p s v _ =>
    intro fuel _ hz _
    rw [SVal.defaultOf_prim]
    have h0 : st' s = 0 := by have := hz 0 (mem_leavesF_prim fuel p); rwa [Slot.add_zero] at this
    exact .prim (by rw [h0]; exact ReprV.dflt_zero p)
  | @struct n s fs hall ih =>
    intro fuel hr hz ho
    cases fuel with
    | zero => exact absurd hr (Nat.not_lt_zero _)
    | succ f' =>
      rw [SVal.defaultOf_struct]
      refine .struct fun g Tg hg => ?_
      rw [SFields.get_defaultOf]
      have hmem := lookupBy_eq_some_mem hg
      have hrank : tyRank Tg < f' := by
        have := tyRank_member hmem; simp only [tyRank] at hr this; omega
      have hleaf : ∀ o ∈ leavesF f' Tg, offset n g + o ∈ leavesF (f' + 1) (.ref (.struct n)) := by
        intro o ho
        simp only [leavesF, List.mem_flatMap]
        exact ⟨(g, Tg), hmem, by simp only [hg]; exact List.mem_map_of_mem ho⟩
      refine ih g Tg hg f' hrank (fun o ho' => ?_) (fun x hx hno => ?_)
      · rw [Slot.add_add]; exact hz _ (hleaf o ho')
      · refine ho x (.field hg hx) fun o hol hxo => ?_
        simp only [leavesF, List.mem_flatMap] at hol
        obtain ⟨⟨h, _⟩, _, hin⟩ := hol
        simp only at hin
        split at hin
        · rename_i Th hTh
          obtain ⟨o'', ho'', rfl⟩ := List.mem_map.1 hin
          by_cases hhg : h = g
          · subst hhg; rw [hg] at hTh; cases hTh
            exact hno o'' ho'' (by rw [Slot.add_add]; exact hxo)
          · have hocc := leavesF_occ f' Th (s.add (offset n h)) o'' ho''
            rw [Slot.add_add, ← hxo] at hocc
            exact occ_members_disjoint hg hTh (Ne.symm hhg) hx hocc
        · cases hin
  | @array E k s e sh hk hl hW hall =>
    intro fuel _ hz _
    rw [SVal.defaultOf_array]
    have h0 : st' s = 0 := by
      have := hz 0 (by simp only [leavesF, List.mem_singleton]); rwa [Slot.add_zero] at this
    refine .array h0 (by omega) fun i x hx => ?_
    rw [SVec.toList_nil, List.getElem?_nil] at hx
    cases hx
  | @fixed E k s e hall ih =>
    intro fuel hr hz ho
    cases fuel with
    | zero => exact absurd hr (Nat.not_lt_zero _)
    | succ f' =>
      rw [SVal.defaultOf_fixed]
      refine .fixed fun i y hy => ?_
      rw [SVec.toList_defaultOf, List.getElem?_map] at hy
      obtain ⟨x, hx, rfl⟩ := Option.map_eq_some_iff.1 hy
      have hin : i < k := by have := lt_of_getElem? hx; rwa [SVec.length_toList] at this
      have hrank : tyRank E < f' := by simp only [tyRank] at hr; omega
      have hleaf : ∀ o ∈ leavesF f' E, i * size E + o ∈ leavesF (f' + 1) (.ref (.fixed E k)) := by
        intro o ho
        simp only [leavesF, List.mem_flatMap, List.mem_range, List.mem_map]
        exact ⟨i, hin, o, ho, rfl⟩
      refine ih i x hx f' hrank (fun o ho' => ?_) (fun z hz' hno => ?_)
      · rw [Slot.add_add]; exact hz _ (hleaf o ho')
      · refine ho z (.felem i hin hz') fun o hol hxo => ?_
        simp only [leavesF, List.mem_flatMap, List.mem_range, List.mem_map] at hol
        obtain ⟨j, hj, o'', ho'', rfl⟩ := hol
        by_cases hji : j = i
        · subst hji; exact hno o'' ho'' (by rw [Slot.add_add]; exact hxo)
        · have hocc := leavesF_occ f' E (s.add (j * size E)) o'' ho''
          rw [Slot.add_add, ← hxo] at hocc
          exact occ_felems_disjoint hji hocc hz'
  | map hall =>
    intro fuel _ _ ho
    rw [SVal.defaultOf_map]
    exact .map fun hK k hk => (hall hK k hk).frame fun x hx =>
      ho x (.entry k hx) fun o hol => by simp only [leavesF, List.not_mem_nil] at hol

/-- **`pop` is represented by decrementing the length.**  The popped
element's slots are left as they are: `ReprAt` constrains only the live
elements, so whatever the slots past the end hold is represented.

Example: with `values = [1, 2]`, `values.pop();` writes `1` to slot `4`;
`keccak(4) + 1` still holds `2`, and nothing reads it. -/
theorem pop_repr {st : WordStore} {E : Ty} {s : Slot} {k : Nat} {e : SVec E k}
    {sh sh' : SList E} {hk : k < 2 ^ 256} (hb : e.toList.dropLast.length < 2 ^ 256)
    (h : ReprAt st L (.ref (.array E)) s (.array e sh hk)) :
    ReprAt (WordStore.write st s (k - 1)) L (.ref (.array E)) s
      (.array (SVec.ofList e.toList.dropLast) sh' hb) := by
  cases h with
  | array hl hW hall =>
    have hlen : e.toList.length = k := SVec.length_toList e
    refine .array (by rw [WordStore.write_same_of_lt _ _ _ (by unfold W; omega), List.length_dropLast, hlen])
      (by rw [List.length_dropLast]; omega) fun j y hy => ?_
    rw [SVec.toList_ofList, List.getElem?_dropLast] at hy
    split at hy
    · exact (hall j y hy).frame fun x hx =>
        WordStore.write_other _ _ fun hxs => by subst hxs; exact occ_len_elem hx
    · cases hy

/-! ## Copies and `push`

A value of a static type (`staticF`: no dynamic array, no mapping) occupies
exactly the slots `leaves` lists, so copying it is copying those words
(`move_repr`), and what the typed run writes, the copy laid over the old
value or laid on fresh slots (`SVal.overlay`, `SVal.strip`), is the copied
value again as far as the slots go (`overlay_repr`). -/

/-- **A static value moves with its leaves.**  If `st'` holds at `d + o` what
`st` holds at `s + o` for every leaf `o`, the value laid out at `s` in `st` is
laid out at `d` in `st'`.  `bob = alice;` copies slots `11`–`13` to `14`–`16`. -/
theorem move_repr {st st' : WordStore} {T : Ty} {s : Slot} {v : SVal T} (h : ReprAt st L T s v) :
    ∀ fuel (d : Slot), tyRank T < fuel → staticF fuel T = true →
      (∀ o ∈ leavesF fuel T, st' (d.add o) = st (s.add o)) → ReprAt st' L T d v := by
  induction h with
  | @prim p s v hv =>
    intro fuel d _ _ hc
    have e : st' d = st s := by
      have := hc 0 (mem_leavesF_prim fuel p); rwa [Slot.add_zero, Slot.add_zero] at this
    exact .prim (by rw [e]; exact hv)
  | @struct n s fs hall ih =>
    intro fuel d hr hs hc
    cases fuel with
    | zero => exact absurd hr (Nat.not_lt_zero _)
    | succ f' =>
      refine .struct fun g Tg hg => ?_
      have hmem := lookupBy_eq_some_mem hg
      have hrank : tyRank Tg < f' := by
        have := tyRank_member hmem; simp only [tyRank] at hr this; omega
      have hst : staticF f' Tg = true := by
        simp only [staticF, List.all_eq_true] at hs; exact hs _ hmem
      refine ih g Tg hg f' (d.add (offset n g)) hrank hst fun o ho => ?_
      have hleaf : offset n g + o ∈ leavesF (f' + 1) (.ref (.struct n)) := by
        simp only [leavesF, List.mem_flatMap]
        exact ⟨(g, Tg), hmem, by simp only [hg]; exact List.mem_map_of_mem ho⟩
      have := hc _ hleaf
      rwa [← Slot.add_add, ← Slot.add_add] at this
  | array => intro fuel d _ hs; cases fuel <;> simp only [staticF, Bool.false_eq_true] at hs
  | map => intro fuel d _ hs; cases fuel <;> simp only [staticF, Bool.false_eq_true] at hs
  | @fixed E k s e hall ih =>
    intro fuel d hr hs hc
    cases fuel with
    | zero => exact absurd hr (Nat.not_lt_zero _)
    | succ f' =>
      refine .fixed fun i x hx => ?_
      have hin : i < k := by have := lt_of_getElem? hx; rwa [SVec.length_toList] at this
      have hrank : tyRank E < f' := by simp only [tyRank] at hr; omega
      have hst : staticF f' E = true := by simpa only [staticF] using hs
      refine ih i x hx f' (d.add (i * size E)) hrank hst fun o ho => ?_
      have hleaf : i * size E + o ∈ leavesF (f' + 1) (.ref (.fixed E k)) := by
        simp only [leavesF, List.mem_flatMap, List.mem_range, List.mem_map]
        exact ⟨i, hin, o, ho, rfl⟩
      have := hc _ hleaf
      rwa [← Slot.add_add, ← Slot.add_add] at this

/-- **A copy lands as the value copied.**  A static value laid out at `d`,
stripped or laid over any old value of its type, is still laid out at `d`:
the slots hold the words, and nothing static has an array's leftovers. -/
theorem overlay_repr {st : WordStore} {T : Ty} {d : Slot} {v : SVal T} (h : ReprAt st L T d v) :
    ∀ fuel, tyRank T < fuel → staticF fuel T = true →
      ReprAt st L T d v.strip ∧ ∀ old : SVal T, ReprAt st L T d (old.overlay v) := by
  induction h with
  | @prim p s v hv =>
    intro _ _ _
    exact ⟨by rw [SVal.strip_prim]; exact .prim hv,
      fun old => by rw [SVal.overlay_prim]; exact .prim hv⟩
  | @struct n d fs hall ih =>
    intro fuel hr hs
    cases fuel with
    | zero => exact absurd hr (Nat.not_lt_zero _)
    | succ f' =>
      have sub : ∀ g Tg (hg : lookupBy g (structDef n) = some Tg),
          ReprAt st L Tg (d.add (offset n g)) (fs.get hg).strip ∧
            ∀ old : SVal Tg, ReprAt st L Tg (d.add (offset n g)) (old.overlay (fs.get hg)) :=
        fun g Tg hg => by
          have hmem := lookupBy_eq_some_mem hg
          have hrank : tyRank Tg < f' := by
            have := tyRank_member hmem; simp only [tyRank] at hr this; omega
          have hst : staticF f' Tg = true := by
            simp only [staticF, List.all_eq_true] at hs; exact hs _ hmem
          exact ih g Tg hg f' hrank hst
      refine ⟨?_, fun old => ?_⟩
      · rw [SVal.strip_struct]
        exact .struct fun g Tg hg => by rw [SFields.get_strip]; exact (sub g Tg hg).1
      · cases old with
        | struct ofs =>
          rw [SVal.overlay_struct]
          exact .struct fun g Tg hg => by rw [SFields.get_overlay]; exact (sub g Tg hg).2 _
  | array => intro fuel _ hs; cases fuel <;> simp only [staticF, Bool.false_eq_true] at hs
  | map => intro fuel _ hs; cases fuel <;> simp only [staticF, Bool.false_eq_true] at hs
  | @fixed E k d e hall ih =>
    intro fuel hr hs
    cases fuel with
    | zero => exact absurd hr (Nat.not_lt_zero _)
    | succ f' =>
      have hrank : tyRank E < f' := by simp only [tyRank] at hr; omega
      have hst : staticF f' E = true := by simpa only [staticF] using hs
      have sub := fun i x hx => ih i x hx f' hrank hst
      refine ⟨?_, fun old => ?_⟩
      · rw [SVal.strip_fixed]
        refine .fixed fun i y hy => ?_
        rw [SVec.toList_strip, List.getElem?_map] at hy
        obtain ⟨x, hx, rfl⟩ := Option.map_eq_some_iff.1 hy
        exact (sub i x hx).1
      · cases old with
        | fixed oel =>
          rw [SVal.overlay_fixed]
          refine .fixed fun i y hy => ?_
          rw [SVec.getElem?_overlayOn] at hy
          cases hx : e.toList[i]? with
          | none => rw [hx, SVal.overlayOpt_none] at hy; cases hy
          | some x =>
            rw [hx] at hy
            cases ho : oel.toList[i]? with
            | none =>
              rw [ho, SVal.overlayOpt_none_some] at hy
              cases hy
              exact (sub i x hx).1
            | some o =>
              rw [ho, SVal.overlayOpt_some_some] at hy
              cases hy
              exact (sub i x hx).2 o

/-- **`push` is represented by one more element.**  If `st'` holds the new
length at `s`, represents the new element at its slot, and agrees with `st`
off the length slot and the new element's slots, it represents the array
grown by the element, under a bound one looser. -/
theorem push_repr {st st' : WordStore} {E : Ty} {s : Slot} {k : Nat} {e : SVec E k}
    {sh sh' : SList E} {hk : k < 2 ^ 256} {new : SVal E}
    (hb : (e.toList ++ [new]).length < 2 ^ 256)
    (h : ReprAt st L (.ref (.array E)) s (.array e sh hk))
    (hlen : st' s = k + 1)
    (hnew : ReprAt st' (L + 1) E (.data s (k * size E)) new)
    (hw : ∀ x, x ≠ s → ¬ Occ E (.data s (k * size E)) x → st' x = st x) :
    ReprAt st' (L + 1) (.ref (.array E)) s (.array (SVec.ofList (e.toList ++ [new])) sh' hb) := by
  cases h with
  | array hl hW hall =>
    have he : e.toList.length = k := SVec.length_toList e
    refine .array (by rw [hlen, List.length_append, he, List.length_singleton])
      (by rw [List.length_append, he, List.length_singleton]; omega) fun j y hy => ?_
    rw [SVec.toList_ofList] at hy
    by_cases hj : j < e.toList.length
    · rw [List.getElem?_append_left hj] at hy
      exact ((hall j y hy).mono (Nat.le_succ L)).frame fun x hx =>
        hw x (fun he' => occ_len_elem (he' ▸ hx)) fun hx' =>
          occ_elems_disjoint (by omega) hx hx'
    · rw [List.getElem?_append_right (by omega)] at hy
      have hj' : j - e.toList.length = 0 := by
        have := lt_of_getElem? hy; rw [List.length_singleton] at this; omega
      rw [hj', List.getElem?_cons_zero, Option.some.injEq] at hy
      subst hy
      obtain rfl : j = k := by omega
      exact hnew

/-! ## Length slots are never primitive slots

An alias bound through an array index (`Person storage p = persons[i];`)
stays in bounds as long as no array shrinks, which the fragment guarantees
until the next `pop` or `delete` (`TyCtx.dropFragile`).  What makes that a
fact about the machine: every write other than a `push`'s length is to a slot
some state variable reaches as a *primitive*, and no such slot is an array's
length slot (`len_prim_disjoint`).  So an array's length only grows, and a
path in bounds stays in bounds (`live_mono`). -/

/-- `OccAt k T s x`: `Occ`, remembering what `x` is: the slot of a primitive
(`k = true`) or the length slot of a dynamic array (`k = false`). -/
inductive OccAt : Bool → Ty → Slot → Slot → Prop
  | prim {p : PrimTy} {s : Slot} : OccAt true (.prim p) s s
  | len {E : Ty} {s : Slot} : OccAt false (.ref (.array E)) s s
  | field {k : Bool} {n f : Name} {T : Ty} {s x : Slot} :
      lookupBy f (structDef n) = some T → OccAt k T (s.add (offset n f)) x →
        OccAt k (.ref (.struct n)) s x
  | elem {k : Bool} {E : Ty} {s x : Slot} (i : Nat) :
      OccAt k E (.data s (i * size E)) x → OccAt k (.ref (.array E)) s x
  | entry {k : Bool} {K : PrimTy} {V : Ty} {s x : Slot} (key : Nat) :
      OccAt k V (.hash key s 0) x → OccAt k (.ref (.mapping K V)) s x
  | felem {k : Bool} {E : Ty} {n : Nat} {s x : Slot} (i : Nat) :
      i < n → OccAt k E (s.add (i * size E)) x → OccAt k (.ref (.fixed E n)) s x

/-- An `OccAt` is an `Occ`. -/
theorem OccAt.occ {k : Bool} {T : Ty} {s x : Slot} (h : OccAt k T s x) : Occ T s x := by
  induction h with
  | prim => exact .prim
  | len => exact .len
  | field hf _ ih => exact .field hf ih
  | elem i _ ih => exact .elem i ih
  | entry key _ ih => exact .entry key ih
  | felem i hi _ ih => exact .felem i hi ih

/-- **A slot is a primitive's or a length, not both.**  Two ways down the
same value that end at the same slot take the same members, keys and indices
(the layout is injective), so they end the same way. -/
theorem OccAt.kind_unique {T : Ty} {s x : Slot} (h₁ : OccAt true T s x) :
    OccAt false T s x → False := by
  generalize hk : true = k at h₁
  induction h₁ with
  | prim => intro h₂; cases h₂
  | len => cases hk
  | @field k n f T s x hf _ ih =>
    intro h₂
    cases h₂ with
    | @field _ _ g T' _ _ hg o₂ =>
      by_cases hfg : f = g
      · subst hfg; rw [hf] at hg; cases hg; exact ih hk o₂
      · exact occ_members_disjoint hf hg hfg (by rename_i o₁; exact o₁.occ) o₂.occ
  | @elem k E s x i o₁ ih =>
    intro h₂
    cases h₂ with
    | len => exact occ_len_elem o₁.occ
    | elem j o₂ =>
      by_cases hij : i = j
      · subst hij; exact ih hk o₂
      · exact occ_elems_disjoint hij o₁.occ o₂.occ
  | @entry k K V s x key o₁ ih =>
    intro h₂
    cases h₂ with
    | entry key' o₂ =>
      by_cases hkk : key = key'
      · subst hkk; exact ih hk o₂
      · exact occ_entries_disjoint hkk o₁.occ o₂.occ
  | @felem k E n s x i hi o₁ ih =>
    intro h₂
    cases h₂ with
    | felem j hj o₂ =>
      by_cases hij : i = j
      · subst hij; exact ih hk o₂
      · exact occ_felems_disjoint hij o₁.occ o₂.occ

/-- What a path reaches, the value it starts from reaches, of the same kind. -/
theorem PathAt.occAt {a : Bool} {T U : Ty} {p : Path T U} {s s' : Slot} (hp : PathAt a p s s')
    {k : Bool} {x : Slot} (h : OccAt k U s' x) : OccAt k T s x := by
  induction hp with
  | nil => exact h
  | @field _ _ _ _ _ hf _ _ _ _ ih => exact .field hf (ih h)
  | key _ _ _ ih => exact .entry _ (ih h)
  | elem _ _ _ ih => exact .elem _ (ih h)
  | felem _ h1 _ ih => exact .felem _ (by omega) (ih h)

/-- The length slot of an array some state variable holds. -/
def LenSlot (C : Contract) (x : Slot) : Prop :=
  ∃ r T, C.rootType r = some T ∧ OccAt false T (rootSlot C r) x

/-- A slot some state variable holds a primitive at. -/
def PrimSlot (C : Contract) (x : Slot) : Prop :=
  ∃ r T, C.rootType r = some T ∧ OccAt true T (rootSlot C r) x

/-- **No write to a primitive touches an array's length.** -/
theorem len_prim_disjoint {C : Contract} {x : Slot} (h₁ : LenSlot C x) (h₂ : PrimSlot C x) :
    False := by
  obtain ⟨r₁, T₁, hr₁, o₁⟩ := h₁
  obtain ⟨r₂, T₂, hr₂, o₂⟩ := h₂
  by_cases hr : r₁ = r₂
  · subst hr; rw [hr₁] at hr₂; cases hr₂; exact o₂.kind_unique o₁
  · rw [rootSlot_eq] at o₁ o₂
    exact occ_members_disjoint hr₁ hr₂ hr o₁.occ o₂.occ

/-- What a reference reaches, of a kind, is held by its state variable. -/
theorem PathSlot.occAt {C : Contract} {a : Bool} {U : Ty} {r : SRef C U} {s : Slot}
    (hp : PathSlot C a r s) {k : Bool} {x : Slot} (h : OccAt k U s x) :
    ∃ T₀, C.rootType r.root = some T₀ ∧ OccAt k T₀ (rootSlot C r.root) x :=
  ⟨r.ty, r.hroot, PathAt.occAt hp h⟩

/-- A primitive a typed reference reaches is at a primitive slot. -/
theorem PathSlot.primSlot {C : Contract} {a : Bool} {p : PrimTy} {r : SRef C (.prim p)}
    {s : Slot} (hp : PathSlot C a r s) : PrimSlot C s :=
  ⟨r.root, r.ty, r.hroot, PathAt.occAt hp OccAt.prim⟩

/-- Every slot a static value occupies holds a primitive. -/
theorem leavesF_occAt : ∀ (fuel : Nat) (T : Ty) (s : Slot) (o : Nat), staticF fuel T = true →
    o ∈ leavesF fuel T → OccAt true T s (s.add o)
  | _, .prim _, s, o, _, h => by
    simp only [leavesF, List.mem_singleton] at h; subst h; rw [Slot.add_zero]; exact OccAt.prim
  | fuel + 1, .ref (.fixed E n), s, o, hs, h => by
    simp only [leavesF, List.mem_flatMap, List.mem_range, List.mem_map] at h
    obtain ⟨i, hi, o', ho', rfl⟩ := h
    exact OccAt.felem i hi (by
      rw [← Slot.add_add]
      exact leavesF_occAt fuel E _ o' (by simpa only [staticF] using hs) ho')
  | fuel + 1, .ref (.struct n), s, o, hs, h => by
    simp only [leavesF, List.mem_flatMap] at h
    obtain ⟨⟨f, Tf⟩, hmem, hf⟩ := h
    simp only at hf
    split at hf
    · rename_i T hT
      obtain ⟨o', ho', rfl⟩ := List.mem_map.1 hf
      have hs' : staticF fuel T = true := by
        simp only [staticF, List.all_eq_true] at hs; exact hs _ (lookupBy_eq_some_mem hT)
      exact OccAt.field hT (by rw [← Slot.add_add]; exact leavesF_occAt fuel T _ o' hs' ho')
    · cases hf
  | 0, .ref (.struct _), _, _, hs, _ => by simp only [staticF, Bool.false_eq_true] at hs
  | 0, .ref (.fixed _ _), _, _, hs, _ => by simp only [staticF, Bool.false_eq_true] at hs
  | f, .ref (.array _), _, _, hs, _ => by cases f <;> simp only [staticF, Bool.false_eq_true] at hs
  | f, .ref (.mapping _ _), _, _, hs, _ => by
    cases f <;> simp only [staticF, Bool.false_eq_true] at hs

/-- **A path in bounds stays in bounds while no length shrinks** (the
value-level `live_mono`). -/
theorem ReprAt.live_mono {st st' : WordStore} {L' : Nat} {a : Bool} {T U : Ty} {p : Path T U}
    {s s' : Slot} (hp : PathAt a p s s') :
    ∀ {v v' : SVal T}, ReprAt st L T s v → ReprAt st' L' T s v' →
      (∀ x, OccAt false T s x → st x ≤ st' x) →
      (∃ w, v.findLiveM p = some w) → ∃ w, v'.findLiveM p = some w := by
  induction hp with
  | nil => intro v v' _ _ _ _; exact ⟨v', by cases v' <;> rfl⟩
  | @field a n f T U h p s s' _ ih =>
    intro v v' hv hv' hlen hw
    cases hv with
    | struct hall =>
      cases hv' with
      | struct hall' =>
        simp only [SVal.findLiveM] at hw ⊢
        exact ih (hall f T h) (hall' f T h) (fun x hx => hlen x (.field h hx)) hw
  | @key a V U k p s s' h0 h1 _ ih =>
    intro v v' hv hv' hlen hw
    cases hv with
    | map hall =>
      cases hv' with
      | map hall' =>
        rw [findLiveM_key] at hw ⊢
        have e1 := hall rfl k.1.toNat (by omega)
        have e2 := hall' rfl k.1.toNat (by omega)
        rw [Int.toNat_of_nonneg h0, show (k.1 : Int) = PrimTy.key k from rfl,
          SMap.lookupBy_hashed] at e1 e2
        exact ih e1 e2 (fun x hx => hlen x (.entry _ hx)) hw
  | @elem E U i p s s' h0 h1 _ ih =>
    intro v v' hv hv' hlen hw
    cases hv with
    | @array _ k₁ _ e sh hk hl hW hall =>
      cases hv' with
      | @array _ k₂ _ e' sh' hk' hl' hW' hall' =>
        simp only [SVal.findLiveM, if_pos h0] at hw ⊢
        obtain ⟨w, hw⟩ := hw
        split at hw
        · rename_i x hx
          have hle := hlen s .len
          have hi : i.1.toNat < e'.toList.length := by
            have := lt_of_getElem? hx; rw [SVec.length_toList] at this ⊢; omega
          obtain ⟨x', hx'⟩ : ∃ x', e'.toList[i.1.toNat]? = some x' :=
            ⟨_, List.getElem?_eq_getElem hi⟩
          rw [hx']
          exact ih (hall _ x hx) (hall' _ x' hx') (fun y hy => hlen y (.elem _ hy)) ⟨w, hw⟩
        · cases hw
  | @felem E U n i p s s' h0 h1 _ ih =>
    intro v v' hv hv' hlen hw
    cases hv with
    | @fixed _ _ _ e hall =>
      cases hv' with
      | @fixed _ _ _ e' hall' =>
        simp only [SVal.findLiveM, if_pos h0] at hw ⊢
        obtain ⟨w, hw⟩ := hw
        split at hw
        · rename_i x hx
          have hi : i.1.toNat < e'.toList.length := by rw [SVec.length_toList]; omega
          obtain ⟨x', hx'⟩ : ∃ x', e'.toList[i.1.toNat]? = some x' :=
            ⟨_, List.getElem?_eq_getElem hi⟩
          rw [hx']
          exact ih (hall _ x hx) (hall' _ x' hx')
            (fun y hy => hlen y (.felem _ (by omega) hy)) ⟨w, hw⟩
        · cases hw

/-- **A path in bounds stays in bounds while no length shrinks.**  If both
storages are represented, and no slot that is an array's length holds less
in `st'` than in `st`, a reference the first storage reads live, the second
reads live too. -/
theorem live_mono {C : Contract} {st st' : WordStore} {stor stor' : Solidity.Storage C}
    {L' : Nat} (hs : ReprStore C L st stor) (hs' : ReprStore C L' st' stor')
    (hlen : ∀ x, LenSlot C x → st x ≤ st' x) {a : Bool} {U : Ty} {r : SRef C U} {s : Slot}
    (hp : PathSlot C a r s) :
    (∃ w, stor.findLive r = some w) → ∃ w, stor'.findLive r = some w := by
  rw [Sto.findLive_eq, Sto.findLive_eq]
  exact ReprAt.live_mono hp (hs r.root r.ty r.hroot) (hs' r.root r.ty r.hroot)
    fun x hx => hlen x ⟨r.root, r.ty, r.hroot, hx⟩

/-! ## A fresh contract -/

/-- An all-zero storage represents every type's default: a fresh `Person` is
three zero slots, a fresh `mapping(uint => Person)` maps every key to one. -/
theorem dfltBelow_repr (hL : 0 < L) : ∀ (k : Nat) (T : Ty) (h : tyRank T < k) (s : Slot),
    ReprAt WordStore.zero L T s (SVal.dfltBelow k T h)
  | 0, _, h, _ => absurd h (Nat.not_lt_zero _)
  | k + 1, .prim p, _, _ => .prim (ReprV.dflt_zero p)
  | k + 1, .ref (.struct n), _, _ => .struct fun f T hT => by
    obtain ⟨hT', e⟩ := get_dfltBelow (f := f) k (SVal.dfltBelow k) _ hT
    rw [e]
    exact dfltBelow_repr hL k T hT' _
  | k + 1, .ref (.array _), _, _ => .array rfl hL fun i x hx => by
    rw [SVec.toList_nil, List.getElem?_nil] at hx
    cases hx
  | k + 1, .ref (.fixed E n), h, _ => .fixed fun i x hx => by
    rw [SVec.toList_replicate, List.getElem?_replicate] at hx
    split at hx
    · cases hx
      exact dfltBelow_repr hL (k + 1) E (by simp only [tyRank] at h; omega) _
    · cases hx
  | k + 1, .ref (.mapping K V), h, _ => .map fun _ k' _ => by
    rw [show (SMap.nil : SMap K V).hashed = [] by
      simp only [SMap.hashed, SMap.toList_nil, List.map_nil]]
    exact dfltBelow_repr hL (k + 1) V (by simpa only [tyRank] using h) _
termination_by k T => (k, sizeOf T)

/-- A fresh contract's storage is represented by the all-zero machine storage. -/
theorem initStorage_repr (C : Contract) (hL : 0 < L) :
    ReprStore C L WordStore.zero (Solidity.Storage.init C) := fun r T h => by
  show ReprAt _ _ _ _ ((SFields.dflt C.vars).get h)
  rw [get_dflt]
  exact dfltBelow_repr hL _ T _ _

end Evm
end Solidity
