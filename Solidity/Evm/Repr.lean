import Solidity.Evm.Compile

/-!
# The machine's storage represents the interpreter's

`ReprAt st L T s v`: the storage tree `v`, of type `T`, is laid out in the
machine storage `st` from slot `s` — every `uint`, `int` (its two's complement
word) and `bool` at its slot, every array's length at its own slot (below `L`)
and its live elements at theirs, every entry of a `uint`-keyed mapping at its
hashed slot.  `ReprStore` says it of every state
variable.  This is mini-solkey's `Sim.store` read by type rather than by path,
which is what makes `delete` and `pop` (writes of a whole subtree) the same
lemma as `alice.age = 1;` (a write of one slot).

The two lemmas the compiler proof needs:

* `find_repr`: a typed path reads, in the interpreter, a value its slot
  represents — or, if it indexes an array, reverts out of bounds;
* `save_repr`: the interpreter's write of a subtree at a typed path is the
  machine's write of the slots that subtree occupies (`Occ`), and leaves every
  other slot as it was.  The step with content is the layout's injectivity
  (`occ_members_disjoint` and its siblings, `Compile.lean`).

A fixed-size array is laid out inline, as solc lays it out: its elements one
after the other from its own slot, no length slot, its length its type's.

What `ReprAt` does not constrain, it does not need to: an array's popped slots
(the interpreter's `shadow`), a mapping keyed by other than `uint`.  The
compiler rejects every read of those: a `push()` of a struct (which revives a
popped slot as it is) and an alias bound through an index after a `pop` or a
`delete` (which may point past the end).

Beyond the two lemmas: a static value is copied by copying its leaves
(`move_repr`, `overlay_repr`), a `push` grows the array by one element
(`push_repr`), and no slot is both a primitive's and an array's length
(`OccAt.kind_unique`), so a path in bounds stays in bounds while no length
shrinks (`live_mono`).
-/

namespace Solidity
namespace Evm

open Semantics SemanticsProperties

variable {L : Nat}

/-! ## Paths through the storage tree -/

/-- `State.findStorage_append` for the live read. -/
theorem findLive_append (σ : State) (r : Name) (segs rest : List Seg) :
    σ.findLive r (segs ++ rest) = (σ.findLive r segs >>= fun w => w.findLive rest) := by
  unfold State.findLive
  split
  · exact SVal.findLive_append _ _ _
  · rfl

/-! ## The representation -/

/-- A stack word represents a value of primitive type `p`: a `uint` below
`2^256` as itself, a `bool` as `1` or `0`, an `int` as its two's complement
word (the word's signed reading, `sgn`, is the value). -/
def ReprV : PrimTy → Value → Word → Prop
  | .uint, .int n, .val w => 0 ≤ n ∧ n < W ∧ w = n.toNat
  | .bool, .bool b, .val w => w = bword b
  | .int, .int n, .val w => w < W ∧ n = sgn w
  | _, _, _ => False

/-- `ReprAt st L T s v`: the storage value `v` of type `T` is laid out in `st`
from slot `s`, and every dynamic array in it holds fewer than `L` elements
(`L` at most solc's `2^64`: what a `push` needs to agree with solc's). -/
inductive ReprAt (st : Slot → Nat) (L : Nat) : Ty → Slot → SVal → Prop
  | uint {s : Slot} {n : Int} : 0 ≤ n → n < W → st s = n.toNat →
      ReprAt st L (.prim .uint) s (.prim (.int n))
  | bool {s : Slot} {b : Bool} : st s = bword b → ReprAt st L (.prim .bool) s (.prim (.bool b))
  | int {s : Slot} {n : Int} : st s < W → n = sgn (st s) →
      ReprAt st L (.prim .int) s (.prim (.int n))
  | struct {n : Name} {s : Slot} {fields : List (Name × SVal)} :
      (∀ f T, lookupBy f (structDef n) = some T → ∃ v, lookupBy f fields = some v) →
      (∀ f T v, lookupBy f (structDef n) = some T → lookupBy f fields = some v →
        ReprAt st L T (s.add (offset n f)) v) →
      ReprAt st L (.ref (.struct n)) s (.struct fields)
  | array {E : Ty} {s : Slot} {elems shadow : List SVal} :
      st s = elems.length → elems.length < L →
      (∀ i (h : i < elems.length), ReprAt st L E (.data s (i * size E)) elems[i]) →
      ReprAt st L (.ref (.array E)) s (.array elems shadow false)
  | fixed {E : Ty} {n : Nat} {s : Slot} {elems shadow : List SVal} :
      elems.length = n →
      (∀ i (h : i < elems.length), ReprAt st L E (s.add (i * size E)) elems[i]) →
      ReprAt st L (.ref (.fixed E n)) s (.array elems shadow true)
  | map {V : Ty} {s : Slot} {entries : List (Int × SVal)} {dflt : SVal} :
      (∀ k, k < W → ReprAt st L V (.hash k s 0) ((lookupBy (k : Int) entries).getD dflt)) →
      ReprAt st L (.ref (.mapping (.prim .uint) V)) s (.map entries dflt)
  | mapOther {K V : Ty} {s : Slot} {v : SVal} : K ≠ .prim .uint →
      ReprAt st L (.ref (.mapping K V)) s v

/-- A representation looks only at the slots the value occupies.

Example: `bob` is represented in slots `[14, 17)`; a write to `alice.age`
(slot `13`) keeps it represented. -/
theorem ReprAt.frame {st st' : Slot → Nat} {T : Ty} {s : Slot} {v : SVal}
    (h : ReprAt st L T s v) (hf : ∀ x, Occ T s x → st' x = st x) : ReprAt st' L T s v := by
  induction h with
  | uint h0 h1 h2 => exact .uint h0 h1 (by rw [hf _ .prim, h2])
  | bool h => exact .bool (by rw [hf _ .prim, h])
  | int h0 h1 => exact .int (by rw [hf _ .prim]; exact h0) (by rw [hf _ .prim]; exact h1)
  | struct hex _ ih =>
    exact .struct hex fun f T v hT hv => ih f T v hT hv fun x hx => hf x (.field hT hx)
  | array hl hW _ ih =>
    exact .array (by rw [hf _ .len, hl]) hW fun i hi => ih i hi fun x hx => hf x (.elem i hx)
  | map _ ih => exact .map fun k hk => ih k hk fun x hx => hf x (.entry k hx)
  | mapOther hK => exact .mapOther hK
  | fixed hl _ ih =>
    exact .fixed hl fun i hi => ih i hi fun x hx => hf x (.felem i (hl ▸ hi) hx)

/-- A looser bound on the arrays keeps a representation: after a `push`, the
bound is one more. -/
theorem ReprAt.mono {st : Slot → Nat} {L' : Nat} {T : Ty} {s : Slot} {v : SVal}
    (h : ReprAt st L T s v) (hL : L ≤ L') : ReprAt st L' T s v := by
  induction h with
  | uint h0 h1 h2 => exact .uint h0 h1 h2
  | bool h => exact .bool h
  | int h0 h1 => exact .int h0 h1
  | struct hex _ ih => exact .struct hex ih
  | array hl hW _ ih => exact .array hl (by omega) ih
  | map _ ih => exact .map ih
  | mapOther hK => exact .mapOther hK
  | fixed hl _ ih => exact .fixed hl ih

/-- Every state variable is represented at its slot. -/
def ReprStore (C : Contract) (L : Nat) (st : Slot → Nat) (stor : List (Name × SVal)) : Prop :=
  ∀ r T, C.rootType r = some T → ∃ sv, lookupBy r stor = some sv ∧ ReprAt st L T (rootSlot C r) sv

/-- `ReprAt.mono` for every state variable. -/
theorem ReprStore.mono {C : Contract} {st : Slot → Nat} {stor : List (Name × SVal)} {L' : Nat}
    (h : ReprStore C L st stor) (hL : L ≤ L') : ReprStore C L' st stor := fun r T hr => by
  obtain ⟨sv, h1, h2⟩ := h r T hr
  exact ⟨sv, h1, h2.mono hL⟩

/-- A state variable's slot is an offset from slot `0`: `alice` is `0 + 11`. -/
theorem rootSlot_eq (C : Contract) (r : Name) :
    rootSlot C r = (Slot.root 0).add (offsetIn C.vars r) := by
  simp [rootSlot, Slot.add]

/-- `PathSlot C free r segs T s`: the storage path `r.segs` has type `T` and
slot `s`.  `free` paths index no array. -/
inductive PathSlot (C : Contract) : Bool → Name → List Seg → Ty → Slot → Prop
  | root {a : Bool} {r : Name} {T : Ty} : C.rootType r = some T → PathSlot C a r [] T (rootSlot C r)
  | field {a : Bool} {r : Name} {segs : List Seg} {n : Name} {s : Slot} {f : Name} {T : Ty} :
      PathSlot C a r segs (.ref (.struct n)) s → C.fieldType n f = some T →
      PathSlot C a r (segs ++ [.field f]) T (s.add (offset n f))
  | key {a : Bool} {r : Name} {segs : List Seg} {V : Ty} {s : Slot} {k : Int} :
      PathSlot C a r segs (.ref (.mapping (.prim .uint) V)) s → 0 ≤ k → k < W →
      PathSlot C a r (segs ++ [.at k]) V (.hash k.toNat s 0)
  | elem {r : Name} {segs : List Seg} {E : Ty} {s : Slot} {i : Int} :
      PathSlot C false r segs (.ref (.array E)) s → 0 ≤ i → i < W →
      PathSlot C false r (segs ++ [.at i]) E (.data s (i.toNat * size E))
  | felem {r : Name} {segs : List Seg} {E : Ty} {n : Nat} {s : Slot} {i : Int} :
      PathSlot C false r segs (.ref (.fixed E n)) s → 0 ≤ i → i < n →
      PathSlot C false r (segs ++ [.at i]) E (s.add (i.toNat * size E))

/-- A path that indexes no array is a path: `folks[7].age`. -/
theorem PathSlot.weaken {C : Contract} {a : Bool} {r : Name} {segs : List Seg} {T : Ty} {s : Slot}
    (h : PathSlot C a r segs T s) : PathSlot C false r segs T s := by
  induction h with
  | root h => exact .root h
  | field _ hf ih => exact .field ih hf
  | key _ h0 h1 ih => exact .key ih h0 h1
  | elem _ h0 h1 ih => exact .elem ih h0 h1
  | felem _ h0 h1 ih => exact .felem ih h0 h1

/-! ## Reading -/

/-- A typed path reads a value its slot represents, or (if it indexes an
array) reverts out of bounds.

Example: `folks[7].age` reads what slot `keccak(7, 7) + 2` holds; with three
`persons`, `persons[5].age` reverts. -/
theorem find_repr {C : Contract} {st : Slot → Nat} {σ : State} (hs : ReprStore C L st σ.storage)
    {a : Bool} {r : Name} {segs : List Seg} {T : Ty} {s : Slot} (hp : PathSlot C a r segs T s) :
    (∃ sv, σ.findLive r segs = .ok sv ∧ ReprAt st L T s sv) ∨
      (a = false ∧ σ.findLive r segs = .error .revert) := by
  induction hp with
  | root h =>
    obtain ⟨sv, hl, hr⟩ := hs _ _ h
    exact .inl ⟨sv, by simp [State.findLive, hl], hr⟩
  | @field a r segs n s f T _ hf ih =>
    rw [findLive_append]
    rcases ih with ⟨sv, hsv, hr⟩ | ⟨ha, hsv⟩
    · rw [hsv]
      cases hr with
      | struct hex hall =>
        rename_i fields
        obtain ⟨v, hv⟩ := hex f T hf
        exact .inl ⟨v, by simp [bind, Except.bind, SVal.findLive, hv], hall f T v hf hv⟩
    · exact .inr ⟨ha, by rw [hsv]; rfl⟩
  | @key a r segs V s k _ h0 h1 ih =>
    rw [findLive_append]
    rcases ih with ⟨sv, hsv, hr⟩ | ⟨ha, hsv⟩
    · rw [hsv]
      cases hr with
      | map hall =>
        rename_i entries dflt
        have := hall k.toNat (by omega)
        rw [Int.toNat_of_nonneg h0] at this
        refine .inl ⟨_, ?_, this⟩
        simp only [bind, Except.bind, SVal.findLive]
        cases lookupBy k entries <;> simp
      | mapOther hK => exact absurd rfl hK
    · exact .inr ⟨ha, by rw [hsv]; rfl⟩
  | @elem r segs E s i _ h0 h1 ih =>
    rw [findLive_append]
    rcases ih with ⟨sv, hsv, hr⟩ | ⟨ha, hsv⟩
    · rw [hsv]
      cases hr with
      | array hl hW hall =>
        rename_i elems shadow
        by_cases hb : i.toNat < elems.length
        · refine .inl ⟨elems[i.toNat], ?_, hall _ hb⟩
          simp [bind, Except.bind, SVal.findLive, h0, hb]
        · refine .inr ⟨rfl, ?_⟩
          simp [bind, Except.bind, SVal.findLive, hb]
    · exact .inr ⟨rfl, by rw [hsv]; rfl⟩
  | @felem r segs E n s i _ h0 h1 ih =>
    rw [findLive_append]
    rcases ih with ⟨sv, hsv, hr⟩ | ⟨ha, hsv⟩
    · rw [hsv]
      cases hr with
      | fixed hl hall =>
        rename_i elems shadow
        have hb : i.toNat < elems.length := by omega
        refine .inl ⟨elems[i.toNat], ?_, hall _ hb⟩
        simp [bind, Except.bind, SVal.findLive, h0, hb]
    · exact .inr ⟨rfl, by rw [hsv]; rfl⟩

/-! ## Writing -/

/-- **A write is represented by the slots it occupies.**  If the interpreter
writes the subtree `new` at a typed path it can read, and the machine storage
`st'` represents `new` at the path's slot and agrees with `st` on every slot
the path's value does not occupy, then the write succeeds and `st'` represents
the whole storage after it.

Example: `alice.age = 5;` stores `5` in slot `13` and nothing else: slot `11`
(`alice.account.balance`) and slots `[14, 17)` (`bob`) keep their words, and
the interpreter's `alice.account` and `bob` do not change either.  `delete
alice;` is the same lemma with `new` the default `Person` and `st'` zero at
three slots. -/
theorem save_repr {C : Contract} {st : Slot → Nat} {σ : State} (hs : ReprStore C L st σ.storage)
    {a : Bool} {r : Name} {segs : List Seg} {T : Ty} {s : Slot} (hp : PathSlot C a r segs T s) :
    ∀ {st' : Slot → Nat} {new : SVal}, (∃ old, σ.findLive r segs = .ok old) →
      ReprAt st' L T s new → (∀ x, ¬ Occ T s x → st' x = st x) →
      ∃ stor, σ.saveStorage r segs new = .ok { σ with storage := stor } ∧ ReprStore C L st' stor := by
  induction hp with
  | @root a r T h =>
    intro st' new _ hnew hout
    obtain ⟨sv, hl, _⟩ := hs _ _ h
    refine ⟨setBy r new σ.storage, by simp only [State.saveStorage, hl, SVal.save_nil]; rfl, ?_⟩
    intro r' T' h'
    by_cases hr : r' = r
    · subst hr; rw [h] at h'; cases h'
      exact ⟨new, lookupBy_setBy_self _ _ _, hnew⟩
    · obtain ⟨sv', hl', hr'⟩ := hs _ _ h'
      refine ⟨sv', by rw [lookupBy_setBy_ne hr]; exact hl', hr'.frame fun x hx => hout x ?_⟩
      intro hx'
      rw [rootSlot_eq] at hx hx'
      exact occ_members_disjoint h' h hr hx hx'
  | @field a r segs n s₀ f T hp hf ih =>
    intro st' new hfind hnew hout
    rcases find_repr hs hp with ⟨sv, hsv, hr⟩ | ⟨_, hsv⟩
    · cases hr with
      | struct hex hall =>
        rename_i fields
        obtain ⟨oldf, hold⟩ := hex f T hf
        have hsd : lookupBy f (structDef n) = some T := hf
        obtain ⟨stor, hsave, hrep⟩ := ih (st' := st') (new := .struct (setBy f new fields))
          ⟨_, hsv⟩
          (by
            refine .struct (fun g Tg hg => ?_) (fun g Tg v hg hv => ?_)
            · by_cases hgf : g = f
              · subst hgf; exact ⟨new, lookupBy_setBy_self _ _ _⟩
              · rw [lookupBy_setBy_ne hgf]; exact hex g Tg hg
            · by_cases hgf : g = f
              · subst hgf; rw [lookupBy_setBy_self] at hv; cases hv
                rw [hsd] at hg; cases hg; exact hnew
              · rw [lookupBy_setBy_ne hgf] at hv
                exact (hall g Tg v hg hv).frame fun x hx => hout x fun hx' =>
                  occ_members_disjoint hg hsd hgf hx hx')
          (fun x hx => hout x fun hx' => hx (.field hsd hx'))
        refine ⟨stor, ?_, hrep⟩
        rw [State.saveStorage_append (State.findStorage_of_findLive hsv)]
        simp [bind, Except.bind, SVal.save, hold, hsave]
    · obtain ⟨old, hold⟩ := hfind
      rw [findLive_append, hsv] at hold; cases hold
  | @key a r segs V s₀ k hp h0 h1 ih =>
    intro st' new hfind hnew hout
    rcases find_repr hs hp with ⟨sv, hsv, hr⟩ | ⟨_, hsv⟩
    · cases hr with
      | map hall =>
        rename_i entries dflt
        obtain ⟨stor, hsave, hrep⟩ := ih (st' := st') (new := .map (setBy k new entries) dflt)
          ⟨_, hsv⟩
          (by
            refine .map fun k' hk' => ?_
            by_cases hkk : (k' : Int) = k
            · have : k' = k.toNat := by omega
              subst this
              rw [hkk, lookupBy_setBy_self]; exact hnew
            · rw [lookupBy_setBy_ne hkk]
              exact (hall k' hk').frame fun x hx => hout x fun hx' =>
                occ_entries_disjoint (by omega) hx hx')
          (fun x hx => hout x fun hx' => hx (.entry _ hx'))
        refine ⟨stor, ?_, hrep⟩
        rw [State.saveStorage_append (State.findStorage_of_findLive hsv)]
        simp only [bind, Except.bind, SVal.save]
        cases lookupBy k entries <;> simpa using hsave
      | mapOther hK => exact absurd rfl hK
    · obtain ⟨old, hold⟩ := hfind
      rw [findLive_append, hsv] at hold; cases hold
  | @elem r segs E s₀ i hp h0 h1 ih =>
    intro st' new hfind hnew hout
    rcases find_repr hs hp with ⟨sv, hsv, hr⟩ | ⟨_, hsv⟩
    · cases hr with
      | array hl hW hall =>
        rename_i elems shadow
        obtain ⟨old, hold⟩ := hfind
        rw [findLive_append, hsv] at hold
        have hb : i.toNat < elems.length := by
          refine Decidable.byContradiction fun hb => ?_
          simp [bind, Except.bind, SVal.findLive, hb] at hold
        obtain ⟨stor, hsave, hrep⟩ := ih (st' := st') (new := .array (elems.set i.toNat new) shadow false)
          ⟨_, hsv⟩
          (by
            refine .array ?_ (by simpa using hW) fun j hj => ?_
            · rw [hout _ fun hx => occ_len_elem hx, hl, List.length_set]
            · simp only [List.length_set] at hj
              by_cases hji : j = i.toNat
              · subst hji; simpa using hnew
              · rw [List.getElem_set_ne (Ne.symm hji)]
                exact (hall j hj).frame fun x hx => hout x fun hx' =>
                  occ_elems_disjoint hji hx hx')
          (fun x hx => hout x fun hx' => hx (.elem _ hx'))
        refine ⟨stor, ?_, hrep⟩
        rw [State.saveStorage_append (State.findStorage_of_findLive hsv)]
        have hb2 : i < (elems.length : Int) + shadow.length := by omega
        simp [bind, Except.bind, SVal.save, h0, hb, hb2, hsave]
    · obtain ⟨old, hold⟩ := hfind
      rw [findLive_append, hsv] at hold; cases hold
  | @felem r segs E n s₀ i hp h0 h1 ih =>
    intro st' new hfind hnew hout
    rcases find_repr hs hp with ⟨sv, hsv, hr⟩ | ⟨_, hsv⟩
    · cases hr with
      | fixed hl hall =>
        rename_i elems shadow
        have hb : i.toNat < elems.length := by omega
        obtain ⟨stor, hsave, hrep⟩ := ih (st' := st')
          (new := .array (elems.set i.toNat new) shadow true) ⟨_, hsv⟩
          (by
            refine .fixed (by rw [List.length_set, hl]) fun j hj => ?_
            simp only [List.length_set] at hj
            by_cases hji : j = i.toNat
            · subst hji; simpa using hnew
            · rw [List.getElem_set_ne (Ne.symm hji)]
              exact (hall j hj).frame fun x hx => hout x fun hx' =>
                occ_felems_disjoint hji hx hx')
          (fun x hx => hout x fun hx' => hx (.felem _ (by omega) hx'))
        refine ⟨stor, ?_, hrep⟩
        rw [State.saveStorage_append (State.findStorage_of_findLive hsv)]
        have hb2 : i < (elems.length : Int) + shadow.length := by omega
        simp [bind, Except.bind, SVal.save, h0, hb, hb2, hsave]
    · obtain ⟨old, hold⟩ := hfind
      rw [findLive_append, hsv] at hold; cases hold

/-! ## `delete` and `pop` -/

/-- `st` with `0` written at `s + o` for each `o`, in order. -/
def zeroAt (st : Slot → Nat) (s : Slot) : List Nat → Slot → Nat
  | [] => st
  | o :: os => zeroAt (upd st (s.add o) 0) s os

/-- Zeroing some slots leaves the others: `delete alice;` leaves `bob.age`. -/
theorem zeroAt_other {st : Slot → Nat} {s x : Slot} :
    ∀ {os : List Nat}, (∀ o ∈ os, x ≠ s.add o) → zeroAt st s os x = st x
  | [], _ => rfl
  | o :: os, h => by
    simp only [zeroAt]
    rw [zeroAt_other fun o' ho' => h o' (List.mem_cons_of_mem _ ho')]
    exact upd_other _ _ (h o List.mem_cons_self)

/-- Every zeroed slot holds `0`: `delete alice;` zeroes `alice.age`. -/
theorem zeroAt_zero {s x : Slot} :
    ∀ {st : Slot → Nat} {os : List Nat}, (∃ o ∈ os, x = s.add o) → zeroAt st s os x = 0
  | _, [], ⟨_, ho, _⟩ => by cases ho
  | st, o :: os, h => by
    simp only [zeroAt]
    by_cases h' : ∃ o' ∈ os, x = s.add o'
    · exact zeroAt_zero h'
    · obtain ⟨o', ho', hx⟩ := h
      rcases List.mem_cons.1 ho' with rfl | ho'
      · rw [zeroAt_other fun o'' ho'' hx' => h' ⟨o'', ho'', hx'⟩, hx, upd_same]
      · exact absurd ⟨o', ho', hx⟩ h'

/-- **`delete` is represented by zeroing its leaves.**  If `st'` is zero at
every slot `delete` writes (`leavesF`) and agrees with `st` on the rest of what
the value occupies, it represents the value's default (`SVal.defaultOf`).

Example: `delete wallet;` zeroes `wallet.owner`'s slot and leaves
`wallet.stash`'s entries where they are, and `SVal.defaultOf` keeps the
mapping's entries too. -/
theorem zero_repr {st st' : Slot → Nat} {T : Ty} {s : Slot} {sv : SVal} (h : ReprAt st L T s sv) :
    ∀ fuel, tyRank T < fuel → (∀ o ∈ leavesF fuel T, st' (s.add o) = 0) →
      (∀ x, Occ T s x → (∀ o ∈ leavesF fuel T, x ≠ s.add o) → st' x = st x) →
      ReprAt st' L T s sv.defaultOf := by
  induction h with
  | uint =>
    intro fuel _ hz _
    exact .uint (Int.le_refl 0) (by have := W_pos; omega)
      (by simpa using hz 0 (by simp [leavesF]))
  | bool =>
    intro fuel _ hz _
    exact .bool (by simpa [bword] using hz 0 (by simp [leavesF]))
  | @int s _ =>
    intro fuel _ hz _
    have h0 : st' s = 0 := by simpa using hz 0 (by simp [leavesF])
    exact .int (by rw [h0]; exact W_pos) (by rw [h0]; rfl)
  | @struct n s fields hex hall ih =>
    intro fuel hr hz ho
    cases fuel with
    | zero => exact absurd hr (Nat.not_lt_zero _)
    | succ f' =>
      refine .struct (fun g Tg hg => ?_) (fun g Tg v hg hv => ?_)
      · obtain ⟨w, hw⟩ := hex g Tg hg
        exact ⟨w.defaultOf, by rw [lookupBy_defaultOfFields, hw]; rfl⟩
      · rw [lookupBy_defaultOfFields] at hv
        obtain ⟨w, hw, rfl⟩ := Option.map_eq_some_iff.1 hv
        have hmem := lookupBy_eq_some_mem hg
        have hrank : tyRank Tg < f' := by
          have := tyRank_member hmem; simp only [tyRank] at hr this; omega
        have hleaf : ∀ o ∈ leavesF f' Tg, offset n g + o ∈ leavesF (f' + 1) (.ref (.struct n)) := by
          intro o ho
          simp only [leavesF, List.mem_flatMap]
          exact ⟨(g, Tg), hmem, by simp only [hg]; exact List.mem_map_of_mem ho⟩
        refine ih g Tg w hg hw f' hrank (fun o ho' => ?_) (fun x hx hno => ?_)
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
  | array hl hW hall =>
    intro fuel _ hz _
    exact .array (by simpa using hz 0 (by simp [leavesF])) (by simp; omega)
      fun i hi => absurd hi (Nat.not_lt_zero _)
  | map hall =>
    intro fuel _ _ ho
    exact .map fun k hk => (hall k hk).frame fun x hx => ho x (.entry k hx) (by simp [leavesF])
  | mapOther hK => intro _ _ _ _; exact .mapOther hK
  | @fixed E n s elems shadow hl hall ih =>
    intro fuel hr hz ho
    cases fuel with
    | zero => exact absurd hr (Nat.not_lt_zero _)
    | succ f' =>
      simp only [SVal.defaultOf, defaultOfElems_eq_map]
      refine .fixed (by rw [List.length_map, hl]) fun i hi => ?_
      rw [List.length_map] at hi
      rw [List.getElem_map]
      have hrank : tyRank E < f' := by simp only [tyRank] at hr; omega
      have hin : i < n := hl ▸ hi
      have hleaf : ∀ o ∈ leavesF f' E, i * size E + o ∈ leavesF (f' + 1) (.ref (.fixed E n)) := by
        intro o ho
        simp only [leavesF, List.mem_flatMap, List.mem_range, List.mem_map]
        exact ⟨i, hin, o, ho, rfl⟩
      refine ih i hi f' hrank (fun o ho' => ?_) (fun x hx hno => ?_)
      · rw [Slot.add_add]; exact hz _ (hleaf o ho')
      · refine ho x (.felem i hin hx) fun o hol hxo => ?_
        simp only [leavesF, List.mem_flatMap, List.mem_range, List.mem_map] at hol
        obtain ⟨j, hj, o'', ho'', rfl⟩ := hol
        by_cases hji : j = i
        · subst hji; exact hno o'' ho'' (by rw [Slot.add_add]; exact hxo)
        · have hocc := leavesF_occ f' E (s.add (j * size E)) o'' ho''
          rw [Slot.add_add, ← hxo] at hocc
          exact occ_felems_disjoint hji hocc hx

/-- **`pop` is represented by decrementing the length.**  The popped element's
slots are left as they are: `ReprAt` constrains only the live elements, so
whatever the recycled slot holds (`x`: the element cleared, or kept) is
represented.

Example: with `values = [1, 2]`, `values.pop();` writes `1` to slot `4`;
`keccak(4) + 1` still holds `2`, and nothing reads it. -/
theorem pop_repr {st : Slot → Nat} {E : Ty} {s : Slot} {elems shadow restRev : List SVal}
    {last : SVal} (x : SVal) (h : ReprAt st L (.ref (.array E)) s (.array elems shadow false))
    (hrev : elems.reverse = last :: restRev) :
    ReprAt (upd st s (elems.length - 1)) L (.ref (.array E)) s
      (.array restRev.reverse (x :: shadow) false) := by
  cases h with
  | array hl hW hall =>
    have he : elems = restRev.reverse ++ [last] := by
      rw [← List.reverse_reverse elems, hrev]; simp
    have hlen : elems.length = restRev.reverse.length + 1 := by rw [he]; simp
    refine .array (by rw [upd_same]; omega) (by omega) fun j hj => ?_
    have hj' : j < elems.length := by omega
    have := (hall j hj').frame (st' := upd st s (elems.length - 1)) fun x hx =>
      upd_other _ _ fun hxs => by subst hxs; exact occ_len_elem hx
    have hget : elems[j] = restRev.reverse[j] := by
      simp only [he]; exact List.getElem_append_left hj
    rw [hget] at this
    exact this

/-! ## Copies and `push`

A value of a static type (`staticF`: no dynamic array, no mapping) occupies
exactly the slots `leaves` lists, so copying it is copying those words
(`move_repr`), and what the interpreter writes, the copy laid over the old
value or laid on fresh slots (`SVal.overlay`, `SVal.strip`), is the copied
value again as far as the slots go (`overlay_repr`). -/

/-- **A static value moves with its leaves.**  If `st'` holds at `d + o` what
`st` holds at `s + o` for every leaf `o`, the value laid out at `s` in `st` is
laid out at `d` in `st'`.  `bob = alice;` copies slots `11`–`13` to `14`–`16`. -/
theorem move_repr {st st' : Slot → Nat} {T : Ty} {s : Slot} {v : SVal} (h : ReprAt st L T s v) :
    ∀ fuel (d : Slot), tyRank T < fuel → staticF fuel T = true →
      (∀ o ∈ leavesF fuel T, st' (d.add o) = st (s.add o)) → ReprAt st' L T d v := by
  induction h with
  | @uint s n h0 h1 h2 =>
    intro fuel d _ _ hc
    exact .uint h0 h1 (by have := hc 0 (by simp [leavesF]); simp at this; rw [this, h2])
  | @bool s b h =>
    intro fuel d _ _ hc
    exact .bool (by have := hc 0 (by simp [leavesF]); simp at this; rw [this, h])
  | @int s n h0 h1 =>
    intro fuel d _ _ hc
    have e : st' d = st s := by have := hc 0 (by simp [leavesF]); simpa using this
    exact .int (by rw [e]; exact h0) (by rw [e]; exact h1)
  | @struct n s fields hex hall ih =>
    intro fuel d hr hs hc
    cases fuel with
    | zero => exact absurd hr (Nat.not_lt_zero _)
    | succ f' =>
      refine .struct hex fun g Tg v hg hv => ?_
      have hmem := lookupBy_eq_some_mem hg
      have hrank : tyRank Tg < f' := by
        have := tyRank_member hmem; simp only [tyRank] at hr this; omega
      have hst : staticF f' Tg = true := by
        simp only [staticF, List.all_eq_true] at hs; exact hs _ hmem
      refine ih g Tg v hg hv f' (d.add (offset n g)) hrank hst fun o ho => ?_
      have hleaf : offset n g + o ∈ leavesF (f' + 1) (.ref (.struct n)) := by
        simp only [leavesF, List.mem_flatMap]
        exact ⟨(g, Tg), hmem, by simp only [hg]; exact List.mem_map_of_mem ho⟩
      have := hc _ hleaf
      rwa [← Slot.add_add, ← Slot.add_add] at this
  | array => intro fuel d _ hs; cases fuel <;> simp [staticF] at hs
  | map => intro fuel d _ hs; cases fuel <;> simp [staticF] at hs
  | mapOther => intro fuel d _ hs; cases fuel <;> simp [staticF] at hs
  | @fixed E n s elems shadow hl hall ih =>
    intro fuel d hr hs hc
    cases fuel with
    | zero => exact absurd hr (Nat.not_lt_zero _)
    | succ f' =>
      refine .fixed hl fun i hi => ?_
      have hrank : tyRank E < f' := by simp only [tyRank] at hr; omega
      have hst : staticF f' E = true := by simpa [staticF] using hs
      refine ih i hi f' (d.add (i * size E)) hrank hst fun o ho => ?_
      have hleaf : i * size E + o ∈ leavesF (f' + 1) (.ref (.fixed E n)) := by
        simp only [leavesF, List.mem_flatMap, List.mem_range, List.mem_map]
        exact ⟨i, hl ▸ hi, o, ho, rfl⟩
      have := hc _ hleaf
      rwa [← Slot.add_add, ← Slot.add_add] at this

/-- Stripping a list is stripping each. -/
theorem stripElems_eq : ∀ l : List SVal, SVal.strip.stripElems l = l.map SVal.strip
  | [] => rfl
  | v :: l => by simp [SVal.strip.stripElems, stripElems_eq l]

/-- A stripped struct's member is the member stripped. -/
theorem lookupBy_stripFields (g : Name) : ∀ fs : List (Name × SVal),
    lookupBy g (SVal.strip.stripFields fs) = (lookupBy g fs).map SVal.strip
  | [] => rfl
  | (h, v) :: fs => by
    simp only [SVal.strip.stripFields, lookupBy]
    split
    · rfl
    · exact lookupBy_stripFields g fs

/-- A member of a struct copied over another is the member copied over the old one. -/
theorem lookupBy_overlayFields (ofs : List (Name × SVal)) (g : Name) : ∀ nfs : List (Name × SVal),
    lookupBy g (SVal.overlay.overlayFields ofs nfs) =
      (lookupBy g nfs).map fun v => match lookupBy g ofs with
        | some o => o.overlay v
        | none => v.strip
  | [] => rfl
  | (h, v) :: nfs => by
    simp only [SVal.overlay.overlayFields, lookupBy]
    split
    · rename_i hg; subst hg; rfl
    · exact lookupBy_overlayFields ofs g nfs

/-- An array copied over another: element `i` is the new one copied over the
old slot `i`, or laid on a fresh slot past the old ones. -/
theorem overlayElems_get : ∀ (os vs : List SVal),
    (SVal.overlay.overlayElems os vs).length = vs.length ∧
      ∀ i (h : i < vs.length) (h' : i < (SVal.overlay.overlayElems os vs).length),
        (SVal.overlay.overlayElems os vs)[i] = match os[i]? with
          | some o => o.overlay vs[i]
          | none => vs[i].strip
  | [], [] => by simp [SVal.overlay.overlayElems, SVal.strip.stripElems]
  | _ :: _, [] => by simp [SVal.overlay.overlayElems]
  | [], v :: vs => by
    simp only [SVal.overlay.overlayElems, stripElems_eq]
    refine ⟨by simp, fun i h h' => ?_⟩
    cases i <;> simp
  | o :: os, v :: vs => by
    obtain ⟨ih1, ih2⟩ := overlayElems_get os vs
    simp only [SVal.overlay.overlayElems]
    refine ⟨by simp [ih1], fun i h h' => ?_⟩
    cases i with
    | zero => rfl
    | succ i => simpa using ih2 i (by simpa using h) (by simpa [ih1] using h)

/-- **A copy lands as the value copied.**  A static value laid out at `d`,
stripped or laid over any old value, is still laid out at `d`: the slots hold
the words, and the old value's leftovers are past the ends of arrays nothing
static has. -/
theorem overlay_repr {st : Slot → Nat} {T : Ty} {d : Slot} {v : SVal} (h : ReprAt st L T d v) :
    ∀ fuel, tyRank T < fuel → staticF fuel T = true →
      ReprAt st L T d v.strip ∧ ∀ old : SVal, ReprAt st L T d (old.overlay v) := by
  induction h with
  | uint h0 h1 h2 =>
    intro _ _ _
    exact ⟨.uint h0 h1 h2, fun old => by cases old <;> exact .uint h0 h1 h2⟩
  | bool h =>
    intro _ _ _
    exact ⟨.bool h, fun old => by cases old <;> exact .bool h⟩
  | int h0 h1 =>
    intro _ _ _
    exact ⟨.int h0 h1, fun old => by cases old <;> exact .int h0 h1⟩
  | @struct n d fields hex hall ih =>
    intro fuel hr hs
    cases fuel with
    | zero => exact absurd hr (Nat.not_lt_zero _)
    | succ f' =>
      have sub : ∀ g Tg v, lookupBy g (structDef n) = some Tg → lookupBy g fields = some v →
          ReprAt st L Tg (d.add (offset n g)) v.strip ∧
            ∀ old : SVal, ReprAt st L Tg (d.add (offset n g)) (old.overlay v) := fun g Tg v hg hv => by
        have hmem := lookupBy_eq_some_mem hg
        have hrank : tyRank Tg < f' := by
          have := tyRank_member hmem; simp only [tyRank] at hr this; omega
        have hst : staticF f' Tg = true := by
          simp only [staticF, List.all_eq_true] at hs; exact hs _ hmem
        exact ih g Tg v hg hv f' hrank hst
      have hstrip : ReprAt st L (.ref (.struct n)) d (SVal.struct fields).strip := by
        refine .struct (fun g Tg hg => ?_) (fun g Tg v hg hv => ?_)
        · obtain ⟨w, hw⟩ := hex g Tg hg
          exact ⟨w.strip, by rw [lookupBy_stripFields, hw]; rfl⟩
        · rw [lookupBy_stripFields] at hv
          obtain ⟨w, hw, rfl⟩ := Option.map_eq_some_iff.1 hv
          exact (sub g Tg w hg hw).1
      refine ⟨hstrip, fun old => ?_⟩
      cases old with
      | struct ofs =>
        refine .struct (fun g Tg hg => ?_) (fun g Tg v hg hv => ?_)
        · obtain ⟨w, hw⟩ := hex g Tg hg
          rw [lookupBy_overlayFields, hw]; exact ⟨_, rfl⟩
        · rw [lookupBy_overlayFields] at hv
          obtain ⟨w, hw, rfl⟩ := Option.map_eq_some_iff.1 hv
          split
          · exact (sub g Tg w hg hw).2 _
          · exact (sub g Tg w hg hw).1
      | prim _ => exact hstrip
      | array _ _ _ => exact hstrip
      | map _ _ => exact hstrip
  | array => intro fuel _ hs; cases fuel <;> simp [staticF] at hs
  | map => intro fuel _ hs; cases fuel <;> simp [staticF] at hs
  | mapOther => intro fuel _ hs; cases fuel <;> simp [staticF] at hs
  | @fixed E n d elems shadow hl hall ih =>
    intro fuel hr hs
    cases fuel with
    | zero => exact absurd hr (Nat.not_lt_zero _)
    | succ f' =>
      have hrank : tyRank E < f' := by simp only [tyRank] at hr; omega
      have hst : staticF f' E = true := by simpa [staticF] using hs
      have sub := fun i hi => ih i hi f' hrank hst
      have hstrip : ReprAt st L (.ref (.fixed E n)) d (SVal.array elems shadow true).strip := by
        simp only [SVal.strip, stripElems_eq]
        refine .fixed (by simp [hl]) fun i hi => ?_
        simp only [List.length_map] at hi
        simpa using (sub i hi).1
      refine ⟨hstrip, fun old => ?_⟩
      cases old with
      | array oel osh ofx =>
        obtain ⟨h1, h2⟩ := overlayElems_get (oel ++ osh) elems
        simp only [SVal.overlay]
        refine .fixed (by rw [h1, hl]) fun i hi => ?_
        have hi' : i < elems.length := h1 ▸ hi
        rw [h2 i hi' hi]
        split
        · exact (sub i hi').2 _
        · exact (sub i hi').1
      | prim _ => exact hstrip
      | struct _ => exact hstrip
      | map _ _ => exact hstrip

/-- **`push` is represented by one more element.**  If `st'` holds the new
length at `s`, represents the new element at its slot, and agrees with `st`
off the length slot and the new element's slots, it represents the array
grown by the element, under a bound one looser. -/
theorem push_repr {st st' : Slot → Nat} {E : Ty} {s : Slot} {elems shadow shadow' : List SVal}
    {new : SVal} (h : ReprAt st L (.ref (.array E)) s (.array elems shadow false))
    (hlen : st' s = elems.length + 1)
    (hnew : ReprAt st' (L + 1) E (.data s (elems.length * size E)) new)
    (hw : ∀ x, x ≠ s → ¬ Occ E (.data s (elems.length * size E)) x → st' x = st x) :
    ReprAt st' (L + 1) (.ref (.array E)) s (.array (elems ++ [new]) shadow' false) := by
  cases h with
  | array hl hW hall =>
    refine .array (by rw [hlen]; simp) (by simp; omega) fun i hi => ?_
    simp only [List.length_append, List.length_singleton] at hi
    by_cases hi' : i < elems.length
    · rw [List.getElem_append_left hi']
      exact ((hall i hi').mono (Nat.le_succ L)).frame fun x hx =>
        hw x (fun he => occ_len_elem (he ▸ hx)) fun hx' => occ_elems_disjoint (by omega) hx hx'
    · obtain rfl : i = elems.length := by omega
      simpa using hnew

/-! ## Length slots are never primitive slots

An alias bound through an array index (`Person storage p = persons[i];`)
stays in bounds as long as no array shrinks, which the fragment guarantees
until the next `pop` or `delete` (`TyCtx.dropFragile`).  What makes that a
fact about the machine: every write other than a `push`'s length is to a slot
some typed path reaches as a *primitive*, and no such slot is an array's
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
  | entry {k : Bool} {K V : Ty} {s x : Slot} (key : Nat) :
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

/-- What a typed path reaches, the state variable it starts from reaches. -/
theorem PathSlot.occAt {C : Contract} {a : Bool} {r : Name} {segs : List Seg} {T : Ty} {s : Slot}
    (hp : PathSlot C a r segs T s) {k : Bool} {x : Slot} (h : OccAt k T s x) :
    ∃ T₀, C.rootType r = some T₀ ∧ OccAt k T₀ (rootSlot C r) x := by
  induction hp generalizing x with
  | root hr => exact ⟨_, hr, h⟩
  | field _ hf ih => exact ih (.field hf h)
  | key _ h0 _ ih => exact ih (.entry _ h)
  | elem _ _ _ ih => exact ih (.elem _ h)
  | felem _ h0 h1 ih => exact ih (.felem _ (by omega) h)

/-- The length slot of an array some typed path reaches. -/
def LenSlot (C : Contract) (x : Slot) : Prop :=
  ∃ a r segs E, PathSlot C a r segs (.ref (.array E)) x

/-- A slot some typed path reaches as a primitive. -/
def PrimSlot (C : Contract) (x : Slot) : Prop :=
  ∃ r T, C.rootType r = some T ∧ OccAt true T (rootSlot C r) x

/-- **No write to a primitive touches an array's length.** -/
theorem len_prim_disjoint {C : Contract} {x : Slot} (h₁ : LenSlot C x) (h₂ : PrimSlot C x) :
    False := by
  obtain ⟨a, r₁, segs, E, hp⟩ := h₁
  obtain ⟨T₁, hr₁, o₁⟩ := hp.occAt OccAt.len
  obtain ⟨r₂, T₂, hr₂, o₂⟩ := h₂
  by_cases hr : r₁ = r₂
  · subst hr; rw [hr₁] at hr₂; cases hr₂; exact o₂.kind_unique o₁
  · rw [rootSlot_eq] at o₁ o₂
    exact occ_members_disjoint hr₁ hr₂ hr o₁.occ o₂.occ

/-- A primitive a typed path reaches is at a primitive slot. -/
theorem PathSlot.primSlot {C : Contract} {a : Bool} {r : Name} {segs : List Seg} {p : PrimTy}
    {s : Slot} (hp : PathSlot C a r segs (.prim p) s) : PrimSlot C s := by
  obtain ⟨T₀, h, o⟩ := hp.occAt OccAt.prim
  exact ⟨r, T₀, h, o⟩

/-- Every slot a static value occupies holds a primitive. -/
theorem leavesF_occAt : ∀ (fuel : Nat) (T : Ty) (s : Slot) (o : Nat), staticF fuel T = true →
    o ∈ leavesF fuel T → OccAt true T s (s.add o)
  | _, .prim _, s, o, _, h => by simp [leavesF] at h; subst h; simpa using OccAt.prim
  | fuel + 1, .ref (.fixed E n), s, o, hs, h => by
    simp only [leavesF, List.mem_flatMap, List.mem_range, List.mem_map] at h
    obtain ⟨i, hi, o', ho', rfl⟩ := h
    exact OccAt.felem i hi (by
      rw [← Slot.add_add]; exact leavesF_occAt fuel E _ o' (by simpa [staticF] using hs) ho')
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
  | 0, .ref (.struct _), _, _, hs, _ => by simp [staticF] at hs
  | 0, .ref (.fixed _ _), _, _, hs, _ => by simp [staticF] at hs
  | _, .ref (.array _), _, _, hs, _ => by cases ‹Nat› <;> simp [staticF] at hs
  | _, .ref (.mapping _ _), _, _, hs, _ => by cases ‹Nat› <;> simp [staticF] at hs

/-- **A path in bounds stays in bounds while no length shrinks.**  If both
states are represented, and no slot that is an array's length holds less in
`st'` than in `st`, a typed path the first state reads in bounds the second
reads in bounds too. -/
theorem live_mono {C : Contract} {st st' : Slot → Nat} {σ σ' : State} {L' : Nat}
    (hs : ReprStore C L st σ.storage) (hs' : ReprStore C L' st' σ'.storage)
    (hlen : ∀ x, LenSlot C x → st x ≤ st' x) {a : Bool} {r : Name} {segs : List Seg} {T : Ty}
    {s : Slot} (hp : PathSlot C a r segs T s) :
    (∃ sv, σ.findLive r segs = .ok sv) → ∃ sv, σ'.findLive r segs = .ok sv := by
  induction hp with
  | root h =>
    intro _
    obtain ⟨sv, hl, _⟩ := hs' _ _ h
    exact ⟨sv, by simp [State.findLive, hl]⟩
  | @field a r segs n s₀ f T hp hf ih =>
    intro ⟨old, hold⟩
    rw [findLive_append] at hold
    obtain ⟨pre, hpre, -⟩ := bind_ok_inv hold
    obtain ⟨sv', hsv'⟩ := ih ⟨pre, hpre⟩
    rcases find_repr hs' hp with ⟨sv, hsv, hr⟩ | ⟨_, hsv⟩
    · cases hr with
      | struct hex _ =>
        obtain ⟨v, hv⟩ := hex f T hf
        exact ⟨v, by rw [findLive_append, hsv]; simp [bind, Except.bind, SVal.findLive, hv]⟩
    · rw [hsv] at hsv'; cases hsv'
  | @key a r segs V s₀ k hp h0 h1 ih =>
    intro ⟨old, hold⟩
    rw [findLive_append] at hold
    obtain ⟨pre, hpre, -⟩ := bind_ok_inv hold
    obtain ⟨sv', hsv'⟩ := ih ⟨pre, hpre⟩
    rcases find_repr hs' hp with ⟨sv, hsv, hr⟩ | ⟨_, hsv⟩
    · cases hr with
      | @map _ _ entries dflt _ =>
        refine ⟨(lookupBy k entries).getD dflt, ?_⟩
        rw [findLive_append, hsv]
        simp only [bind, Except.bind, SVal.findLive]
        cases lookupBy k entries <;> simp
      | mapOther hK => exact absurd rfl hK
    · rw [hsv] at hsv'; cases hsv'
  | @elem r segs E s₀ i hp h0 h1 ih =>
    intro ⟨old, hold⟩
    rw [findLive_append] at hold
    obtain ⟨pre, hpre, hat⟩ := bind_ok_inv hold
    obtain ⟨sv', hsv'⟩ := ih ⟨pre, hpre⟩
    rcases find_repr hs hp with ⟨sv₀, hsv₀, hr₀⟩ | ⟨_, hsv₀⟩
    · rw [hpre] at hsv₀; cases hsv₀
      rcases find_repr hs' hp with ⟨sv, hsv, hr⟩ | ⟨_, hsv⟩
      · cases hr₀ with
        | @array _ _ elems₀ shadow₀ hl₀ _ _ =>
          cases hr with
          | @array _ _ elems shadow hl _ _ =>
            have hb₀ : i.toNat < elems₀.length := by
              refine Decidable.byContradiction fun hb => ?_
              simp [SVal.findLive, hb] at hat
            have := hlen s₀ ⟨false, r, segs, E, hp⟩
            refine ⟨elems[i.toNat]'(by omega), ?_⟩
            rw [findLive_append, hsv]
            simp [bind, Except.bind, SVal.findLive, h0, show i.toNat < elems.length by omega]
      · rw [hsv] at hsv'; cases hsv'
    · rw [hpre] at hsv₀; cases hsv₀
  | @felem r segs E n s₀ i hp h0 h1 ih =>
    intro ⟨old, hold⟩
    rw [findLive_append] at hold
    obtain ⟨pre, hpre, -⟩ := bind_ok_inv hold
    obtain ⟨sv', hsv'⟩ := ih ⟨pre, hpre⟩
    rcases find_repr hs' hp with ⟨sv, hsv, hr⟩ | ⟨_, hsv⟩
    · cases hr with
      | @fixed _ _ _ elems shadow hl _ =>
        refine ⟨elems[i.toNat]'(by omega), ?_⟩
        rw [findLive_append, hsv]
        simp [bind, Except.bind, SVal.findLive, h0, show i.toNat < elems.length by omega]
    · rw [hsv] at hsv'; cases hsv'

/-! ## A fresh contract -/

/-- An all-zero storage represents every type's default: a fresh `Person` is
three zero slots, a fresh `mapping(uint => Person)` maps every key to one. -/
theorem default_repr (hL : 0 < L) : ∀ (T : Ty) (s : Slot), ReprAt (fun _ => 0) L T s (defaultForTy T)
  | .prim .uint, s => by
    rw [defaultForTy]; exact .uint (Int.le_refl 0) (by have := W_pos; omega) rfl
  | .prim .bool, s => by rw [defaultForTy]; exact .bool rfl
  | .prim .int, s => by rw [defaultForTy]; exact .int W_pos rfl
  | .ref (.struct n), s => by
    rw [defaultForTy]
    refine .struct (fun f T hT => ?_) (fun f T v hT hv => ?_)
    · exact ⟨defaultForTy T, by rw [lookupBy_defaultForFields, hT]; rfl⟩
    · rw [lookupBy_defaultForFields, hT] at hv
      cases hv
      exact default_repr hL T _
  | .ref (.array _), s => by rw [defaultForTy]; exact .array rfl hL nofun
  | .ref (.fixed E n), s => by
    rw [defaultForTy]
    exact .fixed (by simp) fun i hi => by
      simp only [List.getElem_replicate]; exact default_repr hL E _
  | .ref (.mapping K V), s => by
    rw [defaultForTy]
    by_cases hK : K = .prim .uint
    · subst hK; exact .map fun k _ => by simpa [lookupBy] using default_repr hL V _
    · exact .mapOther hK
termination_by T => (tyRank T, sizeOf T)
decreasing_by
  · exact Prod.Lex.left _ _ (tyRank_member (lookupBy_eq_some_mem hT))
  all_goals first
    | (apply Prod.Lex.left; simp [tyRank]; done)
    | (apply Prod.Lex.right; simp; omega)

/-- A fresh contract's state variable is its type's default: `uint total;` starts at `0`. -/
theorem lookupBy_initStorage (C : Contract) (r : Name) :
    lookupBy r C.initStorage = (C.rootType r).map defaultForTy := by
  simp only [Contract.initStorage, Contract.rootType]
  induction C.vars with
  | nil => rfl
  | cons x l ih =>
    obtain ⟨g, T⟩ := x
    simp only [List.map, lookupBy]
    split
    · rfl
    · exact ih

/-- A fresh contract's storage is represented by the all-zero machine storage. -/
theorem initStorage_repr (C : Contract) (hL : 0 < L) : ReprStore C L (fun _ => 0) C.initStorage :=
  fun r T h => ⟨defaultForTy T, by rw [lookupBy_initStorage, h]; rfl, default_repr hL T _⟩

end Evm
end Solidity
