import Solidity.Evm.Compile

/-!
# The machine's storage represents the interpreter's

`ReprAt st T s v`: the storage tree `v`, of type `T`, is laid out in the
machine storage `st` from slot `s` — every `uint` and `bool` at its slot, every
array's length at its own slot and its live elements at theirs, every entry of
a `uint`-keyed mapping at its hashed slot.  `ReprStore` says it of every state
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

What `ReprAt` does not constrain, it does not need to: an array's popped slots
(the interpreter's `shadow`), an `int`, a mapping keyed by other than `uint`.
The compiler rejects every read of those.
-/

namespace Solidity
namespace Evm

open Semantics SemanticsProperties

/-! ## Paths through the storage tree -/

/-- Reading at the empty path reads the whole value: `alice` itself. -/
@[simp] theorem SVal.find_nil (v : SVal) : v.find [] = .ok v := by cases v <;> rfl

/-- Writing at the empty path replaces the whole value: `alice = …` at `alice`. -/
@[simp] theorem SVal.save_nil (v new : SVal) : v.save [] new = .ok new := by cases v <;> rfl

/-- Reading along `segs ++ rest` is reading `segs`, then `rest` from there:
`alice.account.balance` is `alice.account`, then `.balance`. -/
theorem SVal.find_append : ∀ (v : SVal) (segs rest : List Seg),
    v.find (segs ++ rest) = (v.find segs >>= fun w => w.find rest)
  | v, [], rest => by simp; rfl
  | .prim _, _ :: _, _ => by simp [SVal.find]; rfl
  | .struct fields, .field name :: segs, rest => by
    simp only [List.cons_append, SVal.find]
    split
    · exact SVal.find_append _ _ _
    · rfl
  | .struct _, .at _ :: _, _ => by simp [SVal.find]; rfl
  | .array elems _, .at i :: segs, rest => by
    simp only [List.cons_append, SVal.find]
    split
    · exact SVal.find_append _ _ _
    · rfl
  | .array elems sh, .field name :: segs, rest => by
    by_cases h : name = "length"
    · subst h; simp only [List.cons_append, SVal.find]; exact SVal.find_append _ _ _
    · have e : ∀ l, SVal.find (.array elems sh) (.field name :: l) = .error .stuck := by
        intro l; simp [SVal.find]
      simp only [List.cons_append, e]; rfl
  | .map entries dflt, .at i :: segs, rest => by
    simp only [List.cons_append, SVal.find]
    split
    · exact SVal.find_append _ _ _
    · exact SVal.find_append _ _ _
  | .map _ _, .field _ :: _, _ => by simp [SVal.find]; rfl

@[simp] theorem SVal.findLive_nil (v : SVal) : v.findLive [] = .ok v := by cases v <;> rfl

/-- `SVal.find_append` for the live read. -/
theorem SVal.findLive_append : ∀ (v : SVal) (segs rest : List Seg),
    v.findLive (segs ++ rest) = (v.findLive segs >>= fun w => w.findLive rest)
  | v, [], rest => by simp; rfl
  | .prim _, _ :: _, _ => by simp [SVal.findLive]; rfl
  | .struct fields, .field name :: segs, rest => by
    simp only [List.cons_append, SVal.findLive]
    split
    · exact SVal.findLive_append _ _ _
    · rfl
  | .struct _, .at _ :: _, _ => by simp [SVal.findLive]; rfl
  | .array elems _, .at i :: segs, rest => by
    simp only [List.cons_append, SVal.findLive]
    split
    · exact SVal.findLive_append _ _ _
    · rfl
  | .array elems sh, .field name :: segs, rest => by
    by_cases h : name = "length"
    · subst h; simp only [List.cons_append, SVal.findLive]; exact SVal.findLive_append _ _ _
    · have e : ∀ l, SVal.findLive (.array elems sh) (.field name :: l) = .error .stuck := by
        intro l; simp [SVal.findLive]
      simp only [List.cons_append, e]; rfl
  | .map entries dflt, .at i :: segs, rest => by
    simp only [List.cons_append, SVal.findLive]
    split
    · exact SVal.findLive_append _ _ _
    · exact SVal.findLive_append _ _ _
  | .map _ _, .field _ :: _, _ => by simp [SVal.findLive]; rfl

/-- A write along a path the read fails on fails the same way: `persons[5].age
= 1;` with three persons reverts, as reading `persons[5]` does. -/
theorem SVal.save_error : ∀ (v : SVal) (segs rest : List Seg) (new : SVal) (e : Halt),
    v.find segs = .error e → v.save (segs ++ rest) new = .error e
  | v, [], rest, new, e, h => by simp at h
  | .prim _, _ :: _, _, _, e, h => by simp [SVal.find] at h; simp [SVal.save, h]
  | .struct fields, .field name :: segs, rest, new, e, h => by
    simp only [List.cons_append, SVal.save]
    simp only [SVal.find] at h
    split
    · rename_i old hold
      rw [hold] at h
      rw [SVal.save_error old segs rest new e h]; rfl
    · rename_i hn; rw [hn] at h; exact h
  | .struct _, .at _ :: _, _, _, e, h => by simp [SVal.find] at h; simp [SVal.save, h]
  | .array elems sh, .at i :: segs, rest, new, e, h => by
    simp only [List.cons_append, SVal.save]
    simp only [SVal.find] at h
    split
    · rename_i hb; rw [dif_pos hb] at h; rw [SVal.save_error _ segs rest new e h]; rfl
    · rename_i hb; rw [dif_neg hb] at h; exact h
  | .array elems sh, .field name :: segs, rest, new, e, h => by
    by_cases hn : name = "length"
    · subst hn
      cases segs with
      | nil => simp [SVal.find] at h
      | cons s segs => simp [SVal.find] at h; simp [SVal.save, h]
    · simp [SVal.find] at h; simp [SVal.save, h]
  | .map entries dflt, .at i :: segs, rest, new, e, h => by
    simp only [List.cons_append, SVal.save]
    simp only [SVal.find] at h
    split
    · rename_i old hold; rw [hold] at h; rw [SVal.save_error _ segs rest new e h]; rfl
    · rename_i hold; rw [hold] at h; rw [SVal.save_error _ segs rest new e h]; rfl
  | .map _ _, .field _ :: _, _, _, e, h => by simp [SVal.find] at h; simp [SVal.save, h]

/-- A write along `segs ++ rest`, where `segs` reads `sub`, writes `rest` into
`sub` and puts the result back at `segs`: `alice.age = 1;` rebuilds `alice`
with its `age` replaced. -/
theorem SVal.save_append : ∀ (v : SVal) (segs rest : List Seg) (new sub : SVal),
    v.find segs = .ok sub → v.save (segs ++ rest) new = (sub.save rest new >>= v.save segs)
  | v, [], rest, new, sub, h => by
    simp at h; subst h
    simp only [List.nil_append]
    cases v.save rest new with
    | error e => rfl
    | ok a => exact (SVal.save_nil v a).symm
  | .prim _, _ :: _, _, _, _, h => by simp [SVal.find] at h
  | .struct fields, .field name :: segs, rest, new, sub, h => by
    simp only [List.cons_append, SVal.save]
    simp only [SVal.find] at h
    split
    · rename_i old hold
      rw [hold] at h
      rw [SVal.save_append old segs rest new sub h]
      cases sub.save rest new <;> rfl
    · rename_i hn; rw [hn] at h; cases h
  | .struct _, .at _ :: _, _, _, _, h => by simp [SVal.find] at h
  | .array elems sh, .at i :: segs, rest, new, sub, h => by
    simp only [List.cons_append, SVal.save]
    simp only [SVal.find] at h
    split
    · rename_i hb; rw [dif_pos hb] at h; rw [SVal.save_append _ segs rest new sub h]
      cases sub.save rest new <;> rfl
    · rename_i hb; rw [dif_neg hb] at h; cases h
  | .array elems sh, .field name :: segs, rest, new, sub, h => by
    by_cases hn : name = "length"
    · subst hn
      cases segs with
      | nil =>
        simp [SVal.find] at h; subst h
        cases rest <;> simp [SVal.save] <;> rfl
      | cons s segs => simp [SVal.find] at h
    · simp [SVal.find] at h
  | .map entries dflt, .at i :: segs, rest, new, sub, h => by
    simp only [List.cons_append, SVal.save]
    simp only [SVal.find] at h
    split
    · rename_i old hold; rw [hold] at h; rw [SVal.save_append _ segs rest new sub h]
      cases sub.save rest new <;> rfl
    · rename_i hold; rw [hold] at h; rw [SVal.save_append _ segs rest new sub h]
      cases sub.save rest new <;> rfl
  | .map _ _, .field _ :: _, _, _, _, h => by simp [SVal.find] at h

/-- `findStorage` along `segs ++ rest`: `folks[7].age` is `folks[7]`, then
`.age`. -/
theorem findStorage_append (σ : State) (r : Name) (segs rest : List Seg) :
    σ.findStorage r (segs ++ rest) = (σ.findStorage r segs >>= fun w => w.find rest) := by
  unfold State.findStorage
  split
  · exact SVal.find_append _ _ _
  · rfl

/-- `findStorage_append` for the live read. -/
theorem findLive_append (σ : State) (r : Name) (segs rest : List Seg) :
    σ.findLive r (segs ++ rest) = (σ.findLive r segs >>= fun w => w.findLive rest) := by
  unfold State.findLive
  split
  · exact SVal.findLive_append _ _ _
  · rfl

/-- A write at a live element replaces it: `persons[0] = p;` with one person. -/
theorem SVal.save_live {elems shadow : List SVal} {i : Int} {rest : List Seg} {new u : SVal}
    (h0 : 0 ≤ i) (hb : i.toNat < elems.length)
    (hu : (elems[i.toNat]'hb).save rest new = .ok u) :
    (SVal.array elems shadow).save (.at i :: rest) new =
      .ok (.array (elems.set i.toNat u) shadow) := by
  have hb' : 0 ≤ i ∧ i.toNat < (elems ++ shadow).length := by
    simp only [List.length_append]; omega
  simp only [SVal.save, dif_pos hb', List.get_eq_getElem, List.getElem_append_left hb, hu,
    bind, Except.bind, List.set_append_left _ _ hb, List.take_left', List.drop_left',
    List.length_set]

/-- A state variable's write fails where its read does: `persons[5].age = 1;` with three persons. -/
theorem saveStorage_error {σ : State} {r : Name} {segs : List Seg} {e : Halt}
    (h : σ.findStorage r segs = .error e) (rest : List Seg) (new : SVal) :
    σ.saveStorage r (segs ++ rest) new = .error e := by
  unfold State.findStorage at h
  unfold State.saveStorage
  split
  · rename_i v hv; rw [hv] at h; rw [SVal.save_error v segs rest new e h]; rfl
  · rename_i hv; simp only [hv, Except.error.injEq] at h; subst h; rfl

/-- A state variable's write along `segs ++ rest` writes `rest` below `segs`: `alice.age = 1;`. -/
theorem saveStorage_append {σ : State} {r : Name} {segs : List Seg} {sub : SVal}
    (h : σ.findStorage r segs = .ok sub) (rest : List Seg) (new : SVal) :
    σ.saveStorage r (segs ++ rest) new = (sub.save rest new >>= σ.saveStorage r segs) := by
  unfold State.findStorage at h
  unfold State.saveStorage
  split
  · rename_i v hv
    rw [hv] at h
    rw [SVal.save_append v segs rest new sub h]
    cases sub.save rest new <;> rfl
  · rename_i hv; rw [hv] at h; cases h

/-! ## The representation -/

/-- A stack word represents a value of primitive type `p`: a `uint` below
`2^256` as itself, a `bool` as `1` or `0`.  Nothing represents an `int`. -/
def ReprV : PrimTy → Value → Word → Prop
  | .uint, .int n, .val w => 0 ≤ n ∧ n < W ∧ w = n.toNat
  | .bool, .bool b, .val w => w = bword b
  | _, _, _ => False

/-- `ReprAt st T s v`: the storage value `v` of type `T` is laid out in `st`
from slot `s`. -/
inductive ReprAt (st : Slot → Nat) : Ty → Slot → SVal → Prop
  | uint {s : Slot} {n : Int} : 0 ≤ n → n < W → st s = n.toNat →
      ReprAt st (.prim .uint) s (.prim (.int n))
  | bool {s : Slot} {b : Bool} : st s = bword b → ReprAt st (.prim .bool) s (.prim (.bool b))
  | int {s : Slot} {v : SVal} : ReprAt st (.prim .int) s v
  | struct {n : Name} {s : Slot} {fields : List (Name × SVal)} :
      (∀ f T, lookupBy f (structDef n) = some T → ∃ v, lookupBy f fields = some v) →
      (∀ f T v, lookupBy f (structDef n) = some T → lookupBy f fields = some v →
        ReprAt st T (s.add (offset n f)) v) →
      ReprAt st (.ref (.struct n)) s (.struct fields)
  | array {E : Ty} {s : Slot} {elems shadow : List SVal} :
      st s = elems.length → elems.length < W →
      (∀ i (h : i < elems.length), ReprAt st E (.data s (i * size E)) elems[i]) →
      ReprAt st (.ref (.array E)) s (.array elems shadow)
  | map {V : Ty} {s : Slot} {entries : List (Int × SVal)} {dflt : SVal} :
      (∀ k, k < W → ReprAt st V (.hash k s 0) ((lookupBy (k : Int) entries).getD dflt)) →
      ReprAt st (.ref (.mapping (.prim .uint) V)) s (.map entries dflt)
  | mapOther {K V : Ty} {s : Slot} {v : SVal} : K ≠ .prim .uint →
      ReprAt st (.ref (.mapping K V)) s v

/-- A representation looks only at the slots the value occupies.

Example: `bob` is represented in slots `[14, 17)`; a write to `alice.age`
(slot `13`) keeps it represented. -/
theorem ReprAt.frame {st st' : Slot → Nat} {T : Ty} {s : Slot} {v : SVal}
    (h : ReprAt st T s v) (hf : ∀ x, Occ T s x → st' x = st x) : ReprAt st' T s v := by
  induction h with
  | uint h0 h1 h2 => exact .uint h0 h1 (by rw [hf _ .prim, h2])
  | bool h => exact .bool (by rw [hf _ .prim, h])
  | int => exact .int
  | struct hex _ ih =>
    exact .struct hex fun f T v hT hv => ih f T v hT hv fun x hx => hf x (.field hT hx)
  | array hl hW _ ih =>
    exact .array (by rw [hf _ .len, hl]) hW fun i hi => ih i hi fun x hx => hf x (.elem i hx)
  | map _ ih => exact .map fun k hk => ih k hk fun x hx => hf x (.entry k hx)
  | mapOther hK => exact .mapOther hK

/-- Every state variable is represented at its slot. -/
def ReprStore (C : Contract) (st : Slot → Nat) (stor : List (Name × SVal)) : Prop :=
  ∀ r T, C.rootType r = some T → ∃ sv, lookupBy r stor = some sv ∧ ReprAt st T (rootSlot C r) sv

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

/-- A path that indexes no array is a path: `folks[7].age`. -/
theorem PathSlot.weaken {C : Contract} {a : Bool} {r : Name} {segs : List Seg} {T : Ty} {s : Slot}
    (h : PathSlot C a r segs T s) : PathSlot C false r segs T s := by
  induction h with
  | root h => exact .root h
  | field _ hf ih => exact .field ih hf
  | key _ h0 h1 ih => exact .key ih h0 h1
  | elem _ h0 h1 ih => exact .elem ih h0 h1

/-! ## Reading -/

/-- A member that `lookupBy` finds is in the list: `age` is a member of `Person`. -/
theorem lookupBy_some_mem {κ α : Type} [DecidableEq κ] {k : κ} {v : α} :
    ∀ {l : List (κ × α)}, lookupBy k l = some v → (k, v) ∈ l
  | [], h => by simp [lookupBy] at h
  | (k', v') :: l, h => by
    simp only [lookupBy] at h
    split at h
    · cases h; rename_i hk; subst hk; exact List.mem_cons_self
    · exact List.mem_cons_of_mem _ (lookupBy_some_mem h)

/-- A typed path reads a value its slot represents, or (if it indexes an
array) reverts out of bounds.

Example: `folks[7].age` reads what slot `keccak(7, 7) + 2` holds; with three
`persons`, `persons[5].age` reverts. -/
theorem find_repr {C : Contract} {st : Slot → Nat} {σ : State} (hs : ReprStore C st σ.storage)
    {a : Bool} {r : Name} {segs : List Seg} {T : Ty} {s : Slot} (hp : PathSlot C a r segs T s) :
    (∃ sv, σ.findLive r segs = .ok sv ∧ ReprAt st T s sv) ∨
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
theorem save_repr {C : Contract} {st : Slot → Nat} {σ : State} (hs : ReprStore C st σ.storage)
    {a : Bool} {r : Name} {segs : List Seg} {T : Ty} {s : Slot} (hp : PathSlot C a r segs T s) :
    ∀ {st' : Slot → Nat} {new : SVal}, (∃ old, σ.findLive r segs = .ok old) →
      ReprAt st' T s new → (∀ x, ¬ Occ T s x → st' x = st x) →
      ∃ stor, σ.saveStorage r segs new = .ok { σ with storage := stor } ∧ ReprStore C st' stor := by
  induction hp with
  | @root a r T h =>
    intro st' new _ hnew hout
    obtain ⟨sv, hl, _⟩ := hs _ _ h
    refine ⟨setBy r new σ.storage, by simp [State.saveStorage, hl]; rfl, ?_⟩
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
        rw [saveStorage_append (State.findStorage_of_findLive hsv)]
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
        rw [saveStorage_append (State.findStorage_of_findLive hsv)]
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
        obtain ⟨stor, hsave, hrep⟩ := ih (st' := st') (new := .array (elems.set i.toNat new) shadow)
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
        rw [saveStorage_append (State.findStorage_of_findLive hsv)]
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

/-- A deleted struct's member is the member deleted: `delete alice;` makes `alice.age` `0`. -/
theorem lookupBy_defaultOfFields (g : Name) : ∀ (fields : List (Name × SVal)),
    lookupBy g (SVal.defaultOf.defaultOfFields fields) = (lookupBy g fields).map SVal.defaultOf
  | [] => rfl
  | (h, v) :: fields => by
    simp only [SVal.defaultOf.defaultOfFields, lookupBy]
    split
    · rfl
    · exact lookupBy_defaultOfFields g fields

/-- **`delete` is represented by zeroing its leaves.**  If `st'` is zero at
every slot `delete` writes (`leavesF`) and agrees with `st` on the rest of what
the value occupies, it represents the value's default (`SVal.defaultOf`).

Example: `delete wallet;` zeroes `wallet.owner`'s slot and leaves
`wallet.stash`'s entries where they are, and `SVal.defaultOf` keeps the
mapping's entries too. -/
theorem zero_repr {st st' : Slot → Nat} {T : Ty} {s : Slot} {sv : SVal} (h : ReprAt st T s sv) :
    ∀ fuel, tyRank T < fuel → (∀ o ∈ leavesF fuel T, st' (s.add o) = 0) →
      (∀ x, Occ T s x → (∀ o ∈ leavesF fuel T, x ≠ s.add o) → st' x = st x) →
      ReprAt st' T s sv.defaultOf := by
  induction h with
  | uint =>
    intro fuel _ hz _
    exact .uint (Int.le_refl 0) (by have := W_pos; omega)
      (by simpa using hz 0 (by simp [leavesF]))
  | bool =>
    intro fuel _ hz _
    exact .bool (by simpa [bword] using hz 0 (by simp [leavesF]))
  | int => intro _ _ _ _; exact .int
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
        have hmem := lookupBy_some_mem hg
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
    exact .array (by simpa using hz 0 (by simp [leavesF])) (by simpa using W_pos)
      fun i hi => absurd hi (Nat.not_lt_zero _)
  | map hall =>
    intro fuel _ _ ho
    exact .map fun k hk => (hall k hk).frame fun x hx => ho x (.entry k hx) (by simp [leavesF])
  | mapOther hK => intro _ _ _ _; exact .mapOther hK

/-- **`pop` is represented by decrementing the length.**  The popped element's
slots are left as they are: `ReprAt` constrains only the live elements, so
whatever the recycled slot holds (`x`: the element cleared, or kept) is
represented.

Example: with `values = [1, 2]`, `values.pop();` writes `1` to slot `4`;
`keccak(4) + 1` still holds `2`, and nothing reads it. -/
theorem pop_repr {st : Slot → Nat} {E : Ty} {s : Slot} {elems shadow restRev : List SVal}
    {last : SVal} (x : SVal) (h : ReprAt st (.ref (.array E)) s (.array elems shadow))
    (hrev : elems.reverse = last :: restRev) :
    ReprAt (upd st s (elems.length - 1)) (.ref (.array E)) s
      (.array restRev.reverse (x :: shadow)) := by
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

/-! ## A fresh contract -/

/-- A fresh struct's member is its type's default: a fresh `Person`'s `age` is `0`. -/
theorem lookupBy_defaultForFields (f : Name) : ∀ (l : List (Name × Ty)),
    lookupBy f (defaultForFields l) = (lookupBy f l).map defaultForTy
  | [] => by simp [defaultForFields, lookupBy]
  | (g, T) :: l => by
    rw [defaultForFields]
    simp only [lookupBy]
    split
    · rfl
    · exact lookupBy_defaultForFields f l

/-- An all-zero storage represents every type's default: a fresh `Person` is
three zero slots, a fresh `mapping(uint => Person)` maps every key to one. -/
theorem default_repr : ∀ (T : Ty) (s : Slot), ReprAt (fun _ => 0) T s (defaultForTy T)
  | .prim .uint, s => by
    rw [defaultForTy]; exact .uint (Int.le_refl 0) (by have := W_pos; omega) rfl
  | .prim .bool, s => by rw [defaultForTy]; exact .bool rfl
  | .prim .int, s => .int
  | .ref (.struct n), s => by
    rw [defaultForTy]
    refine .struct (fun f T hT => ?_) (fun f T v hT hv => ?_)
    · exact ⟨defaultForTy T, by rw [lookupBy_defaultForFields, hT]; rfl⟩
    · rw [lookupBy_defaultForFields, hT] at hv
      cases hv
      exact default_repr T _
  | .ref (.array _), s => by rw [defaultForTy]; exact .array rfl W_pos nofun
  | .ref (.mapping K V), s => by
    rw [defaultForTy]
    by_cases hK : K = .prim .uint
    · subst hK; exact .map fun k _ => by simpa [lookupBy] using default_repr V _
    · exact .mapOther hK
termination_by T => (tyRank T, sizeOf T)
decreasing_by
  · exact Prod.Lex.left _ _ (tyRank_member (lookupBy_some_mem hT))
  · apply Prod.Lex.right; simp; omega

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
theorem initStorage_repr (C : Contract) : ReprStore C (fun _ => 0) C.initStorage :=
  fun r T h => ⟨defaultForTy T, by rw [lookupBy_initStorage, h]; rfl, default_repr T _⟩

end Evm
end Solidity
