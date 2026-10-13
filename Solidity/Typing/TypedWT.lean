import Solidity.Typing.Soundness
import Solidity.Semantics.State
import Solidity.Semantics.TypedErase

/-!
# A typed state erases to a well-typed one

By construction (`docs/intrinsic.md`, W1, lane `typing`): a typed
state (`State`, `Semantics/State.lean`) holds storage values of their
types and a heap whose objects are of the types its typing lists, so its
erasure's global part is well-typed under the store typing its heap typing
lists (`HTy.toHeapTy`), with no run to follow (`State.glob_wt`): type soundness of the typed run, with no
preservation proof (the scoped run's `Stmt.run_wt` went with that run,
`docs/intrinsic.md`, decision 40).

The untyped typing (`SVal.hasTy`, `MObj.hasTyH`) reads a struct's members
by name, the typed value by position; the two agree since no struct has two
members of one name (`structDef_nodup`, decision 16).  The theorem
takes the layout's keys distinct.
-/

namespace Solidity

open Semantics (structDef lookupBy nodupKeysB HeapTy lookupBy_eq_of_nodup wellTypedStorageB
  tyAtSegs segTy)
open SemanticsProperties (HeapWellFormed)

variable {C : Contract}

/-! ## Storage values -/

mutual

theorem SVal.erase_hasTy : {T : Ty} → (v : SVal T) → v.erase.hasTy T = true
  | _, .prim (p := p) x => by
    rw [SVal.erase_prim]
    cases p <;> rfl
  | _, .struct (s := s) fs => by
    rw [SVal.erase_struct]
    exact SFields.erase_hasTy s fs fun _ hm => lookupBy_eq_of_nodup (structDef_nodup s) hm
  | _, .array e sh _ => by
    rw [SVal.erase_array]
    simp only [Semantics.SVal.hasTy, Bool.not_false, Bool.true_and, Bool.and_eq_true]
    exact ⟨SVec.erase_hasTy e, SList.erase_hasTy sh⟩
  | _, .fixed (n := n) e => by
    rw [SVal.erase_fixed]
    simp only [Semantics.SVal.hasTy, SVec.length_erase, beq_self_eq_true, Bool.true_and,
      Bool.and_eq_true]
    exact ⟨SVec.erase_hasTy e, rfl⟩
  | _, .map m d => by
    rw [SVal.erase_map]
    simp only [Semantics.SVal.hasTy, Bool.and_eq_true]
    exact ⟨SMap.erase_hasTy m, SVal.erase_hasTy d⟩

theorem SFields.erase_hasTy (s : Name) : {fs : List (Name × Ty)} → (x : SFields fs) →
    (∀ fT ∈ fs, lookupBy fT.1 (structDef s) = some fT.2) →
    Semantics.SVal.hasTy.hasTyFields s x.erase = true
  | _, .nil, _ => by rw [SFields.erase_nil]; rfl
  | _, .cons (f := f) (T := T) v rest, hl => by
    rw [SFields.erase_cons]
    simp only [Semantics.SVal.hasTy.hasTyFields, hl (f, T) List.mem_cons_self,
      SVal.erase_hasTy v, Bool.true_and]
    exact SFields.erase_hasTy s rest fun fT hm => hl fT (List.mem_cons_of_mem _ hm)

theorem SList.erase_hasTy : {E : Ty} → (l : SList E) →
    Semantics.SVal.hasTy.hasTyElems E l.erase = true
  | _, .nil => by rw [SList.erase_nil]; rfl
  | _, .cons v rest => by
    rw [SList.erase_cons]
    simp only [Semantics.SVal.hasTy.hasTyElems, SVal.erase_hasTy v, SList.erase_hasTy rest,
      Bool.and_self]

theorem SVec.erase_hasTy : {E : Ty} → {n : Nat} → (l : SVec E n) →
    Semantics.SVal.hasTy.hasTyElems E l.erase = true
  | _, _, .nil => by rw [SVec.erase_nil]; rfl
  | _, _, .cons v rest => by
    rw [SVec.erase_cons]
    simp only [Semantics.SVal.hasTy.hasTyElems, SVal.erase_hasTy v, SVec.erase_hasTy rest,
      Bool.and_self]

theorem SMap.erase_hasTy : {V : Ty} → (m : SMap V) →
    Semantics.SVal.hasTy.hasTyEntries V m.erase = true
  | _, .nil => by rw [SMap.erase_nil]; rfl
  | _, .cons _ v rest => by
    rw [SMap.erase_cons]
    simp only [Semantics.SVal.hasTy.hasTyEntries, SVal.erase_hasTy v, SMap.erase_hasTy rest,
      Bool.and_self]

end

/-- A typed storage erases to a well-typed one. -/
theorem Storage.erase_wt (hnd : nodupKeysB C.vars = true) (st : Storage C) :
    wellTypedStorageB C.layout st.erase = true := by
  refine List.all_eq_true.mpr fun g hg => ?_
  have hl : lookupBy g.1 C.vars = some g.2 := lookupBy_eq_of_nodup hnd hg
  show (match lookupBy g.1 (SFields.erase st) with
    | some v => v.hasTy g.2
    | none => false) = true
  rw [SFields.lookupBy_erase st hl]
  exact SVal.erase_hasTy _

/-! ## Paths -/

theorem tyAtSegs_erase : {T U : Ty} → (p : Path T U) → tyAtSegs T p.erase = some U
  | _, _, .nil => rfl
  | _, _, .field h p => by
    simp only [Path.erase, tyAtSegs, segTy, h]
    exact tyAtSegs_erase p
  | _, _, .at _ p => by
    simp only [Path.erase, tyAtSegs, segTy]
    exact tyAtSegs_erase p
  | _, _, .atF _ p => by
    simp only [Path.erase, tyAtSegs, segTy]
    exact tyAtSegs_erase p
  | _, _, .key _ p => by
    simp only [Path.erase, tyAtSegs, segTy]
    exact tyAtSegs_erase p

/-- A typed storage reference names a path the layout types at its type. -/
theorem SRef.tyAt_erase {U : Ty} (r : SRef C U) :
    C.layout.tyAt r.erase.1 r.erase.2 = some U := by
  have h : lookupBy r.root C.vars = some r.ty := r.hroot
  simp only [SRef.erase, Semantics.Layout.tyAt, Contract.layout, h]
  exact tyAtSegs_erase r.path

/-! ## The heap -/

/-- The store typing a heap typing lists: identity `start + i` at its `i`-th
type. -/
def HTy.toHeapTy (start : Nat) : HTy → HeapTy
  | [] => []
  | R :: H => (start, .ref R) :: HTy.toHeapTy (start + 1) H

theorem HTy.mem_toHeapTy {start : Nat} : {H : HTy} → {e : Nat × Ty} → e ∈ HTy.toHeapTy start H →
    start ≤ e.1
  | _ :: _, _, .head _ => Nat.le_refl _
  | _ :: _, _, .tail _ h => Nat.le_of_succ_le (HTy.mem_toHeapTy h)

theorem HTy.lookupBy_toHeapTy_lt {start k : Nat} (hk : k < start) :
    (H : HTy) → lookupBy k (HTy.toHeapTy start H) = none
  | [] => rfl
  | _ :: H => by
    simp only [HTy.toHeapTy, lookupBy, Nat.ne_of_lt hk, ↓reduceIte]
    exact HTy.lookupBy_toHeapTy_lt (Nat.lt_succ_of_lt hk) H

theorem HTy.lookupBy_toHeapTy {start : Nat} : (H : HTy) → (i : Nat) →
    lookupBy (start + i) (HTy.toHeapTy start H) = H[i]?.map (Ty.ref ·)
  | [], _ => rfl
  | _ :: _, 0 => by simp only [HTy.toHeapTy, Nat.add_zero, lookupBy, ↓reduceIte,
      List.getElem?_cons_zero, Option.map_some]
  | _ :: H, i + 1 => by
    simp only [HTy.toHeapTy, lookupBy, List.getElem?_cons_succ]
    rw [if_neg (by omega), show start + (i + 1) = (start + 1) + i by omega]
    exact HTy.lookupBy_toHeapTy H i

theorem HTy.nodup_toHeapTy {start : Nat} : (H : HTy) → nodupKeysB (HTy.toHeapTy start H) = true
  | [] => rfl
  | _ :: H => by
    simp only [HTy.toHeapTy, nodupKeysB, Bool.and_eq_true, Option.isNone_iff_eq_none]
    exact ⟨HTy.lookupBy_toHeapTy_lt (Nat.lt_succ_self _) H, HTy.nodup_toHeapTy H⟩

theorem HRef.lookupBy_toHeapTy {H : HTy} {R : RefTy} (r : HRef H R) :
    lookupBy r.id (HTy.toHeapTy 0 H) = some (.ref R) := by
  have := HTy.lookupBy_toHeapTy (start := 0) H r.id
  rw [Nat.zero_add, r.get?, Option.map_some] at this
  exact this

theorem MVal.erase_hasTyH {H : HTy} : (T : Ty) → (v : MVal H T) →
    Semantics.MVal.hasTyH (HTy.toHeapTy 0 H) (MVal.erase T v) T = true
  | .prim .uint, _ | .prim .int, _ | .prim .bool, _ => rfl
  | .ref R, r => by
    simp only [MVal.erase, Semantics.MVal.hasTyH, HRef.lookupBy_toHeapTy, beq_self_eq_true]

theorem MFields.erase_hasTyH {H : HTy} (s : Name) : (fs : List (Name × Ty)) → (x : MFields H fs) →
    (∀ fT ∈ fs, lookupBy fT.1 (structDef s) = some fT.2) →
    Semantics.MObj.hasTyH.hasTyHFields (HTy.toHeapTy 0 H) s (MFields.erase fs x) = true
  | [], _, _ => rfl
  | (f, T) :: fs, x, hl => by
    simp only [MFields.erase, Semantics.MObj.hasTyH.hasTyHFields, hl (f, T) List.mem_cons_self,
      MVal.erase_hasTyH T x.1, Bool.true_and]
    exact MFields.erase_hasTyH s fs x.2 fun fT hm => hl fT (List.mem_cons_of_mem _ hm)

theorem MVal.erase_hasTyHElems {H : HTy} (E : Ty) : (l : List (MVal H E)) →
    Semantics.MObj.hasTyH.hasTyHElems (HTy.toHeapTy 0 H) E (l.map (MVal.erase E)) = true
  | [] => rfl
  | v :: l => by
    simp only [List.map_cons, Semantics.MObj.hasTyH.hasTyHElems, MVal.erase_hasTyH E v,
      MVal.erase_hasTyHElems E l, Bool.and_self]

theorem MObj.erase_hasTyH {H : HTy} : (R : RefTy) → (o : MObj H R) →
    Semantics.MObj.hasTyH (HTy.toHeapTy 0 H) (MObj.erase R o) (.ref R) = true
  | .struct s, o =>
    MFields.erase_hasTyH s (structDef s) o fun _ hm => lookupBy_eq_of_nodup (structDef_nodup s) hm
  | .array E, o => by
    simp only [MObj.erase, Semantics.MObj.hasTyH, Bool.not_false, Bool.true_and]
    exact MVal.erase_hasTyHElems E (o : {l : List (MVal H E) // l.length < 2 ^ 256}).1
  | .fixed E n, o => by
    obtain ⟨l, hl⟩ := (o : {l : List (MVal H E) // l.length = n})
    simp only [MObj.erase, Semantics.MObj.hasTyH, List.length_map, hl, beq_self_eq_true,
      Bool.true_and]
    exact MVal.erase_hasTyHElems E l
  | .mapping _ _, o => (o : Empty).elim

/-- Every object of a typed heap is of the type its typing lists. -/
theorem Objs.erase_typed {H : HTy} (start : Nat) : (Rs : List RefTy) → (os : Objs H Rs) →
    (HTy.toHeapTy start Rs).all (fun r => match lookupBy r.1 (Objs.erase start Rs os) with
      | some obj => obj.hasTyH (HTy.toHeapTy 0 H) r.2
      | none => false) = true
  | [], _ => rfl
  | R :: Rs, os => by
    simp only [HTy.toHeapTy, List.all_cons, Objs.erase, lookupBy, ↓reduceIte,
      MObj.erase_hasTyH R os.1, Bool.true_and]
    have ih := Objs.erase_typed (start + 1) Rs os.2
    refine List.all_eq_true.mpr fun e he => ?_
    have hne : e.1 ≠ start := Nat.ne_of_gt (HTy.mem_toHeapTy he)
    simp only [if_neg hne]
    exact List.all_eq_true.mp ih e he

theorem Objs.lookupBy_erase_ge {H : HTy} {start k : Nat} : (Rs : List RefTy) → (os : Objs H Rs) →
    start + Rs.length ≤ k → lookupBy k (Objs.erase start Rs os) = none
  | [], _, _ => rfl
  | _ :: Rs, os, hk => by
    simp only [List.length_cons] at hk
    simp only [Objs.erase, lookupBy, show k ≠ start by omega, ↓reduceIte]
    exact Objs.lookupBy_erase_ge Rs os.2 (by omega)

/-! ## The state -/

/-- The global part of a typed state's erasure is well-typed under the store
typing its heap typing lists. -/
theorem State.glob_wt {Γ : Ctx} (hnd : nodupKeysB C.vars = true) (σ : State C Γ) :
    Semantics.StateWT (HTy.toHeapTy 0 σ.H) C.layout σ.globE :=
  ⟨hnd, HTy.nodup_toHeapTy _, Storage.erase_wt hnd σ.storage, Objs.erase_typed 0 σ.H σ.heap,
    fun _ hid => Objs.lookupBy_erase_ge σ.H σ.heap (by simpa only [Nat.zero_add] using hid)⟩

end Solidity
