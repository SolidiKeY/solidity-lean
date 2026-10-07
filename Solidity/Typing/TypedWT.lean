import Solidity.Typing.Soundness
import Solidity.Semantics.Core.TypedState

/-!
# A typed state erases to a well-typed one

`RunWT` by construction (`docs/intrinsic.md`, W1, lane `typing`): a typed
state (`Core.TState`, `Semantics/Core/TypedState.lean`) holds storage values
of their types, a heap whose objects are of the types its typing lists, and
locals of their types, so its erasure is a `RunWT` state under the store
typing its heap typing lists (`HTy.toHeapTy`), with no run to follow
(`TState.erase_wt`).  `Stmt.run_wt`, which follows the scoped run, is then
what the typed run needs no proof of.

"Mostly": the untyped typing (`SVal.hasTy`, `MObj.hasTyH`) reads a struct's
members by name, the typed value by position, so the two agree when no
struct has two members of one name (`Ty.nodupDeep`: every struct the type
reaches, through members, elements and mapping values, is one of
`Core.nodupStructs`, all but `BadDup`).  The theorem takes that of the
contract's state variables and of the heap typing, and the layout's keys
distinct.
-/

namespace Solidity

open Semantics (structDef lookupBy nodupKeysB)

/-- No struct `T` reaches, through members, elements or mapping values, has
two members of one name: each is one of `Core.nodupStructs`.  Decided by
`rfl`, as `Ty.nodupS`, which does not look into a mapping. -/
def Ty.nodupDeep : Ty → Bool
  | .prim _ => true
  | .ref (.struct s) => s ∈ Core.nodupStructs
  | .ref (.array e) => e.nodupDeep
  | .ref (.fixed e _) => e.nodupDeep
  | .ref (.mapping _ v) => v.nodupDeep

theorem nodupStructs_deep : ∀ s ∈ Core.nodupStructs,
    nodupKeysB (structDef s) = true ∧ ∀ fT ∈ structDef s, fT.2.nodupDeep = true := by
  decide

theorem Ty.nodupDeep_struct {s : Name} (h : (Ty.ref (.struct s)).nodupDeep = true) :
    nodupKeysB (structDef s) = true ∧ ∀ fT ∈ structDef s, fT.2.nodupDeep = true :=
  nodupStructs_deep s (by simpa only [Ty.nodupDeep, decide_eq_true_eq] using h)

end Solidity

namespace Solidity.Core

open Semantics (structDef lookupBy nodupKeysB HeapTy lookupBy_eq_of_nodup wellTypedStorageB
  tyAtSegs segTy)
open SemanticsProperties (HeapWellFormed)

variable {C : Contract}

/-! ## Storage values -/

mutual

theorem SVal.erase_hasTy : {T : Ty} → (v : SVal T) → T.nodupDeep = true →
    v.erase.hasTy T = true
  | _, .prim (p := p) x, _ => by
    rw [SVal.erase_prim]
    cases p <;> rfl
  | _, .struct (s := s) fs, h => by
    rw [SVal.erase_struct]
    have hs := Ty.nodupDeep_struct h
    exact SFields.erase_hasTy s fs (fun _ hm => lookupBy_eq_of_nodup hs.1 hm) hs.2
  | _, .array e sh, h => by
    rw [SVal.erase_array]
    simp only [Semantics.SVal.hasTy, Bool.not_false, Bool.true_and, Bool.and_eq_true]
    exact ⟨SList.erase_hasTy e h, SList.erase_hasTy sh h⟩
  | _, .fixed (n := n) e, h => by
    rw [SVal.erase_fixed]
    simp only [Semantics.SVal.hasTy, SVec.length_erase, beq_self_eq_true, Bool.true_and,
      Bool.and_eq_true]
    exact ⟨SVec.erase_hasTy e h, rfl⟩
  | _, .map m d, h => by
    rw [SVal.erase_map]
    simp only [Semantics.SVal.hasTy, Bool.and_eq_true]
    exact ⟨SMap.erase_hasTy m h, SVal.erase_hasTy d h⟩

theorem SFields.erase_hasTy (s : Name) : {fs : List (Name × Ty)} → (x : SFields fs) →
    (∀ fT ∈ fs, lookupBy fT.1 (structDef s) = some fT.2) → (∀ fT ∈ fs, fT.2.nodupDeep = true) →
    Semantics.SVal.hasTy.hasTyFields s x.erase = true
  | _, .nil, _, _ => by rw [SFields.erase_nil]; rfl
  | _, .cons (f := f) (T := T) v rest, hl, hn => by
    rw [SFields.erase_cons]
    simp only [Semantics.SVal.hasTy.hasTyFields, hl (f, T) List.mem_cons_self,
      SVal.erase_hasTy v (hn (f, T) List.mem_cons_self), Bool.true_and]
    exact SFields.erase_hasTy s rest (fun fT hm => hl fT (List.mem_cons_of_mem _ hm))
      (fun fT hm => hn fT (List.mem_cons_of_mem _ hm))

theorem SList.erase_hasTy : {E : Ty} → (l : SList E) → E.nodupDeep = true →
    Semantics.SVal.hasTy.hasTyElems E l.erase = true
  | _, .nil, _ => by rw [SList.erase_nil]; rfl
  | _, .cons v rest, h => by
    rw [SList.erase_cons]
    simp only [Semantics.SVal.hasTy.hasTyElems, SVal.erase_hasTy v h, SList.erase_hasTy rest h,
      Bool.and_self]

theorem SVec.erase_hasTy : {E : Ty} → {n : Nat} → (l : SVec E n) → E.nodupDeep = true →
    Semantics.SVal.hasTy.hasTyElems E l.erase = true
  | _, _, .nil, _ => by rw [SVec.erase_nil]; rfl
  | _, _, .cons v rest, h => by
    rw [SVec.erase_cons]
    simp only [Semantics.SVal.hasTy.hasTyElems, SVal.erase_hasTy v h, SVec.erase_hasTy rest h,
      Bool.and_self]

theorem SMap.erase_hasTy : {V : Ty} → (m : SMap V) → V.nodupDeep = true →
    Semantics.SVal.hasTy.hasTyEntries V m.erase = true
  | _, .nil, _ => by rw [SMap.erase_nil]; rfl
  | _, .cons _ v rest, h => by
    rw [SMap.erase_cons]
    simp only [Semantics.SVal.hasTy.hasTyEntries, SVal.erase_hasTy v h, SMap.erase_hasTy rest h,
      Bool.and_self]

end

/-- A typed storage erases to a well-typed one. -/
theorem Storage.erase_wt (hnd : nodupKeysB C.vars = true)
    (hC : ∀ g ∈ C.vars, g.2.nodupDeep = true) (st : Storage C) :
    wellTypedStorageB C.layout st.erase = true := by
  refine List.all_eq_true.mpr fun g hg => ?_
  have hl : lookupBy g.1 C.vars = some g.2 := lookupBy_eq_of_nodup hnd hg
  show (match lookupBy g.1 (SFields.erase st) with
    | some v => v.hasTy g.2
    | none => false) = true
  rw [SFields.lookupBy_erase st hl]
  exact SVal.erase_hasTy _ (hC g hg)

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
    (Ty.ref R).nodupDeep = true →
    Semantics.MObj.hasTyH (HTy.toHeapTy 0 H) (MObj.erase R o) (.ref R) = true
  | .struct s, o, h =>
    MFields.erase_hasTyH s (structDef s) o fun _ hm => lookupBy_eq_of_nodup (Ty.nodupDeep_struct h).1 hm
  | .array E, o, _ => by
    simp only [MObj.erase, Semantics.MObj.hasTyH, Bool.not_false, Bool.true_and]
    exact MVal.erase_hasTyHElems E o
  | .fixed E n, o, _ => by
    obtain ⟨l, hl⟩ := (o : {l : List (MVal H E) // l.length = n})
    simp only [MObj.erase, Semantics.MObj.hasTyH, List.length_map, hl, beq_self_eq_true,
      Bool.true_and]
    exact MVal.erase_hasTyHElems E l
  | .mapping _ _, o, _ => (o : Empty).elim

theorem Objs.lookupBy_erase_lt {H : HTy} {start k : Nat} (hk : k < start) :
    (Rs : List RefTy) → (os : Objs H Rs) → lookupBy k (Objs.erase start Rs os) = none
  | [], _ => rfl
  | _ :: Rs, os => by
    simp only [Objs.erase, lookupBy, Nat.ne_of_lt hk, ↓reduceIte]
    exact Objs.lookupBy_erase_lt (Nat.lt_succ_of_lt hk) Rs os.2

/-- Every object of a typed heap is of the type its typing lists. -/
theorem Objs.erase_typed {H : HTy} (start : Nat) : (Rs : List RefTy) → (os : Objs H Rs) →
    (∀ R ∈ Rs, (Ty.ref R).nodupDeep = true) →
    (HTy.toHeapTy start Rs).all (fun r => match lookupBy r.1 (Objs.erase start Rs os) with
      | some obj => obj.hasTyH (HTy.toHeapTy 0 H) r.2
      | none => false) = true
  | [], _, _ => rfl
  | R :: Rs, os, hR => by
    simp only [HTy.toHeapTy, List.all_cons, Objs.erase, lookupBy, ↓reduceIte,
      MObj.erase_hasTyH R os.1 (hR R List.mem_cons_self), Bool.true_and]
    have ih := Objs.erase_typed (start + 1) Rs os.2 fun R' hm => hR R' (List.mem_cons_of_mem _ hm)
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

/-! ## The locals -/

/-- A typed local erases to one of its type. -/
theorem LTy.TDenote.erase_wt {H : HTy} : (t : LTy) → (v : t.TDenote C H) →
    LTy.WT C (HTy.toHeapTy 0 H) t (LTy.TDenote.erase t v)
  | .val .uint, _ | .val .int, _ | .val .bool, _ => rfl
  | .alias _, a => by
    intro r segs h
    cases a with
    | none => cases h
    | some ref =>
      simp only [LTy.TDenote.erase, Option.map_some, Option.some.injEq] at h
      have := SRef.tyAt_erase ref
      rw [h] at this
      exact this
  | .mem _, r => by
    simp only [LTy.WT, LTy.TDenote.erase, Semantics.MVal.hasTyH, HRef.lookupBy_toHeapTy,
      beq_self_eq_true]
  | .old, _ | .oldNet, _ => trivial

theorem TEnv.erase_wt {H : HTy} : (Γ : Ctx) → (e : TEnv C H Γ) →
    Env.All (LTy.WT C (HTy.toHeapTy 0 H)) (TEnv.erase Γ e)
  | [], _ => trivial
  | t :: Γ, e => ⟨LTy.TDenote.erase_wt t e.1, TEnv.erase_wt Γ e.2⟩

/-! ## The state -/

/-- **A typed state erases to a well-typed one**, under the store typing its
heap typing lists: `RunWT` by construction, for a contract whose state
variables, and a heap whose objects, reach no struct with two members of one
name. -/
theorem TState.erase_wt {Γ : Ctx} (hnd : nodupKeysB C.vars = true)
    (hC : ∀ g ∈ C.vars, g.2.nodupDeep = true) (σ : TState C Γ)
    (hH : ∀ R ∈ σ.H, (Ty.ref R).nodupDeep = true) :
    RunWT C (HTy.toHeapTy 0 σ.H) σ.erase :=
  ⟨⟨hnd, HTy.nodup_toHeapTy _, Storage.erase_wt hnd hC σ.storage,
      Objs.erase_typed 0 σ.H σ.heap hH,
      fun _ hid => Objs.lookupBy_erase_ge σ.H σ.heap (by simpa only [Nat.zero_add] using hid)⟩,
    TEnv.erase_wt Γ σ.env⟩

/-- The initial state of `StandardExample` erases to a well-typed one. -/
example : RunWT StandardExample [] (TState.init StandardExample).erase :=
  TState.erase_wt (by decide) (by decide) (TState.init StandardExample) (fun _ h => nomatch h)

end Solidity.Core
