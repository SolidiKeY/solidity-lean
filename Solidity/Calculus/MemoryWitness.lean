import Solidity.Calculus.TermEq
import Solidity.Theory.Typed.Mem

/-!
# Given-heap memory witnesses

A hidden memory binder ranges over the references of its existing typed
heap, including unset. Enumeration preserves identities and permits aliases.
Primitive-array heaps supply concrete countermodels without changing a
binder into allocation. The partial checker certifies truth or falsity at
one state; only falsity is used by the decision fallback.
-/

namespace Solidity.MemoryWitness

variable {C : Contract} {Γ : Ctx}

/-- All existing references of the requested type, in identity order. -/
def refs (H : HTy) (R : RefTy) : List (HRef H R) :=
  (List.range H.length).filterMap (HRef.ofId? H R)

/-- Every typed reference occurs, with its original identity. -/
theorem mem_refs {H : HTy} {R : RefTy} (r : HRef H R) : r ∈ refs H R := by
  exact List.mem_filterMap.mpr ⟨r.id,
    List.mem_range.mpr (List.getElem?_eq_some_iff.mp r.get?).1, HRef.ofId?_self r⟩

/-- A memory binder also ranges over unset, even on an empty heap. -/
def values (H : HTy) (R : RefTy) : List (Option (HRef H R)) :=
  (refs H R).map some ++ [none]

/-- Enumeration covers exactly the intrinsic binder domain. -/
theorem mem_values {H : HTy} {R : RefTy} (v : Option (HRef H R)) :
    v ∈ values H R := by
  cases v with
  | none =>
    exact List.mem_append_right _ List.mem_cons_self
  | some r =>
    exact List.mem_append_left _ (List.mem_map.mpr ⟨r, mem_refs r, rfl⟩)

/-- Finite quantification is exact; independent binders may reuse a reference. -/
theorem forall_values {H : HTy} {R : RefTy} (P : Option (HRef H R) → Prop) :
    (∀ v ∈ values H R, P v) ↔ ∀ v, P v :=
  ⟨fun h v => h v (mem_values v), fun h v _ => h v⟩

/-- The hidden binder's given-heap meaning, under either modality. -/
theorem bind_exact (σ : State C Γ) (m : Modality) (x : Var) (R : RefTy)
    (φ : Fml C (.mem R :: Γ)) :
    holds σ (.bind m x (.mem R) φ) ↔
      ∀ v ∈ values σ.H R, holds (σ.push v) φ :=
  (forall_values (H := σ.H) (R := R)
    (fun v => holds (σ.push (t := .mem R) v) φ)).symm

/-- The bounded contents of one primitive array. -/
abbrev Words (p : PrimTy) := { ws : List p.Denote // ws.length < 2 ^ 256 }

/-- Primitive words need no further heap objects. -/
def Words.obj {p : PrimTy} (w : Words p) (H : HTy) : MObj H (.array (.prim p)) :=
  ⟨w.1, w.2⟩

/-- Each supplied array gets its own identity, even with equal contents. -/
def typing {p : PrimTy} (ws : List (Words p)) : HTy :=
  ws.map (fun _ => .array (.prim p))

/-- Objects constructed directly in the prescribed heap typing. -/
def objects {p : PrimTy} (H : HTy) : (ws : List (Words p)) → Objs H (typing ws)
  | [] => ()
  | w :: ws => (w.obj H, objects H ws)

/-- The reference corresponding to one supplied array. -/
def reference {p : PrimTy} (ws : List (Words p)) (i : Fin ws.length) :
    HRef (typing ws) (.array (.prim p)) :=
  ⟨i.1, by
    simp only [typing, List.getElem?_map, List.getElem?_eq_getElem i.2, Option.map_some]⟩

/-- Every constructed object has exactly its supplied contents. -/
theorem objects_get {p : PrimTy} (H : HTy) (ws : List (Words p)) (i : Nat)
    (hi : i < ws.length) :
    Objs.get (typing ws) (objects H ws) i
      (by simp only [typing, List.getElem?_map, List.getElem?_eq_getElem hi, Option.map_some]) =
      (ws[i]).obj H := by
  induction ws generalizing i with
  | nil => exact False.elim (Nat.not_lt_zero i hi)
  | cons w ws ih =>
    cases i with
    | zero => rfl
    | succ i => exact ih i (Nat.lt_of_succ_lt_succ hi)

/-- The witness heap retains the prescribed object at each identity. -/
theorem heap_get {p : PrimTy} (ws : List (Words p)) (i : Fin ws.length) :
    Heap.get (objects (typing ws) ws) (reference ws i) =
      (ws[i.1]).obj (typing ws) :=
  objects_get (typing ws) ws i.1 i.2

/-- Reference equality is exactly identity equality, not content equality. -/
theorem reference_eq_iff {p : PrimTy} (ws : List (Words p)) (i j : Fin ws.length) :
    reference ws i = reference ws j ↔ i = j := by
  constructor
  · intro h
    exact Fin.ext (congrArg HRef.id h)
  · intro h
    cases h
    rfl

/-- A typed state with the supplied existing arrays; no formula is allocated. -/
def state (C : Contract) {p : PrimTy} (ws : List (Words p)) : State C [] :=
  { storage := Storage.init C, H := typing ws, heap := objects (typing ws) ws, env := () }

/-- A result with its proof at the actual state, or an inconclusive result. -/
inductive Checked (P : Prop) : Type where
  | yes (proof : P)
  | no (proof : ¬ P)
  | unknown

namespace Checked

variable {P Q : Prop}

def transport (e : P ↔ Q) : Checked P → Checked Q
  | .yes h => .yes (e.mp h)
  | .no h => .no (fun hq => h (e.mpr hq))
  | .unknown => .unknown

def neg : Checked P → Checked (¬ P)
  | .yes h => .no (fun hn => hn h)
  | .no h => .yes h
  | .unknown => .unknown

def conj : Checked P → Checked Q → Checked (P ∧ Q)
  | .no h, _ => .no (fun hpq => h hpq.1)
  | _, .no h => .no (fun hpq => h hpq.2)
  | .yes h, .yes hq => .yes ⟨h, hq⟩
  | _, _ => .unknown

def impl : Checked P → Checked Q → Checked (P → Q)
  | .no h, _ => .yes (fun hp => False.elim (h hp))
  | _, .yes h => .yes (fun _ => h)
  | .yes h, .no hq => .no (fun hpq => hq (hpq h))
  | _, _ => .unknown

/-- Quantification over a finite list, without asserting missing evaluations. -/
def allList {α : Type} {P : α → Prop} :
    (xs : List α) → ((a : α) → Checked (P a)) → Checked (∀ a ∈ xs, P a)
  | [], _ => .yes (fun _ h => False.elim (List.not_mem_nil h))
  | a :: xs, f =>
    match f a with
    | .no h => .no (fun hall => h (hall a List.mem_cons_self))
    | .unknown => .unknown
    | .yes ha =>
      match allList xs f with
      | .no h => .no (fun hall => h (fun b hb => hall b (List.mem_cons_of_mem a hb)))
      | .unknown => .unknown
      | .yes hs => .yes (by
          intro b hb
          rcases List.mem_cons.mp hb with rfl | hb
          · exact ha
          · exact hs b hb)

def isNo : Checked P → Bool
  | .no _ => true
  | _ => false

/-- A computed negative answer carries a refutation of the original proposition. -/
theorem refutes (v : Checked P) (h : v.isNo = true) : ¬ P := by
  cases v with
  | yes _ => cases h
  | no hn => exact hn
  | unknown => cases h

def isYes : Checked P → Bool
  | .yes _ => true
  | _ => false

/-- A positive answer concerns this state only. -/
theorem proves (v : Checked P) (h : v.isYes = true) : P := by
  cases v with
  | yes hp => exact hp
  | no _ => cases h
  | unknown => cases h

end Checked

/-- Equation checking uses successful evaluations only; reflexivity is total. -/
def equation (σ : State C Γ) {p : PrimTy} (a b : Tm C Γ (.val p)) :
    Checked (holds σ (.eq a b)) :=
  if he : a.beqR b = true then
    .yes (by
      change a.denote σ = b.denote σ
      rw [Tm.eq_of_beqR he])
  else
    match ha : a.eval σ with
    | none => .unknown
    | some x =>
      match hb : b.eval σ with
      | none => .unknown
      | some y =>
        if hxy : x = y then .yes ((holds_eq_of_eval ha hb).mpr hxy)
        else .no (fun h => hxy ((holds_eq_of_eval ha hb).mp h))

/-- Hidden memory binders enumerate the same heap, including repeated identities. -/
def binder (m : Modality) (x : Var) (t : LTy) (φ : Fml C (t :: Γ))
    (ih : (τ : State C (t :: Γ)) → Checked (holds τ φ)) (σ : State C Γ) :
    Checked (holds σ (.bind m x t φ)) := by
  cases t with
  | mem R =>
    exact (Checked.allList (values σ.H R) (fun v => ih (σ.push v))).transport
      (bind_exact σ m x R φ).symm
  | val _ | alias _ | old | oldNet | kint => exact .unknown

/-- Compiled structural twin of the indexed checker. -/
def _root_.Solidity.Fml.checkMemoryAtM : {Γ : Ctx} → (φ : Fml C Γ) →
    (σ : State C Γ) → Checked (holds σ φ)
  | _, .tt, _ => .yes True.intro
  | _, .eq a b, σ => equation σ a b
  | _, .not φ, σ => (φ.checkMemoryAtM σ).neg
  | _, .and φ ψ, σ => (φ.checkMemoryAtM σ).conj (ψ.checkMemoryAtM σ)
  | _, .imp φ ψ, σ => (φ.checkMemoryAtM σ).impl (ψ.checkMemoryAtM σ)
  | _, .bind m x t φ, σ => binder m x t φ (fun τ => φ.checkMemoryAtM τ) σ
  | _, .wellFormed _, _ => .unknown
  | _, .upd _ _ _, _ => .unknown
  | _, .modal _ _ _ _, _ => .unknown
  | _, .havoc _, _ => .unknown
  | _, .all _ _ _, _ => .unknown
  | _, .anon _ _, _ => .unknown
  | _, .allocAll _ _ _, _ => .unknown
  | _, .grow _, _ => .unknown

/-- Partial concrete checking, by the indexed recursor. No allocation,
updates, programs or value quantifiers are reinterpreted. -/
@[implemented_by Fml.checkMemoryAtM]
def _root_.Solidity.Fml.checkMemoryAt {Γ : Ctx} (φ : Fml C Γ) (σ : State C Γ) :
    Checked (holds σ φ) :=
  @Fml.rec C (fun Γ φ => (σ : State C Γ) → Checked (holds σ φ))
    (fun _ => .yes True.intro)
    (fun a b σ => equation σ a b)
    (fun _ _ => .unknown)
    (fun _ ih σ => (ih σ).neg)
    (fun _ _ ih ih' σ => (ih σ).conj (ih' σ))
    (fun _ _ ih ih' σ => (ih σ).impl (ih' σ))
    (fun _ _ _ _ _ => .unknown)
    (fun _ _ _ _ _ _ => .unknown)
    (fun _ _ _ => .unknown)
    (fun _ _ _ _ _ => .unknown)
    (fun m x t φ ih σ => binder m x t φ ih σ)
    (fun _ _ _ _ => .unknown)
    (fun _ _ _ _ _ => .unknown)
    (fun _ _ _ => .unknown) _ φ σ

/-- The compiled and kernel readers agree, including their proof-carrying results. -/
theorem _root_.Solidity.Fml.checkMemoryAt_eq_checkMemoryAtM {Γ : Ctx}
    (φ : Fml C Γ) (σ : State C Γ) :
    φ.checkMemoryAt σ = φ.checkMemoryAtM σ := by
  induction φ with
  | tt | eq | wellFormed | upd | modal | havoc | all | anon | allocAll | grow => rfl
  | not φ ih => exact congrArg Checked.neg (ih σ)
  | and φ ψ ih ih' =>
    change (φ.checkMemoryAt σ).conj (ψ.checkMemoryAt σ) =
      (φ.checkMemoryAtM σ).conj (ψ.checkMemoryAtM σ)
    rw [ih σ, ih' σ]
  | imp φ ψ ih ih' =>
    change (φ.checkMemoryAt σ).impl (ψ.checkMemoryAt σ) =
      (φ.checkMemoryAtM σ).impl (ψ.checkMemoryAtM σ)
    rw [ih σ, ih' σ]
  | bind m x t φ ih =>
    exact congrArg (fun f => binder m x t φ f σ) (funext ih)

/-- A nonempty heap is essential to the original parameter countermodel. -/
def candidate (C : Contract) : State C [] :=
  state C (p := .uint) [⟨[uintOfNat 1], by decide⟩]

/-- A certified countermodel search, never a validity test over all heaps. -/
def countermodel? (φ : Fml C []) : Option { σ : State C [] // ¬ holds σ φ } :=
  let σ := candidate C
  match φ.checkMemoryAt σ with
  | .no h => some ⟨σ, h⟩
  | _ => none

/-- info: 'Solidity.MemoryWitness.bind_exact' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms bind_exact
/-- info: 'Solidity.MemoryWitness.heap_get' depends on axioms: [propext] -/
#guard_msgs in #print axioms heap_get
/-- info: 'Solidity.MemoryWitness.reference_eq_iff' depends on axioms: [propext] -/
#guard_msgs in #print axioms reference_eq_iff
/-- info: 'Solidity.MemoryWitness.Checked.refutes' does not depend on any axioms -/
#guard_msgs in #print axioms Checked.refutes
/-- info: 'Solidity.Fml.checkMemoryAt_eq_checkMemoryAtM' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Fml.checkMemoryAt_eq_checkMemoryAtM

end Solidity.MemoryWitness

