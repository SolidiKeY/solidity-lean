import Solidity.Calculus.ReadTrace
import Solidity.Calculus.TypedLinear

/-!
# Complete arithmetic decisions over dependent read occurrences

A fixed typed occurrence layout supplies finite solver variables even when
the locations depend on earlier values. Its arithmetic certificate includes
the alias implication: inconsistent occurrences cannot refute a query.
Both verdicts use the existing complete arithmetic decision, and a negative
verdict materializes actual storage through the trace realization theorem.
The layout fixes occurrence types and count, not locations or values.
-/

namespace Solidity.ReadRealization

open Linear ScalarCode

variable {C : Contract} {α : Type}

/-- A heterogeneous finite vector supplies values at their occurrence types.
Missing or mismatched entries use the requested type's default. -/
def occurrenceValues : {ps : List PrimTy} → Values ps → ReadValues
  | [], _, _, p => PrimTy.dflt p
  | p :: _, vs, 0, q => if h : p = q then h ▸ vs.1 else PrimTy.dflt q
  | _ :: _, vs, i + 1, q => occurrenceValues vs.2 i q

/-- Retain every occurrence's primitive type and value, including aliases. -/
def Assignment.vector : (a : Assignment C) → Values (a.map fun e => e.1.prim)
  | [] => ()
  | ⟨_, v⟩ :: a => (v, Assignment.vector a)

theorem Assignment.occurrenceValues_vector (a : Assignment C) :
    occurrenceValues a.vector = a.values := by
  induction a with
  | nil => rfl
  | cons entry a ih =>
    funext i p
    cases i with
    | zero => rfl
    | succ i => exact congrFun (congrFun ih i) p

/-- The two-occurrence alias constraint retains equality transport at the
actual primitive endpoint type. -/
theorem Assignment.pair_consistent (r q : Ref C) (v : r.Value) (w : q.Value) :
    Assignment.Consistent [⟨r, v⟩, ⟨q, w⟩] ↔ ∀ h : r = q, h ▸ v = w := by
  constructor
  · intro hc h
    cases h
    exact hc r v w List.mem_cons_self (List.mem_cons_of_mem _ List.mem_cons_self)
  · intro h s x y hx hy
    rcases List.mem_cons.mp hx with hx | hx
    · cases hx
      rcases List.mem_cons.mp hy with hy | hy
      · cases hy; rfl
      · have hy := List.mem_singleton.mp hy
        have he : r = q := congrArg Sigma.fst hy
        cases he
        cases hy
        exact h rfl
    · have hx := List.mem_singleton.mp hx
      cases hx
      rcases List.mem_cons.mp hy with hy | hy
      · have he : q = r := congrArg Sigma.fst hy
        cases he
        cases hy
        exact (h rfl).symm
      · cases List.mem_singleton.mp hy
        rfl

theorem Assignment.pair_consistent_typed {p : PrimTy} (r q : SRef C (.prim p))
    (hr : r.Declared) (hq : q.Declared) (v w : p.Denote) :
    Assignment.Consistent [⟨⟨p, r, hr⟩, v⟩, ⟨⟨p, q, hq⟩, w⟩] ↔
      (Ref.mk p r hr = Ref.mk p q hq → v = w) := by
  rw [Assignment.pair_consistent]
  apply forall_congr'
  intro h
  cases h
  rfl

/-- A read at a primitive type absent from the remaining trace introduces
no new alias constraint. Endpoint types prevent those references equaling. -/
theorem Assignment.cons_different_type (r : Ref C) (v : r.Value) (a : Assignment C)
    (hd : ∀ e ∈ a, e.1.prim ≠ r.prim) :
    Assignment.Consistent (⟨r, v⟩ :: a) ↔ a.Consistent := by
  constructor
  · exact Assignment.Consistent.tail
  · intro hc s x y hx hy
    rcases List.mem_cons.mp hx with hx | hx
    · cases hx
      rcases List.mem_cons.mp hy with hy | hy
      · cases hy; rfl
      · exact (hd ⟨r, y⟩ hy rfl).elim
    · rcases List.mem_cons.mp hy with hy | hy
      · cases hy
        exact (hd ⟨r, x⟩ hx rfl).elim
      · exact hc s x y hx hy

namespace Query

/-- Reading back any replayed trace repeats its complete result and trace,
even when its proposed aliases disagree. Consistency is a separate gate. -/
theorem replay_self (q : Query C α) (values : ReadValues) (start : Nat) :
    replay (replay values start q).2.values 0 q = replay values start q := by
  induction q generalizing start with
  | pure x => rfl
  | read r k ih =>
    simp only [replay, Assignment.values, ↓reduceDIte, replay_cons_values, ih]

/-- An exact typed occurrence layout, for all proposed value choices.
This restricts the occurrence shape, but leaves locations dependent. -/
def HasLayout (q : Query C α) (ps : List PrimTy) : Prop :=
  ∀ values, (replay values 0 q).2.map (fun e => e.1.prim) = ps

/-- Every replay stream is represented by a finite vector of the fixed
layout. No primitive domain or mapping key is enumerated. -/
theorem finite_replay (q : Query C α) {ps : List PrimTy} (hq : q.HasLayout ps)
    (values : ReadValues) : ∃ vs : Values ps,
      replay (occurrenceValues vs) 0 q = replay values 0 q := by
  rw [← hq values]
  exact ⟨(replay values 0 q).2.vector, by
    rw [Assignment.occurrenceValues_vector]
    exact q.replay_self values 0⟩

/-- The arithmetic formula states the alias implication, rather than
treating distinct occurrences as independently realizable storage. -/
structure Arithmetic (q : Query C Bool) where
  types : List PrimTy
  layout : q.HasLayout types
  formula : TypedFormula types
  correct : ∀ vs : Values types, formula.holds vs ↔
    (replay (occurrenceValues vs) 0 q).2.Consistent →
      (replay (occurrenceValues vs) 0 q).1 = true

namespace Arithmetic

/-- Complete arithmetic validity is exactly validity over actual storage. -/
theorem valid_iff {q : Query C Bool} (r : q.Arithmetic) :
    (∀ st : Storage C, q.runStorage st = true) ↔ r.formula.Valid := by
  constructor
  · intro h vs
    exact (r.correct vs).mpr ((q.all_storage_iff_traces.mp h) (occurrenceValues vs))
  · intro h
    apply q.all_storage_iff_traces.mpr
    intro values
    obtain ⟨vs, hv⟩ := q.finite_replay r.layout values
    rw [← hv]
    exact (r.correct vs).mp (h vs)

theorem valid_of_decide {q : Query C Bool} (r : q.Arithmetic)
    (h : r.formula.guarded.decide = true) : ∀ st : Storage C, q.runStorage st = true :=
  r.valid_iff.mpr (r.formula.valid_iff.mpr ((AFml.decide_iff _).mp h))

/-- An arithmetic counterassignment necessarily satisfies alias consistency
and falsifies the replay; the resulting storage falsifies the actual query. -/
def countermodelOf {q : Query C Bool} (r : q.Arithmetic)
    (cm : { vs : Values r.types // ¬ r.formula.holds vs }) :
    { st : Storage C // q.runStorage st = false } := by
  let values : ReadValues := occurrenceValues cm.val
  have hn : ¬ ((replay values 0 q).2.Consistent → (replay values 0 q).1 = true) :=
    fun h => cm.property ((r.correct cm.val).mpr h)
  have hc : (replay values 0 q).2.Consistent :=
    Classical.byContradiction (fun h => hn (fun hc => (h hc).elim))
  have hf : (replay values 0 q).1 = false := Bool.eq_false_iff.mpr (fun h => hn (fun _ => h))
  exact ⟨_, (q.replay_realize values 0 hc).trans hf⟩

/-- Only the finite assignment is replayed by the kernel after compiled
arithmetic exploration. The guarded check includes all typed domains. -/
def checkCodes {q : Query C Bool} (r : q.Arithmetic) (xs : List Nat) : Bool :=
  r.formula.guarded.check (fun k => xs[k]?.getD 0)

def countermodelOfCodes {q : Query C Bool} (r : q.Arithmetic) (xs : List Nat)
    (h : r.checkCodes xs = false) :
    { st : Storage C // q.runStorage st = false } :=
  r.countermodelOf (r.formula.countermodelOf (fun k => xs[k]?.getD 0)
    (fun hv => Bool.false_ne_true (h ▸ (AFml.check_iff _ _).mpr hv)))

/-- One complete graph traversal returns either universal validity or an
actual typed counterstore. There is no bounded candidate search. -/
def verify {q : Query C Bool} (r : q.Arithmetic) :
    Sum (PLift (∀ st : Storage C, q.runStorage st = true))
      { st : Storage C // q.runStorage st = false } :=
  match r.formula.verify with
  | .inl h => .inl ⟨r.valid_iff.mpr h.down⟩
  | .inr cm => .inr (r.countermodelOf cm)

end Arithmetic
end Query
end Solidity.ReadRealization
