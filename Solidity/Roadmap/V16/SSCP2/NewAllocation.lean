import Solidity.Source.Preservation.AllocationSites

/-! SS-CP2 consumers of the existing newData/allocRef allocation site.
No evaluator or admitted source domain is changed. -/
namespace Solidity.Roadmap.V16.SSCP2.NewAllocation
open Solidity.Source Solidity.Source.EM

theorem newData_valid : ∀ (E : Solidity.Source.Env) (H : Solidity.Source.HeapTy) (τ : Solidity.Source.STy) (len : Nat) (x : Solidity.Source.Data E.layout τ), Solidity.Source.newData τ len = .ok x → Solidity.Source.DataOK E H x ∧ Solidity.Source.Data.Top x ∧ Solidity.Source.Data.Inner x := by
  intro E H τ len x actual
  cases τ <;> simp only [Solidity.Source.newData] at actual
  case bytes l =>
    cases actual
    exact ⟨.bytes _,trivial,trivial⟩
  case string l =>
    cases actual
    exact ⟨.string _,trivial,trivial⟩
  case array l σ n =>
    cases n with
    | some n => cases actual
    | none =>
      cases initial : Solidity.Source.Val.default E.layout σ with
      | none => simp only [initial] at actual; cases actual
      | some z =>
        simp only [initial] at actual
        cases actual
        exact ⟨.array (fun _ => .val (Solidity.Source.Val.refOK_of_loc (Solidity.Source.Val.default_loc initial) z)),trivial,fun _ => ⟨z,rfl⟩⟩
  all_goals cases actual

theorem allocation_mem : ∀ (E : Solidity.Source.Env) (Γ : Solidity.Source.RCtx) (H : Solidity.Source.HeapTy) (τ : Solidity.Source.STy) (len : Nat), Solidity.Source.Hoare (Solidity.Source.MemOK E H) ((Solidity.Source.EM.lift (E := E) (Γ := Γ) (Solidity.Source.newData (D := E.layout) τ len)) >>= fun (x : Solidity.Source.Data E.layout τ) => Solidity.Source.allocRef (E := E) (Γ := Γ) x) (fun v y => Solidity.Source.MemOK E H y ∧ Solidity.Source.Val.RefOK E y.2.heap.ty v) (fun _ y => Solidity.Source.MemOK E H y) := by
  intro E Γ H τ len
  cases actual : Solidity.Source.newData (D := E.layout) τ len with
  | error halt =>
    simp only [Solidity.Source.EM.lift]
    exact Solidity.Source.Hoare.halt' (fun _ h => h)
  | ok x =>
    simp only [Solidity.Source.EM.lift,pure_bind]
    have valid := Solidity.Roadmap.V16.SSCP2.NewAllocation.newData_valid E H τ len x actual
    exact Solidity.Source.Hoare.conseq (Solidity.Source.allocRef_mem' x valid.2.1 valid.2.2)
      (fun y h => ⟨h,(Solidity.Roadmap.V16.SSCP2.NewAllocation.newData_valid E y.2.heap.ty τ len x actual).1⟩)
      (fun _ _ h => h) (fun _ _ h => h)

theorem eval_new_mem : ∀ (E : Solidity.Source.Env) (Γ : Solidity.Source.RCtx) (G : Solidity.Source.Glob E) (F : Solidity.Source.Fr) (n : Nat) (H : Solidity.Source.HeapTy) (τ σ : Solidity.Source.STy) (newable : τ.newable = true) (len : Solidity.Source.RExpr E Γ σ) (indexable : σ.isIndex = true), Solidity.Source.Hoare (Solidity.Source.MemOK E H) (Solidity.Source.evalE G F n len) (fun _ y => Solidity.Source.MemOK E H y) (fun _ y => Solidity.Source.MemOK E H y) → Solidity.Source.Hoare (Solidity.Source.MemOK E H) (Solidity.Source.evalE G F (n+1) (.newArray newable len indexable)) (fun v y => Solidity.Source.MemOK E H y ∧ Solidity.Source.RValOK E y.2.heap.ty v) (fun _ y => Solidity.Source.MemOK E H y) := by
  intro E Γ G F n H τ σ newable len indexable child
  rw [Solidity.Source.evalE]
  refine Solidity.Source.Hoare.bind child (fun v => ?_)
  have pureStep : Solidity.Source.Hoare (Solidity.Source.MemOK E H) (Solidity.Source.indexNat (E := E) (Γ := Γ) v) (fun _ y => Solidity.Source.MemOK E H y) (fun _ y => Solidity.Source.MemOK E H y) := by
    apply Solidity.Source.Hoare.lift'
    intro y h
    cases v.amount <;> exact h
  refine Solidity.Source.Hoare.bind pureStep (fun k => ?_)
  split
  · exact Solidity.Source.Hoare.halt' (fun _ h => h)
  · have allocated := Solidity.Roadmap.V16.SSCP2.NewAllocation.allocation_mem E Γ H τ k
    simp only [← bind_assoc]
    exact Solidity.Source.Hoare.bind allocated (fun v => Solidity.Source.Hoare.pure' (a := Solidity.Source.RVal.val (D := E.layout) (τ := τ) v) (fun _ h => h))

theorem local_new_mem : ∀ (E : Solidity.Source.Env) (Γ : Solidity.Source.RCtx) (G : Solidity.Source.Glob E) (F : Solidity.Source.Fr) (n : Nat) (H : Solidity.Source.HeapTy) (τ : Solidity.Source.STy) (newable : τ.newable = true) (i : Solidity.Source.Idx Γ (.int .u256)), Solidity.Source.Hoare (Solidity.Source.MemOK E H) (Solidity.Source.evalE G F (n+2) (.newArray newable (.local i) rfl)) (fun v y => Solidity.Source.MemOK E H y ∧ Solidity.Source.RValOK E y.2.heap.ty v) (fun _ y => Solidity.Source.MemOK E H y) := by
  intro E Γ G F n H τ newable i
  apply Solidity.Roadmap.V16.SSCP2.NewAllocation.eval_new_mem E Γ G F (n+1) H τ (.int .u256) newable (.local i) rfl
  rw [Solidity.Source.evalE]
  exact Solidity.Source.Hoare.bind (Solidity.Source.Hoare.locals' (Q := fun _ y => Solidity.Source.MemOK E H y) (fun _ h => h)) (fun l => Solidity.Source.Hoare.pure' (fun _ h => h))

/-- info: 'Solidity.Roadmap.V16.SSCP2.NewAllocation.newData_valid' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms newData_valid

/-- info: 'Solidity.Roadmap.V16.SSCP2.NewAllocation.allocation_mem' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms allocation_mem

/-- info: 'Solidity.Roadmap.V16.SSCP2.NewAllocation.eval_new_mem' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms eval_new_mem

/-- info: 'Solidity.Roadmap.V16.SSCP2.NewAllocation.local_new_mem' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms local_new_mem
end Solidity.Roadmap.V16.SSCP2.NewAllocation
