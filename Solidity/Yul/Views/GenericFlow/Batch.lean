import Solidity.Yul.Views.GenericFlow.FollowingPlan

namespace Solidity.Yul.Views.GenericFlow.Batch

/-- Canonical checked preparation only. Failure retains the exact successful prefix state; Source errors retain their result and complete state. The finite request list is the recursion index, with no additional root/domain/fuel cap. -/
def run? {E Γ} (F : Source.Fr) (interface : Generic.OwnershipInterface E Γ F)
    (layout : interface.Layout) (fixed : Roadmap.Evm.Fixed)
    (check : List (ScalarPath E.layout (E.lay F.this)) → Bool) :
    List (Roadmap.Word × Roadmap.Word) → Source.EMState E Γ →
      ResidualJournal complementCarrierOwnership →
      (Option (Except Source.Halt Unit) × Source.EMState E Γ × ResidualJournal complementCarrierOwnership)
  | [],s,r => (some (.ok ()),s,r)
  | (q,v)::rest,s,r => match Generic.prepareOwnership? F interface layout fixed q v s r check with
    | none => (none,s,r)
    | some p => match p.step.1.1 with
      | .error e => (some (.error e),p.step.1.2,p.step.2)
      | .ok () => run? F interface layout fixed check rest p.step.1.2 p.step.2

variable {E : Source.Env} {Γ : Source.RCtx} {F : Source.Fr}
variable {interface : Generic.OwnershipInterface E Γ F} {layout : interface.Layout}
variable {fixed : Roadmap.Evm.Fixed} {written value : Roadmap.Word}
variable {s : Source.EMState E Γ} {r : ResidualJournal complementCarrierOwnership}
variable {check : List (ScalarPath E.layout (E.lay F.this)) → Bool}

set_option smartUnfolding false in
theorem prepare_eq
    (p : Generic.OwnershipPlan F interface layout fixed written value s r check) :
    Generic.prepareOwnership? F interface layout fixed written value s r check = some p := by
  exact (planShape F interface layout fixed written value (fun _ => s) (fun _ => r) check).prepare_eq
    p.old p.oldComputed p.raw p.encoded p.oldChecked p.nextChecked p.sourceOp p.prepared

theorem unsupported (F : Source.Fr) (interface : Generic.OwnershipInterface E Γ F)
    (layout : interface.Layout) (fixed : Roadmap.Evm.Fixed)
    (check : List (ScalarPath E.layout (E.lay F.this)) → Bool)
    (q v : Roadmap.Word) (rest) (s : Source.EMState E Γ) (r)
    (missing : Generic.prepareOwnership? F interface layout fixed q v s r check = none) :
    run? F interface layout fixed check ((q,v)::rest) s r = (none,s,r) := by
  rw [run?,missing]

theorem nonstatic
    (p : Generic.OwnershipPlan F interface layout fixed written value s r check)
    (rest) (static : F.static = false) :
    run? F interface layout fixed check ((written,value)::rest) s r =
      run? F interface layout fixed check rest p.step.1.2 p.step.2 := by
  rw [run?,prepare_eq p]
  have success : p.step.1.1 = .ok () := congrArg (fun z => z.1.1) (p.nonstatic static)
  dsimp only
  rw [success]

theorem static
    (p : Generic.OwnershipPlan F interface layout fixed written value s r check)
    (rest) (static : F.static = true) :
    run? F interface layout fixed check ((written,value)::rest) s r =
      (some (.error (.revert [])),s,r) := by
  rw [run?,prepare_eq p]
  dsimp only
  rw [p.static static]

theorem MemOK (F : Source.Fr) (interface : Generic.OwnershipInterface E Γ F)
    (layout : interface.Layout) (fixed : Roadmap.Evm.Fixed)
    (check : List (ScalarPath E.layout (E.lay F.this)) → Bool)
    (requests) (s : Source.EMState E Γ) (r) (H : Source.HeapTy) (ok : Source.MemOK E H s) :
    Source.MemOK E H (run? F interface layout fixed check requests s r).2.1 := by
  induction requests generalizing s r with
  | nil => exact ok
  | cons request rest ih =>
    obtain ⟨q,v⟩ := request
    unfold run?
    split
    next absent => exact ok
    next p prepared =>
      split
      next error failed => exact p.MemOK H ok
      next success => exact ih p.step.1.2 p.step.2 (p.MemOK H ok)

theorem late_unsupported
    (p : Generic.OwnershipPlan F interface layout fixed written value s r check)
    (q v : Roadmap.Word) (rest) (static : F.static = false)
    (missing : Generic.prepareOwnership? F interface layout fixed q v p.step.1.2 p.step.2 check = none) :
    run? F interface layout fixed check ((written,value)::(q,v)::rest) s r =
      (none,p.step.1.2,p.step.2) := by
  rw [nonstatic p ((q,v)::rest) static]
  exact unsupported F interface layout fixed check q v rest p.step.1.2 p.step.2 missing

/-- Actual defining equations determine a typed finite preparation runner.
The hypotheses are computation equations, not desired preservation laws. -/
theorem eq_run_of_equations (F : Source.Fr)
    (interface : Generic.OwnershipInterface E Γ F) (layout : interface.Layout)
    (fixed : Roadmap.Evm.Fixed)
    (check : List (ScalarPath E.layout (E.lay F.this)) → Bool)
    (candidate : List (Roadmap.Word × Roadmap.Word) → Source.EMState E Γ →
      ResidualJournal complementCarrierOwnership →
      (Option (Except Source.Halt Unit) × Source.EMState E Γ × ResidualJournal complementCarrierOwnership))
    (empty : ∀ s r, candidate [] s r = (some (.ok ()),s,r))
    (stepEq : ∀ q v rest s r, candidate ((q,v)::rest) s r =
      match Generic.prepareOwnership? F interface layout fixed q v s r check with
      | none => (none,s,r)
      | some p => match p.step.1.1 with
        | .error e => (some (.error e),p.step.1.2,p.step.2)
        | .ok () => candidate rest p.step.1.2 p.step.2)
    (requests) (s : Source.EMState E Γ) (r) :
    candidate requests s r = run? F interface layout fixed check requests s r := by
  induction requests generalizing s r with
  | nil => rw [empty,run?]
  | cons request rest ih =>
    obtain ⟨q,v⟩ := request
    rw [stepEq,run?.eq_2]
    split <;> grind

end Solidity.Yul.Views.GenericFlow.Batch
