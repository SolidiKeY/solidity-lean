import Solidity.Yul.Views.OwnedBoolOwnershipFrame

namespace Solidity.Yul.Views

/-- Finite PREPARATION sequence, not Yul execution. Unsupported preparation
retains the exact successful prefix, including the owned representation journal.
The request list itself is the recursion index; no extra domain/fuel cap. -/
def runRepresentedOwnership? {E ds d active Γ} (F : Source.Fr)
    (layout : @ComputedStorage E ds d active F.this) (fixed : Roadmap.Evm.Fixed) :
    List (Roadmap.Word × Roadmap.Word) → Source.EMState E Γ → ResidualJournal complementCarrierOwnership → BoolEncodingJournal →
      (Option (Except Source.Halt Unit) × Source.EMState E Γ × ResidualJournal complementCarrierOwnership × BoolEncodingJournal)
  | [],s,r,encoding => (some (.ok ()),s,r,encoding)
  | (q,v)::rest,s,r,encoding => match prepareRepresentedOwnership? F layout fixed q v s r encoding with
    | none => (none,s,r,encoding)
    | some p => match p.step.1.1.1 with
      | .error error => (some (.error error),p.step.1.1.2,p.step.1.2,p.step.2)
      | .ok () => runRepresentedOwnership? F layout fixed rest p.step.1.1.2 p.step.1.2 p.step.2

theorem runRepresentedOwnership?_unsupported {E ds d active Γ} (F : Source.Fr)
    (layout : @ComputedStorage E ds d active F.this) (fixed : Roadmap.Evm.Fixed)
    (q v rest) (s : Source.EMState E Γ) (r encoding)
    (missing : prepareRepresentedOwnership? F layout fixed q v s r encoding=none) :
    runRepresentedOwnership? F layout fixed ((q,v)::rest) s r encoding=(none,s,r,encoding) := by
  rw [runRepresentedOwnership?,missing]

theorem RepresentedOwnershipPlan.batch_nonstatic {E ds d active Γ F layout fixed written value s r encoding}
    (p : @RepresentedOwnershipPlan E ds d active Γ F layout fixed written value s r encoding)
    (rest) (static : F.static=false) :
    runRepresentedOwnership? F layout fixed ((written,value)::rest) s r encoding=
      runRepresentedOwnership? F layout fixed rest p.step.1.1.2 p.step.1.2 p.step.2 := by
  rw [runRepresentedOwnership?,p.prepare_eq]
  have success : p.step.1.1.1=.ok () := congrArg (fun result => result.1.1.1) (p.nonstatic static)
  dsimp only
  rw [success]

theorem RepresentedOwnershipPlan.batch_static {E ds d active Γ F layout fixed written value s r encoding}
    (p : @RepresentedOwnershipPlan E ds d active Γ F layout fixed written value s r encoding)
    (rest) (static : F.static=true) :
    runRepresentedOwnership? F layout fixed ((written,value)::rest) s r encoding=
      (some (.error (.revert [])),s,r,encoding) := by
  rw [runRepresentedOwnership?,p.prepare_eq]
  dsimp only
  rw [p.static static]

theorem runRepresentedOwnership?_MemOK {E ds d active Γ} (F : Source.Fr)
    (layout : @ComputedStorage E ds d active F.this) (fixed : Roadmap.Evm.Fixed)
    (requests) (s : Source.EMState E Γ) (r encoding) (H : Source.HeapTy) (ok : Source.MemOK E H s) :
    Source.MemOK E H (runRepresentedOwnership? F layout fixed requests s r encoding).2.1 := by
  induction requests generalizing s r encoding with
  | nil => exact ok
  | cons request rest ih =>
    obtain ⟨q,v⟩ := request
    unfold runRepresentedOwnership?
    split
    next absent => exact ok
    next p prepared =>
      split
      next error failed => exact p.MemOK H ok
      next success => exact ih p.step.1.1.2 p.step.1.2 p.step.2 (p.MemOK H ok)

theorem RepresentedOwnershipPlan.batch_late_unsupported {E ds d active Γ F layout fixed written value s r encoding}
    (p : @RepresentedOwnershipPlan E ds d active Γ F layout fixed written value s r encoding)
    (q v rest) (static : F.static=false)
    (missing : prepareRepresentedOwnership? F layout fixed q v p.step.1.1.2 p.step.1.2 p.step.2=none) :
    runRepresentedOwnership? F layout fixed ((written,value)::(q,v)::rest) s r encoding=
      (none,p.step.1.1.2,p.step.1.2,p.step.2) := by
  rw [p.batch_nonstatic _ static]
  exact runRepresentedOwnership?_unsupported F layout fixed q v rest p.step.1.1.2 p.step.1.2 p.step.2 missing

end Solidity.Yul.Views
