import Solidity.Yul.Views.PackedResidualFrame

namespace Solidity.Yul.Views

/-- Finite sequences of actual canonical source operations. Each step checks
Source.applyOp's static rule before its paired complementary residual update.
The list is the supplied program, not a new execution/resource limit. -/
def runPackedSource {E : Source.Env} {Γ : Source.RCtx} {ps ts} (F : Source.Fr) :
    List (@PackedSlotPlan E.layout E.lay E.lay ps ts) → Source.EMState E Γ →
    ResidualJournal complementCarrierOwnership →
    ((Except Source.Halt Unit × Source.EMState E Γ) × ResidualJournal complementCarrierOwnership)
  | [], s, r => ((.ok (),s),r)
  | p::plans, s, r =>
    let step := packedSourceStep F p s r
    match step.1.1 with
    | .error _ => step
    | .ok _ => runPackedSource F plans step.1.2 step.2

theorem runPackedSource_nonstatic {E : Source.Env} {Γ : Source.RCtx} {ps ts} (F : Source.Fr)
    (plans : List (@PackedSlotPlan E.layout E.lay E.lay ps ts)) (s : Source.EMState E Γ)
    (r : ResidualJournal complementCarrierOwnership) (static : F.static = false) :
    runPackedSource F plans s r =
      ((.ok (),(s.1,{s.2 with ex := (runPackedSlots ⟨s.2.ex,r⟩ plans).source})),
        (runPackedSlots ⟨s.2.ex,r⟩ plans).residual) := by
  induction plans generalizing s r with
  | nil => rfl
  | cons p plans ih =>
    rw [runPackedSource,packedSourceStep_nonstatic F p s r static]
    rw [ih]
    rfl

theorem runPackedSource_companion {E : Source.Env} {Γ : Source.RCtx} {ps ts} (F : Source.Fr)
    (plans : List (@PackedSlotPlan E.layout E.lay E.lay ps ts)) (s : Source.EMState E Γ)
    (r : ResidualJournal complementCarrierOwnership) (static : F.static = false) :
    (⟨(runPackedSource F plans s r).1.2.2.ex,(runPackedSource F plans s r).2⟩ :
      ResidualCompanion E.layout E.lay E.lay complementCarrierOwnership) = runPackedSlots ⟨s.2.ex,r⟩ plans := by
  rw [runPackedSource_nonstatic F plans s r static]

theorem runPackedSource_static {E : Source.Env} {Γ : Source.RCtx} {ps ts} (F : Source.Fr)
    (p : @PackedSlotPlan E.layout E.lay E.lay ps ts) (plans) (s : Source.EMState E Γ)
    (r : ResidualJournal complementCarrierOwnership) (static : F.static = true) :
    runPackedSource F (p::plans) s r = ((.error (.revert []),s),r) := by
  rw [runPackedSource,packedSourceStep_static F p s r static]

theorem runPackedSource_MemOK {E : Source.Env} {Γ : Source.RCtx} {ps ts} (F : Source.Fr)
    (plans : List (@PackedSlotPlan E.layout E.lay E.lay ps ts)) (s : Source.EMState E Γ)
    (r : ResidualJournal complementCarrierOwnership) (H : Source.HeapTy) (ok : Source.MemOK E H s) :
    Source.MemOK E H (runPackedSource F plans s r).1.2 := by
  cases plans with
  | nil => exact ok
  | cons p plans =>
    cases static : F.static
    · rw [runPackedSource_nonstatic F (p::plans) s r static]
      exact ⟨⟨⟨ok.1.1.heap,ok.1.1.le⟩,ok.1.2⟩,ok.2.1,ok.2.2⟩
    · rw [runPackedSource_static F p plans s r static]
      exact ok

end Solidity.Yul.Views
