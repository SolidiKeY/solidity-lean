import Solidity.Theory.Mutability.Closer
import tests.h62.item2.«audit-theories».BridgeWitnesses
import tests.h62.item2.«audit-theories».CoreTotality

/-!
All four frozen Closer input packets. Ordinary modal/spec inputs share an
actual successful bool declaration with their read-only and postcondition
premises. Transient packets use a populated cell store, real read success and
both read-only-context branches, not a reverting/panicking body.
-/
namespace H62.AuditTheories
open Solidity

/-- Every modal/read-only/run hypothesis holds simultaneously for a real run. -/
theorem closer_modal_joint_witness :
    ∃ (C : Contract) (μ : Mutability) (m : Modality) (Γ Γ' : Ctx)
      (P : Prog C Γ Γ') (σ : State C Γ) (φ : Fml C Γ') (o : Out C σ.H Γ'),
      Prog.within μ P = true ∧ μ ≠ .nonpayable ∧
        holds σ (.modal m P .nil φ) ∧ Prog.run σ P = .ok o := by
  obtain ⟨o, hr, _⟩ := CompilerAudit.bool_source_success bridgeContract true (State.init _)
  refine ⟨bridgeContract, .view, .diamond, [], [.val .bool],
    CompilerAudit.boolProgram bridgeContract true, State.init _, .tt, o, rfl, by decide, ?_, hr⟩
  have frames : Prog.runFrames (State.init bridgeContract)
      (CompilerAudit.boolProgram bridgeContract true) .nil = .ok o.st := by
    unfold Prog.runFrames
    rw [hr]
    rfl
  change Modality.diamond.afterRunTR _ _
  rw [frames]
  exact ⟨True.intro, by intro h; cases h⟩

/-- Spec's box premise, compatible output and source success coexist. -/
theorem closer_spec_joint_witness :
    ∃ (C : Contract) (μ : Mutability) (Γ Γ' : Ctx)
      (P : Prog C Γ Γ') (σ : State C Γ) (φ : Spec C Γ') (o : Out C σ.H Γ'),
      Prog.within μ P = true ∧ μ ≠ .nonpayable ∧
        Spec.sat σ (.box P φ) ∧ Prog.run σ P = .ok o := by
  obtain ⟨o, hr, _⟩ := CompilerAudit.bool_source_success bridgeContract true (State.init _)
  refine ⟨bridgeContract, .view, [], [.val .bool],
    CompilerAudit.boolProgram bridgeContract true, State.init _, .tt, o, rfl, by decide, ?_, hr⟩
  simp only [Spec.sat, hr]

private abbrev CL : Solidity.Transient.Layout := [("flag", .bool)]
/-- A nonempty transient cell store whose selected bool is true. -/
def closerFrame : Solidity.Transient.FrameState bridgeContract CL :=
  ⟨State.init _, (true, ())⟩

/-- Read-only source mutability admits a successful observed transient read. -/
theorem closer_transient_modal_joint_witness :
    ∃ (C : Contract) (L : Solidity.Transient.Layout) (α : Type) (m : Modality)
      (body : Solidity.Transient.Program C L α)
      (post : α → Solidity.Transient.FrameState C L → Prop)
      (ctx : Solidity.Transient.Context) (s : Solidity.Transient.FrameState C L),
      Solidity.Theory.Mutability.Transient.ReadOnlyCtx ctx ∧
        Solidity.Transient.Holds m body post ctx s ∧
          ∃ v t, Solidity.Transient.Program.run body ctx s = .ok (v,t) :=
  ⟨bridgeContract, CL, Bool, .diamond, .read .here,
    (fun v t => v = true ∧ t.cells = closerFrame.cells),
    ⟨.view, false⟩, closerFrame, Or.inr (by decide),
    ⟨⟨rfl, rfl⟩, (by intro h; cases h)⟩, true, closerFrame, rfl⟩

/-- Inherited static mode independently supplies read-only context and no panic,
    together with a real successful read from a populated transient store. -/
theorem closer_transient_frame_joint_witness :
    ∃ (C : Contract) (L : Solidity.Transient.Layout) (α : Type)
      (body : Solidity.Transient.Program C L α) (ctx : Solidity.Transient.Context)
      (s : Solidity.Transient.FrameState C L),
      Solidity.Theory.Mutability.Transient.ReadOnlyCtx ctx ∧
        Solidity.Transient.Program.run body ctx s ≠ .error .panic ∧
          ∃ v t, Solidity.Transient.Program.run body ctx s = .ok (v,t) :=
  ⟨bridgeContract, CL, Bool, .read .here, ⟨.nonpayable, true⟩, closerFrame,
    Or.inl rfl, (by intro h; cases h), true, closerFrame, rfl⟩

#print axioms closer_modal_joint_witness
#print axioms closer_spec_joint_witness
#print axioms closer_transient_modal_joint_witness
#print axioms closer_transient_frame_joint_witness
end H62.AuditTheories
