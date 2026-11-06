import Solidity.Backend.Passes.CapturedValueStability
import Solidity.Backend.InternalFlow.RuntimeFrameV3BareRevertProducer

/-! A typed local-value assignment feeds the actual physical input of the
published failure-only runtime producer. No approved profile is invented. -/
namespace Solidity.Backend.Passes.AssignedBareRevert
open Evm Evm.Memory Evm.Compiler
open Solidity.Backend.InternalFlow.RuntimeFrame

def assignmentStage {C : Contract} {Γ : Ctx} {p : PrimTy} {b : Nat} {F : Frag Γ}
    (dst : Idx Γ (.val p)) (operand : Val C Γ p) (given : CompiledVal b F operand) :
    Compilation b F (.cons (.assignLocal dst operand) .nil) :=
  .memory ⟨F,(given.code ++ [.mstore (cellOf b dst)]) ++ [],
    .cons (.assign F dst operand _ given.cert) (.nil F)⟩


theorem reached
    {C : Solidity.Contract} {Γ Δ : Solidity.Ctx} {p : Solidity.PrimTy}
    {b L frame : Nat} {F : Solidity.Evm.Frag Γ}
    (dst : Solidity.Idx Γ (.val p)) (operand : Solidity.Val C Γ p)
    (given : Solidity.Evm.Memory.CompiledVal b F operand)
    {σ : Solidity.State C Γ} {base : Nat → Fin Solidity.Evm.W} {machine : Solidity.Evm.Machine}
    (represented : Solidity.Evm.Memory.StateRepr L b frame F σ base machine)
    (value : p.Denote) (evaluated : operand.evalT σ = .ok value)
    (statement : Solidity.Stmt C Γ Δ)
    (selected : Solidity.Backend.InternalFlow.RuntimeFrame.Composition.Program b F (.cons statement .nil))
    (lo pointer start : Nat)
    (callerRoom : b+Γ.length ≤ lo) (resultRoom : b+Δ.length ≤ lo)
    (workspace : b+selected.checked.need ≤ lo)
    (pointerAbove : lo ≤ pointer) (pointerBelow : pointer < frame)
    (payloadAbove : lo ≤ start) (reserve : start+(Γ.length+1) ≤ frame)
    (separate : pointer < start ∨ start+(Γ.length+1) ≤ pointer)
    (noWrap : start+(Γ.length+1) < Solidity.Evm.W)
    (cursor : machine.mem pointer = .val (Solidity.Evm.wmod start))
    (capacity : Solidity.Evm.Memory.AllocationInput b frame
      (selected.checked.cost (σ.setLocal dst value)) σ base machine)
    (failed : statement.run (σ.setLocal dst value) = .error .revert) :
    (Solidity.Prog.cons (.assignLocal dst operand) (.cons statement .nil)).run σ = .error .revert ∧
    ∃ word, Solidity.Evm.ReprV p value word ∧ ∀ tail,
      let entry := {machine with stack := tail}
      let mid := Solidity.Evm.Memory.writeMachine entry (Solidity.Evm.cellOf b dst) word
      (Solidity.Backend.Passes.AssignedBareRevert.assignmentStage dst operand given).Input L frame base σ entry ∧
      Solidity.Evm.run (Solidity.Backend.Passes.AssignedBareRevert.assignmentStage dst operand given).code entry = .ok mid 0 ∧
      Solidity.Backend.Passes.MappedOutput (Solidity.Backend.Passes.AssignedBareRevert.assignmentStage dst operand given)
        L frame base σ entry (σ.setLocal dst value) mid base ∧
      Solidity.Backend.InternalFlow.RuntimeFrame.V3BareRevertProducer.admitted selected lo pointer
        L frame (σ.setLocal dst value) base mid start ∧
      Solidity.Evm.run (Solidity.Backend.InternalFlow.RuntimeFrame.V3BareRevertProducer.plan selected lo pointer).code mid = .revert ∧
      Solidity.Evm.run ((Solidity.Backend.Passes.AssignedBareRevert.assignmentStage dst operand given).code ++
        (Solidity.Backend.InternalFlow.RuntimeFrame.V3BareRevertProducer.plan selected lo pointer).code) entry = .revert := by
  have assigned : (Stmt.assignLocal dst operand).run σ =
      .ok ⟨σ.setLocal dst value,List.prefix_refl _⟩ := by
    change TRun.assignLocal dst operand σ = _
    simp only [TRun.assignLocal,evaluated,bind,Except.bind]
    rfl
  constructor
  · rw [Prog.run_cons_ok assigned,Prog.run_cons_error failed]
    rfl
  · obtain ⟨word,repr,runs⟩ := CapturedValueStability.value_shared operand given represented value evaluated
    refine ⟨word,repr,?_⟩
    intro tail
    let entry := {machine with stack := tail}
    let mid := writeMachine entry (cellOf b dst) word
    have below : cellOf b dst < frame :=
      Nat.lt_of_lt_of_le (lvl_lt b dst) represented.locals
    have belowArena : cellOf b dst < lo :=
      Nat.lt_of_lt_of_le (lvl_lt b dst) callerRoom
    have prefixInput : (assignmentStage dst operand given).Input L frame base σ entry := by
      refine ⟨represented.stack tail,?_,Or.inl rfl⟩
      change b + max (max Γ.length (max Γ.length 0)) Γ.length ≤ frame
      have locals := represented.locals
      omega
    have prefixRun : run (assignmentStage dst operand given).code entry = .ok mid 0 := by
      simp only [assignmentStage,Compilation.code,List.append_nil]
      rw [run_append_ok (runs tail)]
      rfl
    have nextRepr := (represented.stack tail).setVal dst value word repr
    have mapped : MappedOutput (assignmentStage dst operand given)
        L frame base σ entry (σ.setLocal dst value) mid base := by
      refine ⟨nextRepr,BaseExtends.refl base,?_⟩
      intro free positive allocation space
      exact allocation.localWrite _ (Nat.lt_of_lt_of_le positive (le_lvl b dst)) below word
    have nextCapacity : AllocationInput b frame (selected.checked.cost (σ.setLocal dst value))
        (σ.setLocal dst value) base mid := by
      rcases capacity with zero | ⟨positive,free,allocation,space⟩
      · exact .inl zero
      · exact .inr ⟨positive,free,(allocation.stack tail).localWrite _
          (Nat.lt_of_lt_of_le positive (le_lvl b dst)) below word,space⟩
    have rightInput : V3BareRevertProducer.admitted selected lo pointer
        L frame (σ.setLocal dst value) base mid start := by
      refine ⟨nextRepr,callerRoom,resultRoom,workspace,pointerAbove,pointerBelow,
        payloadAbove,reserve,separate,noWrap,?_,nextCapacity⟩
      change upd machine.mem (cellOf b dst) word pointer = _
      rw [upd_other _ _ (by omega)]
      exact cursor
    have endpoint := V3BareRevertProducer.bare_revert selected lo pointer
      L frame (σ.setLocal dst value) base mid start
      (V3BareRevertProducer.coverage selected lo pointer
        L frame (σ.setLocal dst value) base mid start rightInput) failed
    refine ⟨prefixInput,prefixRun,mapped,rightInput,endpoint,?_⟩
    rw [run_append_ok prefixRun]
    exact endpoint

end Solidity.Backend.Passes.AssignedBareRevert

/-- info: 'Solidity.Backend.Passes.AssignedBareRevert.reached' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Solidity.Backend.Passes.AssignedBareRevert.reached
