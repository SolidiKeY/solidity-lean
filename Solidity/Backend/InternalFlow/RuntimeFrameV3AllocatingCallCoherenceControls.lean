import Solidity.Backend.InternalFlow.RuntimeFrameV3AllocatingCallCoherence
import Solidity.Backend.InternalFlow.RuntimeFrameV3AllocatingScalarReturn
import Solidity.Backend.InternalFlow.RuntimeFrameV3AllocatingScalarTarget

/-! Real outer callRec arguments/entry/allocation/return at two quotation
indices. Index zero genuinely exhausts and is not bare revert. -/
namespace Solidity.Backend.InternalFlow.RuntimeFrame.AllocatingCallCoherence.Controls
open Evm Evm.Memory RecursiveSource ScalarRecursiveSource
abbrev C := CountdownWitness.P.C
abbrev A := CountdownWitness.A
abbrev σ := AllocatingScalarTarget.initial

def call (depth : Nat) : Stmt C (Frame A) (Frame A) :=
 InterfaceV1.recursiveSource "allocatingClient" (next A (by rfl)) (result A)
   (AllocatingScalarSource.step A (by rfl)) depth

theorem actual : ∃ left right,
 (call 2).run σ=.ok left ∧ (call 4).run σ=.ok right ∧ left=right ∧
 left.st.H.length=3 ∧
 TEnv.get (.here : Idx (Frame A) (.val .uint)) left.st.env=countValue 1 (by decide) ∧
 TEnv.get (.there .here : Idx (Frame A) (.val .uint)) left.st.env=countValue 2 (by decide) ∧
 (call 0).run σ=.error .exhausted ∧ (call 0).run σ≠.error .revert := by
 let arguments : TEnv C σ.H (Parameters A) := (countValue 1 (by decide),(some CountdownWitness.P.r0,()))
 let child := entered σ 1 (by decide) CountdownWitness.P.r0
 let bodyOut : Solidity.Out C child.H (Frame A) :=
   ⟨finished (AllocatingScalarSource.allocated child) 1 (by decide),AllocatingScalarSource.extension child⟩
 let expected := exported (result A) Ext.refl σ arguments bodyOut
 have evaluated : (next A (by rfl)).evalT σ=.ok arguments := next_eval (by rfl) σ 1 (by decide) CountdownWitness.P.r0 rfl rfl
 have inner2 : (AllocatingScalarSource.body A (by rfl) 2).run child=.ok bodyOut :=
   AllocatingScalarSource.one_return (by rfl) child 0 CountdownWitness.P.r0 rfl rfl
 have inner4 : (AllocatingScalarSource.body A (by rfl) 4).run child=.ok bodyOut :=
   AllocatingScalarSource.one_return (by rfl) child 2 CountdownWitness.P.r0 rfl rfl
 have first : (call 2).run σ=.ok expected := by
   change TRun.call (next A (by rfl)) (result A) (AllocatingScalarSource.body A (by rfl) 2).ext
     (AllocatingScalarSource.body A (by rfl) 2).runR σ=_
   have scope : (AllocatingScalarSource.body (C:=C) A (by rfl) 2).ext=Ext.refl := Subsingleton.elim _ _
   rw [scope]
   exact call_return (next A (by rfl)) (result A) .refl _ σ arguments evaluated bodyOut inner2
 have second : (call 4).run σ=.ok expected := by
   change TRun.call (next A (by rfl)) (result A) (AllocatingScalarSource.body A (by rfl) 4).ext
     (AllocatingScalarSource.body A (by rfl) 4).runR σ=_
   have scope : (AllocatingScalarSource.body (C:=C) A (by rfl) 4).ext=Ext.refl := Subsingleton.elim _ _
   rw [scope]
   exact call_return (next A (by rfl)) (result A) .refl _ σ arguments evaluated bodyOut inner4
 have same := source_coherence (by rfl) "allocatingClient" (next A (by rfl)) (result A)
   σ 2 4 expected expected first second
 have exhausted : (call 0).run σ=.error .exhausted := by
   change TRun.call (next A (by rfl)) (result A) (AllocatingScalarSource.body A (by rfl) 0).ext
     (AllocatingScalarSource.body A (by rfl) 0).runR σ=_
   have scope : (AllocatingScalarSource.body (C:=C) A (by rfl) 0).ext=Ext.refl := Subsingleton.elim _ _
   rw [scope]
   unfold TRun.call
   simp only [evaluated,ok_bind]
   rfl
 refine ⟨expected,expected,first,second,same,rfl,rfl,rfl,exhausted,?_⟩
 rw [exhausted]
 intro bad
 cases bad

end Solidity.Backend.InternalFlow.RuntimeFrame.AllocatingCallCoherence.Controls
/-- info: 'Solidity.Backend.InternalFlow.RuntimeFrame.AllocatingCallCoherence.Controls.actual' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Solidity.Backend.InternalFlow.RuntimeFrame.AllocatingCallCoherence.Controls.actual
