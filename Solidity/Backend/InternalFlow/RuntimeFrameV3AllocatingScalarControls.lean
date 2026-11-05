import Solidity.Backend.InternalFlow.RuntimeFrameV3AllocatingScalarOutcomes
import Solidity.Backend.InternalFlow.RuntimeFrameV3AllocatingScalarReturn
import Solidity.Backend.InternalFlow.RuntimeFrameV3CountdownWitness

/-! An actual native call with default private result entry, two recursive
allocating activations and primitive caller export. All observations are source
kernel facts, not physical target/capacity or profile evidence. -/
namespace Solidity.Backend.InternalFlow.RuntimeFrame.AllocatingScalarSource.Controls
open Evm Evm.Memory RecursiveSource ScalarRecursiveSource CountdownWitness
namespace Q
abbrev C := CountdownWitness.P.C
abbrev Γ := CountdownWitness.P.Γ
end Q
def caller := CountdownWitness.caller.setLocal (.here : Idx Q.Γ (.val .uint)) (countValue 77 (by decide))
def args : Args Q.C Q.Γ (Parameters A) :=
 .snoc (.snocMemory .nil A (.user "alias") (.var (.there .here) rfl))
  .uint (.user "count") (.simple (.lit 2 rfl))
def ret : CallRet Q.Γ [.val .uint] Q.Γ := .val .uint (.user "result") (some .here)
def arguments : TEnv Q.C caller.H (Parameters A) := (countValue 2 (by decide),(some P.r0,()))
def initial := (ret.enterT (caller.withEnv arguments)).st

def expected : Solidity.Out Q.C initial.H (Frame A) :=
 ⟨finished (allocated (allocated initial)) 2 (by decide),
  (extension initial).trans (extension (allocated initial))⟩

def invoke (depth : Nat) : Stmt Q.C Q.Γ Q.Γ :=
 .callRec "allocatingScalar" depth args ret (fun _ => body A rfl depth)
def output : Solidity.Out Q.C caller.H Q.Γ :=
 exported ret Ext.refl caller arguments expected

theorem args_run : args.evalT caller=.ok arguments := rfl

theorem default_entry : (TEnv.get (.here : Idx (Frame A) (.val .uint)) initial.env).val=0 := rfl

theorem callee : (body A rfl 3).run initial=.ok expected :=
 two_return rfl initial 0 P.r0 rfl rfl

theorem native : (invoke 3).run caller=.ok output :=
 call_return args ret Ext.refl (body A rfl 3).runR caller arguments args_run expected callee

theorem generic_witness (depth : Nat) (enough : 2<depth) :
 ∃ out,(body A rfl depth).run initial=.ok out ∧
 out.st.H.length=initial.H.length+2 ∧
 out.st.env=TEnv.set (.here : Idx (Frame A) (.val .uint)) (countValue 2 (by decide))
  (TEnv.wk out.ext (Frame A) initial.env) ∧ Heap.Keeps out.ext initial.heap out.st.heap :=
 success rfl depth initial 2 (by decide) P.r0 rfl rfl enough

theorem observations :
 ((TEnv.get (.here : Idx Q.Γ (.val .uint)) output.st.env).val,
 (TEnv.get (.there .here : Idx Q.Γ (.mem A)) output.st.env).map HRef.id,
 (TEnv.get (.there (.there .here) : Idx Q.Γ (.mem A)) output.st.env).map HRef.id,
 (TEnv.get (.there (.there (.there .here)) : Idx Q.Γ (.mem A)) output.st.env).map HRef.id,
 output.st.H.length)= (2,some 0,some 0,some 1,4) := by with_unfolding_all rfl

def firstPrivate : HRef output.st.H (.array (.prim .bool)) := ⟨2,by with_unfolding_all rfl⟩
def secondPrivate : HRef output.st.H (.array (.prim .bool)) := ⟨3,by with_unfolding_all rfl⟩

theorem heap_observations :
 ((output.st.heap.get (P.r0.wk output.ext)).val.map (fun v => v.val),
 (output.st.heap.get (CompileExamples.r1.wk output.ext)).val.map (fun v => v.val),
 (output.st.heap.get firstPrivate).val,(output.st.heap.get secondPrivate).val)=
 ([7,9],[4],[false,false,false],[false,false,false]) := by with_unfolding_all rfl

theorem shallow : (body A rfl 2).run initial=.error .exhausted :=
 exhaustion rfl 2 initial 2 (by decide) P.r0 rfl rfl (by decide)

theorem shallow_not_revert : (body A rfl 2).run initial≠.error .revert := by
 rw [shallow]
 intro wrong
 cases wrong

def absent := initial.setLocal (.there (.there .here)) (none : Option (HRef initial.H A))

theorem bad_reference : (body A rfl 3).run absent=.error .revert := by with_unfolding_all rfl

theorem wrong_result : (TEnv.get (.here : Idx Q.Γ (.val .uint)) output.st.env).val≠77 := by decide +kernel

theorem wrong_growth : output.st.H.length≠3 := by with_unfolding_all decide +kernel

end Solidity.Backend.InternalFlow.RuntimeFrame.AllocatingScalarSource.Controls

/-- info: 'Solidity.Backend.InternalFlow.RuntimeFrame.AllocatingScalarSource.Controls.args_run' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Solidity.Backend.InternalFlow.RuntimeFrame.AllocatingScalarSource.Controls.args_run

/-- info: 'Solidity.Backend.InternalFlow.RuntimeFrame.AllocatingScalarSource.Controls.default_entry' depends on axioms: [propext] -/
#guard_msgs (whitespace := lax) in
#print axioms Solidity.Backend.InternalFlow.RuntimeFrame.AllocatingScalarSource.Controls.default_entry

/-- info: 'Solidity.Backend.InternalFlow.RuntimeFrame.AllocatingScalarSource.Controls.callee' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Solidity.Backend.InternalFlow.RuntimeFrame.AllocatingScalarSource.Controls.callee

/-- info: 'Solidity.Backend.InternalFlow.RuntimeFrame.AllocatingScalarSource.Controls.native' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Solidity.Backend.InternalFlow.RuntimeFrame.AllocatingScalarSource.Controls.native

/-- info: 'Solidity.Backend.InternalFlow.RuntimeFrame.AllocatingScalarSource.Controls.generic_witness' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Solidity.Backend.InternalFlow.RuntimeFrame.AllocatingScalarSource.Controls.generic_witness

/-- info: 'Solidity.Backend.InternalFlow.RuntimeFrame.AllocatingScalarSource.Controls.observations' depends on axioms: [propext] -/
#guard_msgs (whitespace := lax) in
#print axioms Solidity.Backend.InternalFlow.RuntimeFrame.AllocatingScalarSource.Controls.observations

/-- info: 'Solidity.Backend.InternalFlow.RuntimeFrame.AllocatingScalarSource.Controls.heap_observations' depends on axioms: [propext] -/
#guard_msgs (whitespace := lax) in
#print axioms Solidity.Backend.InternalFlow.RuntimeFrame.AllocatingScalarSource.Controls.heap_observations

/-- info: 'Solidity.Backend.InternalFlow.RuntimeFrame.AllocatingScalarSource.Controls.shallow' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Solidity.Backend.InternalFlow.RuntimeFrame.AllocatingScalarSource.Controls.shallow

/-- info: 'Solidity.Backend.InternalFlow.RuntimeFrame.AllocatingScalarSource.Controls.shallow_not_revert' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Solidity.Backend.InternalFlow.RuntimeFrame.AllocatingScalarSource.Controls.shallow_not_revert

/-- info: 'Solidity.Backend.InternalFlow.RuntimeFrame.AllocatingScalarSource.Controls.bad_reference' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Solidity.Backend.InternalFlow.RuntimeFrame.AllocatingScalarSource.Controls.bad_reference

/-- info: 'Solidity.Backend.InternalFlow.RuntimeFrame.AllocatingScalarSource.Controls.wrong_result' depends on axioms: [propext] -/
#guard_msgs (whitespace := lax) in
#print axioms Solidity.Backend.InternalFlow.RuntimeFrame.AllocatingScalarSource.Controls.wrong_result

/-- info: 'Solidity.Backend.InternalFlow.RuntimeFrame.AllocatingScalarSource.Controls.wrong_growth' depends on axioms: [propext] -/
#guard_msgs (whitespace := lax) in
#print axioms Solidity.Backend.InternalFlow.RuntimeFrame.AllocatingScalarSource.Controls.wrong_growth
