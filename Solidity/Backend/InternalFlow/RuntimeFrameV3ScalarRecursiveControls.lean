import Solidity.Backend.InternalFlow.RuntimeFrameV3ScalarRecursiveCall
import Solidity.Backend.InternalFlow.RuntimeFrameV3CountdownWitness

/-! Populated scalar-recursive caller and private-result controls. Source/kernel
execution only; no target recursive image or physical stack claim. -/
namespace Solidity.Backend.InternalFlow.RuntimeFrame.ScalarRecursiveSource.Controls
open Evm Evm.Memory RecursiveSource CountdownWitness
abbrev A := CountdownWitness.A
def Γ : Ctx := .val .uint :: P.Γ
def caller : State P.C Γ := CountdownWitness.caller.push (t:=.val .uint) (P.uint 77 (by decide))
def args : Args P.C Γ (Parameters A) :=
 .snoc (.snocMemory .nil A (.user "alias") (.var (.there (.there .here)) rfl)) .uint (.user "count") (.simple (.lit 3 rfl))
def invoke (destination : Idx Γ (.val .uint)) (depth : Nat) : Stmt P.C Γ Γ :=
 InterfaceV1.recursiveSource "scalarCountdown" args (.val .uint (.user "result") (some destination)) (step A rfl) depth

theorem arguments : args.evalT caller=.ok (countValue 3 (by decide),(some P.r0,())) := rfl

def output : Solidity.Out P.C caller.H Γ := ⟨caller.setLocal .here (countValue 3 (by decide)),List.prefix_refl _⟩
def otherOutput : Solidity.Out P.C caller.H Γ := ⟨caller.setLocal (.there .here) (countValue 3 (by decide)),List.prefix_refl _⟩

theorem source_all (depth : Nat) (enough : 3<depth) : (invoke .here depth).run caller=.ok output := by
 simpa only [if_pos enough] using call_all_horizons rfl "scalarCountdown" args .here depth caller 3 (by decide) P.r0 arguments

theorem alternate_all (depth : Nat) (enough : 3<depth) : (invoke (.there .here) depth).run caller=.ok otherOutput := by
 simpa only [if_pos enough] using call_all_horizons rfl "scalarCountdown" args (.there .here) depth caller 3 (by decide) P.r0 arguments

def entry : Solidity.Out P.C caller.H (Frame A) :=
 (CallRet.val .uint (.user "result") (some (.here : Idx Γ (.val .uint)))).enterT
   (caller.withEnv (Δ:=Parameters A) (countValue 3 (by decide),(some P.r0,())))

theorem private_default : (TEnv.get (.here : Idx (Frame A) (.val .uint)) entry.st.env).val=0 := rfl

theorem private_result : (body A rfl 4).run entry.st=.ok ⟨finished entry.st 3 (by decide),List.prefix_refl _⟩ := by
 simpa only [if_pos (show (3:Nat)<4 from by decide)] using all_horizons rfl 4 entry.st 3 (by decide) P.r0 rfl rfl

theorem ordered_bindings :
 ((TEnv.get (.here : Idx Γ (.val .uint)) output.st.env).val,
 (TEnv.get (.there .here : Idx Γ (.val .uint)) output.st.env).val,
 (TEnv.get (.there (.there .here) : Idx Γ (.mem A)) output.st.env).map HRef.id,
 (TEnv.get (.there (.there (.there .here)) : Idx Γ (.mem A)) output.st.env).map HRef.id,
 (TEnv.get (.there (.there (.there (.there .here))) : Idx Γ (.mem A)) output.st.env).map HRef.id)=
 (3,2,some 0,some 0,some 1) := rfl

theorem ordered_heap :
 (output.st.H.length,output.st.heap.len P.r0 .dyn,output.st.heap.len CompileExamples.r1 .dyn,
 [output.st.heap.readAddr (.index P.r0 .dyn (countValue 0 W_pos)),
  output.st.heap.readAddr (.index P.r0 .dyn (countValue 1 (by decide))),
  output.st.heap.readAddr (.index CompileExamples.r1 .dyn (countValue 0 W_pos))])=
 (2,2,1,[some (P.uint 7 (by decide)),some (P.uint 9 (by decide)),some (P.uint 4 (by decide))]) := by
 with_unfolding_all rfl

theorem other_fields : {output.st with env:=caller.env}=caller := rfl

theorem swapped_destination (depth : Nat) (enough : 3<depth) :
 (invoke .here depth).run caller≠(invoke (.there .here) depth).run caller := by
 rw [source_all depth enough,alternate_all depth enough]
 intro wrong
 have scalar := congrArg (fun o : Solidity.Out P.C caller.H Γ => (TEnv.get (.here : Idx Γ (.val .uint)) o.st.env).val) (Except.ok.inj wrong)
 change (3:Int)=77 at scalar
 omega

theorem not_default (depth : Nat) (enough : 3<depth) :
 (invoke .here depth).run caller≠.ok ⟨caller.setLocal .here (P.uint 0 W_pos),List.prefix_refl _⟩ := by
 rw [source_all depth enough]
 intro wrong
 have scalar := congrArg (fun o : Solidity.Out P.C caller.H Γ => (TEnv.get (.here : Idx Γ (.val .uint)) o.st.env).val) (Except.ok.inj wrong)
 change (3:Int)=0 at scalar
 omega

theorem wrong_alias (depth : Nat) (enough : 3<depth) :
 (invoke .here depth).run caller≠.ok ⟨output.st.setLocal (.there (.there .here)) (some CompileExamples.r1),List.prefix_refl _⟩ := by
 rw [source_all depth enough]
 intro wrong
 have alias := congrArg (fun o : Solidity.Out P.C caller.H Γ =>
   (TEnv.get (.there (.there .here) : Idx Γ (.mem A)) o.st.env).map HRef.id) (Except.ok.inj wrong)
 change (some 0 : Option Nat)=some 1 at alias
 cases alias

theorem shallow (depth : Nat) (short : depth≤3) : (invoke .here depth).run caller=.error .exhausted := by
 simpa only [if_neg (show ¬ (3:Nat)<depth from by omega)] using
   call_all_horizons rfl "scalarCountdown" args .here depth caller 3 (by decide) P.r0 arguments

theorem shallow_not_revert (depth : Nat) (short : depth≤3) : (invoke .here depth).run caller≠.error .revert := by
 rw [shallow depth short]
 intro wrong
 cases wrong

def absent := caller.setLocal (.there (.there .here)) (none : Option (HRef caller.H A))

theorem missing_argument (depth : Nat) : (invoke .here depth).run absent=.error .revert := by
 have failed : args.evalT absent=.error .revert := rfl
 change TRun.call args (.val .uint (.user "result") (some .here)) (body (C:=P.C) A rfl depth).ext
   (body A rfl depth).runR absent=_
 unfold TRun.call
 simp only [failed,error_bind]

end Solidity.Backend.InternalFlow.RuntimeFrame.ScalarRecursiveSource.Controls
