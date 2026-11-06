import Solidity.Backend.InternalFlow.RuntimeFrameV3EffectfulSourceCheck
import Solidity.Backend.InternalFlow.RuntimeFrameV3OrderedCalleeFailure
import Solidity.Backend.InternalFlow.RuntimeFrameV3OrderedEffectfulClient

/-! Inhabited effectful recognition and actual execution controls. Syntax
recognition is separate from the imported checked target endpoints. -/
namespace Solidity.Backend.InternalFlow.RuntimeFrame.EffectfulSourceCheck.Controls
open Evm Evm.Memory RecursiveSource ScalarRecursiveSource
abbrev C := CountdownWitness.P.C

def alteredWrite (index value : Int) (hi : PrimTy.uint.inRange index=true) (hv : PrimTy.uint.inRange value=true) : Stmt C (Frame A) (Frame A) :=
 .assignMem (.index .dyn (.var (.there (.there .here)) rfl) (.simple (.lit index hi)))
   (.val (.simple (.lit value hv)))

theorem wrong_index : checkWrite (alteredWrite 1 37 rfl rfl)=none := by rfl

theorem wrong_value : checkWrite (alteredWrite 0 38 rfl rfl)=none := by rfl

def alteredChild : Prog C (Frame A) (Frame A) :=
 ScalarRecursiveSource.step A rfl 1 (fun _ => .cons .revert .nil)

theorem outer_tail_matches : (ScalarSourceCheck.readHead A rfl alteredChild).isSome=true := by rfl

theorem deep_child_rejected : check 2 (.cons EffectfulScalarSource.write alteredChild)=none := by rfl

theorem missing_effect : check (C:=C) 2 (ScalarRecursiveSource.body A rfl 2)=none := by rfl

theorem wrong_depth : check (C:=C) 2 (EffectfulScalarSource.body 1)=none := by rfl

theorem wrong_effect : check 2 (.cons (alteredWrite 0 38 rfl rfl) (ScalarRecursiveSource.body A rfl 2))=none := by rfl

/-- The zero quotation is recognized, including recBase. Recognition does
    not assert that this exhausted recursive source matches target failure. -/
theorem zero_recognized : check (C:=C) 0 (EffectfulScalarSource.body 0)=some ⟨rfl⟩ := complete 0

theorem actual_success :
 (check (C:=C) 4 (EffectfulScalarSource.body 4)).isSome=true ∧
 (OrderedEffectfulScalar.call DisjointScalarReturn.Client.reference OrderedEffectfulScalar.Client.count
   (.here : Idx DisjointScalarReturn.Client.Γ (.val .uint)) "effectfulChecked" 4).run OrderedEffectfulScalar.Client.caller=
 .ok ⟨(OrderedEffectfulScalar.changed OrderedEffectfulScalar.Client.caller OrderedEffectfulScalar.Client.ref).setLocal
   .here (countValue 3 (by decide)),List.prefix_refl _⟩ ∧
 run (OrderedEffectfulScalar.code 1 5 DisjointScalarReturn.Client.reference OrderedEffectfulScalar.Client.value
   (.here : Idx DisjointScalarReturn.Client.Γ (.val .uint)) 9 8) OrderedEffectfulScalar.Client.before=
 .ok OrderedEffectfulScalar.Client.machine 0 := by
 refine ⟨?_,?_,OrderedEffectfulScalar.Client.specification.1⟩
 · rw [complete];rfl
 · simpa only [if_pos (show (3:Nat)<4 from by decide)] using
     OrderedEffectfulScalar.Client.specification.2.1 "effectfulChecked" 4

/-- Identical recognized callee syntax also has a real argument-success,
    callee-failure client. No output state is supplied by that revert. -/
theorem actual_failure :
 (check (C:=C) 4 (EffectfulScalarSource.body 4)).isSome=true ∧
 OrderedCalleeFailure.Client.args.evalT SameCallInputs.caller=
   .ok (countValue 3 (by decide),(some SameCallInputs.fresh,())) ∧
 run OrderedCalleeFailure.Client.image SameCallInputs.machine=.revert := by
 refine ⟨?_,OrderedCalleeFailure.Client.arguments,OrderedCalleeFailure.Client.target⟩
 rw [complete];rfl

end Solidity.Backend.InternalFlow.RuntimeFrame.EffectfulSourceCheck.Controls
