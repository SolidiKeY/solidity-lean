import Solidity.Backend.InternalFlow.RuntimeFrameV3EffectfulSourceSelection
import Solidity.Backend.InternalFlow.RuntimeFrameV3EffectfulSourceCheckControls

/-! Public source-selector roots and actual populated success, argument-failure
and callee-failure clients. No source-profile adequacy or general recursion
compiler closure is claimed. -/
namespace Solidity.Backend.InternalFlow.RuntimeFrame.EffectfulSourceSelection.Controls
open Evm Evm.Memory RecursiveSource ScalarRecursiveSource
open DisjointScalarReturn.Client (Γ F reference)
abbrev C := CountdownWitness.P.C

def input (count : Val C Γ .uint) (depth : Nat) : Stmt C Γ Γ :=
 call reference count .here (.user "outerAlias") (.user "outerCount") (.user "outerResult")
   "checkedEffectful" depth (fun _ => EffectfulScalarSource.body depth)

def select (count : Val C Γ .uint) (value : CompiledVal 1 F count)
 (root : Memory.compileVal 1 F count=some value) (depth : Nat) : Selected 1 F (input count depth) :=
 make reference count (.here : Idx Γ (.val .uint)) (.user "outerAlias") (.user "outerCount") (.user "outerResult")
   "checkedEffectful" depth (fun _ => EffectfulScalarSource.body depth) rfl
   (EffectfulSourceCheck.complete depth) value root

theorem root (count : Val C Γ .uint) (value : CompiledVal 1 F count)
 (valueRoot : Memory.compileVal 1 F count=some value) (depth : Nat) :
 compile 1 F (input count depth)=some (select count value valueRoot depth) :=
 compile_call reference count (.here : Idx Γ (.val .uint)) (.user "outerAlias") (.user "outerCount") (.user "outerResult")
   "checkedEffectful" depth (fun _ => EffectfulScalarSource.body depth) rfl
   (EffectfulSourceCheck.complete depth) value valueRoot

def good (depth : Nat) := select OrderedEffectfulScalar.Client.count OrderedEffectfulScalar.Client.value (by rfl) depth

theorem good_root (depth : Nat) : compile 1 F (input OrderedEffectfulScalar.Client.count depth)=some (good depth) :=
 root _ _ _ depth

theorem success (depth : Nat) (enough : 3<depth) :
 (input OrderedEffectfulScalar.Client.count depth).run OrderedEffectfulScalar.Client.caller=
   .ok ⟨(OrderedEffectfulScalar.changed OrderedEffectfulScalar.Client.caller OrderedEffectfulScalar.Client.ref).setLocal
     .here (countValue 3 (by decide)),List.prefix_refl _⟩ ∧
 run ((good depth).code 5 9 8) OrderedEffectfulScalar.Client.before=.ok OrderedEffectfulScalar.Client.machine 0 := by
 refine ⟨(good depth).source_run _ |>.trans ?_,OrderedEffectfulScalar.Client.specification.1⟩
 simpa only [if_pos enough] using OrderedEffectfulScalar.Client.specification.2.1 "checkedEffectful" depth

/-- The actual selected image is shared, not rebuilt from each quotation. -/
theorem same_image (left right : Nat) : (good left).code 5 9 8=(good right).code 5 9 8 := by rfl

def badCallee (depth : Nat) :=
 select OrderedCalleeFailure.Client.count OrderedCalleeFailure.Client.value OrderedCalleeFailure.Client.public_value_root depth

theorem bad_callee_root (depth : Nat) : compile 1 F (input OrderedCalleeFailure.Client.count depth)=some (badCallee depth) :=
 root _ _ _ depth

theorem callee_failure (depth : Nat) :
 (input OrderedCalleeFailure.Client.count depth).run SameCallInputs.caller=.error .revert ∧
 (∀ suffix,run ((badCallee depth).code 5 9 8++suffix) SameCallInputs.machine=.revert) :=
 (badCallee depth).callee_failure (c:=5) SameCallInputs.caller SameCallInputs.fresh rfl 3 (by decide)
   OrderedCalleeFailure.Client.evaluated EffectfulScalarFailure.Client.actual_write_failure
   SameCallInputs.addresses SameCallInputs.machine SameCallInputs.reached.2.2.1 (by decide) (by decide) 9 8

theorem argument_failure (depth : Nat) :
 (input OrderedEffectfulScalar.Client.count depth).run SameCallInputs.caller=.error .revert ∧
 (∀ suffix,run ((good depth).code 5 9 8++suffix) SameCallInputs.machine=.revert) :=
 (good depth).argument_failure (c:=5) SameCallInputs.caller SameCallInputs.count_fails
   SameCallInputs.addresses SameCallInputs.machine SameCallInputs.reached.2.2.1 (by decide) (by decide) 9 8

def altered (depth : Nat) : Stmt C Γ Γ :=
 call reference OrderedEffectfulScalar.Client.count .here (.user "outerAlias") (.user "outerCount") (.user "outerResult")
   "checkedEffectful" depth (fun _ => .cons (EffectfulSourceCheck.Controls.alteredWrite 0 38 rfl rfl)
      (ScalarRecursiveSource.body EffectfulScalarSource.A rfl depth))

theorem wrong_effect_rejected : compile 1 F (altered 2)=none := by rfl

def deepAltered : Stmt C Γ Γ :=
 call reference OrderedEffectfulScalar.Client.count .here (.user "outerAlias") (.user "outerCount") (.user "outerResult")
   "checkedEffectful" 2 (fun _ => .cons EffectfulScalarSource.write EffectfulSourceCheck.Controls.alteredChild)

theorem deep_child_rejected : compile 1 F deepAltered=none := by rfl

theorem ordinary_call_refused : compile 1 F
 (.call "checkedEffectful" (DisjointScalarEntry.args rfl reference OrderedEffectfulScalar.Client.count)
   (.val .uint (.user "outerResult") (some (.here : Idx Γ (.val .uint)))) (EffectfulScalarSource.body 4))=none := by rfl

/-- The selected target succeeds here while quotation zero exhausts. It must
    not be relabeled as all-outcome correspondence. -/
theorem exhausted_boundary :
 (input OrderedEffectfulScalar.Client.count 0).run OrderedEffectfulScalar.Client.caller=.error .exhausted ∧
 run ((good 0).code 5 9 8) OrderedEffectfulScalar.Client.before=.ok OrderedEffectfulScalar.Client.machine 0 := by
 refine ⟨(good 0).source_run _ |>.trans ?_,OrderedEffectfulScalar.Client.specification.1⟩
 simpa only [if_neg (show ¬(3:Nat)<0 from by decide)] using
   OrderedEffectfulScalar.Client.specification.2.1 "checkedEffectful" 0

end Solidity.Backend.InternalFlow.RuntimeFrame.EffectfulSourceSelection.Controls
