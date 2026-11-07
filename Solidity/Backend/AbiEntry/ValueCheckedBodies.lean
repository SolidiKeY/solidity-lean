import Solidity.Backend.AbiEntry.ValueCheckedBodiesInterface

/-! Existing value-gate and primitive compiler proofs compose without a new
framework. Payability precedes all calldata-local reads; body outcomes remain
observable. Source body association/native realization are separate. -/
namespace Solidity.Backend.AbiEntry.ValueCheckedBodies
open Solidity.Evm
open Interface
variable {C : Contract} {Δ : Ctx}

namespace UInt
def program (bits : Nat) (payable : Bool) (label : Fin W) (body : Prog C UIntBoundCtx Δ) : Prog C RouteCtx Δ :=
  ValueGateBody.guard payable (UIntBindingBody.program bits label body)

theorem admitted (bits : Nat) (payable : Bool) (label : Fin W) (body : Prog C UIntBoundCtx Δ)
    (outFrag : Frag Δ) (bodyCore : inFragP (Frag.init UIntBoundCtx) body=some outFrag) :
    inFragP (Frag.init RouteCtx) (program bits payable label body)=some outFrag :=
  ValueGateBody.admitted _ _ payable outFrag (UIntBindingBody.admitted bits label body outFrag bodyCore)

def compiled (base bits : Nat) (payable : Bool) (label : Fin W) (body : Prog C UIntBoundCtx Δ)
    (outFrag : Frag Δ) (bodyCore : inFragP (Frag.init UIntBoundCtx) body=some outFrag) :
    Compiler.Compilation base (Frag.init RouteCtx) (program bits payable label body) :=
  ValueGateBody.selectedWhole base _ (UIntBindingBody.program bits label body) payable outFrag
    (UIntBindingBody.admitted bits label body outFrag bodyCore)

theorem selected (base bits : Nat) (payable : Bool) (label : Fin W) (body : Prog C UIntBoundCtx Δ)
    (outFrag : Frag Δ) (bodyCore : inFragP (Frag.init UIntBoundCtx) body=some outFrag) :
    Compiler.compile base (Frag.init RouteCtx) (program bits payable label body)=
      some (compiled base bits payable label body outFrag bodyCore) :=
  ValueGateBody.whole_selected base _ (UIntBindingBody.program bits label body) payable outFrag
    (UIntBindingBody.admitted bits label body outFrag bodyCore)

theorem gated (base bits : Nat) (payable : Bool) (label : Fin W) (body : Prog C UIntBoundCtx Δ)
    (outFrag : Frag Δ) (bodyCore : inFragP (Frag.init UIntBoundCtx) body=some outFrag)
    (whole : Compiler.Compilation base (Frag.init RouteCtx) (program bits payable label body))
    (found : Compiler.compile base (Frag.init RouteCtx) (program bits payable label body)=some whole)
    (machine : Machine) :
    run whole.code machine=if payable || decide (machine.callvalue.val=0) then
      run (UIntBindingBody.selectedWhole base bits label body outFrag bodyCore).code machine else .revert :=
  ValueGateBody.executed base _ (UIntBindingBody.program bits label body) payable outFrag
    (UIntBindingBody.admitted bits label body outFrag bodyCore) whole
    (UIntBindingBody.selectedWhole base bits label body outFrag bodyCore) found
    (UIntBindingBody.whole_selected base bits label body outFrag bodyCore) machine

theorem executed (base bits : Nat) (payable : Bool) (label : Fin W) (body : Prog C UIntBoundCtx Δ)
    (outFrag : Frag Δ) (bodyCore : inFragP (Frag.init UIntBoundCtx) body=some outFrag)
    (whole : Compiler.Compilation base (Frag.init RouteCtx) (program bits payable label body))
    (back : Compiler.Compilation base (Frag.init UIntBoundCtx) body)
    (wholeFound : Compiler.compile base (Frag.init RouteCtx) (program bits payable label body)=some whole)
    (bodyFound : Compiler.compile base (Frag.init UIntBoundCtx) body=some back)
    (machine : Machine) (word size : Fin W) (initialWord : machine.mem base=.val word)
    (initialSize : machine.mem (base+1)=.val size) :
    run whole.code machine=if payable || decide (machine.callvalue.val=0) then
      if size.val<36 then .revert else if (Solidity.AbiEntry.Kind.uint bits).valid word.val then
        run back.code (uintBoundMachine base label word machine) else .revert else .revert := by
  rw [gated base bits payable label body outFrag bodyCore whole wholeFound machine]
  rw [UIntBindingBody.executed base bits label body outFrag bodyCore
    (UIntBindingBody.selectedWhole base bits label body outFrag bodyCore) back
    (UIntBindingBody.whole_selected base bits label body outFrag bodyCore) bodyFound machine word size initialWord initialSize]

theorem early_rejection (base bits : Nat) (payable : Bool) (label : Fin W) (body : Prog C UIntBoundCtx Δ)
    (outFrag : Frag Δ) (bodyCore : inFragP (Frag.init UIntBoundCtx) body=some outFrag)
    (whole : Compiler.Compilation base (Frag.init RouteCtx) (program bits payable label body))
    (found : Compiler.compile base (Frag.init RouteCtx) (program bits payable label body)=some whole)
    (machine : Machine) (blocked : (payable || decide (machine.callvalue.val=0))=false) :
    run whole.code machine=.revert := by
  rw [gated base bits payable label body outFrag bodyCore whole found machine]
  simp only [blocked,Bool.false_eq_true,if_false]

theorem decoded_body (base bits : Nat) (payable : Bool) (label : Fin W) (body : Prog C UIntBoundCtx Δ)
    (outFrag : Frag Δ) (bodyCore : inFragP (Frag.init UIntBoundCtx) body=some outFrag)
    (whole : Compiler.Compilation base (Frag.init RouteCtx) (program bits payable label body))
    (back : Compiler.Compilation base (Frag.init UIntBoundCtx) body)
    (wholeFound : Compiler.compile base (Frag.init RouteCtx) (program bits payable label body)=some whole)
    (bodyFound : Compiler.compile base (Frag.init UIntBoundCtx) body=some back)
    (input : Solidity.AbiEntry.Input) (fuel : Nat) (machine : Machine) (size : Fin W)
    (initialWord : machine.mem base=.val (rawArgumentWord input))
    (initialSize : machine.mem (base+1)=.val size) (represented : size.val=input.size)
    (allowed : (payable || decide (machine.callvalue.val=0))=true) (full : ¬input.size<36)
    (valid : (Solidity.AbiEntry.Kind.uint bits).valid (Solidity.AbiEntry.load input.data 4)=true) :
    ∃ value : Solidity.AbiEntry.Word (.uint bits),
      Solidity.AbiEntry.entry input (fuel+2) (singleWordParams (.uint bits))=.ok (.cons (.val (.word value)) .nil) ∧
      (uintBoundMachine base label (rawArgumentWord input) machine).mem
        (cellOf base (.here : Idx UIntBoundCtx (.val .uint)))=.val ⟨value.val,value.lt⟩ ∧
      run whole.code machine=run back.code (uintBoundMachine base label (rawArgumentWord input) machine) := by
  rcases UIntBindingBody.decoded_body base bits label body outFrag bodyCore
    (UIntBindingBody.selectedWhole base bits label body outFrag bodyCore) back
    (UIntBindingBody.whole_selected base bits label body outFrag bodyCore) bodyFound
    input fuel machine size initialWord initialSize represented full valid with ⟨value,semantic,cell,bodyRun⟩
  refine ⟨value,semantic,cell,?_⟩
  rw [gated base bits payable label body outFrag bodyCore whole wholeFound machine,if_pos allowed,bodyRun]

def certificate : Interface.ValueCheckedUIntBodyCertificate program where
  selected := fun base bits payable label body outFrag bodyCore =>
    ⟨compiled base bits payable label body outFrag bodyCore,UIntBindingBody.selectedBody base body outFrag bodyCore,
      selected base bits payable label body outFrag bodyCore,UIntBindingBody.body_selected base body outFrag bodyCore⟩
  executed := executed
  early_rejection := early_rejection

/-- info: 'Solidity.Backend.AbiEntry.ValueCheckedBodies.UInt.admitted' depends on axioms: [propext] -/
#guard_msgs (whitespace := lax) in #print axioms admitted
/-- info: 'Solidity.Backend.AbiEntry.ValueCheckedBodies.UInt.selected' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms selected
/-- info: 'Solidity.Backend.AbiEntry.ValueCheckedBodies.UInt.gated' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms gated
/-- info: 'Solidity.Backend.AbiEntry.ValueCheckedBodies.UInt.executed' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms executed
/-- info: 'Solidity.Backend.AbiEntry.ValueCheckedBodies.UInt.early_rejection' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms early_rejection
/-- info: 'Solidity.Backend.AbiEntry.ValueCheckedBodies.UInt.decoded_body' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms decoded_body
/-- info: 'Solidity.Backend.AbiEntry.ValueCheckedBodies.UInt.certificate' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms certificate
end UInt

namespace Bool
def program (payable : Bool) (label : Fin W) (body : Prog C BoolBoundCtx Δ) : Prog C RouteCtx Δ :=
  ValueGateBody.guard payable (BoolBindingBody.program label body)

theorem admitted (payable : Bool) (label : Fin W) (body : Prog C BoolBoundCtx Δ)
    (outFrag : Frag Δ) (bodyCore : inFragP (Frag.init BoolBoundCtx) body=some outFrag) :
    inFragP (Frag.init RouteCtx) (program payable label body)=some outFrag :=
  ValueGateBody.admitted _ _ payable outFrag (BoolBindingBody.admitted label body outFrag bodyCore)

def compiled (base : Nat) (payable : Bool) (label : Fin W) (body : Prog C BoolBoundCtx Δ)
    (outFrag : Frag Δ) (bodyCore : inFragP (Frag.init BoolBoundCtx) body=some outFrag) :
    Compiler.Compilation base (Frag.init RouteCtx) (program payable label body) :=
  ValueGateBody.selectedWhole base _ (BoolBindingBody.program label body) payable outFrag
    (BoolBindingBody.admitted label body outFrag bodyCore)

theorem selected (base : Nat) (payable : Bool) (label : Fin W) (body : Prog C BoolBoundCtx Δ)
    (outFrag : Frag Δ) (bodyCore : inFragP (Frag.init BoolBoundCtx) body=some outFrag) :
    Compiler.compile base (Frag.init RouteCtx) (program payable label body)=
      some (compiled base payable label body outFrag bodyCore) :=
  ValueGateBody.whole_selected base _ (BoolBindingBody.program label body) payable outFrag
    (BoolBindingBody.admitted label body outFrag bodyCore)

theorem gated (base : Nat) (payable : Bool) (label : Fin W) (body : Prog C BoolBoundCtx Δ)
    (outFrag : Frag Δ) (bodyCore : inFragP (Frag.init BoolBoundCtx) body=some outFrag)
    (whole : Compiler.Compilation base (Frag.init RouteCtx) (program payable label body))
    (found : Compiler.compile base (Frag.init RouteCtx) (program payable label body)=some whole)
    (machine : Machine) :
    run whole.code machine=if payable || decide (machine.callvalue.val=0) then
      run (BoolBindingBody.selectedWhole base label body outFrag bodyCore).code machine else .revert :=
  ValueGateBody.executed base _ (BoolBindingBody.program label body) payable outFrag
    (BoolBindingBody.admitted label body outFrag bodyCore) whole
    (BoolBindingBody.selectedWhole base label body outFrag bodyCore) found
    (BoolBindingBody.whole_selected base label body outFrag bodyCore) machine

theorem executed (base : Nat) (payable : Bool) (label : Fin W) (body : Prog C BoolBoundCtx Δ)
    (outFrag : Frag Δ) (bodyCore : inFragP (Frag.init BoolBoundCtx) body=some outFrag)
    (whole : Compiler.Compilation base (Frag.init RouteCtx) (program payable label body))
    (back : Compiler.Compilation base (Frag.init BoolBoundCtx) body)
    (wholeFound : Compiler.compile base (Frag.init RouteCtx) (program payable label body)=some whole)
    (bodyFound : Compiler.compile base (Frag.init BoolBoundCtx) body=some back)
    (machine : Machine) (word size : Fin W) (initialWord : machine.mem base=.val word)
    (initialSize : machine.mem (base+1)=.val size) :
    run whole.code machine=if payable || decide (machine.callvalue.val=0) then
      if size.val<36 then .revert else if (Solidity.AbiEntry.Kind.bool).valid word.val then
        run back.code (boolBoundMachine base label word machine) else .revert else .revert := by
  rw [gated base payable label body outFrag bodyCore whole wholeFound machine]
  rw [BoolBindingBody.executed base label body outFrag bodyCore
    (BoolBindingBody.selectedWhole base label body outFrag bodyCore) back
    (BoolBindingBody.whole_selected base label body outFrag bodyCore) bodyFound machine word size initialWord initialSize]

theorem early_rejection (base : Nat) (payable : Bool) (label : Fin W) (body : Prog C BoolBoundCtx Δ)
    (outFrag : Frag Δ) (bodyCore : inFragP (Frag.init BoolBoundCtx) body=some outFrag)
    (whole : Compiler.Compilation base (Frag.init RouteCtx) (program payable label body))
    (found : Compiler.compile base (Frag.init RouteCtx) (program payable label body)=some whole)
    (machine : Machine) (blocked : (payable || decide (machine.callvalue.val=0))=false) :
    run whole.code machine=.revert := by
  rw [gated base payable label body outFrag bodyCore whole found machine]
  simp only [blocked,Bool.false_eq_true,if_false]

theorem decoded_body (base : Nat) (payable : Bool) (label : Fin W) (body : Prog C BoolBoundCtx Δ)
    (outFrag : Frag Δ) (bodyCore : inFragP (Frag.init BoolBoundCtx) body=some outFrag)
    (whole : Compiler.Compilation base (Frag.init RouteCtx) (program payable label body))
    (back : Compiler.Compilation base (Frag.init BoolBoundCtx) body)
    (wholeFound : Compiler.compile base (Frag.init RouteCtx) (program payable label body)=some whole)
    (bodyFound : Compiler.compile base (Frag.init BoolBoundCtx) body=some back)
    (input : Solidity.AbiEntry.Input) (fuel : Nat) (machine : Machine) (size : Fin W)
    (initialWord : machine.mem base=.val (rawArgumentWord input))
    (initialSize : machine.mem (base+1)=.val size) (represented : size.val=input.size)
    (allowed : (payable || decide (machine.callvalue.val=0))=true) (full : ¬input.size<36)
    (valid : (Solidity.AbiEntry.Kind.bool).valid (Solidity.AbiEntry.load input.data 4)=true) :
    ∃ value : Solidity.AbiEntry.Word .bool,
      Solidity.AbiEntry.entry input (fuel+2) (singleWordParams .bool)=.ok (.cons (.val (.word value)) .nil) ∧
      (boolBoundMachine base label (rawArgumentWord input) machine).mem
        (cellOf base (.here : Idx BoolBoundCtx (.val .bool)))=.val ⟨value.val,value.lt⟩ ∧
      run whole.code machine=run back.code (boolBoundMachine base label (rawArgumentWord input) machine) := by
  rcases BoolBindingBody.decoded_body base label body outFrag bodyCore
    (BoolBindingBody.selectedWhole base label body outFrag bodyCore) back
    (BoolBindingBody.whole_selected base label body outFrag bodyCore) bodyFound
    input fuel machine size initialWord initialSize represented full valid with ⟨value,semantic,cell,bodyRun⟩
  refine ⟨value,semantic,cell,?_⟩
  rw [gated base payable label body outFrag bodyCore whole wholeFound machine,if_pos allowed,bodyRun]

def certificate : Interface.ValueCheckedBoolBodyCertificate program where
  selected := fun base payable label body outFrag bodyCore =>
    ⟨compiled base payable label body outFrag bodyCore,BoolBindingBody.selectedBody base body outFrag bodyCore,
      selected base payable label body outFrag bodyCore,BoolBindingBody.body_selected base body outFrag bodyCore⟩
  executed := executed
  early_rejection := early_rejection

/-- info: 'Solidity.Backend.AbiEntry.ValueCheckedBodies.Bool.admitted' depends on axioms: [propext] -/
#guard_msgs (whitespace := lax) in #print axioms admitted
/-- info: 'Solidity.Backend.AbiEntry.ValueCheckedBodies.Bool.selected' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms selected
/-- info: 'Solidity.Backend.AbiEntry.ValueCheckedBodies.Bool.gated' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms gated
/-- info: 'Solidity.Backend.AbiEntry.ValueCheckedBodies.Bool.executed' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms executed
/-- info: 'Solidity.Backend.AbiEntry.ValueCheckedBodies.Bool.early_rejection' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms early_rejection
/-- info: 'Solidity.Backend.AbiEntry.ValueCheckedBodies.Bool.decoded_body' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms decoded_body
/-- info: 'Solidity.Backend.AbiEntry.ValueCheckedBodies.Bool.certificate' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms certificate
end Bool

end Solidity.Backend.AbiEntry.ValueCheckedBodies
