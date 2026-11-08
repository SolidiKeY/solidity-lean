import Solidity.Backend.AbiEntry.WordGateInterface
import Solidity.Backend.AbiEntry.BytesGate

/-! Unified actual compiler validation reuses the checked primitive families.
No replacement interpreter, decoder or new word-kind classification is added. -/
namespace Solidity.Backend.AbiEntry.WordGate
open Solidity.Evm
open Interface (RouteCtx wordGateOutcome)

def program (C : Contract) : Solidity.AbiEntry.Kind → Fin W → Prog C RouteCtx RouteCtx
  | .uint bits,label => UnsignedGate.program C (2^bits) label
  | .int bits,label => SignedGate.program C bits label
  | .bool,label => UnsignedGate.program C 2 label
  | .fixedBytes size,label => BytesGate.program C size label
  | .enumBelow members,label => UnsignedGate.program C members label

theorem admitted (C : Contract) (kind : Solidity.AbiEntry.Kind) (label : Fin W) :
    inFragP (Frag.init RouteCtx) (program C kind label)=some (Frag.init RouteCtx) := by
  cases kind with
  | uint bits => exact UnsignedGate.admitted C _ label
  | int bits => exact SignedGate.admitted C _ label
  | bool => exact UnsignedGate.admitted C _ label
  | fixedBytes size => exact BytesGate.admitted C _ label
  | enumBelow members => exact UnsignedGate.admitted C _ label

def compiled (C : Contract) (base : Nat) (kind : Solidity.AbiEntry.Kind) (label : Fin W) :
    Compiler.Compilation base (Frag.init RouteCtx) (program C kind label) :=
  .core (Frag.init RouteCtx) (admitted C kind label)
theorem selected (C : Contract) (base : Nat) (kind : Solidity.AbiEntry.Kind) (label : Fin W) :
    Compiler.compile base (Frag.init RouteCtx) (program C kind label)=some (compiled C base kind label) :=
  ValueGateBody.body_selected base _ _ _ (admitted C kind label)

theorem run_program (C : Contract) (base : Nat) (kind : Solidity.AbiEntry.Kind) (label : Fin W)
    (machine : Machine) (word : Fin W) (initial : machine.mem base=.val word) :
    run (compileProg base (program C kind label)) machine=wordGateOutcome base kind label word machine := by
  cases kind with
  | uint bits =>
    simpa only [program,wordGateOutcome,Interface.unsignedGateOutcome,Solidity.AbiEntry.Kind.valid,decide_eq_true_eq]
      using UnsignedGate.run_program C base (2^bits) label machine word initial
  | int bits => exact SignedGate.run_program C base bits label machine word initial
  | bool =>
    simpa only [program,wordGateOutcome,Interface.unsignedGateOutcome,Solidity.AbiEntry.Kind.valid,decide_eq_true_eq]
      using UnsignedGate.run_program C base 2 label machine word initial
  | fixedBytes size => exact BytesGate.run_program C base size label machine word initial
  | enumBelow members =>
    simpa only [program,wordGateOutcome,Interface.unsignedGateOutcome,Solidity.AbiEntry.Kind.valid,decide_eq_true_eq]
      using UnsignedGate.run_program C base members label machine word initial

theorem executed (C : Contract) (base : Nat) (kind : Solidity.AbiEntry.Kind) (label : Fin W)
    (result : Compiler.Compilation base (Frag.init RouteCtx) (program C kind label))
    (found : Compiler.compile base (Frag.init RouteCtx) (program C kind label)=some result)
    (machine : Machine) (word : Fin W) (initial : machine.mem base=.val word) :
    run result.code machine=wordGateOutcome base kind label word machine := by
  have same : result=compiled C base kind label := Option.some.inj (found.symm.trans (selected C base kind label))
  rw [same]
  exact run_program C base kind label machine word initial

theorem rejected_iff (C : Contract) (base : Nat) (kind : Solidity.AbiEntry.Kind) (label : Fin W)
    (result : Compiler.Compilation base (Frag.init RouteCtx) (program C kind label))
    (found : Compiler.compile base (Frag.init RouteCtx) (program C kind label)=some result)
    (machine : Machine) (word : Fin W) (initial : machine.mem base=.val word) :
    (run result.code machine=.revert ↔ kind.valid word.val=false) := by
  rw [executed C base kind label result found machine word initial]
  cases valid : kind.valid word.val with
  | false => simp only [wordGateOutcome,valid,Bool.false_eq_true,if_false]
  | true =>
    simp only [wordGateOutcome,valid,if_true]
    constructor <;> intro impossible <;> cases impossible

theorem correspondence (C : Contract) (base : Nat) (kind : Solidity.AbiEntry.Kind) (label : Fin W)
    (result : Compiler.Compilation base (Frag.init RouteCtx) (program C kind label))
    (found : Compiler.compile base (Frag.init RouteCtx) (program C kind label)=some result)
    (machine : Machine) (word : Fin W) (initial : machine.mem base=.val word)
    (input : Solidity.AbiEntry.Input) (offset fuel len : Nat)
    (loaded : word.val=Solidity.AbiEntry.load input.data offset) :
    (run result.code machine=.revert ↔
      Solidity.AbiEntry.cval input (fuel+1) (.word kind) offset len=.error .revert) := by
  rw [rejected_iff C base kind label result found machine word initial,loaded]
  cases valid : kind.valid (Solidity.AbiEntry.load input.data offset) with
  | false => simp only [Solidity.AbiEntry.cval,valid,Bool.false_eq_true,dite_false]
  | true =>
    simp only [Solidity.AbiEntry.cval,valid,dite_true]
    constructor <;> intro impossible <;> cases impossible

def certificate : Interface.WordGateCertificate program where
  selected := fun C base kind label => ⟨compiled C base kind label,selected C base kind label⟩
  executed := executed
/-- info: 'Solidity.Backend.AbiEntry.WordGate.admitted' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms admitted
/-- info: 'Solidity.Backend.AbiEntry.WordGate.selected' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms selected
/-- info: 'Solidity.Backend.AbiEntry.WordGate.run_program' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms run_program
/-- info: 'Solidity.Backend.AbiEntry.WordGate.executed' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms executed
/-- info: 'Solidity.Backend.AbiEntry.WordGate.rejected_iff' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms rejected_iff
/-- info: 'Solidity.Backend.AbiEntry.WordGate.correspondence' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms correspondence
/-- info: 'Solidity.Backend.AbiEntry.WordGate.certificate' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms certificate
end Solidity.Backend.AbiEntry.WordGate
