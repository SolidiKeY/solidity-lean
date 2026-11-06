import Solidity.Lowering.Readonly.SourcePayloadDecodeEffects
import Solidity.Lowering.Readonly.LocationEffects
import Solidity.Lowering.Readonly.CopyControls

/-! Finite actual helper observations, with populated pre-existing storage.
These do not constitute general ABI value correctness, admission or native
correspondence; failed helper runs retain their reached allocation state. -/
namespace Solidity.Lowering.Readonly.SourcePayloadControls
open Solidity.Source Solidity.Source.SemanticsExamples
open SourceHistory
namespace C
abbrev E := CopyControls.E
abbrev frame := CopyControls.frame
abbrev checkpoint := CopyControls.checkpoint
end C
def dynamicData := wordBytes (word 32) ++ wordBytes (word 2) ++ [7,9]
def partialData := wordBytes (word 64) ++ wordBytes (word 2) ++ wordBytes (word 2) ++ [7,9]
def boolArrayData (b : Nat) := wordBytes (word 32) ++ wordBytes (word 1) ++ wordBytes (toWord b)
def decoded := (decodeArg dynamicData 0 (.bytes .memory) : EM C.E [] _).run (L0 C.E, C.checkpoint)
def partialDecode := (decodeArgs partialData [.bytes .memory, .bool] 0 : EM C.E [] _).run (L0 C.E, C.checkpoint)
def arrayDecode (b : Nat) := (decodeArg (boolArrayData b) 0 (.array .memory .bool none) : EM C.E [] _).run (L0 C.E, C.checkpoint)
def arrayRead := (memElem 0 0 .bool : EM C.E [] _).run (L0 C.E, (arrayDecode 1).2.2)
def encoded := (encodeOne {C.frame with static := true} 12 false (RVal.val CopyControls.sourceRef) : EM C.E [] _).run (L0 C.E, C.checkpoint)
def packed := (encodeVals {C.frame with static := true} 0 true
  (RVals.cons (.val (.bool true)) (.cons (.val (.bool false)) .nil)) : EM C.E [] _).run (L0 C.E, C.checkpoint)
def refusedEncode := (encodeOne {C.frame with static := true} 0 false (RVal.tuple .nil) : EM C.E [] _).run (L0 C.E, C.checkpoint)
def returnPhase (rs : List STy) (out : Solidity.Roadmap.Outcome) :=
  (extReturn rs out : EM C.E [] _).run (L0 C.E, C.checkpoint)
def shortABI := (abiDecodeData [1] [uint] : EM C.E [] _).run (L0 C.E, C.checkpoint)

theorem observations : Solidity.Lowering.Readonly.SourcePayloadControls.decoded.1 = .ok (.memRef (by rfl) 0) ∧
 Solidity.Lowering.Readonly.SourcePayloadControls.decoded.2.2.heap.get 0 = some ⟨.bytes .memory, .bytes [7,9]⟩ ∧
 Solidity.Lowering.Readonly.SourcePayloadControls.decoded.2.2.ex = Solidity.Lowering.Readonly.SourcePayloadControls.C.checkpoint.ex ∧
 Solidity.Lowering.Readonly.SourcePayloadControls.partialDecode.1 = .error (.revert []) ∧
 Solidity.Lowering.Readonly.SourcePayloadControls.partialDecode.2.2.heap.get 0 = some ⟨.bytes .memory, .bytes [7,9]⟩ ∧
 Solidity.Lowering.Readonly.SourcePayloadControls.partialDecode.2.2.ex = Solidity.Lowering.Readonly.SourcePayloadControls.C.checkpoint.ex ∧
 (Solidity.Lowering.Readonly.SourcePayloadControls.arrayDecode 1).1 = .ok (.memRef (by rfl) 0) ∧
 Solidity.Lowering.Readonly.SourcePayloadControls.arrayRead.1 = .ok (.bool true) ∧
 (Solidity.Lowering.Readonly.SourcePayloadControls.arrayDecode 2).1 = .error (.revert []) ∧
 (Solidity.Lowering.Readonly.SourcePayloadControls.arrayDecode 2).2.2.heap.next = 0 ∧
 Solidity.Lowering.Readonly.SourcePayloadControls.encoded.1 = .ok (true, [7,9]) ∧
 Solidity.Lowering.Readonly.SourcePayloadControls.encoded.2.2.ex = Solidity.Lowering.Readonly.SourcePayloadControls.C.checkpoint.ex ∧
 Solidity.Lowering.Readonly.SourcePayloadControls.packed.1 = .ok [1,0] ∧
 Solidity.Lowering.Readonly.SourcePayloadControls.refusedEncode.1 = .error (.stuck "not ABI-encodable") ∧
 (Solidity.Lowering.Readonly.SourcePayloadControls.returnPhase [Solidity.Source.SemanticsExamples.uint] (.success (Solidity.Source.wordBytes (Solidity.Source.SemanticsExamples.word 7)))).1 = .ok (.val (.int 7 (by decide))) ∧
 (Solidity.Lowering.Readonly.SourcePayloadControls.returnPhase [Solidity.Source.SemanticsExamples.uint] (.success [1])).1 = .error (.revert []) ∧
 (Solidity.Lowering.Readonly.SourcePayloadControls.returnPhase [Solidity.Source.SemanticsExamples.uint] (.revert [9])).1 = .error (.revert [9]) ∧
 (Solidity.Lowering.Readonly.SourcePayloadControls.returnPhase [] (.success [1])).1 = .ok (.tuple .nil) ∧
 Solidity.Lowering.Readonly.SourcePayloadControls.shortABI.1 = .error (.revert []) := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;> rfl

end Solidity.Lowering.Readonly.SourcePayloadControls
