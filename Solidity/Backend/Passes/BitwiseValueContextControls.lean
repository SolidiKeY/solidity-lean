import Solidity.Backend.Passes.BitwiseValueContext
import Solidity.Backend.MemoryOps.StructDefaults.WordControls

/-! Inhabited typed local inputs, complete frame observations and refusals. -/
namespace Solidity.Backend.Passes.BitwiseValueContextControls
open Evm Evm.Memory
open Backend.PrimitivePackets.Bitwise
open Backend.MemoryOps.StructDefaults.WordControls (C initial bases machine initial_repr)
def state : State C context :=
  (initial.push (t := .val .uint) (indexValue (wmod 3))).push
    (t := .val .uint) (indexValue (wmod 5))
def input : Machine := writeMachine (writeMachine machine 1 w[3]) 2 w[5]
theorem represented : StateRepr 1 1 64 (Frag.init context) state bases input := by
  exact (initial_repr.1.consVal (indexValue (wmod 3)) w[3]
    ⟨wmod 3,rfl,rfl⟩ (by decide)).consVal (indexValue (wmod 5)) w[5]
      ⟨wmod 5,rfl,rfl⟩ (by decide)

theorem inhabited (op : Source.BinOp) (supported : Supported op) : type_of%
    (BitwiseValueContext.application op supported ⟨0,by decide⟩ 5 3
      (by decide) (by decide) represented (by rfl) (by rfl)) :=
  BitwiseValueContext.application op supported ⟨0,by decide⟩ 5 3
    (by decide) (by decide) represented (by rfl) (by rfl)

def observe (out : Evm.Out) : Option (List Word × List Word) :=
  match out with
  | .ok m _ => some ([2,1,0,63,128].map m.mem,m.stack)
  | _ => none

theorem and_vector (tail : List Word) :
    observe (run (code 1 .bitAnd) {input with stack := tail}) =
      some ([w[5],w[3],w[128],w[99],w[0]],w[1]::tail) := by
  rw [execute 1 .bitAnd (Or.inl rfl) ⟨0,by decide⟩ 5 3
    (by decide) (by decide) _ (by rfl) (by rfl)]
  rfl

theorem or_vector : observe (run (code 1 .bitOr) input) =
    some ([w[5],w[3],w[128],w[99],w[0]],[w[7],w[77]]) := by decide +kernel

theorem xor_vector : observe (run (code 1 .bitXor) input) =
    some ([w[5],w[3],w[128],w[99],w[0]],[w[6],w[77]]) := by decide +kernel

/-- The actual Source expression keeps both pipeline and horizon parameters.
Its result word is the one reflected by the typed receiving-context theorem. -/
theorem source_result {E : Source.Env} (G : Source.Glob E) (F : Source.Fr)
    (fuel : Nat) (s : Source.St E) (op : Source.BinOp) (supported : Supported op) : type_of%
    (evalE_operand G F fuel ⟨0,by decide⟩ op supported 5 3 (by decide) (by decide) s) :=
  evalE_operand G F fuel ⟨0,by decide⟩ op supported 5 3 (by decide) (by decide) s

theorem wrong_value : observe (run (code 1 .bitAnd) input) ≠
    some ([w[5],w[3],w[128],w[99],w[0]],[w[7],w[77]]) := by decide +kernel

theorem corrupted_tail : observe (run (code 1 .bitAnd) input) ≠
    some ([w[5],w[3],w[128],w[99],w[0]],[w[1],w[88]]) := by decide +kernel

theorem dirty_refusal : ¬ 256 < 2 ^ (unsigned ⟨0,by decide⟩).bits := by decide

theorem signed_acceptance :
    (compileVal 1 (Frag.init _) (signedExpression C .bitAnd)).isSome = true :=
  signed_accepted C 1 .bitAnd (Or.inl rfl)

/-- info: 'Solidity.Backend.Passes.BitwiseValueContextControls.source_result' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms source_result
/-- info: 'Solidity.Backend.Passes.BitwiseValueContextControls.represented' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms represented
/-- info: 'Solidity.Backend.Passes.BitwiseValueContextControls.inhabited' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms inhabited
/-- info: 'Solidity.Backend.Passes.BitwiseValueContextControls.and_vector' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms and_vector
/-- info: 'Solidity.Backend.Passes.BitwiseValueContextControls.or_vector' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms or_vector
/-- info: 'Solidity.Backend.Passes.BitwiseValueContextControls.xor_vector' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms xor_vector
/-- info: 'Solidity.Backend.Passes.BitwiseValueContextControls.wrong_value' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms wrong_value
/-- info: 'Solidity.Backend.Passes.BitwiseValueContextControls.corrupted_tail' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms corrupted_tail
/-- info: 'Solidity.Backend.Passes.BitwiseValueContextControls.dirty_refusal' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms dirty_refusal
/-- info: 'Solidity.Backend.Passes.BitwiseValueContextControls.signed_acceptance' depends on axioms: [propext, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms signed_acceptance
end Solidity.Backend.Passes.BitwiseValueContextControls
