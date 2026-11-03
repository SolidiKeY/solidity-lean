import Solidity.Yul.EvmBitwise
import Solidity.Yul.Checks.EvmArithmetic

namespace Solidity.Yul.Checks.EvmBitwise
open Solidity.Yul.Checks.EvmArithmetic (seed tail initial)

def nested : Expr [] [] 0 1 :=
  .builtin (.pure .and) (fun i =>
    if i = 0 then .builtin (.pure .shr) (fun j =>
      if j = 0 then .literal (word 8)
      else .builtin (.pure .shl) (fun k =>
        if k = 0 then .literal (word 8) else .literal (word (2^255+257))))
    else .literal (word 255))
def supported : Policy.ExprP .A nested :=
  (Policy.expr_iff .A nested).mp rfl
def expressionWitness : Nonempty (Expr [] [] 0 1) := ⟨nested⟩

def chain : Solidity.Evm.Out :=
  match Solidity.Evm.Instr.step .shl
      { seed with stack := .val (word 8) :: .val (word (2^255+257)) :: .val (word 255) :: tail } with
  | .ok a 0 => match Solidity.Evm.Instr.step (.push (.val (word 8))) a with
    | .ok b 0 => match Solidity.Evm.Instr.step .shr b with
      | .ok c 0 => Solidity.Evm.Instr.step .and c
      | _ => .fault
    | _ => .fault
  | _ => .fault

theorem boundaries : (
(Solidity.Yul.Pure.eval .and (Solidity.Yul.EvmSigned.args (Solidity.Yul.word (2^256-1)) (Solidity.Yul.word (257)))).val = 257 ∧
(Solidity.Yul.Pure.eval .or (Solidity.Yul.EvmSigned.args (Solidity.Yul.word (256)) (Solidity.Yul.word (1)))).val = 257 ∧
(Solidity.Yul.Pure.eval .xor (Solidity.Yul.EvmSigned.args (Solidity.Yul.word (257)) (Solidity.Yul.word (1)))).val = 256 ∧
(Solidity.Yul.Pure.eval .not (fun _ => Solidity.Yul.word (0))).val = 2^256-1 ∧
(Solidity.Yul.Pure.eval .not (fun _ => Solidity.Yul.word (2^256-1))).val = 0 ∧
(Solidity.Yul.Pure.eval .lt (Solidity.Yul.EvmSigned.args (Solidity.Yul.word (257)) (Solidity.Yul.word (256)))).val = 0 ∧
(Solidity.Yul.Pure.eval .gt (Solidity.Yul.EvmSigned.args (Solidity.Yul.word (257)) (Solidity.Yul.word (256)))).val = 1 ∧
(Solidity.Yul.Pure.eval .eq (Solidity.Yul.EvmSigned.args (Solidity.Yul.word (257)) (Solidity.Yul.word (1)))).val = 0 ∧
(Solidity.Yul.Pure.eval .eq (Solidity.Yul.EvmSigned.args (Solidity.Yul.word (2^256-1)) (Solidity.Yul.word (2^256-1)))).val = 1 ∧
(Solidity.Yul.Pure.eval .iszero (fun _ => Solidity.Yul.word (0))).val = 1 ∧
(Solidity.Yul.Pure.eval .iszero (fun _ => Solidity.Yul.word (257))).val = 0 ∧
(Solidity.Yul.Pure.eval .shl (Solidity.Yul.EvmSigned.args (Solidity.Yul.word (0)) (Solidity.Yul.word (257)))).val = 257 ∧
(Solidity.Yul.Pure.eval .shl (Solidity.Yul.EvmSigned.args (Solidity.Yul.word (255)) (Solidity.Yul.word (1)))).val = 2^255 ∧
(Solidity.Yul.Pure.eval .shl (Solidity.Yul.EvmSigned.args (Solidity.Yul.word (256)) (Solidity.Yul.word (2^256-1)))).val = 0 ∧
(Solidity.Yul.Pure.eval .shl (Solidity.Yul.EvmSigned.args (Solidity.Yul.word (257)) (Solidity.Yul.word (1)))).val = 0 ∧
(Solidity.Yul.Pure.eval .shl (Solidity.Yul.EvmSigned.args (Solidity.Yul.word (2^256-1)) (Solidity.Yul.word (1)))).val = 0 ∧
(Solidity.Yul.Pure.eval .shr (Solidity.Yul.EvmSigned.args (Solidity.Yul.word (255)) (Solidity.Yul.word (2^256-1)))).val = 1 ∧
(Solidity.Yul.Pure.eval .shr (Solidity.Yul.EvmSigned.args (Solidity.Yul.word (256)) (Solidity.Yul.word (2^256-1)))).val = 0 ∧
(Solidity.Yul.Pure.eval .shr (Solidity.Yul.EvmSigned.args (Solidity.Yul.word (2^256-1)) (Solidity.Yul.word (2^256-1)))).val = 0 ∧
(Solidity.Yul.Pure.eval .exp (Solidity.Yul.EvmSigned.args (Solidity.Yul.word (0)) (Solidity.Yul.word (0)))).val = 1 ∧
(Solidity.Yul.Pure.eval .exp (Solidity.Yul.EvmSigned.args (Solidity.Yul.word (2)) (Solidity.Yul.word (256)))).val = 0 ∧
(Solidity.Yul.Pure.eval .exp (Solidity.Yul.EvmSigned.args (Solidity.Yul.word (2^255+1)) (Solidity.Yul.word (2)))).val = 1 ∧
(Solidity.Yul.DirectWords.eval 3 Solidity.Yul.Checks.EvmBitwise.nested Solidity.Yul.Checks.EvmBitwise.supported Solidity.Yul.Checks.EvmArithmetic.initial).isNone = true ∧
((Solidity.Yul.DirectWords.eval 4 Solidity.Yul.Checks.EvmBitwise.nested Solidity.Yul.Checks.EvmBitwise.supported Solidity.Yul.Checks.EvmArithmetic.initial).map (fun values => (values 0).val)) = some 1
) := by
  decide

theorem composition : Solidity.Yul.Checks.EvmBitwise.chain =
 .ok { Solidity.Yul.Checks.EvmArithmetic.seed with stack := .val (Solidity.Yul.word 1) :: Solidity.Yul.Checks.EvmArithmetic.tail } 0 := by
  rfl

theorem negative : Solidity.Evm.Instr.step .shl { Solidity.Yul.Checks.EvmArithmetic.seed with stack := [.slot (.root 11), .val (Solidity.Yul.word 8)] } = .fault ∧
 Solidity.Evm.Instr.step .not { Solidity.Yul.Checks.EvmArithmetic.seed with stack := [.slot (.root 11)] } = .fault ∧
 Solidity.Evm.Instr.step .eq { Solidity.Yul.Checks.EvmArithmetic.seed with stack := [.val (Solidity.Yul.word 8)] } = .fault ∧
 (Solidity.Yul.Pure.eval .shl (Solidity.Yul.EvmSigned.args (Solidity.Yul.word 1) (Solidity.Yul.word 8))).val ≠
 (Solidity.Yul.Pure.eval .shl (Solidity.Yul.EvmSigned.args (Solidity.Yul.word 8) (Solidity.Yul.word 1))).val ∧
 (Solidity.Yul.Pure.eval .shr (Solidity.Yul.EvmSigned.args (Solidity.Yul.word 255) (Solidity.Yul.word (2^256-1)))).val ≠
 (Solidity.Yul.Pure.eval .sar (Solidity.Yul.EvmSigned.args (Solidity.Yul.word 255) (Solidity.Yul.word (2^256-1)))).val := by
  exact ⟨rfl,rfl,rfl,by decide,by decide +kernel⟩

#print axioms Solidity.Yul.EvmBitwise.step_and
#print axioms Solidity.Yul.EvmBitwise.step_or
#print axioms Solidity.Yul.EvmBitwise.step_xor
#print axioms Solidity.Yul.EvmBitwise.step_not
#print axioms Solidity.Yul.EvmBitwise.step_lt
#print axioms Solidity.Yul.EvmBitwise.step_gt
#print axioms Solidity.Yul.EvmBitwise.step_eq
#print axioms Solidity.Yul.EvmBitwise.step_iszero
#print axioms Solidity.Yul.EvmBitwise.step_shl
#print axioms Solidity.Yul.EvmBitwise.step_shr
#print axioms Solidity.Yul.EvmBitwise.step_exp
#print axioms boundaries
#print axioms composition
#print axioms negative

end Solidity.Yul.Checks.EvmBitwise
