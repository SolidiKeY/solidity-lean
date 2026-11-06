import Solidity.Yul.EvmArithmetic
import Solidity.Yul.DirectWords

namespace Solidity.Yul.Checks.EvmArithmetic

def seed : Solidity.Evm.Machine :=
  { Solidity.Evm.Machine.init (fun _ => 17) (word 9) with
    mem := fun _ => .val (word 88), callvalue := word 5 }
def tail : List Solidity.Evm.Word := [.slot (.root 11), .val (word 257)]
def nested : Expr [] [] 0 1 :=
  .builtin (.pure .div) (fun i =>
    if i = 0 then .builtin (.pure .mul) (fun j =>
      if j = 0 then .literal (word (2^255+1)) else .literal (word 2))
    else .literal (word 2))
def supported : Policy.ExprP .A nested :=
  (Policy.expr_iff .A nested).mp rfl
def initial : WordState [] 0 :=
  ⟨Fin.elim0,fun cell => Fin.elim0 cell.slot⟩
def expressionWitness : Nonempty (Expr [] [] 0 1) := ⟨nested⟩

theorem boundaries : (
(Solidity.Yul.Pure.eval .add (Solidity.Yul.EvmSigned.args (Solidity.Yul.word (2^256-1)) (Solidity.Yul.word 1))).val = 0 ∧
(Solidity.Yul.Pure.eval .sub (Solidity.Yul.EvmSigned.args (Solidity.Yul.word 0) (Solidity.Yul.word 1))).val = 2^256-1 ∧
(Solidity.Yul.Pure.eval .mul (Solidity.Yul.EvmSigned.args (Solidity.Yul.word (2^255+1)) (Solidity.Yul.word 2))).val = 2 ∧
(Solidity.Yul.Pure.eval .div (Solidity.Yul.EvmSigned.args (Solidity.Yul.word (2^256-1)) (Solidity.Yul.word 0))).val = 0 ∧
(Solidity.Yul.Pure.eval .mod (Solidity.Yul.EvmSigned.args (Solidity.Yul.word (2^256-1)) (Solidity.Yul.word 0))).val = 0 ∧
(Solidity.Yul.Pure.eval .div (Solidity.Yul.EvmSigned.args (Solidity.Yul.word 257) (Solidity.Yul.word 1))).val = 257 ∧
(Solidity.Yul.Pure.eval .mod (Solidity.Yul.EvmSigned.args (Solidity.Yul.word (2^256-1)) (Solidity.Yul.word 256))).val = 255 ∧
(Solidity.Yul.DirectWords.eval 2 Solidity.Yul.Checks.EvmArithmetic.nested Solidity.Yul.Checks.EvmArithmetic.supported Solidity.Yul.Checks.EvmArithmetic.initial).isNone = true ∧
((Solidity.Yul.DirectWords.eval 3 Solidity.Yul.Checks.EvmArithmetic.nested Solidity.Yul.Checks.EvmArithmetic.supported Solidity.Yul.Checks.EvmArithmetic.initial).map (fun values => (values 0).val)) = some 1 ∧
((2^255+1 : Nat)*2)/2 ≠ 1
) := by
  decide

theorem composition_control : Solidity.Yul.EvmArithmetic.mulDiv Solidity.Yul.Checks.EvmArithmetic.seed (Solidity.Yul.word (2^255+1)) (Solidity.Yul.word 2) (Solidity.Yul.word 2) Solidity.Yul.Checks.EvmArithmetic.tail =
 .ok { Solidity.Yul.Checks.EvmArithmetic.seed with stack := .val (Solidity.Yul.word 1) :: Solidity.Yul.Checks.EvmArithmetic.tail } 0 := by
  rfl

theorem malformed : Solidity.Evm.Instr.step .div { Solidity.Yul.Checks.EvmArithmetic.seed with stack := [.val (Solidity.Yul.word 7)] } = .fault ∧
 Solidity.Evm.Instr.step .mod { Solidity.Yul.Checks.EvmArithmetic.seed with stack := [.slot (.root 11), .val (Solidity.Yul.word 3)] } = .fault ∧
 Solidity.Evm.Instr.step .sub { Solidity.Yul.Checks.EvmArithmetic.seed with stack := [.val (Solidity.Yul.word 3), .slot (.root 11)] } = .fault ∧
 (Solidity.Yul.Pure.eval .div (Solidity.Yul.EvmSigned.args (Solidity.Yul.word 7) (Solidity.Yul.word 3))).val ≠
 (Solidity.Yul.Pure.eval .div (Solidity.Yul.EvmSigned.args (Solidity.Yul.word 3) (Solidity.Yul.word 7))).val := by
  exact ⟨rfl,rfl,rfl,by decide⟩

#print axioms Solidity.Yul.EvmArithmetic.step_add
#print axioms Solidity.Yul.EvmArithmetic.step_sub
#print axioms Solidity.Yul.EvmArithmetic.step_mul
#print axioms Solidity.Yul.EvmArithmetic.step_div
#print axioms Solidity.Yul.EvmArithmetic.step_mod
#print axioms Solidity.Yul.EvmArithmetic.mulDiv_agrees
#print axioms boundaries
#print axioms composition_control
#print axioms malformed

end Solidity.Yul.Checks.EvmArithmetic
