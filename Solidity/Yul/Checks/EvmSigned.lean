import Solidity.Yul.EvmSigned
import Solidity.Yul.DirectWords

namespace Solidity.Yul.Checks.EvmSigned
def seed : Solidity.Evm.Machine :=
  { Solidity.Evm.Machine.init (fun _ => 17) (word 9) with
    mem := fun _ => .val (word 88), callvalue := word 5 }
def tail : List Solidity.Evm.Word := [.slot (.root 11),.val (word 257)]
def chain : Solidity.Evm.Out :=
  match Solidity.Evm.Instr.step .sdiv
    { seed with stack := .val (word (2^256-7)) :: .val (word 3) :: .val (word 0) :: tail } with
  | .ok next 0 => Solidity.Evm.Instr.step .slt next
  | _ => .fault

def nested : Expr [] [] 0 1 :=
  .builtin (.pure .slt) (fun i =>
    if i = 0 then .builtin (.pure .sdiv) (fun j =>
      if j = 0 then .literal (word (2^256-7)) else .literal (word 3))
    else .literal (word 0))
def supported : Policy.ExprP .A nested := by
  apply (Policy.expr_iff .A _).mp
  rfl
def initial : WordState [] 0 :=
  ⟨Fin.elim0,fun cell => Fin.elim0 cell.slot⟩
def syntaxWitness : Nonempty (Expr [] [] 0 1) := ⟨nested⟩
def machineWitness : Nonempty Solidity.Evm.Machine := ⟨seed⟩

theorem boundaries : (
 (Solidity.Yul.Pure.eval .sdiv (Solidity.Yul.EvmSigned.args (Solidity.Yul.word (2^255)) (Solidity.Yul.word (2^256-1)))).val = 2^255 ∧
 (Solidity.Yul.Pure.eval .sdiv (Solidity.Yul.EvmSigned.args (Solidity.Yul.word (2^256-7)) (Solidity.Yul.word 3))).val = 2^256-2 ∧
 (Solidity.Yul.Pure.eval .smod (Solidity.Yul.EvmSigned.args (Solidity.Yul.word (2^256-7)) (Solidity.Yul.word 3))).val = 2^256-1 ∧
 (Solidity.Yul.Pure.eval .sdiv (Solidity.Yul.EvmSigned.args (Solidity.Yul.word 257) (Solidity.Yul.word 1))).val = 257 ∧
 (Solidity.Yul.Pure.eval .sdiv (Solidity.Yul.EvmSigned.args (Solidity.Yul.word (2^255)) (Solidity.Yul.word 0))).val = 0 ∧
 (Solidity.Yul.Pure.eval .smod (Solidity.Yul.EvmSigned.args (Solidity.Yul.word (2^256-1)) (Solidity.Yul.word 0))).val = 0 ∧
 (Solidity.Yul.Pure.eval .slt (Solidity.Yul.EvmSigned.args (Solidity.Yul.word (2^255)) (Solidity.Yul.word (2^255-1)))).val = 1 ∧
 (Solidity.Yul.Pure.eval .sgt (Solidity.Yul.EvmSigned.args (Solidity.Yul.word (2^255)) (Solidity.Yul.word (2^255-1)))).val = 0 ∧
 (Solidity.Yul.DirectWords.eval 2 Solidity.Yul.Checks.EvmSigned.nested Solidity.Yul.Checks.EvmSigned.supported Solidity.Yul.Checks.EvmSigned.initial).isNone = true ∧
 ((Solidity.Yul.DirectWords.eval 3 Solidity.Yul.Checks.EvmSigned.nested Solidity.Yul.Checks.EvmSigned.supported Solidity.Yul.Checks.EvmSigned.initial).map (fun values => (values 0).val)) = some 1 ∧
 Solidity.Yul.iword (-(Solidity.Evm.W : Int)-1) ≠ Solidity.Evm.sword (-(Solidity.Evm.W : Int)-1)
) := by
  decide +kernel

theorem composition : Solidity.Yul.Checks.EvmSigned.chain = .ok { Solidity.Yul.Checks.EvmSigned.seed with stack := .val (Solidity.Yul.word 1) :: Solidity.Yul.Checks.EvmSigned.tail } 0 := by
  rfl

theorem malformed_stack : Solidity.Evm.Instr.step .sdiv { Solidity.Yul.Checks.EvmSigned.seed with stack := [.val (Solidity.Yul.word 3)] } = .fault ∧
Solidity.Evm.Instr.step .smod { Solidity.Yul.Checks.EvmSigned.seed with stack := [.slot (.root 11),.val (Solidity.Yul.word 3)] } = .fault := by
  exact ⟨rfl,rfl⟩
#print axioms Solidity.Yul.EvmSigned.iword_eq_sword
#print axioms Solidity.Yul.EvmSigned.signed_eq_sgn
#print axioms Solidity.Yul.EvmSigned.eval_sdiv
#print axioms Solidity.Yul.EvmSigned.eval_smod
#print axioms Solidity.Yul.EvmSigned.eval_slt
#print axioms Solidity.Yul.EvmSigned.eval_sgt
#print axioms Solidity.Yul.EvmSigned.step_sdiv
#print axioms Solidity.Yul.EvmSigned.step_smod
#print axioms Solidity.Yul.EvmSigned.step_slt
#print axioms Solidity.Yul.EvmSigned.step_sgt
#print axioms boundaries
#print axioms composition
#print axioms malformed_stack

end Solidity.Yul.Checks.EvmSigned
