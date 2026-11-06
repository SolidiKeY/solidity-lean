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


/- Arithmetic right shift: negative floor behavior, sign fill and actual instruction composition. -/
def sarNested : Expr [] [] 0 1 :=
  .builtin (.pure .sar) (fun i =>
    if i = 0 then .literal (word 1)
    else .builtin (.pure .sub) (fun j =>
      if j = 0 then .literal (word 0) else .literal (word 3)))
def sarSupported : Policy.ExprP .A sarNested :=
  (Policy.expr_iff .A sarNested).mp rfl
def sarExpressionWitness : Nonempty (Expr [] [] 0 1) := ⟨sarNested⟩
def sarChain : Solidity.Evm.Out :=
  match Solidity.Evm.Instr.step .sub
      { seed with stack := .val (word 0) :: .val (word 3) :: tail } with
  | .ok afterSub 0 =>
    match Solidity.Evm.Instr.step (.push (.val (word 1))) afterSub with
    | .ok prepared 0 => Solidity.Evm.Instr.step .sar prepared
    | _ => .fault
  | _ => .fault

theorem sar_boundaries : (Solidity.Yul.Pure.eval .sar (Solidity.Yul.EvmSigned.args (Solidity.Yul.word (0)) (Solidity.Yul.word (2^255)))).val = 2^255 ∧
(Solidity.Yul.Pure.eval .sar (Solidity.Yul.EvmSigned.args (Solidity.Yul.word (1)) (Solidity.Yul.word (2^256-3)))).val = 2^256-2 ∧
(Solidity.Yul.Pure.eval .sar (Solidity.Yul.EvmSigned.args (Solidity.Yul.word (255)) (Solidity.Yul.word (2^255)))).val = 2^256-1 ∧
(Solidity.Yul.Pure.eval .sar (Solidity.Yul.EvmSigned.args (Solidity.Yul.word (256)) (Solidity.Yul.word (2^255)))).val = 2^256-1 ∧
(Solidity.Yul.Pure.eval .sar (Solidity.Yul.EvmSigned.args (Solidity.Yul.word (2^256-1)) (Solidity.Yul.word (2^256-3)))).val = 2^256-1 ∧
(Solidity.Yul.Pure.eval .sar (Solidity.Yul.EvmSigned.args (Solidity.Yul.word (255)) (Solidity.Yul.word (2^255-1)))).val = 0 ∧
(Solidity.Yul.Pure.eval .sar (Solidity.Yul.EvmSigned.args (Solidity.Yul.word (256)) (Solidity.Yul.word (257)))).val = 0 ∧
(Solidity.Yul.Pure.eval .sar (Solidity.Yul.EvmSigned.args (Solidity.Yul.word (1)) (Solidity.Yul.word (257)))).val = 128 ∧
(Solidity.Yul.Pure.eval .sar (Solidity.Yul.EvmSigned.args (Solidity.Yul.word (0)) (Solidity.Yul.word (0)))).val = 0 := by
  decide +kernel

theorem sar_nested : (Solidity.Yul.DirectWords.eval 2 Solidity.Yul.Checks.EvmBitwise.sarNested Solidity.Yul.Checks.EvmBitwise.sarSupported Solidity.Yul.Checks.EvmArithmetic.initial).isNone = true ∧
 (Solidity.Yul.DirectWords.eval 3 Solidity.Yul.Checks.EvmBitwise.sarNested Solidity.Yul.Checks.EvmBitwise.sarSupported Solidity.Yul.Checks.EvmArithmetic.initial).map (fun values => (values 0).val) = some (2^256-2) := by
  decide +kernel

theorem sar_composition : Solidity.Yul.Checks.EvmBitwise.sarChain = .ok { Solidity.Yul.Checks.EvmArithmetic.seed with stack := .val (Solidity.Yul.word (2^256-2)) :: Solidity.Yul.Checks.EvmArithmetic.tail } 0 := by
  rfl

theorem sar_negative : Solidity.Evm.Instr.step .sar { Solidity.Yul.Checks.EvmArithmetic.seed with stack := [] } = .fault ∧
 Solidity.Evm.Instr.step .sar { Solidity.Yul.Checks.EvmArithmetic.seed with stack := [.val (Solidity.Yul.word 1)] } = .fault ∧
 Solidity.Evm.Instr.step .sar { Solidity.Yul.Checks.EvmArithmetic.seed with stack := [.slot (.root 11),.val (Solidity.Yul.word 1)] } = .fault ∧
 Solidity.Evm.Instr.step .sar { Solidity.Yul.Checks.EvmArithmetic.seed with stack := [.val (Solidity.Yul.word 1),.slot (.root 11)] } = .fault ∧
 (Solidity.Yul.Pure.eval .sar (Solidity.Yul.EvmSigned.args (Solidity.Yul.word (1)) (Solidity.Yul.word (2^256-3)))).val ≠
 (Solidity.Yul.Pure.eval .sdiv (Solidity.Yul.EvmSigned.args (Solidity.Yul.word (2^256-3)) (Solidity.Yul.word 2))).val ∧
 (Solidity.Yul.Pure.eval .sar (Solidity.Yul.EvmSigned.args (Solidity.Yul.word (1)) (Solidity.Yul.word (2^256-3)))).val ≠ (Solidity.Yul.Pure.eval .sar (Solidity.Yul.EvmSigned.args (Solidity.Yul.word (2^256-3)) (Solidity.Yul.word (1)))).val := by
  repeat first | apply And.intro | rfl | decide +kernel

/-- info: 'Solidity.Yul.EvmBitwise.eval_sar' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Solidity.Yul.EvmBitwise.eval_sar

/-- info: 'Solidity.Yul.EvmBitwise.step_sar' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Solidity.Yul.EvmBitwise.step_sar

/-- info: 'Solidity.Yul.Checks.EvmBitwise.sar_boundaries' depends on axioms: [propext] -/
#guard_msgs (whitespace := lax) in
#print axioms Solidity.Yul.Checks.EvmBitwise.sar_boundaries

/-- info: 'Solidity.Yul.Checks.EvmBitwise.sar_nested' depends on axioms: [propext, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Solidity.Yul.Checks.EvmBitwise.sar_nested

/-- info: 'Solidity.Yul.Checks.EvmBitwise.sar_composition' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Solidity.Yul.Checks.EvmBitwise.sar_composition

/-- info: 'Solidity.Yul.Checks.EvmBitwise.sar_negative' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Solidity.Yul.Checks.EvmBitwise.sar_negative

/-- info: 'Solidity.Yul.EvmBitwise.step_sar_fault_iff' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Solidity.Yul.EvmBitwise.step_sar_fault_iff

end Solidity.Yul.Checks.EvmBitwise
