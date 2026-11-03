import Solidity.Evm.Machine

/-! Sound data equality for flat lists of EXISTING instructions. This is
not an AST, evaluator, target admission change or trust shortcut. Loop nodes
are conservatively not recognized even against themselves, so it cannot
certify the recursive images (they contain `.loop`); no module uses it yet. -/
namespace Solidity.Backend.InternalFlow.RuntimeFrame.CodeEquality
open Evm

def instruction : Instr → Instr → Bool
  | .push x,right => match right with | .push y => decide (x = y) | _ => false
  | .dup x,right => match right with | .dup y => decide (x = y) | _ => false
  | .swap x,right => match right with | .swap y => decide (x = y) | _ => false
  | .mload x,right => match right with | .mload y => decide (x = y) | _ => false
  | .mstore x,right => match right with | .mstore y => decide (x = y) | _ => false
  | .jump x,right => match right with | .jump y => decide (x = y) | _ => false
  | .jumpi x,right => match right with | .jumpi y => decide (x = y) | _ => false
  | .pop,right => match right with | .pop => true | _ => false
  | .add,right => match right with | .add => true | _ => false
  | .sub,right => match right with | .sub => true | _ => false
  | .mul,right => match right with | .mul => true | _ => false
  | .div,right => match right with | .div => true | _ => false
  | .mod,right => match right with | .mod => true | _ => false
  | .lt,right => match right with | .lt => true | _ => false
  | .gt,right => match right with | .gt => true | _ => false
  | .eq,right => match right with | .eq => true | _ => false
  | .iszero,right => match right with | .iszero => true | _ => false
  | .or,right => match right with | .or => true | _ => false
  | .and,right => match right with | .and => true | _ => false
  | .slt,right => match right with | .slt => true | _ => false
  | .sgt,right => match right with | .sgt => true | _ => false
  | .sdiv,right => match right with | .sdiv => true | _ => false
  | .smod,right => match right with | .smod => true | _ => false
  | .keccakMap,right => match right with | .keccakMap => true | _ => false
  | .keccakArr,right => match right with | .keccakArr => true | _ => false
  | .sload,right => match right with | .sload => true | _ => false
  | .sstore,right => match right with | .sstore => true | _ => false
  | .mloadAt,right => match right with | .mloadAt => true | _ => false
  | .mstoreAt,right => match right with | .mstoreAt => true | _ => false
  | .call,right => match right with | .call => true | _ => false
  | .revert,right => match right with | .revert => true | _ => false
  | .xor,right => match right with | .xor => true | _ => false
  | .not,right => match right with | .not => true | _ => false
  | .shl,right => match right with | .shl => true | _ => false
  | .shr,right => match right with | .shr => true | _ => false
  | .exp,right => match right with | .exp => true | _ => false
  | .caller,right => match right with | .caller => true | _ => false
  | .callvalue,right => match right with | .callvalue => true | _ => false
  | .timestamp,right => match right with | .timestamp => true | _ => false
  | .selfbalance,right => match right with | .selfbalance => true | _ => false
  | .address,right => match right with | .address => true | _ => false
  | .loop ..,_ => false

theorem instruction_sound {left right : Instr} (same : instruction left right = true) : left = right := by
  cases left <;> simp only [instruction,Bool.false_eq_true] at same
  all_goals split at same <;>
    simp only [Bool.false_eq_true,decide_eq_true_eq] at same <;>
    first | contradiction | rfl | (cases same; rfl)

def code : List Instr → List Instr → Bool
  | [],[] => true
  | left :: rest,right :: tail => instruction left right && code rest tail
  | _,_ => false

theorem code_sound {left right : List Instr} (same : code left right = true) : left = right := by
  induction left generalizing right with
  | nil => cases right with | nil => rfl | cons x xs => cases same
  | cons x xs ih =>
    cases right with
    | nil => cases same
    | cons y ys =>
      have both := Bool.and_eq_true_iff.mp same
      rw [instruction_sound both.1,ih both.2]

end Solidity.Backend.InternalFlow.RuntimeFrame.CodeEquality
