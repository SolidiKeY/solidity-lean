import Solidity.Yul.Compilation.WordExpressions
/-! Recursive original-AST compiler extension with AND/OR/XOR/SHL/SHR.
Actual full-word semantics and >=256 shift results zero are proved here;
older visitors/refusals remain untouched. No AST/state/layout is duplicated. -/
namespace Solidity.Yul.Compilation.BitExpressions
open Backend Scalar
open Solidity.Yul.Closed ProducerExpressions WordExpressions

def selectOr : BinarySelection := ⟨.OR,(· ||| ·),fun _ _ _ => rfl⟩
def selectXor : BinarySelection := ⟨.XOR,(· ^^^ ·),fun _ _ _ => rfl⟩
def selectShl : BinarySelection := ⟨.SHL,(Scalar.binary .SHL).getD (fun _ _ => 0),fun _ _ _ => rfl⟩
def selectShr : BinarySelection := ⟨.SHR,(Scalar.binary .SHR).getD (fun _ _ => 0),fun _ _ _ => rfl⟩

def andBridge : BinaryBridge .and := ⟨selectAnd,by
  intro a b
  apply Fin.ext
  change (a &&& b).toNat = (a.toNat &&& b.toNat) % 2^256
  rw [BitVec.toNat_and,Nat.mod_eq_of_lt (Nat.and_lt_two_pow _ b.isLt)]⟩
def orBridge : BinaryBridge .or := ⟨selectOr,by
  intro a b
  apply Fin.ext
  change (a ||| b).toNat = (a.toNat ||| b.toNat) % 2^256
  rw [BitVec.toNat_or,Nat.mod_eq_of_lt (Nat.or_lt_two_pow a.isLt b.isLt)]⟩
def xorBridge : BinaryBridge .xor := ⟨selectXor,by
  intro a b
  apply Fin.ext
  change (a ^^^ b).toNat = (a.toNat ^^^ b.toNat) % 2^256
  rw [BitVec.toNat_xor,Nat.mod_eq_of_lt (Nat.xor_lt_two_pow a.isLt b.isLt)]⟩
def shlBridge : BinaryBridge .shl := ⟨selectShl,by
  intro a b
  apply Fin.ext
  change (if a.toNat < 256 then b <<< a.toNat else (0 : Scalar.Word)).toNat =
    (if a.toNat ≥ 256 then word 0 else word (b.toNat <<< a.toNat)).val
  by_cases small : a.toNat < 256
  · rw [if_pos small,if_neg (by omega)]
    exact BitVec.toNat_shiftLeft
  · rw [if_neg small,if_pos (by omega)]
    rfl⟩
def shrBridge : BinaryBridge .shr := ⟨selectShr,by
  intro a b
  apply Fin.ext
  change (if a.toNat < 256 then b >>> a.toNat else (0 : Scalar.Word)).toNat =
    (if a.toNat ≥ 256 then word 0 else word (b.toNat >>> a.toNat)).val
  by_cases small : a.toNat < 256
  · rw [if_pos small,if_neg (by omega)]
    change (b >>> a.toNat).toNat = (b.toNat >>> a.toNat) % 2^256
    rw [BitVec.toNat_ushiftRight,Nat.mod_eq_of_lt (Nat.lt_of_le_of_lt (Nat.shiftRight_le _ _) b.isLt)]
  · rw [if_neg small,if_pos (by omega)]
    rfl⟩

/-- Actual recursive compiler certificates at the SAME source horizon. -/
def compile {n r : Nat} (fuel : Nat) (expr : Expr [] [] n r) : Option (Compiled fuel expr) :=
  match fuel with
  | 0 => none
  | fuel+1 => by
      apply Expr.casesOn (motive := fun r expr => Option (Compiled (fuel+1) expr)) expr
      case literal => intro w; exact some (literal fuel w)
      case «local» => intro i; exact some (localExpr fuel i)
      case external => intro ref; cases ref.index
      case call => intro sig f args; cases f
      case builtin =>
        intro a r builtin args
        cases builtin with
        | pure op =>
            cases op with
            | add => exact do
                let left ← compile fuel (args 0)
                let right ← compile fuel (args 1)
                pure (ProducerExpressions.binary addBridge left right)
            | sub => exact do
                let left ← compile fuel (args 0)
                let right ← compile fuel (args 1)
                pure (ProducerExpressions.binary subBridge left right)
            | mul => exact do
                let left ← compile fuel (args 0)
                let right ← compile fuel (args 1)
                pure (ProducerExpressions.binary mulBridge left right)
            | «div» => exact do
                let left ← compile fuel (args 0)
                let right ← compile fuel (args 1)
                pure (ProducerExpressions.binary QuotientExpressions.divBridge left right)
            | «mod» => exact do
                let left ← compile fuel (args 0)
                let right ← compile fuel (args 1)
                pure (ProducerExpressions.binary QuotientExpressions.modBridge left right)
            | lt => exact do
                let left ← compile fuel (args 0)
                let right ← compile fuel (args 1)
                pure (ProducerExpressions.binary ltBridge left right)
            | gt => exact do
                let left ← compile fuel (args 0)
                let right ← compile fuel (args 1)
                pure (ProducerExpressions.binary gtBridge left right)
            | eq => exact do
                let left ← compile fuel (args 0)
                let right ← compile fuel (args 1)
                pure (ProducerExpressions.binary eqBridge left right)
            | iszero => exact do
                let arg ← compile fuel (args 0)
                pure (WordExpressions.unary iszeroBridge arg)
            | «not» => exact do
                let arg ← compile fuel (args 0)
                pure (WordExpressions.unary notBridge arg)
            | «and» => exact do
                let left ← compile fuel (args 0)
                let right ← compile fuel (args 1)
                pure (ProducerExpressions.binary andBridge left right)
            | «or» => exact do
                let left ← compile fuel (args 0)
                let right ← compile fuel (args 1)
                pure (ProducerExpressions.binary orBridge left right)
            | «xor» => exact do
                let left ← compile fuel (args 0)
                let right ← compile fuel (args 1)
                pure (ProducerExpressions.binary xorBridge left right)
            | «shl» => exact do
                let left ← compile fuel (args 0)
                let right ← compile fuel (args 1)
                pure (ProducerExpressions.binary shlBridge left right)
            | «shr» => exact do
                let left ← compile fuel (args 0)
                let right ← compile fuel (args 1)
                pure (ProducerExpressions.binary shrBridge left right)
            | _ => exact none
        | _ => exact none
termination_by structural fuel

/-- Single-target assignment uses the existing real statement certificate. -/
def assignment {fuel n : Nat} {c : Control} (targets : Fin 1 → Target [] n) (expr : Expr [] [] n 1) :
    Option (ProducerStatements.Compiled (fuel+1) (Stmt.assign (c := c) targets expr)) :=
  (compile fuel expr).map (ProducerStatements.assignTargets targets)

#print axioms andBridge
#print axioms orBridge
#print axioms xorBridge
#print axioms shlBridge
#print axioms shrBridge
#print axioms compile
end Solidity.Yul.Compilation.BitExpressions
