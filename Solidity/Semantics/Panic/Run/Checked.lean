import Solidity.Semantics.Panic.Run.Control

namespace Solidity.Semantics.Panic

/-- The five source compound operators retain the actual numeric operands.
Other operators retain the original helper's unclassified outcome. -/
def compound (op : BinOp) (p : PrimTy) (hp : p.isNumeric = true)
    (x y : p.Denote) : EvalResult p.Denote :=
  match op with
  | .add => evalProducer (.binary .add p hp x y)
  | .sub => evalProducer (.binary .sub p hp x y)
  | .mul => evalProducer (.binary .mul p hp x y)
  | .div => evalProducer (.binary .div p hp x y)
  | .mod => evalProducer (.binary .mod p hp x y)
  | op => ofOpt (compoundT op p (PrimTy.key x) (PrimTy.key y))

def numericOne : (p : PrimTy) → p.isNumeric = true → p.Denote
  | .uint, _ => ⟨1, by decide⟩
  | .int, _ => ⟨1, by decide⟩
  | .bool, h => nomatch h

/-- Increment/decrement is checked addition/subtraction of the typed value one. -/
def bump (op : IncDec) (p : PrimTy) (hp : p.isNumeric = true)
    (x : p.Denote) : EvalResult p.Denote :=
  if op.isIncrement then evalProducer (.binary .add p hp x (numericOne p hp))
  else evalProducer (.binary .sub p hp x (numericOne p hp))

/-- A local projection; this does not assert whole-program result erasure. -/
theorem compound_erase (op : BinOp) (p : PrimTy) (hp : p.isNumeric = true)
    (x y : p.Denote) : erase (compound op p hp x y) =
      TRes.ofOpt (compoundT op p (PrimTy.key x) (PrimTy.key y)) := by
  cases op <;> simp only [compound, erase_evalProducer, Solidity.Panic.Producer.run,
    erase_checked, erase_ofOpt]
  all_goals cases p with
    | bool => contradiction
    | uint => rfl
    | int => rfl

theorem bump_erase (op : IncDec) (p : PrimTy) (hp : p.isNumeric = true)
    (x : p.Denote) : erase (bump op p hp x) =
      TRes.ofOpt (bumpT op p (PrimTy.key x)) := by
  cases op <;> simp only [bump, IncDec.isIncrement, Bool.false_eq_true, if_true,
    if_false, erase_evalProducer, Solidity.Panic.Producer.run, erase_checked]
  all_goals cases p with
    | bool => contradiction
    | uint => rfl
    | int => rfl

end Solidity.Semantics.Panic
