import Solidity.TermSimp
import Solidity.Theory.Segs

/-!
# Modalities, and what the terms' signature leaves to the interpreter

The terms of the calculus are typed (`Signature.lean`: KeY's sorts indexed
by Solidity types, the symbols over the contract; `Calculus/Fml.lean`: the
terms, updates and formulas in a context).  The untyped signature that was
here (`Srt`, `Op0` … `Op3`, read on the untyped state) went at W9.8.3
(`docs/intrinsic.md`), the untyped reading of a halt (`Modality.after`)
and the untyped callback and loop states (`State.havoc`, `State.anon`) at
W10.1 (their typed versions are `Modality.afterRunTR`, `Calculus/Logic.lean`,
and `Semantics/RunFrame.lean`'s), and the Theory's untyped readings of a
result at W10.3, the interpreter's memory read (`readAddr`) at W10.5.4,
when the memory laws went over to the typed heap (`Heap.readAddr`,
`Semantics/Run.lean`).  What stays: the two modalities and how a halt reads
under each (`Modality.onHalt`), and the ledger's arithmetic (`IntOp`).

Unlike KeY's, the terms can halt: they are read by the interpreter's own
operations, so `a + b` reverts on overflow and `values[i]` on an index out
of range, exactly as the statement they came from.  An update therefore
carries the modality of the goal it was produced in, and `{U} φ` with a
halting `U` is judged as the halting statement would be.
-/
namespace Solidity

open Semantics

/-- The two modalities: the diamond `⟨ P ⟩ φ` and the box `[ P ] φ`. -/
inductive Modality where
  | diamond
  | box
  deriving DecidableEq, Repr, Inhabited, Lean.ToExpr

/-- What a modality says of a run that reverts: every box
formula holds of it, no diamond formula does. -/
def Modality.onHalt : Modality → Prop
  | .diamond => False
  | .box => True

/-! ## Updates -/

/-- `+` or `-` of KeY's `int`, which has no range to check: the arithmetic
of the ledger updates, where a `Term.binop` would be range-checked. -/
inductive IntOp where
  | add | sub
  deriving DecidableEq, Repr

def IntOp.apply : IntOp → Int → Int → Int
  | .add, a, b => a + b
  | .sub, a, b => a - b

/-- The operator as a Lean term, for the quoter (`Calculus/Quote.lean`). -/
def IntOp.quote : IntOp → Lean.Expr
  | .add => Lean.mkConst ``IntOp.add
  | .sub => Lean.mkConst ``IntOp.sub

end Solidity
