import Solidity.Semantics.WellFormed
import Solidity.TermSimp
import Solidity.Theory.Abs

/-!
# Modalities, and what the terms' signature leaves to the interpreter

The terms of the calculus are typed (`Signature.lean`: KeY's sorts indexed
by Solidity types, the symbols over the contract; `Calculus/Fml.lean`: the
terms, updates and formulas in a context).  The untyped signature that was
here (`Srt`, `Op0` … `Op3`, read on `Semantics.State`) went at W9.8.3
(`docs/intrinsic.md`), and the untyped reading of a halt
(`Modality.after`) and the untyped callback and loop states
(`State.havoc`, `State.anon`) at W10.1: their typed versions are
`Modality.afterRunTR` (`Calculus/Logic.lean`) and `State.havoc`,
`State.anon` (`Semantics/RunFrame.lean`).  What stays: the two modalities
and how a halt reads under each (`Modality.onHalt`), the ledger's
arithmetic (`IntOp`), and, untyped on purpose, what `sol_decide`'s
language (`Calculus/DecideLang.lean`) and the Theory read: the
interpreter's memory read (`readAddr`), a quantifier's range
(`PrimTy.admits`), the Theory's reading of a result (`StValue.toRes`,
`Res.toSt`).

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

/-- What a modality says of a run that reverts (or is `undef`): every box
formula holds of it, no diamond formula does. -/
def Modality.onHalt : Modality → Prop
  | .diamond => False
  | .box => True

/-! ## Memory reads

The slot a memory address names, as the interpreter reads it: `sol_decide`'s
language and the Theory read memory so (the typed read is `Heap.readAddr`,
`Semantics/Run.lean`). -/

variable {C : Contract}

/-- The slot at a memory address. -/
def readAddr (σ : State) : Addr → Res MVal
  | .memoryField id f => do
    match ← σ.getObj id with
    | .struct fields =>
      match lookupBy f fields with
      | some v => pure v
      | none => .error .undef
    | .array _ _ => .error .undef
  | .memoryIndex id i => do
    match ← σ.getObj id with
    | .array elems _ =>
      if h : 0 ≤ i ∧ i.toNat < elems.length then pure (elems.get ⟨i.toNat, h.2⟩)
      else .error .revert
    | .struct _ => .error .undef

/-! ## The Theory's readings of results -/

section Denote

open Theory Theory.StValue

/-- A Theory value as an interpreter result: a primitive, or a halt. -/
def Theory.StValue.toRes : StValue → Res Value
  | .prim p => .ok p
  | .st _ => .error .undef

/-- An interpreter result as a Theory value: a halt reads as nothing. -/
def Semantics.Res.toSt : Res Value → StValue
  | .ok v => .prim v
  | .error _ => .st .mtSt

end Denote

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

/-- The values of the primitive type `p`, which a quantifier ranges over. -/
def PrimTy.admits : PrimTy → Value → Prop
  | .bool, .bool _ => True
  | .uint, .int n => 0 ≤ n ∧ n < uintBound
  | .int, .int n => -intBound ≤ n ∧ n < intBound
  | _, _ => False

end Solidity
