import Solidity.Semantics.Run
import Solidity.Semantics.Erase

/-!
# The value-level erasure

The typed run's values against the untyped interpreter's, below the
statements: the value-level erasure lemmas the Typing chain and the tools
read (`compound_erase`, `bump_erase`, …), with
`Semantics/StorageErase.lean`, `Semantics/HeapErase.lean` and
`Semantics/Erase.lean` below it; importing this module imports the whole
erasure.  The typed core does not (W10.5.1): an expression's not panicking
(`Val.evalT_noPanic`) is `Semantics/NoPanic.lean`'s.  Since W9.8.3 the
rules' soundness reads the typed run against typed terms with nothing
erased (`Calculus/LowerRun.lean`, `TRes.AgreesO`).

A storage copy overlays a struct by position in the typed run and by name in
the erasure (`SVal.overlay_erase`), which agree since no struct repeats a
member name (`structDef_nodup`, decision 16).  A `bool` mapping key is
hashed as `0`/`1` by both (`Value.keyAt`, `PrimTy.key`; decisions 10 and 14).
-/

namespace Solidity

open Semantics (Value Res lookupBy)

variable {C : Contract}

/-! ## Expressions -/

section Eval

variable {Γ : Ctx}

theorem SRef.erase_index {R : RefTy} {k : PrimTy} {V : Ty} (r : SRef C (.ref R))
    (it : IndexTy R k V) (i : Int) : (r.index it i).erase = (r.root, r.path.erase ++ [.at i]) := by
  simp only [SRef.index, SRef.erase, SRef.append, Path.erase_append, Path.erase_index]

/-! ### Compound assignments and `++` -/

theorem PrimTy.erase_numeric {p : PrimTy} (hp : p.isNumeric = true) (x : p.Denote) :
    PrimTy.erase x = .int (PrimTy.key x) := by
  cases p <;> first | rfl | cases hp

theorem compound_erase {op : BinOp} (hop : op.hasCompoundAssign = true) {p : PrimTy}
    (hp : p.isNumeric = true) (x y : Int) :
    (Semantics.applyBinOp op (.int x) (.int y) >>= Semantics.checkArith (.prim p)) =
      toRes PrimTy.erase (compoundT op p x y) := by
  have hA : op.isArith = true := by
    cases op <;> simp only [BinOp.hasCompoundAssign, Bool.false_eq_true] at hop <;> rfl
  rw [BinOp.applyBinOp_int hA]
  unfold compoundT
  cases BinOp.arithInt op x y with
  | none => rfl
  | some n => exact PrimTy.checkArith_ofInt hp n

theorem bump_erase {p : PrimTy} (hp : p.isNumeric = true) (op : IncDec) (x : Int) :
    Semantics.checkArith (.prim p) (.int (if op.isIncrement then x + 1 else x - 1)) =
      toRes PrimTy.erase (bumpT op p x) :=
  PrimTy.checkArith_ofInt hp _

end Eval

end Solidity
