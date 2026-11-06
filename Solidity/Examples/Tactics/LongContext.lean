import Solidity.Examples.Tactics.SymbolicCounterexample

/-!
# Long-array certificates with a supplied local

The source formula is closed, while peeling its supplied parameter leaves a
nonempty intrinsic context. These pins exercise the existing context discovery
in `Tools.certifyLong`; the empty source context must not replace the peeled one.
-/

namespace Solidity.Examples.Tactics.LongContext
open SymbolicCounterexample
open scoped Solidity.Scoped
local instance : InContract := ⟨Counted⟩

def supplied : List (Var × Semantics.CallValue) :=
  [(.user "n", .uint (uintOfNat 5))]

def candidate : Tools.LongCand := ⟨"values", 0, .prim .uint, 2 ^ 255⟩

def falseLength : Fml Counted [] := dl!{ ∀ uint n; wt(storage) → values.length = n }
def trueLength : Fml Counted [] :=
  dl!{ ∀ uint n; wt(storage) → values.length + (n - n) = values.length }

example : (Fml.peel supplied (State.ofStorage longValues) falseLength).1 = [.val .uint] := rfl
example : (Fml.peel [] (State.ofStorage longValues) falseLength).1 = [] := rfl

open Lean Elab Term Meta in
elab "certifySuppliedLong" : term => do
  let some pf ← Tools.certifyLong (mkConst ``Counted) (mkConst ``falseLength) supplied candidate
    | throwError "long-array certificate lost its supplied context"
  return pf

/-- Solidity `require(values.length == n);` is false for `n = 5` in the
well-formed storage whose array has `2^255` elements. -/
theorem falseLengthRefuted : ¬ (⊨ᶠ falseLength) := certifySuppliedLong

open Lean Meta in
run_meta do
  if (← Tools.certifyLong (mkConst ``Counted) (mkConst ``trueLength) supplied candidate).isSome then
    throwError "a true property was refuted"
  if (← Tools.certifyLong (mkConst ``Counted) (mkConst ``falseLength) [] candidate).isSome then
    throwError "an unsupplied binder was silently assigned"

/-- info: 'Solidity.Examples.Tactics.LongContext.falseLengthRefuted' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms falseLengthRefuted

end Solidity.Examples.Tactics.LongContext
