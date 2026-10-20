import Solidity.Calculus.AutoComplete
import Solidity.Examples.ReadRealization
import Solidity.Tools.CompleteVerification

/-!
# Completeness of the automatic decision, on a write at a symbolic key

A write at a symbolic mapping key followed by a read at another symbolic
key leaves conditionals in the eliminated leaf (`kite` on the two keys,
`ite` on the location's presence), which the arithmetic compiler does not
read; folding and lifting them (`Calculus/CondLift.lean`) puts the leaf in
the fragment, and `auto_complete` (`Calculus/AutoComplete.lean`) gives the
certificate and the exact verdict.  A refuted claim gets its countermodel.

The verdicts on a `bool`-keyed mapping are checked by the kernel; on the
`uint`-keyed one the kernel's arithmetic decision is too deep for the
language server (256-bit codes), so the positive verdict there is the
compiled one and the refutation is checked at its finite codes.
-/

namespace Solidity.Examples.AutoComplete

open Solidity.Decide

/-! ## A `bool`-keyed mapping: both verdicts kernel-checked -/

def Flags : Contract := contract!{ mapping(bool => bool) flags; }

section Flags

local instance : InContract := ⟨Flags⟩

/-- Setting the flag at `k` and reading at `j = k` gives `true`. -/
def flagWrite : Fml Flags [] :=
  dl!{ ∀ bool k; ∀ bool j; [ flags[k] = true; ] (k == j → flags[j] == true) }

/-- Without `j = k` the read may see the other key. -/
def flagBad : Fml Flags [] :=
  dl!{ ∀ bool k; ∀ bool j; [ flags[k] = true; ] flags[j] == true }

end Flags

/-! The eliminated leaf has conditionals: it is outside the conditional-free
fragment the compiler reads, inside the one lifting completes. -/

/-- info: some (false, true) -/
#guard_msgs in
#eval (leafOf? flagWrite).map fun ψ => ((ψ.stripAll.2.src? false).isSome, (ψ.stripAll.2.src? true).isSome)

theorem flagWrite_inExact : flagWrite.inExact = true := by decide +kernel
theorem flagWrite_bounded : flagWrite.exactBounded = true := by decide +kernel

/-- The certificate `dependentReduction?_isSome` guarantees. -/
def flagWriteReduction : DependentReduction flagWrite :=
  (dependentReduction? flagWrite).get
    (dependentReduction?_isSome flagWrite flagWrite_inExact flagWrite_bounded)

/-- `auto_complete`, applied: the verdict is exact. -/
theorem flagWrite_iff : Valid flagWrite ↔ flagWriteReduction.arithmetic.guarded.decide = true := by
  obtain ⟨r, hr, h⟩ := auto_complete flagWrite flagWrite_inExact flagWrite_bounded
  obtain rfl : r = flagWriteReduction := Option.some.inj (hr.symm.trans (Option.some_get _).symm)
  exact h

theorem flagWrite_valid : Valid flagWrite := flagWrite_iff.mpr (by decide +kernel)

/-- The public tactic, which runs the same decision, proves it too. -/
example : Valid flagWrite := by sol_exact

theorem flagBad_inExact : flagBad.inExact = true := by decide +kernel
theorem flagBad_bounded : flagBad.exactBounded = true := by decide +kernel

def flagBadReduction : DependentReduction flagBad :=
  (dependentReduction? flagBad).get (dependentReduction?_isSome flagBad flagBad_inExact flagBad_bounded)

theorem flagBad_decide : flagBadReduction.arithmetic.guarded.decide = false := by decide +kernel

/-- The countermodel `auto_countermodel` promises: an actual starting state. -/
def flagBadCountermodel : flagBadReduction.Countermodel :=
  flagBadReduction.countermodelOfDecide flagBad_decide

theorem flagBad_invalid : ¬ Valid flagBad :=
  fun h => flagBadCountermodel.refutes (h flagBadCountermodel.state)

-- The countermodel's `k` and `j`: different keys.
/-- info: (true, false) -/
#guard_msgs in
#eval (flagBadCountermodel.atoms.get .bool 0, flagBadCountermodel.atoms.get .bool 1)

/-! ## A `uint`-keyed mapping -/

section Bank

open Solidity.Examples.ReadRealization (Bank)

local instance : InContract := ⟨Bank⟩

def symWrite : Fml Bank [] :=
  dl!{ ∀ uint k; ∀ uint j; [ balances[k] = 17; ] (k == j → balances[j] == 17) }

def symBad : Fml Bank [] :=
  dl!{ ∀ uint k; ∀ uint j; [ balances[k] = 17; ] balances[j] == 17 }

end Bank

theorem symWrite_inExact : symWrite.inExact = true := by decide +kernel
theorem symWrite_bounded : symWrite.exactBounded = true := by decide +kernel

def symWriteReduction : DependentReduction symWrite :=
  (dependentReduction? symWrite).get
    (dependentReduction?_isSome symWrite symWrite_inExact symWrite_bounded)

/-- info: true -/
#guard_msgs in #eval symWriteReduction.verify.isLeft

theorem symBad_inExact : symBad.inExact = true := by decide +kernel
theorem symBad_bounded : symBad.exactBounded = true := by decide +kernel

def symBadReduction : DependentReduction symBad :=
  (dependentReduction? symBad).get (dependentReduction?_isSome symBad symBad_inExact symBad_bounded)

/-- info: [(PrimTy.uint, 1), (PrimTy.uint, 2), (PrimTy.uint, 0)] -/
#guard_msgs in
#eval symBadReduction.body.encoding.parameters.map fun p => (p.prim, p.index)

/-- The refutation, at finite codes in that order: `j = 1`, the starting
value `0` read at `j`, `k = 0`. -/
theorem symBad_invalid : ¬ Valid symBad :=
  symBadReduction.not_valid_of_codes [1, 0, 0] (by decide +kernel)

end Solidity.Examples.AutoComplete
