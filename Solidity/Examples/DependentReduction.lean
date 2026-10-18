import Solidity.Tools.Verify
import Solidity.Examples.ReadFlattening
import Solidity.Examples.ReadTrace

/-!
# Dependent-read decisions through original function specifications

The public exact verifier generates occurrences and guarded alias arithmetic,
chooses values, and certifies an original-source counterstate. Universal
parameters and generated declaration facts are preserved throughout.
-/

namespace Solidity.Examples.DependentReduction

open Solidity.Tools Solidity.Decide Solidity.Semantics
open scoped Solidity.Scoped

def Bank : Contract := contract!{
  mapping(uint => uint) balances;
  ensures balances[balances[k]] == balances[k];
  function same(uint k) { balances[k] = k; }
  ensures balances[k] == 17;
  function follow(uint k) { balances[k] = balances[balances[k]]; }
  requires b == true;
  requires d == -2;
  requires k == 3;
  ensures balances[k] == 17;
  function mixed(bool b, int d, uint k) { balances[k] = balances[balances[k]]; }
}

def followClaim : Fml Bank [] := cspec[Bank]{follow}
def reduced : Solidity.Decide.DependentReduction followClaim := declaration_dependent_reduce[followClaim]
def countermodel : reduced.Countermodel := reduced.countermodelOfCodes [] (by decide +kernel)
theorem follow_invalid : ¬ Valid followClaim := fun h => countermodel.refutes (h countermodel.state)

def exactNegative : Lean.Elab.Term.TermElabM Bool := do
  match ← exactVerify (Lean.mkConst ``followClaim) with
  | .proved _ | .refuted _ _ _ => pure false
  | .refutedDependent _ r xs =>
    let report ← dependentRefutation ``Bank Bank "follow" (Lean.mkConst ``followClaim) r xs
    pure report.certified

/-- info: true -/
#guard_msgs in #eval exactNegative

theorem same_valid : Valid (cspec[Bank]{same}) := by sol_exact

/--
info: ✗ follow (certified):
  k = 0, msg.sender = 0, msg.value = 0
  before: balances = {0: 0, _: 0}
  after: balances = {0: 0, _: 0}
  fails: ensures balances[k] == 17
-/
#guard_msgs in
#verify Bank.follow

/--
info: ✗ mixed (certified):
  b = true, d = -2, k = 3, msg.sender = 0, msg.value = 0
  before: balances = {28948022309329048855892746252171976963317496166410141009864396001978282409987: 3, 3: 28948022309329048855892746252171976963317496166410141009864396001978282409987, _: 0}
  after: balances = {28948022309329048855892746252171976963317496166410141009864396001978282409987: 3, 3: 3, _: 0}
  fails: ensures balances[k] == 17
-/
#guard_msgs in
#verify Bank.mixed

/--
info: ✓ same
---
info: Try this:
  theorem same_spec : ⊨ spec[Bank]{same} := by sol_exact
-/
#guard_msgs in #verify Bank.same

def minimalNegative : Lean.Elab.Term.TermElabM Bool := do
  match ← exactVerify (Lean.mkConst ``followClaim) with
  | .proved _ | .refuted _ _ _ => pure false
  | .refutedDependent _ r xs =>
    let report ← dependentRefutation ``Bank Bank "missing" (Lean.mkConst ``followClaim) r xs
    pure (report.certified && report.witness.contains "parameter #0 = 0" &&
      report.witness.contains "before: balances = {0: 0, _: 0}")

/-- info: true -/
#guard_msgs in #eval minimalNegative

def sameClaim : Fml Bank [] := cspec[Bank]{same}
def rejectForgedReport : Lean.Elab.Term.TermElabM Bool := do
  let φ := Lean.mkConst ``sameClaim
  let r ← DeclarationReduction.compileDependent φ
  Lean.tryCatchRuntimeEx
    (do
      let _ ← dependentRefutation ``Bank Bank "missing" φ r []
      pure false)
    (fun e => do pure ((← errText e) == "exact verification: kernel rejected certificate"))

/-- info: true -/
#guard_msgs in #eval rejectForgedReport

def guardedClaim : Fml Solidity.Examples.ReadTrace.Follower [] :=
  cspec[Solidity.Examples.ReadTrace.Follower]{guarded}

def rejectQuantifiedPremise : Lean.Elab.Term.TermElabM Bool :=
  Lean.tryCatchRuntimeEx
    (do
      let _ ← DeclarationReduction.compileDependent (Lean.mkConst ``guardedClaim)
      pure false)
    (fun _ => pure true)

/-- info: true -/
#guard_msgs in #eval rejectQuantifiedPremise

/-- info: 'Solidity.Decide.DependentReduction.valid_iff' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Solidity.Decide.DependentReduction.valid_iff
/-- info: 'Solidity.Examples.DependentReduction.follow_invalid' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms follow_invalid

end Solidity.Examples.DependentReduction
