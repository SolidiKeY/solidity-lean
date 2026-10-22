import Solidity.Tools.Verify
import Solidity.Calculus.Surface

/-!
# Exact verification through the public tools

Generated mapping premises are certified before compilation. Countermodel
reports retain the original arguments and transaction, and unsupported
programs continue through the existing verifier.
-/

namespace Solidity.Examples.CompleteVerification

open Solidity.Tools Solidity.Decide
open scoped Solidity.Scoped

def Bank : Contract := contract!{
  mapping(uint => uint) balances;
  uint total;
  ensures balances[3] == 17;
  function put() { balances[3] = 17; }
  ensures balances[3] == x;
  function putParam(uint x) { balances[3] = x; }
  ensures balances[3] == 18;
  function badMap() { balances[3] = 17; }
  requires x > 17;
  requires x < 19;
  ensures total == x + 1;
  function bad(uint x) { total = x; }
  requires b == true;
  requires z == -2;
  requires x == 17;
  ensures total == x + 1;
  function mixed(bool b, int z, uint x) { total = x; }
  requires address(this) == 31;
  ensures total == 1;
  function addressBad() { total = 0; }
}

/-- Generated quantified mapping ranges are retained in the proved claim. -/
theorem mapping_valid : Fml.Valid (cspec[Bank]{put}) := by sol_exact

def mappingClaim : Fml Bank [] := cspec[Bank]{put}

def exactPositive : Lean.Elab.Term.TermElabM Bool := do
  match ← exactVerify (Lean.mkConst ``mappingClaim) with
  | .proved _ => pure true
  | .refuted _ _ _ | .refutedDependent _ _ _ => pure false

/-- info: true -/
#guard_msgs in #eval exactPositive

/--
info: ✓ put
---
info: Try this:
  theorem put_spec : ⊨ᶠ spec[Bank]{put} := by sol_exact
-/
#guard_msgs in #verify Bank.put

/-- Replay the theorem offered by the public verifier. -/
theorem put_spec : ⊨ᶠ spec[Bank]{put} := by sol_exact

/--
info: ✓ putParam
---
info: Try this:
  theorem putParam_spec : ⊨ᶠ spec[Bank]{putParam} := by sol_exact
-/
#guard_msgs in #verify Bank.putParam

/-- Generated mapping facts are certified under real hidden parameters. -/
theorem putParam_spec : ⊨ᶠ spec[Bank]{putParam} := by sol_exact

def minimalNegative : Lean.Elab.Term.TermElabM Bool := do
  let φ ← Lean.Elab.Term.elabTerm (← `(cspec[Bank]{ $(Lean.mkIdent (.mkSimple "bad")) })) none
  match ← exactVerify φ with
  | .proved _ => pure false
  | .refutedDependent _ _ _ => pure false
  | .refuted _ r xs =>
    -- Deliberately prevent function-specific rendering after the original
    -- countermodel proof has already passed the kernel.
    let report ← exactRefutation ``Bank Bank "missing" φ r xs
    pure (report.certified && report.witness.contains "parameter #0 = 18" &&
      report.witness.contains "before: balances = {_: 0}; total = 0")

/-- info: true -/
#guard_msgs in #eval minimalNegative

def rejectForgedReport : Lean.Elab.Term.TermElabM Bool := do
  let φ := Lean.mkConst ``mappingClaim
  let r ← DeclarationReduction.compileInput φ
  Lean.tryCatchRuntimeEx
    (do
      let _ ← exactRefutation ``Bank Bank "missing" φ r []
      pure false)
    (fun e => do pure ((← errText e) == "exact verification: kernel rejected certificate"))

-- Arbitrary codes and unavailable rendering cannot certify a valid claim.
/-- info: true -/
#guard_msgs in #eval rejectForgedReport

/--
info: ✗ bad (certified):
  x = 18, msg.sender = 0, msg.value = 0
  before: balances = {_: 0}; total = 0
  after: balances = {_: 0}; total = 18
  fails: ensures total == x + 1
-/
#guard_msgs in #verify Bank.bad

/--
info: ✗ mixed (certified):
  b = true, z = -2, x = 17, msg.sender = 0, msg.value = 0
  before: balances = {_: 0}; total = 0
  after: balances = {_: 0}; total = 17
  fails: ensures total == x + 1
-/
#guard_msgs in #verify Bank.mixed

/--
info: ✗ badMap (certified):
  msg.sender = 0, msg.value = 0
  before: balances = {_: 0}; total = 0
  after: balances = {3: 17, _: 0}; total = 0
  fails: ensures balances[3] == 18
-/
#guard_msgs in #verify Bank.badMap

/--
info: ✗ addressBad (certified):
  msg.sender = 0, msg.value = 0
  before: balances = {_: 0}; total = 0
  after: balances = {_: 0}; total = 0
  address(this) = 31
  fails: ensures total == 1
-/
#guard_msgs in #verify Bank.addressBad

end Solidity.Examples.CompleteVerification
