import Solidity.Calculus.InputReduction
import Solidity.Calculus.Surface
import Solidity.Calculus.Spec
import Solidity.Tools.CompleteVerification

/-!
# Reconstructed transaction inputs and original function claims

Environment fields, scalar parameters and actual storage are reconstructed
together. Generated function premises remain part of the original claim.
-/

namespace Solidity.Examples.InputReduction

open Solidity.Decide Solidity.ReadRealization
open scoped Solidity.Scoped

def Bank : Contract := contract!{
  uint total;
  ensures total == x;
  function put(uint x) { total = x; }
  ensures total == x + 1;
  function bad(uint x) { total = x; }
}

local instance : InContract := ⟨Bank⟩

def total : Ref Bank := ⟨.uint, SRef.ofRoot "total" rfl, .nil⟩

def sameEnvironment : Fml Bank [] := dl!{ msg.value == msg.value }
def sameReduction : InputReduction sameEnvironment :=
  (inputReduction? sameEnvironment).get (by decide +kernel)

/-- info: true -/
#guard_msgs in #eval sameReduction.verify.isLeft

def jointClaim : Fml Bank [] := dl!{ ∀ uint x; msg.value == x ∧ total == 17 → false }
def jointReduction : InputReduction jointClaim :=
  (inputReduction? jointClaim).get (by decide +kernel)

/-- info: some true -/
#guard_msgs in
#eval match jointReduction.verify with
  | .inl _ => none
  | .inr cm => some (decide (cm.state.tx.msgValue = cm.atoms.get .uint 0 ∧
      (total.read cm.state.storage).val = 17))

def allInputs : Fml Bank [] :=
  dl!{ msg.sender == 17 ∧ msg.value == 19 ∧ block.timestamp == 23 ∧
    address(this).balance == 29 ∧ this == 31 → false }
def allReduction : InputReduction allInputs :=
  (inputReduction? allInputs).get (by decide +kernel)

/-- info: some (17, 19, 23, 29, 31) -/
#guard_msgs in
#eval match allReduction.verify with
  | .inl _ => none
  | .inr cm => some (cm.state.tx.msgSender.val, cm.state.tx.msgValue.val,
      cm.state.tx.timestamp.val, cm.state.selfBalance.val, cm.state.tx.selfAddress.val)

def inputProgram : Fml Bank [] := dl!{ [ total = msg.value; ] total == msg.value }
def programReduction : InputReduction inputProgram :=
  (inputReduction? inputProgram).get (by decide +kernel)

/-- info: true -/
#guard_msgs in #eval programReduction.verify.isLeft

def setterClaim : Fml Bank [] := cspec[Bank]{put}
def setterReduction : InputReduction setterClaim :=
  (inputReduction? setterClaim).get (by decide +kernel)

/-- info: true -/
#guard_msgs in #eval setterReduction.verify.isLeft

/-- `put(x)` writes exactly `x`, for every typed call and initial state. -/
theorem setter_valid : Fml.Valid setterClaim := setterReduction.valid_of_decide (by decide +kernel)

/-- The exact decision tactic proves the original generated specification. -/
theorem setter_exact : Fml.Valid setterClaim := by sol_exact

def badClaim : Fml Bank [] := cspec[Bank]{bad}
def badReduction : InputReduction badClaim :=
  (inputReduction? badClaim).get (by decide +kernel)

/-- info: some true -/
#guard_msgs in
#eval match badReduction.verify with
  | .inl _ => none
  | .inr cm => some (decide (cm.state.tx.msgValue.val = 0 ∧
      (cm.atoms.get .uint 0).val + 1 < 2 ^ 256))

/-- The original `bad(x)` specification fails at the all-zero input. -/
theorem bad_invalid : ¬ Fml.Valid badClaim := badReduction.not_valid_of_codes [] (by decide +kernel)

def badExact : Lean.Elab.Term.TermElabM String := do
  match ← Tools.exactVerify (Lean.mkConst ``badClaim) with
  | .proved _ => pure "proved"
  | .refutedDependent _ _ _ => pure "unexpected dependent route"
  | .refuted _ r xs =>
    let _ ← Tools.exactRefutation ``Bank Bank "bad" (Lean.mkConst ``badClaim) r xs
    pure "certified"

/-- info: "certified" -/
#guard_msgs in #eval badExact

def mixedInputs : Fml Bank [] := dl!{ ∀ bool b; ∀ int z; ∀ uint x;
  msg.value == 19 ∧ b == true ∧ z == (0 - 2) ∧ x == 17 ∧ total == 23 → false }
def mixedReduction : InputReduction mixedInputs :=
  (inputReduction? mixedInputs).get (by decide +kernel)

/-- info: some (19, true, -2, 17, 23) -/
#guard_msgs in
#eval match mixedReduction.verify with
  | .inl _ => none
  | .inr cm => some (cm.state.tx.msgValue.val, cm.atoms.get .bool 0,
      (cm.atoms.get .int 1).val, (cm.atoms.get .uint 2).val, (total.read cm.state.storage).val)

/-- info: 'Solidity.Decide.InputReduction.valid_iff' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms InputReduction.valid_iff

/-- info: 'Solidity.Decide.Inputs.observe_realize' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms Inputs.observe_realize

/-- info: 'Solidity.Decide.InputReduction.not_valid_of_codes' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms InputReduction.not_valid_of_codes

/-- info: 'Solidity.Examples.InputReduction.setter_exact' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms setter_exact

end Solidity.Examples.InputReduction
