import Solidity.Calculus.ProgramReduction
import Solidity.Calculus.Spec
import Solidity.Calculus.Surface

/-!
# Exact source calls before complete arithmetic

Arguments are evaluated in caller order, return locals are initialized and
the callee's frame is removed before the caller continues. Countermodels
refer to the original call, including failure before entering its body.
-/

namespace Solidity.Examples.CallReduction

open Solidity.Decide Solidity.ReadRealization
open scoped Solidity.Scoped

def Calls : Contract := contract!{
  uint total;
  ensures total == x;
  function put(uint x) { total = x; }
  function echo(uint x) returns (uint r) { return x; }
  function step(uint x) returns (uint r) { return x - 1; }
  function pair(uint x) returns (uint a, uint b) { a = x; b = x - 1; }
  function combine(uint x) returns (uint r) { uint a = echo(x); return step(a); }
  function zero() returns (uint r) { }
  function diff(uint x, uint y) returns (uint r) { return x - y; }
  function gate(bool b) { assert(b); }
  function abort() { revert(); }
}

local instance : InContract := ⟨Calls⟩

def total : Ref Calls := ⟨.uint, SRef.ofRoot "total" rfl, .nil⟩

def voidClaim : Fml Calls [] := dl!{ ∀ uint v; [ put(v); ] total == v }
def voidReduction : ParameterReduction voidClaim :=
  (programReduction? voidClaim).get (by decide +kernel)

/-- info: true -/
#guard_msgs in #eval voidReduction.verify.isLeft

def echoClaim : Fml Calls [] := dl!{ ∀ uint v; [ uint r = echo(v); ] r == v }
def echoReduction : ParameterReduction echoClaim :=
  (programReduction? echoClaim).get (by decide +kernel)

/-- info: true -/
#guard_msgs in #eval echoReduction.verify.isLeft

def nestedClaim : Fml Calls [] := dl!{ ∀ uint v; [ uint r = combine(v); ] r < v }
def nestedReduction : ParameterReduction nestedClaim :=
  (programReduction? nestedClaim).get (by decide +kernel)

/-- info: true -/
#guard_msgs in #eval nestedReduction.verify.isLeft

def tupleClaim : Fml Calls [] := dl!{ [ (uint a, uint b) = pair(17); ] (a == 17 ∧ b == 16) }
def tupleReduction : ParameterReduction tupleClaim :=
  (programReduction? tupleClaim).get (by decide +kernel)

/-- info: true -/
#guard_msgs in #eval tupleReduction.verify.isLeft

def discardedClaim : Fml Calls [] := dl!{ ⟨ echo(17); ⟩ true }
def discardedReduction : ParameterReduction discardedClaim :=
  (programReduction? discardedClaim).get (by decide +kernel)

/-- info: true -/
#guard_msgs in #eval discardedReduction.verify.isLeft

def defaultReturn : Fml Calls [] := dl!{ ⟨ uint r = zero(); ⟩ r == 0 }
def defaultReturnReduction : ParameterReduction defaultReturn :=
  (programReduction? defaultReturn).get (by decide +kernel)

/-- info: true -/
#guard_msgs in #eval defaultReturnReduction.verify.isLeft

def callerLocals : Fml Calls [] :=
  dl!{ ⟨ uint x = 17; uint y = 2; uint r = 23; r = diff(x, y); ⟩ (r == 15 ∧ x == 17 ∧ y == 2) }
def callerLocalsReduction : ParameterReduction callerLocals :=
  (programReduction? callerLocals).get (by decide +kernel)

/-- info: true -/
#guard_msgs in #eval callerLocalsReduction.verify.isLeft

def calleePanic : Fml Calls [] := dl!{ [ gate(false); ] true }
def calleePanicReduction : ParameterReduction calleePanic :=
  (programReduction? calleePanic).get (by decide +kernel)

/-- info: true -/
#guard_msgs in #eval calleePanicReduction.verify.isRight

def calleeRevert : Fml Calls [] := dl!{ [ abort(); ] false }
def calleeRevertReduction : ParameterReduction calleeRevert :=
  (programReduction? calleeRevert).get (by decide +kernel)

/-- info: true -/
#guard_msgs in #eval calleeRevertReduction.verify.isLeft

def calleeRevertDiamond : Fml Calls [] := dl!{ ⟨ abort(); ⟩ true }
def calleeRevertDiamondReduction : ParameterReduction calleeRevertDiamond :=
  (programReduction? calleeRevertDiamond).get (by decide +kernel)

/-- info: true -/
#guard_msgs in #eval calleeRevertDiamondReduction.verify.isRight

def failedArgument : Fml Calls [] := dl!{ ⟨ uint r = echo(total - 1); ⟩ true }
def failedArgumentReduction : ParameterReduction failedArgument :=
  (programReduction? failedArgument).get (by decide +kernel)

/-- info: some 0 -/
#guard_msgs in
#eval match failedArgumentReduction.verify with
  | .inl _ => none
  | .inr cm => some (total.read cm.state.storage).val

def wrongResult : Fml Calls [] := dl!{ ∀ uint v; v == 17 → [ uint r = echo(v); ] r == 19 }
def wrongResultRaw : ParameterReduction wrongResult :=
  (programReduction? wrongResult).get (by decide +kernel)

def wrongResultReduction : ParameterReduction wrongResult :=
  wrongResultRaw.withLayout [⟨.uint, 0⟩] [] (by decide +kernel) (by decide +kernel)

/-- info: some 17 -/
#guard_msgs in
#eval match wrongResultReduction.verify with
  | .inl _ => none
  | .inr cm => some (cm.atoms.get .uint 0).val

def wrongResultCountermodel : wrongResultReduction.Countermodel :=
  wrongResultReduction.countermodelOfCheck (⟨17, by decide +kernel⟩, ()) (by decide +kernel)

/-- Calling `echo(17)` returns 17, so the original claim demanding 19 is invalid. -/
theorem wrongResult_invalid : ¬ Valid wrongResult :=
  fun h => wrongResultCountermodel.refutes (h wrongResultCountermodel.state)

example : (ProgramNormalization.ofFormula? 2048 (cspec[Calls]{put})).isSome = true := by
  decide +kernel

/-- info: 'Solidity.Stmt.runSt_callRets' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Stmt.runSt_callRets

/-- info: 'Solidity.Examples.CallReduction.wrongResult_invalid' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms wrongResult_invalid

end Solidity.Examples.CallReduction
