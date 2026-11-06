import Solidity.Lowering.V07.EnumGuard
import Solidity.Lowering.V07.EnumConversionControls

namespace Solidity.Lowering.V07.EnumGuardControls
open EnumGuard
open EnumConversionControls (E d capacity globals ints int_initial)
open Source.SemanticsExamples
open MixedAssignmentControls (C)

def tgt := WordCastControls.target .u256 0 2 (by decide) (by decide)
def bad := WordCastControls.target .u256 0 3 (by decide) (by decide)
def word_client := word_range (integerValue .u256 WordCastControls.umax (by decide))
def condition_client := condition_run tgt (E.layout.enumSize d) capacity (.there .here)
  (integerValue .u256 2 (by decide)) rfl

def success_guard_client := guard_success tgt (E.layout.enumSize d) capacity (.there .here)
  (integerValue .u256 2 (by decide)) rfl (by decide)
def failure_guard_client := guard_failure bad (E.layout.enumSize d) capacity (.there .here)
  (integerValue .u256 3 (by decide)) rfl (by decide)
def assignment_client := assignment_run tgt .here (.there .here) (integerValue .u256 2 (by decide)) rfl

def code_success_client := code_success tgt (E.layout.enumSize d) capacity .here (.there .here)
  (integerValue .u256 2 (by decide)) rfl (by decide)
def code_failure_client := code_failure bad (E.layout.enumSize d) capacity .here (.there .here)
  (integerValue .u256 3 (by decide)) rfl (by decide)
def operand_success_client := operand_success tgt (E.layout.enumSize d) capacity .here (.there .here)
  (integerValue .u256 2 (by decide)) rfl (by decide)
def operand_failure_client := operand_failure bad (E.layout.enumSize d) capacity .here (.there .here)
  (integerValue .u256 3 (by decide)) rfl (by decide)

def success_transport_client (p : Roadmap.Pipeline) (checked : Bool) (fuel : Nat) :=
  transport_success (globals p) {F0 with checked := checked} fuel (ints 0 2 (by decide) (by decide)) tgt
    d capacity (WordCastControls.si .u256) (WordCastControls.ti .u256) (int_initial 0 2 (by decide) (by decide))
    true false 2 (by decide) (by decide) rfl
def failure_transport_client (p : Roadmap.Pipeline) (checked : Bool) (fuel : Nat) :=
  transport_failure (globals p) {F0 with checked := checked} fuel (ints 0 3 (by decide) (by decide)) bad
    d capacity (WordCastControls.si .u256) (WordCastControls.ti .u256) (int_initial 0 3 (by decide) (by decide))
    true false 3 (by decide) (by decide) rfl

def self_client (p : Roadmap.Pipeline) (checked : Bool) (fuel : Nat) :=
  transport_success (globals p) {F0 with checked := checked} fuel (ints 0 2 (by decide) (by decide)) tgt
    d capacity (WordCastControls.si .u256) (WordCastControls.ti .u256) (int_initial 0 2 (by decide) (by decide))
    false false 2 (by decide) (by decide) rfl

def equal_client (p : Roadmap.Pipeline) (checked : Bool) (fuel : Nat) :=
  transport_success (globals p) {F0 with checked := checked} fuel (ints 2 2 (by decide) (by decide))
    (WordCastControls.target .u256 2 2 (by decide) (by decide))
    d capacity (WordCastControls.si .u256) (WordCastControls.ti .u256) (int_initial 2 2 (by decide) (by decide))
    true false 2 (by decide) (by decide) rfl

def extension_client := DeferredSource.Operand.run_wk
  (operand (E.layout.enumSize d) capacity .here (.there .here))
  (Thin.drop (t := .val .bool) Thin.refl) tgt (true,tgt.env)

-- Actual zero/full capacity branches; these native witnesses do not assert
-- Source admission of empty or word-sized enum declarations.
def zero_client := guard_failure tgt 0 (by decide) .here (integerValue .u256 0 (by decide)) rfl (by decide)
def full_client := guard_success tgt (2^256) (by omega) (.there .here)
  (integerValue .u256 2 (by decide)) rfl (by decide)

def check (p : Roadmap.Pipeline) (checked : Bool) (old rhs : Nat)
    (oldBound : old < 2^256) (rhsBound : rhs < 2^256) : Bool := Id.run do
  have ho : Source.IntTy.u256.lo ≤ (old : Int) ∧ (old : Int) ≤ Source.IntTy.u256.hi := by
    change 0 ≤ (old : Int) ∧ (old : Int) ≤ ((2^256-1 : Nat) : Int); omega
  have hr : Source.IntTy.u256.lo ≤ (rhs : Int) ∧ (rhs : Int) ≤ Source.IntTy.u256.hi := by
    change 0 ≤ (rhs : Int) ∧ (rhs : Int) ≤ ((2^256-1 : Nat) : Int); omega
  let src := ints old rhs ho hr
  let tgt := WordCastControls.target .u256 old rhs ho hr
  let sr := (Source.evalE (globals p) {F0 with checked := checked} 3
    (.convExplicit (τ := .enum d) (.assign (.local .here) (.local (.there .here))) (EnumConversions.allowed_from E d))).run src
  let native := (operand (E.layout.enumSize d) capacity .here (.there .here)).run tgt
  let assignmentResult := (Stmt.assignLocal .here (.simple (.local (.there .here)))).run tgt
  match assignmentResult with
  | .error _ => return false
  | .ok reached =>
    if rhs < 3 then
      match sr.1,native,(code (E.layout.enumSize d) capacity .here (.there .here)).run tgt with
      | .ok (.val (.enum a)),.ok (out,.prim v),.ok captured =>
        return a.val == rhs && v.val == (rhs : Int) &&
          (sr.2.1.get .here).key == some (rhs : Int) &&
          (TEnv.get .here reached.st.env).val == (rhs : Int) &&
          (TEnv.get .here captured.st.env).val == (rhs : Int) &&
          (TEnv.get (.there .here) captured.st.env).val == (rhs : Int) &&
          (TEnv.get .here out.st.env).val == (rhs : Int) &&
          (TEnv.get (.there .here) out.st.env).val == (rhs : Int)
      | _,_,_ => return false
    else
      match sr.1,native with
      | .error (.revert payload),.error halt =>
        return (payload == Source.panicData .enumConv &&
          payload != Source.panicData .arithmetic && halt == THalt.ofData payload &&
          (sr.2.1.get .here).key == some (rhs : Int) &&
          (TEnv.get .here reached.st.env).val == (rhs : Int))
      | _,_ => return false

/-- info: true -/
#guard_msgs in
#eval IO.println (reprStr ([Roadmap.Pipeline.legacy,.viaIR].all fun p => [false,true].all fun checked =>
  [0,1,2,3,255].all fun old => [0,1,2,3,255].all fun rhs =>
    if ho : old < 2^256 then if hr : rhs < 2^256 then check p checked old rhs ho hr else false else false))

-- A guard before the assignment sees old0 and incorrectly accepts assigned3.
def earlyCode : Prog C EnumConversionControls.TgtCtx (.val .uint :: EnumConversionControls.TgtCtx) := Prog.cons (guard (E.layout.enumSize d) capacity (.here : Idx EnumConversionControls.TgtCtx (.val .uint)))
  (assignLocalOperand .here (.there .here)).code
def early : DeferredSource.Operand C EnumConversionControls.TgtCtx (.prim .uint) :=
  ⟨_,earlyCode,.val (.simple (.local .here))⟩
/-- info: true -/
#guard_msgs in
#eval IO.println (reprStr (
  match (operand (E.layout.enumSize d) capacity .here (.there .here)).run bad,early.run bad with
  | .error halt,.ok (_, .prim v) => halt == THalt.ofData (Source.panicData .enumConv) && v.val == 3
  | _,_ => false))

-- Full native-word capacity must not be encoded as the wrapped bound0.
def maxTarget := WordCastControls.target .u256 0 WordCastControls.umax (by decide) (by decide)
/-- info: true -/
#guard_msgs in
#eval IO.println (reprStr (
  match (operand (2^256) (by omega) .here (.there .here)).run maxTarget,
        (operand 0 (by decide) .here (.there .here)).run maxTarget with
  | .ok (_, .prim v),.error halt => v.val == WordCastControls.umax &&
      halt == THalt.ofData (Source.panicData .enumConv)
  | _,_ => false))
end Solidity.Lowering.V07.EnumGuardControls

/-- info: 'Solidity.Lowering.V07.EnumGuardControls.word_client' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Solidity.Lowering.V07.EnumGuardControls.word_client

/-- info: 'Solidity.Lowering.V07.EnumGuardControls.condition_client' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Solidity.Lowering.V07.EnumGuardControls.condition_client

/-- info: 'Solidity.Lowering.V07.EnumGuardControls.success_guard_client' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms Solidity.Lowering.V07.EnumGuardControls.success_guard_client

/-- info: 'Solidity.Lowering.V07.EnumGuardControls.failure_guard_client' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms Solidity.Lowering.V07.EnumGuardControls.failure_guard_client

/-- info: 'Solidity.Lowering.V07.EnumGuardControls.assignment_client' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Solidity.Lowering.V07.EnumGuardControls.assignment_client

/-- info: 'Solidity.Lowering.V07.EnumGuardControls.code_success_client' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Solidity.Lowering.V07.EnumGuardControls.code_success_client

/-- info: 'Solidity.Lowering.V07.EnumGuardControls.code_failure_client' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Solidity.Lowering.V07.EnumGuardControls.code_failure_client

/-- info: 'Solidity.Lowering.V07.EnumGuardControls.operand_success_client' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms Solidity.Lowering.V07.EnumGuardControls.operand_success_client

/-- info: 'Solidity.Lowering.V07.EnumGuardControls.operand_failure_client' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms Solidity.Lowering.V07.EnumGuardControls.operand_failure_client

/-- info: 'Solidity.Lowering.V07.EnumGuardControls.success_transport_client' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms Solidity.Lowering.V07.EnumGuardControls.success_transport_client

/-- info: 'Solidity.Lowering.V07.EnumGuardControls.failure_transport_client' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms Solidity.Lowering.V07.EnumGuardControls.failure_transport_client

/-- info: 'Solidity.Lowering.V07.EnumGuardControls.self_client' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Solidity.Lowering.V07.EnumGuardControls.self_client

/-- info: 'Solidity.Lowering.V07.EnumGuardControls.equal_client' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Solidity.Lowering.V07.EnumGuardControls.equal_client

/-- info: 'Solidity.Lowering.V07.EnumGuardControls.extension_client' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Solidity.Lowering.V07.EnumGuardControls.extension_client

/-- info: 'Solidity.Lowering.V07.EnumGuardControls.zero_client' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Solidity.Lowering.V07.EnumGuardControls.zero_client

/-- info: 'Solidity.Lowering.V07.EnumGuardControls.full_client' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Solidity.Lowering.V07.EnumGuardControls.full_client
