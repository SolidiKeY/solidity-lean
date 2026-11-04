import Solidity.Lowering.V07.EnumSignedWord
import Solidity.Lowering.V07.EnumConversionControls
import Solidity.Lowering.V07.UnsignedCasts

namespace Solidity.Lowering.V07.EnumSignedWordControls
open EnumSignedWord
open WordCasts (signed)
open EnumConversionControls (E d capacity zero two source target mapping BindingRel initial reflect globals)
open Source.SemanticsExamples
open MixedAssignmentControls (C)

def allowed_client := allowed E d
def source_value_client := source_value (D := E.layout) d two

def run_client (p : Roadmap.Pipeline) (checked : Bool) (fuel : Nat) :=
  source_run (globals p) {F0 with checked := checked} (fuel+1) (source zero two) (source zero two)
    d (.local (.there .here)) two rfl
def assignment_client (p : Roadmap.Pipeline) (checked : Bool) (fuel : Nat) :=
  source_assignment (globals p) {F0 with checked := checked} fuel (source zero two)
    d .here (.there .here) two rfl

def value_client := value_run (D := E.layout) (target zero two) d capacity
  (.simple (.local (.there .here))) two rfl
def related_client := value_related (D := E.layout) d two

def transport_client (p : Roadmap.Pipeline) (checked : Bool) (fuel : Nat) :=
  transport (globals p) {F0 with checked := checked} fuel (source zero two) (target zero two)
    d capacity mapping BindingRel (initial zero two) reflect .here (.there .here)
    .here (.there .here) rfl rfl two rfl

def self_client (p : Roadmap.Pipeline) (checked : Bool) (fuel : Nat) :=
  transport (globals p) {F0 with checked := checked} fuel (source zero two) (target zero two)
    d capacity mapping BindingRel (initial zero two) reflect .here .here
    .here .here rfl rfl zero rfl

def equal_client (p : Roadmap.Pipeline) (checked : Bool) (fuel : Nat) :=
  transport (globals p) {F0 with checked := checked} fuel (source two two) (target two two)
    d capacity mapping BindingRel (initial two two) reflect .here (.there .here)
    .here (.there .here) rfl rfl two rfl

def extension_client := DeferredSource.Operand.run_wk
  (WordCasts.assignedToInt .here (.there .here))
  (Thin.drop (t := .val .bool) Thin.refl) (target zero two) (true,(target zero two).env)

def check (p : Roadmap.Pipeline) (checked : Bool) (old rhs : Fin (E.layout.enumSize d)) : Bool :=
  let src := source old rhs
  let tgt := target old rhs
  let expected := signed.wrap rhs.val
  let sr := (Source.evalE (globals p) {F0 with checked := checked} 3
    (.convExplicit (τ := .int signed) (.assign (.local .here) (.local (.there .here))) (allowed E d))).run src
  match sr.1,(WordCasts.assignedToInt .here (.there .here)).run tgt,
    (assignLocalOperand .here (.there .here)).code.run tgt with
  | .ok (.val (.int x _)),.ok (out,.prim v),.ok cap =>
      x == expected && v.val == expected &&
      (sr.2.1.get .here).key == some (rhs.val : Int) &&
      (TEnv.get .here cap.st.env).val == (rhs.val : Int) &&
      (TEnv.get (.there .here) cap.st.env).val == (rhs.val : Int) &&
      (TEnv.get .here out.st.env).val == (rhs.val : Int) &&
      (TEnv.get (.there .here) out.st.env).val == (rhs.val : Int)
  | _,_,_ => false

/-- info: true -/
#guard_msgs in
#eval IO.println (reprStr ([Roadmap.Pipeline.legacy,.viaIR].all fun p =>
  [false,true].all fun checked =>
    [zero,⟨1,by decide⟩,two].all fun old =>
      [zero,⟨1,by decide⟩,two].all fun rhs => check p checked old rhs))

-- Existing mathematical Layout/value fixture, NOT an admitted enum declaration.
def large : Source.Layout where
  fields _ := []
  enumSize _ := 2^256
  underlying _ := .bool
def largeCapacity : large.enumSize d ≤ 2^256 := Nat.le_refl _
def lo : Fin (large.enumSize d) := ⟨0,by decide⟩
def beforeSign : Fin (large.enumSize d) := ⟨2^255-1,by decide⟩
def atSign : Fin (large.enumSize d) := ⟨2^255,by decide⟩
def maximum : Fin (large.enumSize d) := ⟨2^256-1,by decide⟩
def wideTarget (a : Fin (large.enumSize d)) :=
  WordCastControls.target .u256 0 a.val (by decide) (EnumConversions.enum_range d largeCapacity a)
def boundary_client := value_run (D := large) (wideTarget atSign) d largeCapacity
  (.simple (.local (.there .here))) atSign rfl

def highCheck (a : Fin (large.enumSize d)) (expected : Int) : Bool :=
  let tgt := wideTarget a
  let v : Val C EnumConversionControls.TgtCtx .uint := .simple (.local (.there .here))
  let wrong : Val C EnumConversionControls.TgtCtx .int :=
    .unop .toInt rfl rfl (UnsignedCasts.castValue 8 v)
  match (Source.convExplicitVal (.int signed) (.enum a : Source.Val large (.enum d))).map Source.Val.key,
      (WordCasts.assignedToInt .here (.there .here)).run tgt,
      (assignLocalOperand .here (.there .here)).code.run tgt,
      wrong.evalT tgt with
  | .ok src,.ok (out,.prim result),.ok cap,.ok wrongResult =>
      src == some expected && result.val == expected &&
      (TEnv.get .here out.st.env).val == (a.val : Int) &&
      (TEnv.get (.there .here) out.st.env).val == (a.val : Int) &&
      (TEnv.get .here cap.st.env).val == (a.val : Int) &&
      (TEnv.get (.there .here) cap.st.env).val == (a.val : Int) &&
      (if expected < 0 then wrongResult.val != expected else true)
  | _,_,_,_ => false

/-- info: true -/
#guard_msgs in
#eval IO.println (reprStr (highCheck lo 0 && highCheck beforeSign (2^255-1) &&
  highCheck atSign (-(2^255)) && highCheck maximum (-1)))

-- Same-type actual native stale-read control, with different caller/RHS values.
/-- info: true -/
#guard_msgs in
#eval IO.println (reprStr (
  match (WordCasts.assignedToInt .here (.there .here)).run (target zero two),
    (Val.unop .toInt rfl rfl (.simple (.local .here)) : Val C EnumConversionControls.TgtCtx .int).evalT (target zero two) with
  | .ok (out,.prim reached),.ok stale => reached.val == 2 && stale.val == 0 &&
      reached.val != stale.val && (TEnv.get .here out.st.env).val == 2
  | _,_ => false))

/-- info: 'Solidity.Lowering.V07.EnumSignedWordControls.allowed_client' does not depend on any axioms -/
#guard_msgs in
#print axioms Solidity.Lowering.V07.EnumSignedWordControls.allowed_client

/-- info: 'Solidity.Lowering.V07.EnumSignedWordControls.source_value_client' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms Solidity.Lowering.V07.EnumSignedWordControls.source_value_client

/-- info: 'Solidity.Lowering.V07.EnumSignedWordControls.run_client' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Solidity.Lowering.V07.EnumSignedWordControls.run_client

/-- info: 'Solidity.Lowering.V07.EnumSignedWordControls.assignment_client' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms Solidity.Lowering.V07.EnumSignedWordControls.assignment_client

/-- info: 'Solidity.Lowering.V07.EnumSignedWordControls.value_client' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Solidity.Lowering.V07.EnumSignedWordControls.value_client

/-- info: 'Solidity.Lowering.V07.EnumSignedWordControls.related_client' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Solidity.Lowering.V07.EnumSignedWordControls.related_client

/-- info: 'Solidity.Lowering.V07.EnumSignedWordControls.transport_client' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms Solidity.Lowering.V07.EnumSignedWordControls.transport_client

/-- info: 'Solidity.Lowering.V07.EnumSignedWordControls.self_client' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Solidity.Lowering.V07.EnumSignedWordControls.self_client

/-- info: 'Solidity.Lowering.V07.EnumSignedWordControls.equal_client' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Solidity.Lowering.V07.EnumSignedWordControls.equal_client

/-- info: 'Solidity.Lowering.V07.EnumSignedWordControls.extension_client' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms Solidity.Lowering.V07.EnumSignedWordControls.extension_client

/-- info: 'Solidity.Lowering.V07.EnumSignedWordControls.boundary_client' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms Solidity.Lowering.V07.EnumSignedWordControls.boundary_client

end Solidity.Lowering.V07.EnumSignedWordControls
