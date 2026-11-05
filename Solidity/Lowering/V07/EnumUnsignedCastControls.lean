import Solidity.Lowering.V07.EnumUnsignedCasts
import Solidity.Lowering.V07.EnumConversionControls

namespace Solidity.Lowering.V07.EnumUnsignedCastControls
open EnumUnsignedCasts
open UnsignedNarrowing (ty)
open EnumConversionControls (E d capacity zero two source target mapping BindingRel initial reflect globals)
open Source.SemanticsExamples
open MixedAssignmentControls (C)

def allowed_client := allowed E d 8 (by decide)
def source_value_client := source_value (D := E.layout) d 16 (by decide) two

def run_client (p : Roadmap.Pipeline) (checked : Bool) (fuel : Nat) :=
  source_run (globals p) {F0 with checked := checked} (fuel+1) (source zero two) (source zero two)
    d 8 (by decide) (.local (.there .here)) two rfl
def assignment_client (p : Roadmap.Pipeline) (checked : Bool) (fuel : Nat) :=
  source_assignment (globals p) {F0 with checked := checked} fuel (source zero two)
    d 8 (by decide) .here (.there .here) two rfl

def value_client := value_run (D := E.layout) (target zero two) d capacity 8 (by decide)
  (.simple (.local (.there .here))) two rfl
def related_client := value_related (D := E.layout) d 8 (by decide) two

def transport_client (p : Roadmap.Pipeline) (checked : Bool) (fuel : Nat) :=
  transport (globals p) {F0 with checked := checked} fuel (source zero two) (target zero two)
    d capacity 8 (by decide) mapping BindingRel (initial zero two) reflect .here (.there .here)
    .here (.there .here) rfl rfl two rfl

def self_client (p : Roadmap.Pipeline) (checked : Bool) (fuel : Nat) :=
  transport (globals p) {F0 with checked := checked} fuel (source zero two) (target zero two)
    d capacity 8 (by decide) mapping BindingRel (initial zero two) reflect .here .here
    .here .here rfl rfl zero rfl

def equal_client (p : Roadmap.Pipeline) (checked : Bool) (fuel : Nat) :=
  transport (globals p) {F0 with checked := checked} fuel (source two two) (target two two)
    d capacity 8 (by decide) mapping BindingRel (initial two two) reflect .here (.there .here)
    .here (.there .here) rfl rfl two rfl

def extension_client := DeferredSource.Operand.run_wk
  (UnsignedCasts.assignedOperand 8 .here (.there .here))
  (Thin.drop (t := .val .bool) Thin.refl) (target zero two) (true,(target zero two).env)

def check (bits : Nat) (width : bits % 8 = 0 ∧ 8 ≤ bits ∧ bits ≤ 256)
    (p : Roadmap.Pipeline) (checked : Bool) (old rhs : Fin (E.layout.enumSize d)) : Bool :=
  let src := source old rhs
  let tgt := target old rhs
  let expected := (ty bits width).wrap rhs.val
  let sr := (Source.evalE (globals p) {F0 with checked := checked} 3
    (.convExplicit (τ := .int (ty bits width)) (.assign (.local .here) (.local (.there .here))) (allowed E d bits width))).run src
  match sr.1,(UnsignedCasts.assignedOperand bits .here (.there .here)).run tgt,
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
#eval IO.println (reprStr ((List.range 257).all fun bits =>
  if width : bits % 8 = 0 ∧ 8 ≤ bits ∧ bits ≤ 256 then
    [Roadmap.Pipeline.legacy,.viaIR].all fun p => [false,true].all fun checked =>
      [zero,⟨1,by decide⟩,two].all fun old => [zero,⟨1,by decide⟩,two].all fun rhs => check bits width p checked old rhs
  else true))

-- Existing Layout/value counterexample only: no admission of a 257-member
-- Source enum or raw literal is claimed. Result truncation is not injective.
def large : Source.Layout where
  fields _ := []
  enumSize _ := 257
  underlying _ := .bool
def largeCapacity : large.enumSize d ≤ 2^256 := by decide
def i0 : Fin (large.enumSize d) := ⟨0,by decide⟩
def i256 : Fin (large.enumSize d) := ⟨256,by decide⟩
def wideTarget := WordCastControls.target .u256 0 256 (by decide) (by decide)
def narrowing_client := value_run (D := large) wideTarget d largeCapacity 8 (by decide)
  (.simple (.local (.there .here))) i256 rfl

-- Wrong code narrows the caller binding, rather than just the return value.
def wrong : DeferredSource.Operand C EnumConversionControls.TgtCtx (.prim .uint) :=
  ⟨_,.cons (.assignLocal .here (UnsignedCasts.castValue 8 (.simple (.local (.there .here)))))
    (.cons (.declLocal .uint (.user "v07_wrong_enum") (some (.simple (.local .here)))) .nil),
    .val (.simple (.local .here))⟩
def negativeCheck : Bool :=
  match (Source.convExplicitVal (.int (ty 8 (by decide))) (.enum i0 : Source.Val large (.enum d))).map Source.Val.key,
        (Source.convExplicitVal (.int (ty 8 (by decide))) (.enum i256 : Source.Val large (.enum d))).map Source.Val.key,
        (UnsignedCasts.assignedOperand 8 .here (.there .here)).run wideTarget,wrong.run wideTarget,
        (assignLocalOperand .here (.there .here)).run wideTarget with
  | .ok a,.ok b,.ok (out,.prim v),.ok (bad,.prim w),.ok (_, .prim omitted) =>
      a == some 0 && b == some 0 && i0.val != i256.val && v.val == 0 && w.val == 0 && omitted.val == 256 &&
      (TEnv.get .here out.st.env).val == 256 && (TEnv.get .here bad.st.env).val == 0
  | _,_,_,_,_ => false

/-- info: true -/
#guard_msgs in
#eval IO.println (reprStr negativeCheck)

/-- info: 'Solidity.Lowering.V07.EnumUnsignedCastControls.allowed_client' does not depend on any axioms -/
#guard_msgs in
#print axioms Solidity.Lowering.V07.EnumUnsignedCastControls.allowed_client

/-- info: 'Solidity.Lowering.V07.EnumUnsignedCastControls.source_value_client' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms Solidity.Lowering.V07.EnumUnsignedCastControls.source_value_client

/-- info: 'Solidity.Lowering.V07.EnumUnsignedCastControls.run_client' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Solidity.Lowering.V07.EnumUnsignedCastControls.run_client

/-- info: 'Solidity.Lowering.V07.EnumUnsignedCastControls.assignment_client' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms Solidity.Lowering.V07.EnumUnsignedCastControls.assignment_client

/-- info: 'Solidity.Lowering.V07.EnumUnsignedCastControls.value_client' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Solidity.Lowering.V07.EnumUnsignedCastControls.value_client

/-- info: 'Solidity.Lowering.V07.EnumUnsignedCastControls.related_client' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms Solidity.Lowering.V07.EnumUnsignedCastControls.related_client

/-- info: 'Solidity.Lowering.V07.EnumUnsignedCastControls.transport_client' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms Solidity.Lowering.V07.EnumUnsignedCastControls.transport_client

/-- info: 'Solidity.Lowering.V07.EnumUnsignedCastControls.self_client' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Solidity.Lowering.V07.EnumUnsignedCastControls.self_client

/-- info: 'Solidity.Lowering.V07.EnumUnsignedCastControls.equal_client' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Solidity.Lowering.V07.EnumUnsignedCastControls.equal_client

/-- info: 'Solidity.Lowering.V07.EnumUnsignedCastControls.extension_client' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms Solidity.Lowering.V07.EnumUnsignedCastControls.extension_client

/-- info: 'Solidity.Lowering.V07.EnumUnsignedCastControls.narrowing_client' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms Solidity.Lowering.V07.EnumUnsignedCastControls.narrowing_client

end Solidity.Lowering.V07.EnumUnsignedCastControls
