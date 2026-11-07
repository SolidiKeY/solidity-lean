import Solidity.Lowering.V07.UnsignedEnumGuard
import Solidity.Lowering.V07.EnumGuardControls

namespace Solidity.Lowering.V07.UnsignedEnumGuardControls
open UnsignedEnumGuard
open UnsignedNarrowing (ty)
open Source.SemanticsExamples
open EnumConversionControls (E d capacity globals)
open MixedAssignmentControls (C path)

def source (bits : Nat) (width : bits % 8 = 0 ∧ 8 ≤ bits ∧ bits ≤ 256) (x y : Int)
    (hx : (ty bits width).lo ≤ x ∧ x ≤ (ty bits width).hi)
    (hy : (ty bits width).lo ≤ y ∧ y ≤ (ty bits width).hi) :
    Source.EMState E [.int (ty bits width),.int (ty bits width),.bytes .memory,.bytes .storage] :=
  (.cons (.int x hx) (.cons (.int y hy) (.cons (.memRef rfl 0) (.cons (.storRef rfl path) .nil))),
    (EnumConversionControls.ints 0 2 (by decide) (by decide)).2)

theorem initial (bits : Nat) (width : bits % 8 = 0 ∧ 8 ≤ bits ∧ bits ≤ 256) (x y : Int)
    (hx : (ty bits width).lo ≤ x ∧ x ≤ (ty bits width).hi)
    (hy : (ty bits width).lo ≤ y ∧ y ≤ (ty bits width).hi) :
    IntegerLocalFamily (ty bits width) (WordCastControls.si (ty bits width)) (WordCastControls.ti (ty bits width))
      (source bits width x y hx hy).1 (WordCastControls.target (ty bits width) x y hx hy).env := by
  refine ⟨?_,?_⟩
  · intro k
    cases k <;> exact integer_related (ty bits width) _ _
  · intro k l
    cases k <;> cases l <;> rfl

def word_client := word_value 8 (by decide) 255 (by decide)
def bridge_client := value_bridge (D := E.layout) d 16 (by decide) 2 (by decide)
def allowed_client := allowed E d 8 (by decide)
def value_client := source_value (D := E.layout) d 8 (by decide) 2 (by decide) (by decide)
def failed_value_client := source_value_failure (D := E.layout) d 8 (by decide) 255 (by decide) (by decide)
def related_client := enum_related (D := E.layout) d 8 (by decide) 2 (by decide) (by decide)

def src := source 8 (by decide) 0 2 (by decide) (by decide)
def tgt := WordCastControls.target (ty 8 (by decide)) 0 2 (by decide) (by decide)
def badSrc := source 8 (by decide) 0 3 (by decide) (by decide)
def badTgt := WordCastControls.target (ty 8 (by decide)) 0 3 (by decide) (by decide)

def run_client (p : Roadmap.Pipeline) (checked : Bool) (fuel : Nat) :=
  source_run (globals p) {F0 with checked := checked} (fuel+1) src src d 8 (by decide)
    (.local (.there .here)) 2 (by decide) (by decide) rfl
def failed_run_client (p : Roadmap.Pipeline) (checked : Bool) (fuel : Nat) :=
  source_failed_run (globals p) {F0 with checked := checked} (fuel+1) badSrc badSrc d 8 (by decide)
    (.local (.there .here)) 3 (by decide) (by decide) rfl

def success_client (p : Roadmap.Pipeline) (checked : Bool) (fuel : Nat) :=
  transport_success (globals p) {F0 with checked := checked} fuel src tgt d capacity 8 (by decide)
    (WordCastControls.si (ty 8 (by decide))) (WordCastControls.ti (ty 8 (by decide)))
    (initial 8 (by decide) 0 2 (by decide) (by decide)) true false 2 (by decide) (by decide) rfl

def failure_client (p : Roadmap.Pipeline) (checked : Bool) (fuel : Nat) :=
  transport_failure (globals p) {F0 with checked := checked} fuel badSrc badTgt d capacity 8 (by decide)
    (WordCastControls.si (ty 8 (by decide))) (WordCastControls.ti (ty 8 (by decide)))
    (initial 8 (by decide) 0 3 (by decide) (by decide)) true false 3 (by decide) (by decide) rfl

def self_failure_client (p : Roadmap.Pipeline) (checked : Bool) (fuel : Nat) :=
  transport_failure (globals p) {F0 with checked := checked} fuel badSrc badTgt d capacity 8 (by decide)
    (WordCastControls.si (ty 8 (by decide))) (WordCastControls.ti (ty 8 (by decide)))
    (initial 8 (by decide) 0 3 (by decide) (by decide)) false false 3 (by decide) (by decide) rfl

def equal_client (p : Roadmap.Pipeline) (checked : Bool) (fuel : Nat) :=
  transport_success (globals p) {F0 with checked := checked} fuel
    (source 8 (by decide) 2 2 (by decide) (by decide))
    (WordCastControls.target (ty 8 (by decide)) 2 2 (by decide) (by decide)) d capacity 8 (by decide)
    (WordCastControls.si (ty 8 (by decide))) (WordCastControls.ti (ty 8 (by decide)))
    (initial 8 (by decide) 2 2 (by decide) (by decide)) true false 2 (by decide) (by decide) rfl

def extension_client := DeferredSource.Operand.run_wk
  (EnumGuard.operand (E.layout.enumSize d) capacity .here (.there .here))
  (Thin.drop (t := .val .bool) Thin.refl) tgt (true,tgt.env)

-- Typed input construction only, not literal-admission evidence. All tested
-- values0..255 and each width maximum fit the declared width; observations
-- check that construction did not truncate them.
def check (bits : Nat) (width : bits % 8 = 0 ∧ 8 ≤ bits ∧ bits ≤ 256)
    (p : Roadmap.Pipeline) (checked : Bool) (old rhs : Int) : Bool := Id.run do
  let x := (ty bits width).wrap old
  let y := (ty bits width).wrap rhs
  let src := source bits width x y ((ty bits width).wrap_mem old) ((ty bits width).wrap_mem rhs)
  let tgt := WordCastControls.target (ty bits width) x y ((ty bits width).wrap_mem old) ((ty bits width).wrap_mem rhs)
  let sr := (Source.evalE (globals p) {F0 with checked := checked} 3
    (.convExplicit (τ := .enum d) (.assign (.local .here) (.local (.there .here))) (allowed E d bits width))).run src
  let native := (EnumGuard.operand (E.layout.enumSize d) capacity .here (.there .here)).run tgt
  let reached := (Stmt.assignLocal .here (.simple (.local (.there .here)))).run tgt
  match reached with
  | .error _ => return false
  | .ok assigned =>
    if rhs < 3 then
      match sr.1,native,(EnumGuard.code (E.layout.enumSize d) capacity .here (.there .here)).run tgt with
      | .ok (.val (.enum a)),.ok (out,.prim v),.ok cap =>
        return a.val == rhs.toNat && v.val == rhs && x == old && y == rhs &&
          (sr.2.1.get .here).key == some rhs && (TEnv.get .here assigned.st.env).val == rhs &&
          (TEnv.get .here cap.st.env).val == rhs && (TEnv.get (.there .here) cap.st.env).val == rhs &&
          (TEnv.get .here out.st.env).val == rhs && (TEnv.get (.there .here) out.st.env).val == rhs
      | _,_,_ => return false
    else
      match sr.1,native with
      | .error (.revert payload),.error halt =>
        return (x == old && y == rhs && payload == Source.panicData .enumConv &&
          payload != Source.panicData .arithmetic && halt == THalt.ofData payload &&
          (sr.2.1.get .here).key == some rhs && (TEnv.get .here assigned.st.env).val == rhs)
      | _,_ => return false

/-- info: true -/
#guard_msgs in
#eval IO.println (reprStr ((List.range 257).all fun bits =>
  if width : bits % 8 = 0 ∧ 8 ≤ bits ∧ bits ≤ 256 then
    [Roadmap.Pipeline.legacy,.viaIR].all fun p => [false,true].all fun checked =>
      [0,1,2,3,255,(ty bits width).hi].all fun old =>
        [0,1,2,3,255,(ty bits width).hi].all fun rhs => check bits width p checked old rhs
  else true))

-- Width8 counterexample: omitting the guard wrongly succeeds with canonical255.
/-- info: true -/
#guard_msgs in
#eval IO.println (reprStr (
  let target := WordCastControls.target (ty 8 (by decide)) 0 255 (by decide) (by decide)
  match (EnumGuard.operand (E.layout.enumSize d) capacity .here (.there .here)).run target,
        (assignLocalOperand .here (.there .here)).run target with
  | .error halt,.ok (_, .prim v) => halt == THalt.ofData (Source.panicData .enumConv) && v.val == 255
  | _,_ => false))
end Solidity.Lowering.V07.UnsignedEnumGuardControls

/-- info: 'Solidity.Lowering.V07.UnsignedEnumGuardControls.initial' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Solidity.Lowering.V07.UnsignedEnumGuardControls.initial

/-- info: 'Solidity.Lowering.V07.UnsignedEnumGuardControls.word_client' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Solidity.Lowering.V07.UnsignedEnumGuardControls.word_client

/-- info: 'Solidity.Lowering.V07.UnsignedEnumGuardControls.bridge_client' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms Solidity.Lowering.V07.UnsignedEnumGuardControls.bridge_client

/-- info: 'Solidity.Lowering.V07.UnsignedEnumGuardControls.allowed_client' does not depend on any axioms -/
#guard_msgs in
#print axioms Solidity.Lowering.V07.UnsignedEnumGuardControls.allowed_client

/-- info: 'Solidity.Lowering.V07.UnsignedEnumGuardControls.value_client' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms Solidity.Lowering.V07.UnsignedEnumGuardControls.value_client

/-- info: 'Solidity.Lowering.V07.UnsignedEnumGuardControls.failed_value_client' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms Solidity.Lowering.V07.UnsignedEnumGuardControls.failed_value_client

/-- info: 'Solidity.Lowering.V07.UnsignedEnumGuardControls.related_client' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms Solidity.Lowering.V07.UnsignedEnumGuardControls.related_client

/-- info: 'Solidity.Lowering.V07.UnsignedEnumGuardControls.run_client' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Solidity.Lowering.V07.UnsignedEnumGuardControls.run_client

/-- info: 'Solidity.Lowering.V07.UnsignedEnumGuardControls.failed_run_client' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms Solidity.Lowering.V07.UnsignedEnumGuardControls.failed_run_client

/-- info: 'Solidity.Lowering.V07.UnsignedEnumGuardControls.success_client' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms Solidity.Lowering.V07.UnsignedEnumGuardControls.success_client

/-- info: 'Solidity.Lowering.V07.UnsignedEnumGuardControls.failure_client' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms Solidity.Lowering.V07.UnsignedEnumGuardControls.failure_client

/-- info: 'Solidity.Lowering.V07.UnsignedEnumGuardControls.self_failure_client' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms Solidity.Lowering.V07.UnsignedEnumGuardControls.self_failure_client

/-- info: 'Solidity.Lowering.V07.UnsignedEnumGuardControls.equal_client' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms Solidity.Lowering.V07.UnsignedEnumGuardControls.equal_client

/-- info: 'Solidity.Lowering.V07.UnsignedEnumGuardControls.extension_client' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms Solidity.Lowering.V07.UnsignedEnumGuardControls.extension_client
