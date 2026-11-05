import Solidity.Lowering.V07.SignedEnumTransport
import Solidity.Lowering.V07.EnumGuardControls

namespace Solidity.Lowering.V07.SignedEnumControls
open SignedEnumTransport
open SignedWidthCasts (ty)
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

def word_client := word_value 8 (by decide) (-1) (by decide)
def allowed_client := allowed E d 8 (by decide)
def value_client := source_value (D := E.layout) d 8 (by decide) 2 (by decide) (by decide)
def failed_value_client := source_value_failure (D := E.layout) d 8 (by decide) (-1) (by decide) (by decide)
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
  (SignedEnumGuard.operand (E.layout.enumSize d) capacity .here (.there .here))
  (Thin.drop (t := .val .bool) Thin.refl) tgt (true,tgt.env)

-- Typed inputs only, not literal-admission evidence. Observations ensure
-- negative values and each signed-width extremum were not truncated away.
def check (bits : Nat) (width : bits % 8 = 0 ∧ 8 ≤ bits ∧ bits ≤ 256)
    (p : Roadmap.Pipeline) (checked : Bool) (old rhs : Int) : Bool := Id.run do
  let x := (ty bits width).wrap old
  let y := (ty bits width).wrap rhs
  let src := source bits width x y ((ty bits width).wrap_mem old) ((ty bits width).wrap_mem rhs)
  let tgt := WordCastControls.target (ty bits width) x y ((ty bits width).wrap_mem old) ((ty bits width).wrap_mem rhs)
  let sr := (Source.evalE (globals p) {F0 with checked := checked} 3
    (.convExplicit (τ := .enum d) (.assign (.local .here) (.local (.there .here))) (allowed E d bits width))).run src
  let native := (SignedEnumGuard.operand (E.layout.enumSize d) capacity .here (.there .here)).run tgt
  let reached := (Stmt.assignLocal .here (.simple (.local (.there .here)))).run tgt
  match reached with
  | .error _ => return false
  | .ok assigned =>
    if 0 ≤ rhs ∧ rhs < 3 then
      match sr.1,native,(SignedEnumGuard.code (E.layout.enumSize d) capacity .here (.there .here)).run tgt with
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
      [0,1,2,3,-1,(ty bits width).lo,(ty bits width).hi].all fun old =>
        [0,1,2,3,-1,(ty bits width).lo,(ty bits width).hi].all fun rhs => check bits width p checked old rhs
  else true))


def negSrc := source 8 (by decide) 0 (-1) (by decide) (by decide)
def negTgt := WordCastControls.target (ty 8 (by decide)) 0 (-1) (by decide) (by decide)
def negative_client (p : Roadmap.Pipeline) (checked : Bool) (fuel : Nat) :=
  transport_failure (globals p) {F0 with checked := checked} fuel negSrc negTgt d capacity 8 (by decide)
    (WordCastControls.si (ty 8 (by decide))) (WordCastControls.ti (ty 8 (by decide)))
    (initial 8 (by decide) 0 (-1) (by decide) (by decide)) true false (-1) (by decide) (by decide) rfl

def wordTarget := WordCastControls.target WordCasts.signed 0 2 (by decide) (by decide)
def negativeWordTarget := WordCastControls.target WordCasts.signed 0 (-1) (by decide) (by decide)
def uint_range_client := SignedEnumGuard.uint_range 2 (by decide) (by decide)
def condition_client := SignedEnumGuard.condition_run wordTarget (.there .here) 2 (by decide) rfl
def guard_client := SignedEnumGuard.guard_success wordTarget (.there .here) 2 (by decide) rfl (by decide)
def guard_negative_client := SignedEnumGuard.guard_negative negativeWordTarget (.there .here) (-1) (by decide) rfl (by decide)
def cast_client := SignedEnumGuard.cast_run wordTarget (.there .here) 2 (by decide) rfl (by decide)
def assignment_client := SignedEnumGuard.assignment_run wordTarget .here (.there .here) 2 (by decide) rfl
def capture_client := SignedEnumGuard.capture_run wordTarget (.there .here) 2 (by decide) rfl (by decide)
def code_client := SignedEnumGuard.code_success wordTarget 3 (by decide) .here (.there .here) 2 (by decide) rfl (by decide)
def code_failure_client := SignedEnumGuard.code_failure negativeWordTarget 3 (by decide) .here (.there .here) (-1) (by decide) rfl (by decide)
def operand_client := SignedEnumGuard.operand_success wordTarget 3 (by decide) .here (.there .here) 2 (by decide) rfl (by decide)
def operand_failure_client := SignedEnumGuard.operand_failure negativeWordTarget 3 (by decide) .here (.there .here) (-1) (by decide) rfl (by decide)

-- Deliberately wrong typed native code: signedness check omitted.
def missingSign {Γ : Ctx} (count : Nat) (cap : count ≤ 2^256) (i r : Idx Γ (.val .int)) :
    DeferredSource.Operand C Γ (.prim .uint) :=
  ⟨_,.cons (.assignLocal i (.simple (.local r)))
    (.cons (.declLocal .uint (.user "v07_wrong_sign") (some (.unop .toUint rfl rfl (.simple (.local i)))))
      (.cons (EnumGuard.guard count cap .here) .nil)),.val (.simple (.local .here))⟩
-- Mathematical full-capacity Layout only; no declaration admission is claimed.
def full : Source.Layout where
  fields _ := []
  enumSize _ := 2^256
  underlying _ := .bool
/-- info: true -/
#guard_msgs in
#eval IO.println (reprStr (
  match Source.convExplicitVal (.enum d) (.int (-1) (by decide) : Source.Val full (.int (ty 8 (by decide)))),
    (SignedEnumGuard.operand (2^256) (Nat.le_refl _) .here (.there .here)).run negativeWordTarget,
    (missingSign (2^256) (Nat.le_refl _) .here (.there .here)).run negativeWordTarget with
  | .error (.revert payload),.error halt,.ok (out,.prim wrong) =>
      payload == Source.panicData .enumConv && halt == THalt.ofData payload &&
      wrong.val == Semantics.uintBound-1 && (TEnv.get .here out.st.env).val == -1
  | _,_,_ => false))

-- Deliberately wrong order checks stale caller before assigning positive RHS.
def staleCheck {Γ : Ctx} (count : Nat) (cap : count ≤ 2^256) (i r : Idx Γ (.val .int)) :
    Prog C Γ (.val .uint :: Γ) :=
  .cons (SignedEnumGuard.guard i) (SignedEnumGuard.code count cap i r)
/-- info: true -/
#guard_msgs in
#eval IO.println (reprStr (
  let target := WordCastControls.target WordCasts.signed (-1) 2 (by decide) (by decide)
  match (SignedEnumGuard.operand 3 (by decide) .here (.there .here)).run target,
    (staleCheck 3 (by decide) .here (.there .here)).run target with
  | .ok (out,.prim reached),.error halt => reached.val == 2 &&
      (TEnv.get .here out.st.env).val == 2 && halt == THalt.ofData (Source.panicData .enumConv)
  | _,_ => false))

/-- info: true -/
#guard_msgs in
#eval IO.println (reprStr (
  let target := WordCastControls.target WordCasts.signed 0 0 (by decide) (by decide)
  match (SignedEnumGuard.operand 0 (by decide) .here (.there .here)).run target with
  | .error halt => halt == THalt.ofData (Source.panicData .enumConv)
  | _ => false))

/-- info: 'Solidity.Lowering.V07.SignedEnumControls.initial' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Solidity.Lowering.V07.SignedEnumControls.initial

/-- info: 'Solidity.Lowering.V07.SignedEnumControls.word_client' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Solidity.Lowering.V07.SignedEnumControls.word_client

/-- info: 'Solidity.Lowering.V07.SignedEnumControls.allowed_client' does not depend on any axioms -/
#guard_msgs in
#print axioms Solidity.Lowering.V07.SignedEnumControls.allowed_client

/-- info: 'Solidity.Lowering.V07.SignedEnumControls.value_client' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Solidity.Lowering.V07.SignedEnumControls.value_client

/-- info: 'Solidity.Lowering.V07.SignedEnumControls.failed_value_client' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms Solidity.Lowering.V07.SignedEnumControls.failed_value_client

/-- info: 'Solidity.Lowering.V07.SignedEnumControls.related_client' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Solidity.Lowering.V07.SignedEnumControls.related_client

/-- info: 'Solidity.Lowering.V07.SignedEnumControls.run_client' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Solidity.Lowering.V07.SignedEnumControls.run_client

/-- info: 'Solidity.Lowering.V07.SignedEnumControls.failed_run_client' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Solidity.Lowering.V07.SignedEnumControls.failed_run_client

/-- info: 'Solidity.Lowering.V07.SignedEnumControls.success_client' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Solidity.Lowering.V07.SignedEnumControls.success_client

/-- info: 'Solidity.Lowering.V07.SignedEnumControls.failure_client' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Solidity.Lowering.V07.SignedEnumControls.failure_client

/-- info: 'Solidity.Lowering.V07.SignedEnumControls.self_failure_client' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms Solidity.Lowering.V07.SignedEnumControls.self_failure_client

/-- info: 'Solidity.Lowering.V07.SignedEnumControls.equal_client' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Solidity.Lowering.V07.SignedEnumControls.equal_client

/-- info: 'Solidity.Lowering.V07.SignedEnumControls.extension_client' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Solidity.Lowering.V07.SignedEnumControls.extension_client

/-- info: 'Solidity.Lowering.V07.SignedEnumControls.negative_client' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Solidity.Lowering.V07.SignedEnumControls.negative_client

/-- info: 'Solidity.Lowering.V07.SignedEnumControls.uint_range_client' depends on axioms: [propext] -/
#guard_msgs in
#print axioms Solidity.Lowering.V07.SignedEnumControls.uint_range_client

/-- info: 'Solidity.Lowering.V07.SignedEnumControls.condition_client' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Solidity.Lowering.V07.SignedEnumControls.condition_client

/-- info: 'Solidity.Lowering.V07.SignedEnumControls.guard_client' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Solidity.Lowering.V07.SignedEnumControls.guard_client

/-- info: 'Solidity.Lowering.V07.SignedEnumControls.guard_negative_client' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms Solidity.Lowering.V07.SignedEnumControls.guard_negative_client

/-- info: 'Solidity.Lowering.V07.SignedEnumControls.cast_client' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Solidity.Lowering.V07.SignedEnumControls.cast_client

/-- info: 'Solidity.Lowering.V07.SignedEnumControls.assignment_client' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Solidity.Lowering.V07.SignedEnumControls.assignment_client

/-- info: 'Solidity.Lowering.V07.SignedEnumControls.capture_client' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Solidity.Lowering.V07.SignedEnumControls.capture_client

/-- info: 'Solidity.Lowering.V07.SignedEnumControls.code_client' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Solidity.Lowering.V07.SignedEnumControls.code_client

/-- info: 'Solidity.Lowering.V07.SignedEnumControls.code_failure_client' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms Solidity.Lowering.V07.SignedEnumControls.code_failure_client

/-- info: 'Solidity.Lowering.V07.SignedEnumControls.operand_client' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Solidity.Lowering.V07.SignedEnumControls.operand_client

/-- info: 'Solidity.Lowering.V07.SignedEnumControls.operand_failure_client' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms Solidity.Lowering.V07.SignedEnumControls.operand_failure_client

end Solidity.Lowering.V07.SignedEnumControls
