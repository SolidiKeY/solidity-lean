import Solidity.Lowering.V07.EnumSignedCasts
import Solidity.Lowering.V07.EnumConversionControls

namespace Solidity.Lowering.V07.EnumSignedCastControls
open EnumSignedCasts
open SignedWidthCasts (ty)
open EnumConversions Source.SemanticsExamples
open MixedAssignmentControls (C path)

def d : Source.DeclName := ⟨none,"Choice"⟩
abbrev members := (List.range 255).map (fun n => "Member" ++ toString n)
def E : Source.Env := ⟨⟨.enum,"Choice",none,false,.enum "Choice" "Zero" members⟩ ::
  MixedAssignmentControls.E.decls⟩
theorem enum_count : E.layout.enumSize d = 256 := by
  change members.length+1 = 256
  simp only [members,List.length_map,List.length_range]
def ordinal (n : Nat) (bound : n < 256) : Fin (E.layout.enumSize d) :=
  ⟨n,by rw [enum_count]; exact bound⟩
def capacity : E.layout.enumSize d ≤ 2^256 := by rw [enum_count]; decide
def zero : Fin (E.layout.enumSize d) := ordinal 0 (by decide)
def two : Fin (E.layout.enumSize d) := ordinal 2 (by decide)
def heap : Source.Heap E.layout :=
  ((Source.Heap.empty : Source.Heap E.layout).alloc ⟨.bytes .memory,.bytes [0,0]⟩).1
def program : Source.Program E where
  body _ := none
  consts _ := none
  inits _ := []
  ctor _ := none
  ctorLocals _ := []
  baseArgs _ := []
  contracts := []
def globals (p : Roadmap.Pipeline) : Source.Glob E :=
  ⟨program,p,toyFixed,fun _ => word 0,fun _ _ => false,fun _ => .answer (.success []),word 0⟩
abbrev EnumCtx : Source.RCtx := [.enum d,.enum d,.bytes .memory,.bytes .storage]
abbrev IntCtx : Source.RCtx := [.int .u256,.int .u256,.bytes .memory,.bytes .storage]
abbrev TgtCtx : Ctx := [.val .uint,.val .uint,.mem bytesR,.alias bytesR]
def source (old rhs : Fin (E.layout.enumSize d)) : Source.EMState E EnumCtx :=
  (.cons (.enum old) (.cons (.enum rhs) (.cons (.memRef rfl 0) (.cons (.storRef rfl path) .nil))),
    {s0 with heap := heap})
def target (old rhs : Fin (E.layout.enumSize d)) : State C TgtCtx :=
  WordCastControls.target .u256 old.val rhs.val (enum_range d capacity old) (enum_range d capacity rhs)
def mapping : ContextMap EnumCtx TgtCtx :=
  (((ContextMap.empty.cons (.bytes .storage) (.alias bytesR)).cons (.bytes .memory) (.mem bytesR)).cons
    (.enum d) (.val .uint)).cons (.enum d) (.val .uint)
def BindingRel : (τ : Source.STy) → (u : LTy) → Source.Val E.layout τ → u.TDenote C (target zero two).H → Prop
  | .enum δ,.val .uint,v,n => EnumRel δ v n
  | .bytes .memory,.mem (.array (.prim .uint)),v,r => v = .memRef rfl 0 ∧ r = some P12Controls.memoryRef
  | .bytes .storage,.alias (.array (.prim .uint)),v,r => v = .storRef rfl path ∧ r = some MixedAssignmentControls.storageRef
  | _,_,_,_ => False

theorem initial (old rhs : Fin (E.layout.enumSize d)) :
    mapping.Related BindingRel (source old rhs).1 (target old rhs).env := by
  intro τ i
  cases i with
  | here => exact enum_related d capacity old
  | there i => cases i with
    | here => exact enum_related d capacity rhs
    | there i => cases i with
      | here => exact ⟨rfl,rfl⟩
      | there i => cases i with
        | here => exact ⟨rfl,rfl⟩
        | there i => nomatch i

theorem reflect (v : Source.Val E.layout (.enum d)) (n : PrimTy.uint.Denote)
    (related : BindingRel (.enum d) (.val .uint) v n) : EnumRel d v n := related



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

def negative_transport_client (p : Roadmap.Pipeline) (checked : Bool) (fuel : Nat) :=
  transport (globals p) {F0 with checked := checked} fuel
    (source zero (ordinal 255 (by decide))) (target zero (ordinal 255 (by decide)))
    d capacity 8 (by decide) mapping BindingRel (initial zero (ordinal 255 (by decide))) reflect
    .here (.there .here) .here (.there .here) rfl rfl (ordinal 255 (by decide)) rfl

def self_client (p : Roadmap.Pipeline) (checked : Bool) (fuel : Nat) :=
  transport (globals p) {F0 with checked := checked} fuel (source zero two) (target zero two)
    d capacity 8 (by decide) mapping BindingRel (initial zero two) reflect .here .here
    .here .here rfl rfl zero rfl

def equal_client (p : Roadmap.Pipeline) (checked : Bool) (fuel : Nat) :=
  transport (globals p) {F0 with checked := checked} fuel (source two two) (target two two)
    d capacity 8 (by decide) mapping BindingRel (initial two two) reflect .here (.there .here)
    .here (.there .here) rfl rfl two rfl

def extension_client := DeferredSource.Operand.run_wk
  (assignedOperand 8 .here (.there .here))
  (Thin.drop (t := .val .bool) Thin.refl) (target zero two) (true,(target zero two).env)

def check (bits : Nat) (width : bits % 8 = 0 ∧ 8 ≤ bits ∧ bits ≤ 256)
    (p : Roadmap.Pipeline) (checked : Bool) (old rhs : Fin (E.layout.enumSize d)) : Bool :=
  let src := source old rhs
  let tgt := target old rhs
  let expected := (ty bits width).wrap rhs.val
  let sr := (Source.evalE (globals p) {F0 with checked := checked} 3
    (.convExplicit (τ := .int (ty bits width)) (.assign (.local .here) (.local (.there .here))) (allowed E d bits width))).run src
  match sr.1,(assignedOperand bits .here (.there .here)).run tgt,
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
      [zero,(ordinal 1 (by decide)),two,(ordinal 127 (by decide)),(ordinal 128 (by decide)),(ordinal 255 (by decide))].all fun old => [zero,(ordinal 1 (by decide)),two,(ordinal 127 (by decide)),(ordinal 128 (by decide)),(ordinal 255 (by decide))].all fun rhs => check bits width p checked old rhs
  else true))

-- Existing mathematical Layout/value fixture, NOT an admitted enum declaration.
def large : Source.Layout where
  fields _ := []
  enumSize _ := 2^256
  underlying _ := .bool
def largeCapacity : large.enumSize d ≤ 2^256 := Nat.le_refl _
def atSign : Fin (large.enumSize d) := ⟨2^255,by decide⟩
def wideTarget (a : Fin (large.enumSize d)) :=
  WordCastControls.target .u256 0 a.val (by decide) (EnumConversions.enum_range d largeCapacity a)
def boundary_client := value_run (D := large) (wideTarget atSign) d largeCapacity 8 (by decide)
  (.simple (.local (.there .here))) atSign rfl

def highCheck (bits : Nat) (width : bits % 8 = 0 ∧ 8 ≤ bits ∧ bits ≤ 256) (n : Nat) : Bool :=
 if inWord : n < large.enumSize d then
  let a : Fin (large.enumSize d) := ⟨n,inWord⟩
  let residue := (n : Int) % ((2^bits : Nat) : Int)
  let expected := if residue < ((2^(bits-1) : Nat) : Int) then residue else residue-((2^bits : Nat) : Int)
  let tgt := wideTarget a
  let v : Val C EnumConversionControls.TgtCtx .uint := .simple (.local (.there .here))
  let wrong : Val C EnumConversionControls.TgtCtx .int :=
    .unop .toInt rfl rfl (UnsignedCasts.castValue bits v)
  match (Source.convExplicitVal (.int (ty bits width)) (.enum a : Source.Val large (.enum d))).map Source.Val.key,
      (assignedOperand bits .here (.there .here)).run tgt,
      (assignLocalOperand .here (.there .here)).code.run tgt,
      wrong.evalT tgt with
  | .ok src,.ok (out,.prim result),.ok cap,.ok wrongResult =>
      src == some expected && result.val == expected &&
      (TEnv.get .here out.st.env).val == (a.val : Int) &&
      (TEnv.get (.there .here) out.st.env).val == (a.val : Int) &&
      (TEnv.get .here cap.st.env).val == (a.val : Int) &&
      (TEnv.get (.there .here) cap.st.env).val == (a.val : Int) &&
      (if bits < 256 ∧ expected < 0 then wrongResult.val != expected else true)
  | _,_,_,_ => false

 else false

def assigned_client := assigned_run (target zero two) d capacity 8 (by decide)
  .here (.there .here) two rfl

/-- info: true -/
#guard_msgs in
#eval IO.println (reprStr ((List.range 257).all fun bits =>
  if width : bits % 8 = 0 ∧ 8 ≤ bits ∧ bits ≤ 256 then
    [0,2^(bits-1)-1,2^(bits-1),2^bits-1,2^256-1].all fun n => highCheck bits width n
  else true))

/-- info: true -/
#guard_msgs in
#eval IO.println (reprStr (
  match (assignedOperand 8 .here (.there .here)).run (target zero (ordinal 255 (by decide))),
    (castValue 8 (.simple (.local .here))).evalT (target zero (ordinal 255 (by decide))) with
  | .ok (out,.prim reached),.ok stale => reached.val == -1 && stale.val == 0 &&
      (TEnv.get .here out.st.env).val == 255
  | _,_ => false))

/-- info: 'Solidity.Lowering.V07.EnumSignedCastControls.enum_count' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Solidity.Lowering.V07.EnumSignedCastControls.enum_count

/-- info: 'Solidity.Lowering.V07.EnumSignedCastControls.initial' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Solidity.Lowering.V07.EnumSignedCastControls.initial

/-- info: 'Solidity.Lowering.V07.EnumSignedCastControls.reflect' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Solidity.Lowering.V07.EnumSignedCastControls.reflect

/-- info: 'Solidity.Lowering.V07.EnumSignedCastControls.allowed_client' does not depend on any axioms -/
#guard_msgs in
#print axioms Solidity.Lowering.V07.EnumSignedCastControls.allowed_client

/-- info: 'Solidity.Lowering.V07.EnumSignedCastControls.source_value_client' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms Solidity.Lowering.V07.EnumSignedCastControls.source_value_client

/-- info: 'Solidity.Lowering.V07.EnumSignedCastControls.run_client' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Solidity.Lowering.V07.EnumSignedCastControls.run_client

/-- info: 'Solidity.Lowering.V07.EnumSignedCastControls.assignment_client' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms Solidity.Lowering.V07.EnumSignedCastControls.assignment_client

/-- info: 'Solidity.Lowering.V07.EnumSignedCastControls.value_client' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Solidity.Lowering.V07.EnumSignedCastControls.value_client

/-- info: 'Solidity.Lowering.V07.EnumSignedCastControls.related_client' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Solidity.Lowering.V07.EnumSignedCastControls.related_client

/-- info: 'Solidity.Lowering.V07.EnumSignedCastControls.transport_client' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms Solidity.Lowering.V07.EnumSignedCastControls.transport_client

/-- info: 'Solidity.Lowering.V07.EnumSignedCastControls.negative_transport_client' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms Solidity.Lowering.V07.EnumSignedCastControls.negative_transport_client

/-- info: 'Solidity.Lowering.V07.EnumSignedCastControls.self_client' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Solidity.Lowering.V07.EnumSignedCastControls.self_client

/-- info: 'Solidity.Lowering.V07.EnumSignedCastControls.equal_client' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Solidity.Lowering.V07.EnumSignedCastControls.equal_client

/-- info: 'Solidity.Lowering.V07.EnumSignedCastControls.extension_client' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms Solidity.Lowering.V07.EnumSignedCastControls.extension_client

/-- info: 'Solidity.Lowering.V07.EnumSignedCastControls.boundary_client' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms Solidity.Lowering.V07.EnumSignedCastControls.boundary_client

/-- info: 'Solidity.Lowering.V07.EnumSignedCastControls.assigned_client' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms Solidity.Lowering.V07.EnumSignedCastControls.assigned_client

end Solidity.Lowering.V07.EnumSignedCastControls
