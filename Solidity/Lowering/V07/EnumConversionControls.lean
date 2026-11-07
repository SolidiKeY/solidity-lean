import Solidity.Lowering.V07.EnumConversions
import Solidity.Lowering.V07.WordCastControls
import Solidity.Lowering.V07.P12Controls

namespace Solidity.Lowering.V07.EnumConversionControls
open EnumConversions Source.SemanticsExamples
open MixedAssignmentControls (C path)

def d : Source.DeclName := ⟨none,"Choice"⟩
def E : Source.Env := ⟨⟨.enum,"Choice",none,false,.enum "Choice" "Zero" ["One","Two"]⟩ ::
  MixedAssignmentControls.E.decls⟩
def capacity : E.layout.enumSize d ≤ 2^256 := by decide
def zero : Fin (E.layout.enumSize d) := ⟨0,by decide⟩
def two : Fin (E.layout.enumSize d) := ⟨2,by decide⟩
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
def ints (x y : Int) (hx : Source.IntTy.u256.lo ≤ x ∧ x ≤ Source.IntTy.u256.hi)
    (hy : Source.IntTy.u256.lo ≤ y ∧ y ≤ Source.IntTy.u256.hi) : Source.EMState E IntCtx :=
  (.cons (.int x hx) (.cons (.int y hy) (.cons (.memRef rfl 0) (.cons (.storRef rfl path) .nil))),
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

theorem int_initial (x y : Int) (hx : Source.IntTy.u256.lo ≤ x ∧ x ≤ Source.IntTy.u256.hi)
    (hy : Source.IntTy.u256.lo ≤ y ∧ y ≤ Source.IntTy.u256.hi) :
    IntegerLocalFamily .u256 (WordCastControls.si .u256) (WordCastControls.ti .u256)
      (ints x y hx hy).1 (WordCastControls.target .u256 x y hx hy).env := by
  refine ⟨?_,?_⟩
  · intro k
    cases k <;> exact integer_related .u256 _ _
  · intro k l
    cases k <;> cases l <;> rfl

def range_client := enum_range d capacity two
def related_client := enum_related d capacity two
def read_client := enum_read d capacity two (enumValue d capacity two) (enum_related d capacity two)
def allowed_from_client := allowed_from E d
def allowed_to_client := allowed_to E d
def from_value_client := source_from_uint (D := E.layout) d 2 (by decide) (by decide)
def to_value_client := source_to_uint d capacity two
def from_related_client := from_related (D := E.layout) d 2 (by decide) (by decide)
def to_run_client (p : Roadmap.Pipeline) (checked : Bool) (fuel : Nat) :=
  source_to_run (globals p) {F0 with checked := checked} (fuel+1) (source zero two) (source zero two)
    d capacity (.local .here) zero rfl
def from_run_client (p : Roadmap.Pipeline) (checked : Bool) (fuel : Nat) :=
  source_from_run (globals p) {F0 with checked := checked} (fuel+1) (ints 0 2 (by decide) (by decide))
    (ints 0 2 (by decide) (by decide)) d (.local (.there .here)) 2 (by decide) (by decide) rfl

def from_transport_client (p : Roadmap.Pipeline) (checked : Bool) (fuel : Nat) :=
  from_assignment_transport (globals p) {F0 with checked := checked} fuel
    (ints 0 2 (by decide) (by decide)) (WordCastControls.target .u256 0 2 (by decide) (by decide)) d
    (WordCastControls.si .u256) (WordCastControls.ti .u256) (int_initial 0 2 (by decide) (by decide))
    true false 2 (by decide) (by decide) rfl

def to_transport_client (p : Roadmap.Pipeline) (checked : Bool) (fuel : Nat) :=
  to_assignment_transport (globals p) {F0 with checked := checked} fuel (source zero two) (target zero two)
    d capacity mapping BindingRel (initial zero two) reflect .here (.there .here)
    .here (.there .here) rfl rfl two rfl

def self_client (p : Roadmap.Pipeline) (checked : Bool) (fuel : Nat) :=
  to_assignment_transport (globals p) {F0 with checked := checked} fuel (source zero two) (target zero two)
    d capacity mapping BindingRel (initial zero two) reflect .here .here .here .here rfl rfl zero rfl

def equal_client (p : Roadmap.Pipeline) (checked : Bool) (fuel : Nat) :=
  to_assignment_transport (globals p) {F0 with checked := checked} fuel (source two two) (target two two)
    d capacity mapping BindingRel (initial two two) reflect .here (.there .here)
    .here (.there .here) rfl rfl two rfl

def extension_client := DeferredSource.Operand.run_wk (assignLocalOperand .here (.there .here))
  (Thin.drop (t := .val .bool) Thin.refl) (target zero two) (true,(target zero two).env)

def refused_value_client := source_from_uint_refused (D := E.layout) d 3 (by decide) (by decide)
def refused_run_client (p : Roadmap.Pipeline) (checked : Bool) (fuel : Nat) :=
  source_from_refused_run (globals p) {F0 with checked := checked} (fuel+1)
    (ints 0 3 (by decide) (by decide)) (ints 0 3 (by decide) (by decide))
    d (.local (.there .here)) 3 (by decide) (by decide) rfl

def refused_assignment_client (p : Roadmap.Pipeline) (checked : Bool) (fuel : Nat) :=
  source_from_refused_assignment (globals p) {F0 with checked := checked} fuel
    (ints 0 3 (by decide) (by decide)) d .here (.there .here) 3 (by decide) (by decide) rfl

-- Valid instances have real enum declarations and live independent Source memory/storage.
def heap_client : heap.get 0 = some ⟨.bytes .memory,.bytes [0,0]⟩ := rfl
def storage_client : E.pathTy path = some (.bytes .storage) := rfl

def check (p : Roadmap.Pipeline) (checked : Bool) (old rhs : Fin (E.layout.enumSize d)) : Bool := Id.run do
  let src := source old rhs
  let intsrc := ints old.val rhs.val (enum_range d capacity old) (enum_range d capacity rhs)
  let tgt := target old rhs
  let to := (Source.evalE (globals p) {F0 with checked := checked} 3
    (.convExplicit (τ := .int .u256) (.assign (.local .here) (.local (.there .here))) (allowed_to E d))).run src
  let fromResult := (Source.evalE (globals p) {F0 with checked := checked} 3
    (.convExplicit (τ := .enum d) (.assign (.local .here) (.local (.there .here))) (allowed_from E d))).run intsrc
  match to.1,fromResult.1,(assignLocalOperand .here (.there .here)).code.run tgt,(assignLocalOperand .here (.there .here)).run tgt with
  | .ok (.val (.int x _)),.ok (.val (.enum i)),.ok cap,.ok (out,.prim v) =>
      return x == (rhs.val : Int) && i.val == rhs.val && v.val == x &&
        (to.2.1.get .here).key == some x && (fromResult.2.1.get .here).key == some x &&
        (TEnv.get .here cap.st.env).val == x && (TEnv.get (.there .here) cap.st.env).val == x &&
        (TEnv.get .here out.st.env).val == x && (TEnv.get (.there .here) out.st.env).val == x
  | _,_,_,_ => return false

/-- info: true -/
#guard_msgs in
#eval IO.println (reprStr ([Roadmap.Pipeline.legacy,.viaIR].all fun p => [false,true].all fun checked =>
  [zero,⟨1,by decide⟩,two].all fun old => [zero,⟨1,by decide⟩,two].all fun rhs => check p checked old rhs))

-- Invalid native copies SUCCEED: therefore the valid-input premise cannot be
-- removed and a real native enum range guard remains an open lowering clause.
def rejected (p : Roadmap.Pipeline) (checked : Bool) (x : Nat) (bound : x < 2^256) : Bool :=
  let src := ints 0 x (by decide) (by change 0 ≤ (x : Int) ∧ (x : Int) ≤ ((2^256-1 : Nat) : Int); omega)
  let tgt := WordCastControls.target .u256 0 x (by decide)
    (by change 0 ≤ (x : Int) ∧ (x : Int) ≤ ((2^256-1 : Nat) : Int); omega)
  let result := (Source.evalE (globals p) {F0 with checked := checked} 3
    (.convExplicit (τ := .enum d) (.assign (.local .here) (.local (.there .here))) (allowed_from E d))).run src
  match result.1,(assignLocalOperand .here (.there .here)).run tgt with
  | .error (.revert payload),.ok (out,.prim v) =>
      payload == Source.panicData .enumConv && payload != Source.panicData .arithmetic &&
      (result.2.1.get .here).key == some (x : Int) && v.val == (x : Int) &&
      (TEnv.get .here out.st.env).val == (x : Int)
  | _,_ => false
/-- info: true -/
#guard_msgs in
#eval IO.println (reprStr ([Roadmap.Pipeline.legacy,.viaIR].all fun p => [false,true].all fun checked =>
  rejected p checked 3 (by decide) && rejected p checked 255 (by decide)))
-- Existing Layout/Val countermodel only, not an admitted declaration profile:
-- capacity cannot be inferred from selected content or silently truncated.
def oversized : Source.Layout where
  fields _ := []
  enumSize _ := 2^256+1
  underlying _ := .bool
def high : Fin (oversized.enumSize d) := ⟨2^256,Nat.lt_succ_self _⟩
/-- info: true -/
#guard_msgs in
#eval IO.println (reprStr (
  (Source.Val.enum high : Source.Val oversized (.enum d)).key !=
    PrimTy.num? (p := .uint) (⟨0,by decide⟩ : PrimTy.uint.Denote)))
end Solidity.Lowering.V07.EnumConversionControls

/-- info: 'Solidity.Lowering.V07.EnumConversionControls.initial' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Solidity.Lowering.V07.EnumConversionControls.initial

/-- info: 'Solidity.Lowering.V07.EnumConversionControls.reflect' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Solidity.Lowering.V07.EnumConversionControls.reflect

/-- info: 'Solidity.Lowering.V07.EnumConversionControls.int_initial' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Solidity.Lowering.V07.EnumConversionControls.int_initial

/-- info: 'Solidity.Lowering.V07.EnumConversionControls.range_client' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Solidity.Lowering.V07.EnumConversionControls.range_client

/-- info: 'Solidity.Lowering.V07.EnumConversionControls.related_client' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Solidity.Lowering.V07.EnumConversionControls.related_client

/-- info: 'Solidity.Lowering.V07.EnumConversionControls.read_client' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Solidity.Lowering.V07.EnumConversionControls.read_client

/-- info: 'Solidity.Lowering.V07.EnumConversionControls.allowed_from_client' does not depend on any axioms -/
#guard_msgs in
#print axioms Solidity.Lowering.V07.EnumConversionControls.allowed_from_client

/-- info: 'Solidity.Lowering.V07.EnumConversionControls.allowed_to_client' does not depend on any axioms -/
#guard_msgs in
#print axioms Solidity.Lowering.V07.EnumConversionControls.allowed_to_client

/-- info: 'Solidity.Lowering.V07.EnumConversionControls.from_value_client' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms Solidity.Lowering.V07.EnumConversionControls.from_value_client

/-- info: 'Solidity.Lowering.V07.EnumConversionControls.to_value_client' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms Solidity.Lowering.V07.EnumConversionControls.to_value_client

/-- info: 'Solidity.Lowering.V07.EnumConversionControls.from_related_client' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms Solidity.Lowering.V07.EnumConversionControls.from_related_client

/-- info: 'Solidity.Lowering.V07.EnumConversionControls.to_run_client' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Solidity.Lowering.V07.EnumConversionControls.to_run_client

/-- info: 'Solidity.Lowering.V07.EnumConversionControls.from_run_client' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms Solidity.Lowering.V07.EnumConversionControls.from_run_client

/-- info: 'Solidity.Lowering.V07.EnumConversionControls.from_transport_client' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms Solidity.Lowering.V07.EnumConversionControls.from_transport_client

/-- info: 'Solidity.Lowering.V07.EnumConversionControls.to_transport_client' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms Solidity.Lowering.V07.EnumConversionControls.to_transport_client

/-- info: 'Solidity.Lowering.V07.EnumConversionControls.self_client' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Solidity.Lowering.V07.EnumConversionControls.self_client

/-- info: 'Solidity.Lowering.V07.EnumConversionControls.equal_client' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Solidity.Lowering.V07.EnumConversionControls.equal_client

/-- info: 'Solidity.Lowering.V07.EnumConversionControls.extension_client' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms Solidity.Lowering.V07.EnumConversionControls.extension_client

/-- info: 'Solidity.Lowering.V07.EnumConversionControls.refused_value_client' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms Solidity.Lowering.V07.EnumConversionControls.refused_value_client

/-- info: 'Solidity.Lowering.V07.EnumConversionControls.refused_run_client' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms Solidity.Lowering.V07.EnumConversionControls.refused_run_client

/-- info: 'Solidity.Lowering.V07.EnumConversionControls.refused_assignment_client' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms Solidity.Lowering.V07.EnumConversionControls.refused_assignment_client

/-- info: 'Solidity.Lowering.V07.EnumConversionControls.heap_client' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Solidity.Lowering.V07.EnumConversionControls.heap_client

/-- info: 'Solidity.Lowering.V07.EnumConversionControls.storage_client' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Solidity.Lowering.V07.EnumConversionControls.storage_client
