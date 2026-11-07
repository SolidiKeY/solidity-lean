import Solidity.Lowering.V07.UdvtBoolAssignment
import Solidity.Lowering.V07.P12Controls

namespace Solidity.Lowering.V07.UdvtBoolAssignmentControls
open UdvtBoolAssignment Source.SemanticsExamples
open MixedAssignmentControls (C path)
def d : Source.DeclName := ⟨none,"Enabled"⟩
def e : Source.DeclName := ⟨none,"Other"⟩
def E : Source.Env :=
  ⟨⟨.udvt,"Enabled",none,false,.udvt "Enabled" .bool⟩ ::
    ⟨.udvt,"Other",none,false,.udvt "Other" .bool⟩ :: MixedAssignmentControls.E.decls⟩
theorem underlying : E.layout.underlying d = .bool := rfl
abbrev SrcCtx : Source.RCtx := [.udvt d,.udvt d,.bytes .memory,.bytes .storage]
abbrev TgtCtx : Ctx := [.val .bool,.val .bool,.mem bytesR,.alias bytesR]
def source (x y : Bool) : Source.EMState E SrcCtx :=
  (.cons (value d underlying x) (.cons (value d underlying y)
    (.cons (.memRef rfl 0) (.cons (.storRef rfl path) .nil))),
    {s0 with heap := ((Source.Heap.empty : Source.Heap E.layout).alloc ⟨.bytes .memory,.bytes [0,0]⟩).1})
def target (x y : Bool) : State C TgtCtx := (MixedAssignmentControls.memory.push y).push x

def mapping : ContextMap SrcCtx TgtCtx :=
  (((ContextMap.empty.cons (.bytes .storage) (.alias bytesR)).cons (.bytes .memory) (.mem bytesR)).cons
    (.udvt d) (.val .bool)).cons (.udvt d) (.val .bool)
def BindingRel : (τ : Source.STy) → (u : LTy) → Source.Val E.layout τ →
    u.TDenote C MixedAssignmentControls.memory.H → Prop
  | .udvt δ,.val .bool,v,b => ∃ h : E.layout.underlying δ = .bool, Rel δ h v b
  | .bytes .memory,.mem (.array (.prim .uint)),v,r => v = .memRef rfl 0 ∧ r = some P12Controls.memoryRef
  | .bytes .storage,.alias (.array (.prim .uint)),v,r => v = .storRef rfl path ∧ r = some MixedAssignmentControls.storageRef
  | _,_,_,_ => False

def key_client := value_key d underlying true
def related_client := value_related d underlying false
def read_client := read_value d underlying false false related_client

-- Actual Source assignment reuses the independently proved same-tag execution clause.
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
def source_client (p : Roadmap.Pipeline) (checked : Bool) (x y : Bool) :=
  UdvtAssignment.source_assignment (globals p) {F0 with checked := checked} 0
    (source x y) d .here (.there .here) (value d underlying y) rfl

theorem initial (x y : Bool) : mapping.Related BindingRel (source x y).1 (target x y).env := by
  intro τ i
  cases i with
  | here => exact ⟨underlying,rfl⟩
  | there i => cases i with
    | here => exact ⟨underlying,rfl⟩
    | there i => cases i with
      | here => exact ⟨rfl,rfl⟩
      | there i => cases i with
        | here => exact ⟨rfl,rfl⟩
        | there i => nomatch i

theorem reflect (v : Source.Val E.layout (.udvt d)) (n : Bool)
    (related : BindingRel (.udvt d) (.val .bool) v n) : Rel d underlying v n := by
  obtain ⟨h,rel⟩ := related
  exact rel

def transport_client (p : Roadmap.Pipeline) (checked : Bool) (x y : Bool) :=
  transport (globals p) {F0 with checked := checked} 0 (source x y) (target x y)
    d underlying mapping BindingRel (initial x y) reflect
    .here (.there .here) .here (.there .here) rfl rfl y rfl

def self_client (p : Roadmap.Pipeline) (checked : Bool) :=
  transport (globals p) {F0 with checked := checked} 0 (source true false) (target true false)
    d underlying mapping BindingRel (initial true false) reflect
    .here .here .here .here rfl rfl true rfl

def extension_client := DeferredSource.Operand.run_wk
  (assignLocalOperand .here (.there .here) : DeferredSource.Operand C TgtCtx (.prim .bool))
  (Thin.drop (t := .val .bool) Thin.refl) (target false true) (true,(target false true).env)

def check (p : Roadmap.Pipeline) (checked x y : Bool) : Bool :=
  let src := source x y
  let tgt := target x y
  match (Source.evalE (globals p) {F0 with checked := checked} 3
      (.conv (.assign (.local (.here : Source.Idx SrcCtx (.udvt d)))
        (.local (.there .here))) (Or.inr rfl))).run src,
      (assignLocalOperand .here (.there .here)).run tgt,
      (assignLocalOperand .here (.there .here)).code.run tgt with
  | (.ok (.val v),post),.ok (out,.prim n),.ok cap =>
      v.key == some (if y then 1 else 0) && n == y &&
      (post.1.get .here).key == v.key &&
      (post.1.get (.there .here)).key == v.key &&
      TEnv.get .here out.st.env == y && TEnv.get (.there .here) out.st.env == y &&
      TEnv.get .here cap.st.env == y && TEnv.get (.there .here) cap.st.env == y
  | _,_,_ => false

/-- info: true -/
#guard_msgs in
#eval IO.println (reprStr ([Roadmap.Pipeline.legacy,.viaIR].all fun p =>
  [false,true].all fun checked => [false,true].all fun x => [false,true].all fun y => check p checked x y))

-- Capturing the assigned value differs from a stale pre-assignment local read.
/-- info: true -/
#guard_msgs in
#eval IO.println (reprStr (
  let tgt := target false true
  match (assignLocalOperand .here (.there .here)).run tgt,
      (Val.simple (.local .here) : Val C TgtCtx .bool).evalT tgt with
  | .ok (out,.prim reached),.ok stale => reached && !stale && TEnv.get .here out.st.env
  | _,_ => false))

-- Equal Boolean contents do not authorize a cross-nominal Source conversion.
/-- info: true -/
#guard_msgs in
#eval IO.println (reprStr (
  let v := value d underlying true
  let w := value e (rfl : E.layout.underlying e = .bool) true
  match Source.convVal (.udvt e) v with
  | .error (.stuck why) => v.key == w.key && why == "user-defined value type" &&
      !(Source.STy.udvt d).implicit E.isBase E.mapFree (.udvt e)
  | _ => false))

/-- info: 'Solidity.Lowering.V07.UdvtBoolAssignmentControls.underlying' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Solidity.Lowering.V07.UdvtBoolAssignmentControls.underlying

/-- info: 'Solidity.Lowering.V07.UdvtBoolAssignmentControls.initial' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Solidity.Lowering.V07.UdvtBoolAssignmentControls.initial

/-- info: 'Solidity.Lowering.V07.UdvtBoolAssignmentControls.reflect' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Solidity.Lowering.V07.UdvtBoolAssignmentControls.reflect

/-- info: 'Solidity.Lowering.V07.UdvtBoolAssignmentControls.key_client' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Solidity.Lowering.V07.UdvtBoolAssignmentControls.key_client

/-- info: 'Solidity.Lowering.V07.UdvtBoolAssignmentControls.related_client' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms Solidity.Lowering.V07.UdvtBoolAssignmentControls.related_client

/-- info: 'Solidity.Lowering.V07.UdvtBoolAssignmentControls.read_client' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms Solidity.Lowering.V07.UdvtBoolAssignmentControls.read_client

/-- info: 'Solidity.Lowering.V07.UdvtBoolAssignmentControls.source_client' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms Solidity.Lowering.V07.UdvtBoolAssignmentControls.source_client

/-- info: 'Solidity.Lowering.V07.UdvtBoolAssignmentControls.transport_client' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms Solidity.Lowering.V07.UdvtBoolAssignmentControls.transport_client

/-- info: 'Solidity.Lowering.V07.UdvtBoolAssignmentControls.self_client' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms Solidity.Lowering.V07.UdvtBoolAssignmentControls.self_client

/-- info: 'Solidity.Lowering.V07.UdvtBoolAssignmentControls.extension_client' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms Solidity.Lowering.V07.UdvtBoolAssignmentControls.extension_client

end Solidity.Lowering.V07.UdvtBoolAssignmentControls
