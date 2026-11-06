import Solidity.Lowering.V07.UdvtAssignment
import Solidity.Lowering.V07.WordCastControls
import Solidity.Lowering.V07.P12Controls

namespace Solidity.Lowering.V07.UdvtAssignmentControls
open UdvtAssignment Source.SemanticsExamples
open MixedAssignmentControls (C path)
def d : Source.DeclName := ⟨none,"Meter"⟩
def e : Source.DeclName := ⟨none,"Other"⟩
def E (t : Source.IntTy) : Source.Env :=
  ⟨⟨.udvt,"Meter",none,false,.udvt "Meter" (.int t.signed t.bits t.valid)⟩ ::
    ⟨.udvt,"Other",none,false,.udvt "Other" (.int t.signed t.bits t.valid)⟩ :: MixedAssignmentControls.E.decls⟩
theorem underlying (t : Source.IntTy) : (E t).layout.underlying d = .int t := by cases t; rfl
theorem other_underlying (t : Source.IntTy) : (E t).layout.underlying e = .int t := by cases t; rfl
def heap (t : Source.IntTy) : Source.Heap (E t).layout :=
  ((Source.Heap.empty : Source.Heap (E t).layout).alloc ⟨.bytes .memory,.bytes [0,0]⟩).1
def program (t : Source.IntTy) : Source.Program (E t) where
  body _ := none
  consts _ := none
  inits _ := []
  ctor _ := none
  ctorLocals _ := []
  baseArgs _ := []
  contracts := []
def globals (t : Source.IntTy) (p : Roadmap.Pipeline) : Source.Glob (E t) :=
  ⟨program t,p,toyFixed,fun _ => word 0,fun _ _ => false,fun _ => .answer (.success []),word 0⟩
abbrev SrcCtx : Source.RCtx := [.udvt d,.udvt d,.bytes .memory,.bytes .storage]
abbrev TgtCtx (t : Source.IntTy) : Ctx := [.val (integerPrim t),.val (integerPrim t),.mem bytesR,.alias bytesR]
def source (t : Source.IntTy) (x y : Int) (hx : t.lo ≤ x ∧ x ≤ t.hi) (hy : t.lo ≤ y ∧ y ≤ t.hi) :
    Source.EMState (E t) SrcCtx :=
  (.cons (value d t (underlying t) x hx) (.cons (value d t (underlying t) y hy)
    (.cons (.memRef rfl 0) (.cons (.storRef rfl path) .nil))),{s0 with heap := heap t})
def target (t : Source.IntTy) (x y : Int) (hx : t.lo ≤ x ∧ x ≤ t.hi) (hy : t.lo ≤ y ∧ y ≤ t.hi) :=
  WordCastControls.target t x y hx hy
def mapping (t : Source.IntTy) : ContextMap SrcCtx (TgtCtx t) :=
  (((ContextMap.empty.cons (.bytes .storage) (.alias bytesR)).cons (.bytes .memory) (.mem bytesR)).cons
    (.udvt d) (.val (integerPrim t))).cons (.udvt d) (.val (integerPrim t))
def BindingRel (t : Source.IntTy) : (τ : Source.STy) → (u : LTy) → Source.Val (E t).layout τ →
    u.TDenote C MixedAssignmentControls.memory.H → Prop
  | .udvt δ,u,v,n => ∃ h : u = .val (integerPrim t), Rel δ t v (cast (congrArg (fun u : LTy => u.TDenote C MixedAssignmentControls.memory.H) h) n)
  | .bytes .memory,.mem (.array (.prim .uint)),v,r => v = .memRef rfl 0 ∧ r = some P12Controls.memoryRef
  | .bytes .storage,.alias (.array (.prim .uint)),v,r => v = .storRef rfl path ∧ r = some MixedAssignmentControls.storageRef
  | _,_,_,_ => False

theorem initial (t : Source.IntTy) (x y : Int) (hx : t.lo ≤ x ∧ x ≤ t.hi) (hy : t.lo ≤ y ∧ y ≤ t.hi) :
    (mapping t).Related (BindingRel t) (source t x y hx hy).1 (target t x y hx hy).env := by
  intro τ i
  cases i with
  | here => exact ⟨rfl,value_related d t (underlying t) x hx⟩
  | there i => cases i with
    | here => exact ⟨rfl,value_related d t (underlying t) y hy⟩
    | there i => cases i with
      | here => exact ⟨rfl,rfl⟩
      | there i => cases i with
        | here => exact ⟨rfl,rfl⟩
        | there i => nomatch i

theorem reflect (t : Source.IntTy) (v : Source.Val (E t).layout (.udvt d)) (n : (integerPrim t).Denote)
    (related : BindingRel t (.udvt d) (.val (integerPrim t)) v n) : Rel d t v n := by
  obtain ⟨h,rel⟩ := related
  exact rel

def key_client := value_key d .u8 (underlying .u8) 255 (by decide)
def related_client := value_related d .u8 (underlying .u8) 255 (by decide)
def read_client := read_value d .u8 (underlying .u8) 255 (by decide) _ related_client
def cast_client := key_cast (D := (E .u8).layout) (rfl : Source.STy.int .u8 = .int .u8) (.int 255 (by decide))
def nominal_client := nominal_implicit (E .u8) d e
def refused_client := nominal_refused (D := (E .u8).layout) d e (by decide) (value d .u8 (underlying .u8) 255 (by decide))
def run_client (p : Roadmap.Pipeline) (checked : Bool) (fuel : Nat) :=
  source_run (globals .u8 p) {F0 with checked := checked} (fuel+1)
    (source .u8 0 255 (by decide) (by decide)) (source .u8 0 255 (by decide) (by decide))
    d (.local (.there .here)) (value d .u8 (underlying .u8) 255 (by decide)) rfl
def assignment_client (p : Roadmap.Pipeline) (checked : Bool) (fuel : Nat) :=
  source_assignment (globals .u8 p) {F0 with checked := checked} fuel
    (source .u8 0 255 (by decide) (by decide)) d .here (.there .here)
    (value d .u8 (underlying .u8) 255 (by decide)) rfl
def transport_client (t : Source.IntTy) (p : Roadmap.Pipeline) (checked : Bool) (fuel : Nat)
    (x y : Int) (hx : t.lo ≤ x ∧ x ≤ t.hi) (hy : t.lo ≤ y ∧ y ≤ t.hi) :=
  transport (globals t p) {F0 with checked := checked} fuel (source t x y hx hy) (target t x y hx hy)
    d t (underlying t) (mapping t) (BindingRel t) (initial t x y hx hy) (reflect t)
    .here (.there .here) .here (.there .here) rfl rfl y hy rfl

def self_client (p : Roadmap.Pipeline) (checked : Bool) (fuel : Nat) :=
  transport (globals .u8 p) {F0 with checked := checked} fuel
    (source .u8 255 0 (by decide) (by decide)) (target .u8 255 0 (by decide) (by decide))
    d .u8 (underlying .u8) (mapping .u8) (BindingRel .u8)
    (initial .u8 255 0 (by decide) (by decide)) (reflect .u8)
    .here .here .here .here rfl rfl 255 (by decide) rfl

def extension_client := DeferredSource.Operand.run_wk
  (assignLocalOperand .here (.there .here) : DeferredSource.Operand C (TgtCtx .u8) (.prim .uint))
  (Thin.drop (t := .val .bool) Thin.refl) (target .u8 0 255 (by decide) (by decide))
  (true,(target .u8 0 255 (by decide) (by decide)).env)

def check (t : Source.IntTy) (p : Roadmap.Pipeline) (checked : Bool) (old rhs : Int) : Bool :=
  if ho : t.lo ≤ old ∧ old ≤ t.hi then
    if hr : t.lo ≤ rhs ∧ rhs ≤ t.hi then
      let src := source t old rhs ho hr
      let tgt := target t old rhs ho hr
      let sr := (Source.evalE (globals t p) {F0 with checked := checked} 3
        (.conv (.assign (.local (.here : Source.Idx SrcCtx (.udvt d))) (.local (.there .here))) (Or.inr rfl))).run src
      match sr.1,(assignLocalOperand .here (.there .here)).run tgt,(assignLocalOperand .here (.there .here)).code.run tgt with
      | .ok (.val v),.ok (out,.prim n),.ok cap =>
          v.key == some rhs && PrimTy.num? n == some rhs &&
          (sr.2.1.get .here).key == some rhs &&
          PrimTy.num? (TEnv.get .here out.st.env) == some rhs &&
          PrimTy.num? (TEnv.get (.there .here) out.st.env) == some rhs &&
          PrimTy.num? (TEnv.get .here cap.st.env) == some rhs &&
          PrimTy.num? (TEnv.get (.there .here) cap.st.env) == some rhs
      | _,_,_ => false
    else false
  else false

/-- info: true -/
#guard_msgs in
#eval IO.println (reprStr ((List.range 257).all fun bits =>
  if width : bits % 8 = 0 ∧ 8 ≤ bits ∧ bits ≤ 256 then
    [false,true].all fun sign =>
      let t : Source.IntTy := ⟨sign,bits,width⟩
      [Roadmap.Pipeline.legacy,.viaIR].all fun p => [false,true].all fun checked =>
        [0,1,t.lo,t.hi].all fun old => [0,1,t.lo,t.hi].all fun rhs => check t p checked old rhs
  else true))

-- Same contents do not imply nominal conversion permission.
/-- info: true -/
#guard_msgs in
#eval IO.println (reprStr (
  let v := value d Source.IntTy.u8 (underlying .u8) 255 (by decide)
  let w := value e Source.IntTy.u8 (other_underlying .u8) 255 (by decide)
  match Source.convVal (.udvt e) v,
      (assignLocalOperand .here (.there .here)).run (target .u8 0 255 (by decide) (by decide)) with
  | .error (.stuck why),.ok (out,.prim n) => v.key == w.key &&
      !(Source.STy.udvt d).implicit (E .u8).isBase (E .u8).mapFree (.udvt e) &&
      why == "user-defined value type" && n.val == 255 && (TEnv.get .here out.st.env).val == 255
  | _,_ => false))

-- A stale, uncaptured old local disagrees with the reached RHS result.
/-- info: true -/
#guard_msgs in
#eval IO.println (reprStr (
  let tgt := target .u8 0 255 (by decide) (by decide)
  match (assignLocalOperand .here (.there .here)).run tgt,
      (Val.simple (.local .here) : Val C (TgtCtx .u8) .uint).evalT tgt with
  | .ok (out,.prim reached),.ok stale => reached.val == 255 && stale.val == 0 &&
      (TEnv.get .here out.st.env).val == 255
  | _,_ => false))

/-- info: 'Solidity.Lowering.V07.UdvtAssignmentControls.underlying' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Solidity.Lowering.V07.UdvtAssignmentControls.underlying

/-- info: 'Solidity.Lowering.V07.UdvtAssignmentControls.other_underlying' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms Solidity.Lowering.V07.UdvtAssignmentControls.other_underlying

/-- info: 'Solidity.Lowering.V07.UdvtAssignmentControls.initial' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Solidity.Lowering.V07.UdvtAssignmentControls.initial

/-- info: 'Solidity.Lowering.V07.UdvtAssignmentControls.reflect' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Solidity.Lowering.V07.UdvtAssignmentControls.reflect

/-- info: 'Solidity.Lowering.V07.UdvtAssignmentControls.key_client' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Solidity.Lowering.V07.UdvtAssignmentControls.key_client

/-- info: 'Solidity.Lowering.V07.UdvtAssignmentControls.related_client' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Solidity.Lowering.V07.UdvtAssignmentControls.related_client

/-- info: 'Solidity.Lowering.V07.UdvtAssignmentControls.read_client' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Solidity.Lowering.V07.UdvtAssignmentControls.read_client

/-- info: 'Solidity.Lowering.V07.UdvtAssignmentControls.cast_client' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Solidity.Lowering.V07.UdvtAssignmentControls.cast_client

/-- info: 'Solidity.Lowering.V07.UdvtAssignmentControls.nominal_client' does not depend on any axioms -/
#guard_msgs in
#print axioms Solidity.Lowering.V07.UdvtAssignmentControls.nominal_client

/-- info: 'Solidity.Lowering.V07.UdvtAssignmentControls.refused_client' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Solidity.Lowering.V07.UdvtAssignmentControls.refused_client

/-- info: 'Solidity.Lowering.V07.UdvtAssignmentControls.run_client' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Solidity.Lowering.V07.UdvtAssignmentControls.run_client

/-- info: 'Solidity.Lowering.V07.UdvtAssignmentControls.assignment_client' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms Solidity.Lowering.V07.UdvtAssignmentControls.assignment_client

/-- info: 'Solidity.Lowering.V07.UdvtAssignmentControls.transport_client' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms Solidity.Lowering.V07.UdvtAssignmentControls.transport_client

/-- info: 'Solidity.Lowering.V07.UdvtAssignmentControls.self_client' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Solidity.Lowering.V07.UdvtAssignmentControls.self_client

/-- info: 'Solidity.Lowering.V07.UdvtAssignmentControls.extension_client' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms Solidity.Lowering.V07.UdvtAssignmentControls.extension_client

end Solidity.Lowering.V07.UdvtAssignmentControls
