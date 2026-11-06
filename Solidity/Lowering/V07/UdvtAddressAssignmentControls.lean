import Solidity.Lowering.V07.UdvtAddressAssignment
import Solidity.Lowering.V07.AddressConversionControls
import Solidity.Lowering.V07.UnsignedCasts

namespace Solidity.Lowering.V07.UdvtAddressAssignmentControls
open UdvtAddressAssignment Source.SemanticsExamples
open AddressConversions (addressValue)
open AddressConversionControls (a5 a17)
open MixedAssignmentControls (C path)
def d : Source.DeclName := ⟨none,"Account"⟩
def e : Source.DeclName := ⟨none,"Other"⟩
def E (p : Bool) : Source.Env :=
  ⟨⟨.udvt,"Account",none,false,.udvt "Account" (if p then .addressPayable else .address)⟩ ::
    ⟨.udvt,"Other",none,false,.udvt "Other" (if p then .addressPayable else .address)⟩ :: MixedAssignmentControls.E.decls⟩
theorem underlying (p : Bool) : (E p).layout.underlying d = .address p := by
  cases p <;> rfl
theorem other_underlying (p : Bool) : (E p).layout.underlying e = .address p := by
  cases p <;> rfl
abbrev SrcCtx : Source.RCtx := [.udvt d,.udvt d,.bytes .memory,.bytes .storage]
abbrev TgtCtx : Ctx := [.val .uint,.val .uint,.mem bytesR,.alias bytesR]
def source (p : Bool) (old rhs : Roadmap.Address) : Source.EMState (E p) SrcCtx :=
  (.cons (value d p (underlying p) old) (.cons (value d p (underlying p) rhs)
    (.cons (.memRef rfl 0) (.cons (.storRef rfl path) .nil))),
    {s0 with heap := ((Source.Heap.empty : Source.Heap (E p).layout).alloc ⟨.bytes .memory,.bytes [0,0]⟩).1})
def target := AddressConversionControls.target
def mapping : ContextMap SrcCtx TgtCtx :=
  (((ContextMap.empty.cons (.bytes .storage) (.alias bytesR)).cons (.bytes .memory) (.mem bytesR)).cons
    (.udvt d) (.val .uint)).cons (.udvt d) (.val .uint)
def BindingRel (p : Bool) : (τ : Source.STy) → (u : LTy) → Source.Val (E p).layout τ →
    u.TDenote C MixedAssignmentControls.memory.H → Prop
  | .udvt δ,.val .uint,v,n => Rel δ v n
  | .bytes .memory,.mem (.array (.prim .uint)),v,r => v = .memRef rfl 0 ∧ r = some P12Controls.memoryRef
  | .bytes .storage,.alias (.array (.prim .uint)),v,r => v = .storRef rfl path ∧ r = some MixedAssignmentControls.storageRef
  | _,_,_,_ => False

theorem initial (p : Bool) (old rhs : Roadmap.Address) :
    mapping.Related (BindingRel p) (source p old rhs).1 (target old rhs).env := by
  intro τ i
  cases i with
  | here => exact value_related d p (underlying p) old
  | there i => cases i with
    | here => exact value_related d p (underlying p) rhs
    | there i => cases i with
      | here => exact ⟨rfl,rfl⟩
      | there i => cases i with
        | here => exact ⟨rfl,rfl⟩
        | there i => nomatch i

theorem reflect (p : Bool) (v : Source.Val (E p).layout (.udvt d)) (n : PrimTy.uint.Denote)
    (related : BindingRel p (.udvt d) (.val .uint) v n) : Rel d v n := by
  exact related

def program (p : Bool) : Source.Program (E p) where
  body _ := none
  consts _ := none
  inits _ := []
  ctor _ := none
  ctorLocals _ := []
  baseArgs _ := []
  contracts := []
def globals (p : Bool) (pipeline : Roadmap.Pipeline) : Source.Glob (E p) :=
  ⟨program p,pipeline,toyFixed,fun _ => word 0,fun _ _ => false,fun _ => .answer (.success []),word 0⟩
def key_client (p : Bool) := value_key d p (underlying p) a17
def related_client (p : Bool) := value_related d p (underlying p) a17
def read_client (p : Bool) := read_value d p (underlying p) a17 _ (related_client p)
def source_client (p : Bool) (pipeline : Roadmap.Pipeline) (checked : Bool) :=
  UdvtAssignment.source_assignment (globals p pipeline) {F0 with checked := checked} 0
    (source p a5 a17) d .here (.there .here) (value d p (underlying p) a17) rfl
def transport_client (p : Bool) (pipeline : Roadmap.Pipeline) (checked : Bool) (old rhs : Roadmap.Address) :=
  transport (globals p pipeline) {F0 with checked := checked} 0 (source p old rhs) (target old rhs)
    d p (underlying p) mapping (BindingRel p) (initial p old rhs) (reflect p)
    .here (.there .here) .here (.there .here) rfl rfl rhs rfl

def self_client (p : Bool) (pipeline : Roadmap.Pipeline) (checked : Bool) :=
  transport (globals p pipeline) {F0 with checked := checked} 0 (source p a17 a5) (target a17 a5)
    d p (underlying p) mapping (BindingRel p) (initial p a17 a5) (reflect p)
    .here .here .here .here rfl rfl a17 rfl

def extension_client := DeferredSource.Operand.run_wk
  (assignLocalOperand .here (.there .here) : DeferredSource.Operand C TgtCtx (.prim .uint))
  (Thin.drop (t := .val .bool) Thin.refl) (target a5 a17) (true,(target a5 a17).env)

def check (p : Bool) (pipeline : Roadmap.Pipeline) (checked : Bool) (old rhs : Roadmap.Address) : Bool :=
  let src := source p old rhs
  let tgt := target old rhs
  match (Source.evalE (globals p pipeline) {F0 with checked := checked} 3
      (.conv (.assign (.local (.here : Source.Idx SrcCtx (.udvt d))) (.local (.there .here))) (Or.inr rfl))).run src,
      (assignLocalOperand .here (.there .here)).run tgt,
      (assignLocalOperand .here (.there .here)).code.run tgt with
  | (.ok (.val v),post),.ok (out,.prim n),.ok cap =>
      v.key == some (rhs.val : Int) && n.val == (rhs.val : Int) &&
      (post.1.get .here).key == v.key && (post.1.get (.there .here)).key == v.key &&
      (TEnv.get .here out.st.env).val == (rhs.val : Int) &&
      (TEnv.get (.there .here) out.st.env).val == (rhs.val : Int) &&
      (TEnv.get .here cap.st.env).val == (rhs.val : Int) &&
      (TEnv.get (.there .here) cap.st.env).val == (rhs.val : Int)
  | _,_,_ => false

/-- info: true -/
#guard_msgs in
#eval IO.println (reprStr ([false,true].all fun p => [Roadmap.Pipeline.legacy,.viaIR].all fun pipeline =>
  [false,true].all fun checked => [AddressConversionControls.addr 0,AddressConversionControls.addr 1,AddressConversionControls.addr (2^159),AddressConversionControls.addr (2^160-1)].all fun old =>
    [AddressConversionControls.addr 0,AddressConversionControls.addr 1,AddressConversionControls.addr (2^159),AddressConversionControls.addr (2^160-1)].all fun rhs => check p pipeline checked old rhs))

/-- info: true -/
#guard_msgs in
#eval IO.println (reprStr (
  let tgt := target a5 a17
  match (assignLocalOperand .here (.there .here)).run tgt,
      (Val.simple (.local .here) : Val C TgtCtx .uint).evalT tgt with
  | .ok (out,.prim reached),.ok stale => reached.val == 17 && stale.val == 5 &&
      (TEnv.get .here out.st.env).val == 17
  | _,_ => false))

/-- info: true -/
#guard_msgs in
#eval IO.println (reprStr ([false,true].all fun p =>
  let v := value d p (underlying p) a17
  let w := value e p (other_underlying p) a17
  match Source.convVal (.udvt e) v with
  | .error (.stuck why) => v.key == w.key && why == "user-defined value type" &&
      !(Source.STy.udvt d).implicit (E p).isBase (E p).mapFree (.udvt e)
  | _ => false))

-- Execute the incorrect typed uint8 truncation on the actual fresh capture.
/-- info: true -/
#guard_msgs in
#eval IO.println (reprStr (
  let a := AddressConversionControls.addr (2^160-1)
  let tgt := target a5 a
  match (assignLocalOperand .here (.there .here)).run tgt,
      (assignLocalOperand .here (.there .here)).code.run tgt with
  | .ok (_,.prim n),.ok cap =>
      match (UnsignedCasts.castValue 8 (.simple (.local .here))).evalT cap.st with
      | .ok wrong => n.val == (a.val : Int) && wrong.val == 255 && n.val != wrong.val &&
          (TEnv.get .here cap.st.env).val == n.val
      | _ => false
  | _,_ => false))

/-- info: 'Solidity.Lowering.V07.UdvtAddressAssignmentControls.underlying' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms Solidity.Lowering.V07.UdvtAddressAssignmentControls.underlying

/-- info: 'Solidity.Lowering.V07.UdvtAddressAssignmentControls.other_underlying' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms Solidity.Lowering.V07.UdvtAddressAssignmentControls.other_underlying

/-- info: 'Solidity.Lowering.V07.UdvtAddressAssignmentControls.initial' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Solidity.Lowering.V07.UdvtAddressAssignmentControls.initial

/-- info: 'Solidity.Lowering.V07.UdvtAddressAssignmentControls.reflect' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Solidity.Lowering.V07.UdvtAddressAssignmentControls.reflect

/-- info: 'Solidity.Lowering.V07.UdvtAddressAssignmentControls.key_client' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms Solidity.Lowering.V07.UdvtAddressAssignmentControls.key_client

/-- info: 'Solidity.Lowering.V07.UdvtAddressAssignmentControls.related_client' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms Solidity.Lowering.V07.UdvtAddressAssignmentControls.related_client

/-- info: 'Solidity.Lowering.V07.UdvtAddressAssignmentControls.read_client' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms Solidity.Lowering.V07.UdvtAddressAssignmentControls.read_client

/-- info: 'Solidity.Lowering.V07.UdvtAddressAssignmentControls.source_client' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms Solidity.Lowering.V07.UdvtAddressAssignmentControls.source_client

/-- info: 'Solidity.Lowering.V07.UdvtAddressAssignmentControls.transport_client' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms Solidity.Lowering.V07.UdvtAddressAssignmentControls.transport_client

/-- info: 'Solidity.Lowering.V07.UdvtAddressAssignmentControls.self_client' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms Solidity.Lowering.V07.UdvtAddressAssignmentControls.self_client

/-- info: 'Solidity.Lowering.V07.UdvtAddressAssignmentControls.extension_client' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms Solidity.Lowering.V07.UdvtAddressAssignmentControls.extension_client

end Solidity.Lowering.V07.UdvtAddressAssignmentControls
