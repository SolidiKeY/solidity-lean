import Solidity.Lowering.V07.UdvtFixedBytesAssignment
import Solidity.Lowering.V07.FixedBytesAssignmentControls

namespace Solidity.Lowering.V07.UdvtFixedBytesAssignmentControls
open UdvtFixedBytesAssignment Source.SemanticsExamples
open MixedAssignmentControls (C path)
def d : Source.DeclName := ⟨none,"Packet"⟩
def e : Source.DeclName := ⟨none,"Other"⟩
def E (n : Nat) (w : 1 ≤ n ∧ n ≤ 32) : Source.Env :=
  ⟨⟨.udvt,"Packet",none,false,.udvt "Packet" (.fixedBytes n w)⟩ ::
    ⟨.udvt,"Other",none,false,.udvt "Other" (.fixedBytes n w)⟩ :: MixedAssignmentControls.E.decls⟩
theorem underlying (n : Nat) (w : 1 ≤ n ∧ n ≤ 32) : (E n w).layout.underlying d = .fixedBytes n w := by
  rfl
theorem other_underlying (n : Nat) (w : 1 ≤ n ∧ n ≤ 32) : (E n w).layout.underlying e = .fixedBytes n w := by
  rfl
abbrev SrcCtx : Source.RCtx := [.udvt d,.udvt d,.bytes .memory,.bytes .storage]
abbrev TgtCtx : Ctx := [.val .uint,.val .uint,.mem bytesR,.alias bytesR]
def source (n : Nat) (w : 1 ≤ n ∧ n ≤ 32) (old rhs : List UInt8) : Source.EMState (E n w) SrcCtx :=
  (.cons (value d n w (underlying n w) (FixedBytesAssignmentControls.payload n old) (Source.fitBytes_length n old))
    (.cons (value d n w (underlying n w) (FixedBytesAssignmentControls.payload n rhs) (Source.fitBytes_length n rhs))
    (.cons (.memRef rfl 0) (.cons (.storRef rfl path) .nil))),
    {s0 with heap := ((Source.Heap.empty : Source.Heap (E n w).layout).alloc ⟨.bytes .memory,.bytes [0,0]⟩).1})
def target := FixedBytesAssignmentControls.target
def mapping : ContextMap SrcCtx TgtCtx :=
  (((ContextMap.empty.cons (.bytes .storage) (.alias bytesR)).cons (.bytes .memory) (.mem bytesR)).cons
    (.udvt d) (.val .uint)).cons (.udvt d) (.val .uint)
def BindingRel (n : Nat) (w : 1 ≤ n ∧ n ≤ 32) : (τ : Source.STy) → (u : LTy) → Source.Val (E n w).layout τ →
    u.TDenote C MixedAssignmentControls.memory.H → Prop
  | .udvt δ,.val .uint,v,x => Rel δ v x
  | .bytes .memory,.mem (.array (.prim .uint)),v,r => v = .memRef rfl 0 ∧ r = some P12Controls.memoryRef
  | .bytes .storage,.alias (.array (.prim .uint)),v,r => v = .storRef rfl path ∧ r = some MixedAssignmentControls.storageRef
  | _,_,_,_ => False

theorem initial (n : Nat) (w : 1 ≤ n ∧ n ≤ 32) (old rhs : List UInt8) :
    mapping.Related (BindingRel n w) (source n w old rhs).1 (target n w old rhs).env := by
  intro τ i
  cases i with
  | here => exact value_related d n w (underlying n w) (FixedBytesAssignmentControls.payload n old) (Source.fitBytes_length n old)
  | there i => cases i with
    | here => exact value_related d n w (underlying n w) (FixedBytesAssignmentControls.payload n rhs) (Source.fitBytes_length n rhs)
    | there i => cases i with
      | here => exact ⟨rfl,rfl⟩
      | there i => cases i with
        | here => exact ⟨rfl,rfl⟩
        | there i => nomatch i

theorem reflect (n : Nat) (w : 1 ≤ n ∧ n ≤ 32) (v : Source.Val (E n w).layout (.udvt d))
    (x : PrimTy.uint.Denote) (agrees : BindingRel n w (.udvt d) (.val .uint) v x) : Rel d v x := by
  exact agrees

def program (n : Nat) (w : 1 ≤ n ∧ n ≤ 32) : Source.Program (E n w) where
  body _ := none
  consts _ := none
  inits _ := []
  ctor _ := none
  ctorLocals _ := []
  baseArgs _ := []
  contracts := []
def globals (n : Nat) (w : 1 ≤ n ∧ n ≤ 32) (p : Roadmap.Pipeline) : Source.Glob (E n w) :=
  ⟨program n w,p,toyFixed,fun _ => word 0,fun _ _ => false,fun _ => .answer (.success []),word 0⟩
def key_client (n : Nat) (w : 1 ≤ n ∧ n ≤ 32) (bs : List UInt8) :=
  value_key d n w (underlying n w) (FixedBytesAssignmentControls.payload n bs) (Source.fitBytes_length n bs)
def related_client (n : Nat) (w : 1 ≤ n ∧ n ≤ 32) (bs : List UInt8) :=
  value_related d n w (underlying n w) (FixedBytesAssignmentControls.payload n bs) (Source.fitBytes_length n bs)
def read_client (n : Nat) (w : 1 ≤ n ∧ n ≤ 32) (bs : List UInt8) :=
  read_value d n w (underlying n w) (FixedBytesAssignmentControls.payload n bs) (Source.fitBytes_length n bs) _ (related_client n w bs)
def contents_client (n : Nat) (w : 1 ≤ n ∧ n ≤ 32) (bs : List UInt8) :=
  contents_observe d n w (underlying n w) (FixedBytesAssignmentControls.payload n bs) (Source.fitBytes_length n bs) _ (related_client n w bs)
def source_client (n : Nat) (w : 1 ≤ n ∧ n ≤ 32) (p : Roadmap.Pipeline) (checked : Bool) (old rhs : List UInt8) :=
  UdvtAssignment.source_assignment (globals n w p) {F0 with checked := checked} 0
    (source n w old rhs) d .here (.there .here)
    (value d n w (underlying n w) (FixedBytesAssignmentControls.payload n rhs) (Source.fitBytes_length n rhs)) rfl
def transport_client (n : Nat) (w : 1 ≤ n ∧ n ≤ 32) (p : Roadmap.Pipeline) (checked : Bool) (old rhs : List UInt8) :=
  transport (globals n w p) {F0 with checked := checked} 0 (source n w old rhs) (target n w old rhs)
    d n w (underlying n w) mapping (BindingRel n w) (initial n w old rhs) (reflect n w)
    .here (.there .here) .here (.there .here) rfl rfl (FixedBytesAssignmentControls.payload n rhs) (Source.fitBytes_length n rhs) rfl
def self_client (n : Nat) (w : 1 ≤ n ∧ n ≤ 32) (p : Roadmap.Pipeline) (checked : Bool) (bs : List UInt8) :=
  transport (globals n w p) {F0 with checked := checked} 0 (source n w bs []) (target n w bs [])
    d n w (underlying n w) mapping (BindingRel n w) (initial n w bs []) (reflect n w)
    .here .here .here .here rfl rfl (FixedBytesAssignmentControls.payload n bs) (Source.fitBytes_length n bs) rfl
def extension_client := DeferredSource.Operand.run_wk
  (assignLocalOperand .here (.there .here) : DeferredSource.Operand C TgtCtx (.prim .uint))
  (Thin.drop (t := .val .bool) Thin.refl) (target 2 (by decide) [0,0] [0,1])
  (true,(target 2 (by decide) [0,0] [0,1]).env)

def check (n : Nat) (w : 1 ≤ n ∧ n ≤ 32) (p : Roadmap.Pipeline) (checked : Bool) (old rhs : List UInt8) : Bool :=
  let expected := FixedBytesAssignmentControls.payload n rhs
  match (Source.evalE (globals n w p) {F0 with checked := checked} 3
      (.conv (.assign (.local (.here : Source.Idx SrcCtx (.udvt d))) (.local (.there .here))) (Or.inr rfl))).run (source n w old rhs),
      (assignLocalOperand .here (.there .here)).run (target n w old rhs),
      (assignLocalOperand .here (.there .here)).code.run (target n w old rhs) with
  | (.ok (.val v),post),.ok (out,.prim x),.ok cap =>
      v.key == some (Source.bytesNat expected : Int) && x.val == (Source.bytesNat expected : Int) &&
      (post.1.get .here).key == v.key && (post.1.get (.there .here)).key == v.key &&
      (TEnv.get .here out.st.env).val == x.val && (TEnv.get (.there .here) out.st.env).val == x.val &&
      (TEnv.get .here cap.st.env).val == x.val && (TEnv.get (.there .here) cap.st.env).val == x.val &&
      Source.beBytes n (TEnv.get .here cap.st.env).val.toNat == expected
  | _,_,_ => false

/-- info: true -/
#guard_msgs in
#eval IO.println (reprStr ((List.range 33).all fun n =>
  if w : 1 ≤ n ∧ n ≤ 32 then [Roadmap.Pipeline.legacy,.viaIR].all fun p => [false,true].all fun checked =>
    [[],List.replicate (n-1) 0 ++ [1],List.replicate n 255,1 :: List.replicate (n-1) 0].all fun old =>
      [[],List.replicate (n-1) 0 ++ [1],List.replicate n 255,1 :: List.replicate (n-1) 0].all fun rhs => check n w p checked old rhs
  else true))

-- Equal payload and underlying width do not authorize a cross-nominal Source conversion.
/-- info: true -/
#guard_msgs in
#eval IO.println (reprStr ((List.range 33).all fun n =>
  if w : 1 ≤ n ∧ n ≤ 32 then
    let bs := FixedBytesAssignmentControls.payload n [0,1]
    let v := value d n w (underlying n w) bs (Source.fitBytes_length n [0,1])
    let other := value e n w (other_underlying n w) bs (Source.fitBytes_length n [0,1])
    match Source.convVal (.udvt e) v with
    | .error (.stuck why) => v.key == other.key && why == "user-defined value type" &&
        !(Source.STy.udvt d).implicit (E n w).isBase (E n w).mapFree (.udvt e)
    | _ => false
  else true))

-- Actual stale read and wrong typed truncation of the fresh native capture.
/-- info: true -/
#guard_msgs in
#eval IO.println (reprStr (
  let tgt := target 2 (by decide) [0,0] [1,2]
  match (assignLocalOperand .here (.there .here)).code.run tgt,
      (Val.simple (.local .here) : Val C TgtCtx .uint).evalT tgt with
  | .ok cap,.ok stale => match (UnsignedCasts.castValue 8 (.simple (.local .here))).evalT cap.st with
      | .ok wrong => stale.val == 0 && wrong.val == 2 && (TEnv.get .here cap.st.env).val == 258 &&
          Source.beBytes 2 (TEnv.get .here cap.st.env).val.toNat == [1,2]
      | _ => false
  | _,_ => false))
/-- info: 'Solidity.Lowering.V07.UdvtFixedBytesAssignmentControls.underlying' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms Solidity.Lowering.V07.UdvtFixedBytesAssignmentControls.underlying

/-- info: 'Solidity.Lowering.V07.UdvtFixedBytesAssignmentControls.other_underlying' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms Solidity.Lowering.V07.UdvtFixedBytesAssignmentControls.other_underlying

/-- info: 'Solidity.Lowering.V07.UdvtFixedBytesAssignmentControls.initial' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms Solidity.Lowering.V07.UdvtFixedBytesAssignmentControls.initial

/-- info: 'Solidity.Lowering.V07.UdvtFixedBytesAssignmentControls.reflect' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms Solidity.Lowering.V07.UdvtFixedBytesAssignmentControls.reflect

/-- info: 'Solidity.Lowering.V07.UdvtFixedBytesAssignmentControls.key_client' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms Solidity.Lowering.V07.UdvtFixedBytesAssignmentControls.key_client

/-- info: 'Solidity.Lowering.V07.UdvtFixedBytesAssignmentControls.related_client' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms Solidity.Lowering.V07.UdvtFixedBytesAssignmentControls.related_client

/-- info: 'Solidity.Lowering.V07.UdvtFixedBytesAssignmentControls.read_client' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms Solidity.Lowering.V07.UdvtFixedBytesAssignmentControls.read_client

/-- info: 'Solidity.Lowering.V07.UdvtFixedBytesAssignmentControls.contents_client' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms Solidity.Lowering.V07.UdvtFixedBytesAssignmentControls.contents_client

/-- info: 'Solidity.Lowering.V07.UdvtFixedBytesAssignmentControls.source_client' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms Solidity.Lowering.V07.UdvtFixedBytesAssignmentControls.source_client

/-- info: 'Solidity.Lowering.V07.UdvtFixedBytesAssignmentControls.transport_client' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms Solidity.Lowering.V07.UdvtFixedBytesAssignmentControls.transport_client

/-- info: 'Solidity.Lowering.V07.UdvtFixedBytesAssignmentControls.self_client' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms Solidity.Lowering.V07.UdvtFixedBytesAssignmentControls.self_client

/-- info: 'Solidity.Lowering.V07.UdvtFixedBytesAssignmentControls.extension_client' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms Solidity.Lowering.V07.UdvtFixedBytesAssignmentControls.extension_client

end Solidity.Lowering.V07.UdvtFixedBytesAssignmentControls
