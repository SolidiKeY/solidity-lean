import Solidity.Lowering.V07.FixedBytesAssignment
import Solidity.Lowering.V07.P12Controls
import Solidity.Lowering.V07.UnsignedCasts

namespace Solidity.Lowering.V07.FixedBytesAssignmentControls
open FixedBytesAssignment Source.SemanticsExamples
open MixedAssignmentControls (C E path globals)
def payload (n : Nat) (bs : List UInt8) := Source.fitBytes n bs
abbrev SrcCtx (n : Nat) (w : 1 ≤ n ∧ n ≤ 32) : Source.RCtx :=
  [.fixedBytes n w,.fixedBytes n w,.bytes .memory,.bytes .storage]
abbrev TgtCtx : Ctx := [.val .uint,.val .uint,.mem bytesR,.alias bytesR]
def source (n : Nat) (w : 1 ≤ n ∧ n ≤ 32) (old rhs : List UInt8) : Source.EMState E (SrcCtx n w) :=
  (.cons (.fixedBytes (payload n old) (Source.fitBytes_length n old))
    (.cons (.fixedBytes (payload n rhs) (Source.fitBytes_length n rhs))
    (.cons (.memRef rfl 0) (.cons (.storRef rfl path) .nil))),
    {s0 with heap := ((Source.Heap.empty : Source.Heap E.layout).alloc ⟨.bytes .memory,.bytes [0,0]⟩).1})
def target (n : Nat) (w : 1 ≤ n ∧ n ≤ 32) (old rhs : List UInt8) : State C TgtCtx :=
  (MixedAssignmentControls.memory.push (value n w (payload n rhs) (Source.fitBytes_length n rhs))).push
    (value n w (payload n old) (Source.fitBytes_length n old))
def mapping (n : Nat) (w : 1 ≤ n ∧ n ≤ 32) : ContextMap (SrcCtx n w) TgtCtx :=
  (((ContextMap.empty.cons (.bytes .storage) (.alias bytesR)).cons (.bytes .memory) (.mem bytesR)).cons
    (.fixedBytes n w) (.val .uint)).cons (.fixedBytes n w) (.val .uint)
def BindingRel : (τ : Source.STy) → (u : LTy) → Source.Val E.layout τ →
    u.TDenote C MixedAssignmentControls.memory.H → Prop
  | .fixedBytes n w,.val .uint,v,x => Rel n w v x
  | .bytes .memory,.mem (.array (.prim .uint)),v,r => v = .memRef rfl 0 ∧ r = some P12Controls.memoryRef
  | .bytes .storage,.alias (.array (.prim .uint)),v,r => v = .storRef rfl path ∧ r = some MixedAssignmentControls.storageRef
  | _,_,_,_ => False

theorem initial (n : Nat) (w : 1 ≤ n ∧ n ≤ 32) (old rhs : List UInt8) :
    (mapping n w).Related BindingRel (source n w old rhs).1 (target n w old rhs).env := by
  intro τ i
  cases i with
  | here => exact related n w (payload n old) (Source.fitBytes_length n old)
  | there i => cases i with
    | here => exact related n w (payload n rhs) (Source.fitBytes_length n rhs)
    | there i => cases i with
      | here => exact ⟨rfl,rfl⟩
      | there i => cases i with
        | here => exact ⟨rfl,rfl⟩
        | there i => nomatch i

theorem reflect (n : Nat) (w : 1 ≤ n ∧ n ≤ 32) (v : Source.Val E.layout (.fixedBytes n w))
    (x : PrimTy.uint.Denote) (agrees : BindingRel (.fixedBytes n w) (.val .uint) v x) : Rel n w v x := by
  exact agrees

def range_client (n : Nat) (w : 1 ≤ n ∧ n ≤ 32) (bs : List UInt8) :=
  FixedBytesAssignment.range n w (payload n bs) (Source.fitBytes_length n bs)
def related_client (n : Nat) (w : 1 ≤ n ∧ n ≤ 32) (bs : List UInt8) :=
  related (D := E.layout) n w (payload n bs) (Source.fitBytes_length n bs)
def read_client (n : Nat) (w : 1 ≤ n ∧ n ≤ 32) (bs : List UInt8) :=
  read_value n w (payload n bs) (Source.fitBytes_length n bs) _ (related_client n w bs)
def decode_client (n : Nat) (w : 1 ≤ n ∧ n ≤ 32) (bs : List UInt8) :=
  decode_value n w (payload n bs) (Source.fitBytes_length n bs)
def contents_client := contents_reflect 2 (by decide) [0,1] (Source.beBytes 2 1)
  (by decide) (Source.beBytes_length 2 1) (by decide)
def source_client (n : Nat) (w : 1 ≤ n ∧ n ≤ 32) (p : Roadmap.Pipeline) (checked : Bool)
    (old rhs : List UInt8) :=
  source_assign_local_run (globals p) {F0 with checked := checked} 0 (source n w old rhs)
    (.here : Source.Idx (SrcCtx n w) (.fixedBytes n w)) (.there .here)
    (.fixedBytes (payload n rhs) (Source.fitBytes_length n rhs)) rfl
def transport_client (n : Nat) (w : 1 ≤ n ∧ n ≤ 32) (p : Roadmap.Pipeline) (checked : Bool)
    (old rhs : List UInt8) :=
  transport (globals p) {F0 with checked := checked} 0 (source n w old rhs) (target n w old rhs)
    n w (mapping n w) BindingRel (initial n w old rhs) (reflect n w)
    .here (.there .here) .here (.there .here) rfl rfl (payload n rhs) (Source.fitBytes_length n rhs) rfl
def self_client (n : Nat) (w : 1 ≤ n ∧ n ≤ 32) (p : Roadmap.Pipeline) (checked : Bool) (bs : List UInt8) :=
  transport (globals p) {F0 with checked := checked} 0 (source n w bs []) (target n w bs [])
    n w (mapping n w) BindingRel (initial n w bs []) (reflect n w)
    .here .here .here .here rfl rfl (payload n bs) (Source.fitBytes_length n bs) rfl
def extension_client := DeferredSource.Operand.run_wk
  (assignLocalOperand .here (.there .here) : DeferredSource.Operand C TgtCtx (.prim .uint))
  (Thin.drop (t := .val .bool) Thin.refl) (target 2 (by decide) [0,0] [0,1])
  (true,(target 2 (by decide) [0,0] [0,1]).env)

def check (n : Nat) (w : 1 ≤ n ∧ n ≤ 32) (p : Roadmap.Pipeline) (checked : Bool)
    (old rhs : List UInt8) : Bool :=
  let expected := payload n rhs
  match (Source.evalE (globals p) {F0 with checked := checked} 2
      (.assign (.local (.here : Source.Idx (SrcCtx n w) (.fixedBytes n w))) (.local (.there .here)))).run (source n w old rhs),
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
  if w : 1 ≤ n ∧ n ≤ 32 then
    [Roadmap.Pipeline.legacy,.viaIR].all fun p => [false,true].all fun checked =>
      [[],List.replicate (n-1) 0 ++ [1],List.replicate n 255,1 :: List.replicate (n-1) 0].all fun old =>
        [[],List.replicate (n-1) 0 ++ [1],List.replicate n 255,1 :: List.replicate (n-1) 0].all fun rhs => check n w p checked old rhs
  else true))

-- Equal numeric keys do not erase the Source byte width or leading zero.
/-- info: true -/
#guard_msgs in
#eval IO.println (reprStr (
  let x : Source.Val E.layout (.fixedBytes 1 (by decide)) := .fixedBytes [1] (by decide)
  let y : Source.Val E.layout (.fixedBytes 2 (by decide)) := .fixedBytes [0,1] (by decide)
  x.key == y.key && Source.beBytes 1 1 != Source.beBytes 2 1 &&
    Source.beBytes 2 1 == [0,1]))

-- Compare actual big-endian assignment/capture against reversed-byte and stale reads.
/-- info: true -/
#guard_msgs in
#eval IO.println (reprStr (
  let tgt := target 2 (by decide) [0,0] [1,2]
  match (assignLocalOperand .here (.there .here)).run tgt,
      (Val.simple (.local .here) : Val C TgtCtx .uint).evalT tgt with
  | .ok (_,.prim x),.ok stale => x.val == 258 && stale.val == 0 &&
      Source.beBytes 2 x.val.toNat == [1,2] && Source.bytesNat [2,1] != x.val.toNat
  | _,_ => false))

-- Incorrect executed uint8 truncation loses the leading byte of the fresh capture.
/-- info: true -/
#guard_msgs in
#eval IO.println (reprStr (
  let tgt := target 2 (by decide) [0,0] [1,2]
  match (assignLocalOperand .here (.there .here)).code.run tgt with
  | .ok cap => match (UnsignedCasts.castValue 8 (.simple (.local .here))).evalT cap.st with
      | .ok wrong => wrong.val == 2 && (TEnv.get .here cap.st.env).val == 258
      | _ => false
  | _ => false))
/-- info: 'Solidity.Lowering.V07.FixedBytesAssignmentControls.initial' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Solidity.Lowering.V07.FixedBytesAssignmentControls.initial

/-- info: 'Solidity.Lowering.V07.FixedBytesAssignmentControls.reflect' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Solidity.Lowering.V07.FixedBytesAssignmentControls.reflect

/-- info: 'Solidity.Lowering.V07.FixedBytesAssignmentControls.range_client' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms Solidity.Lowering.V07.FixedBytesAssignmentControls.range_client

/-- info: 'Solidity.Lowering.V07.FixedBytesAssignmentControls.related_client' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms Solidity.Lowering.V07.FixedBytesAssignmentControls.related_client

/-- info: 'Solidity.Lowering.V07.FixedBytesAssignmentControls.read_client' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms Solidity.Lowering.V07.FixedBytesAssignmentControls.read_client

/-- info: 'Solidity.Lowering.V07.FixedBytesAssignmentControls.decode_client' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms Solidity.Lowering.V07.FixedBytesAssignmentControls.decode_client

/-- info: 'Solidity.Lowering.V07.FixedBytesAssignmentControls.contents_client' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms Solidity.Lowering.V07.FixedBytesAssignmentControls.contents_client

/-- info: 'Solidity.Lowering.V07.FixedBytesAssignmentControls.source_client' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms Solidity.Lowering.V07.FixedBytesAssignmentControls.source_client

/-- info: 'Solidity.Lowering.V07.FixedBytesAssignmentControls.transport_client' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms Solidity.Lowering.V07.FixedBytesAssignmentControls.transport_client

/-- info: 'Solidity.Lowering.V07.FixedBytesAssignmentControls.self_client' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms Solidity.Lowering.V07.FixedBytesAssignmentControls.self_client

/-- info: 'Solidity.Lowering.V07.FixedBytesAssignmentControls.extension_client' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms Solidity.Lowering.V07.FixedBytesAssignmentControls.extension_client

end Solidity.Lowering.V07.FixedBytesAssignmentControls
