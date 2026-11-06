import Solidity.Lowering.V07.AddressConversions
import Solidity.Lowering.V07.WordCastControls
import Solidity.Lowering.V07.P12Controls

namespace Solidity.Lowering.V07.AddressConversionControls
open AddressConversions
open Source.SemanticsExamples
open MixedAssignmentControls (C E globals path)

def addr (n : Nat) : Roadmap.Address := ⟨n % 2^160,Nat.mod_lt _ (by decide)⟩
def a5 := addr 5
def a17 := addr 17
abbrev AddrCtx : Source.RCtx := [.address false,.address false,.bytes .memory,.bytes .storage]
abbrev TgtCtx : Ctx := [.val .uint,.val .uint,.mem bytesR,.alias bytesR]
def source (old rhs : Roadmap.Address) : Source.EMState E AddrCtx :=
  (.cons (.address old) (.cons (.address rhs) (.cons (.memRef rfl 0)
    (.cons (.storRef rfl path) .nil))),WordCastControls.source ty 5 17 (by decide) (by decide) |>.2)
def target (old rhs : Roadmap.Address) : State C TgtCtx :=
  WordCastControls.target ty old.val rhs.val (address_range old) (address_range rhs)
def intSource := WordCastControls.source ty 5 17 (by decide) (by decide)
def tgt := target a5 a17

def mapping : ContextMap AddrCtx TgtCtx :=
  (((ContextMap.empty.cons (.bytes .storage) (.alias bytesR)).cons (.bytes .memory) (.mem bytesR)).cons
    (.address false) (.val .uint)).cons (.address false) (.val .uint)
def BindingRel : (τ : Source.STy) → (u : LTy) → Source.Val E.layout τ → u.TDenote C tgt.H → Prop
  | .address false,.val .uint,v,n => AddressRel false v n
  | τ,u,v,n => P12Controls.BindingRel τ u v n

theorem initial_addr (old rhs : Roadmap.Address) :
    mapping.Related BindingRel (source old rhs).1 (target old rhs).env := by
  intro τ i
  cases i with
  | here => exact address_related false old
  | there i => cases i with
    | here => exact address_related false rhs
    | there i => cases i with
      | here => exact ⟨rfl,rfl⟩
      | there i => cases i with
        | here => exact ⟨rfl,rfl⟩
        | there i => nomatch i

theorem reflect_addr (v : Source.Val E.layout (.address false)) (n : PrimTy.uint.Denote)
    (related : BindingRel (.address false) (.val .uint) v n) : AddressRel false v n := related

def range_client := address_range a17
def observe_client := addressOfInteger_observe 17 (by decide)
def related_client := address_related (D := E.layout) false a17
def read_client := address_read (D := E.layout) false a17 (addressValue a17) (address_related false a17)
def integer_read_client := integer_read (D := E.layout) 17 (by decide) (integerValue ty 17 (by decide)) (integer_related ty _ _)
def from_related_client := from_uint_related (D := E.layout) 17 (by decide)
def rule_client := direct_int_rule E Source.IntTy.u256 false
def allowed_from_client := allowed_from E
def allowed_to_client := allowed_to E
def from_value_client := source_from_uint (D := E.layout) 17 (by decide)
def to_value_client := source_to_uint (D := E.layout) a17
def injective_client := addressValue_injective a17 a17 rfl
def distinct_client : addressValue a5 ≠ addressValue a17 := by decide

def from_run_client (p : Roadmap.Pipeline) (checked : Bool) (fuel : Nat) :=
  source_from_run (globals p) {F0 with checked := checked} (fuel+1) intSource intSource
    (.local .here) 5 (by decide) rfl
def to_run_client (p : Roadmap.Pipeline) (checked : Bool) (fuel : Nat) :=
  source_to_run (globals p) {F0 with checked := checked} (fuel+1) (source a5 a17) (source a5 a17)
    (.local .here) a5 rfl
def from_local_client (p : Roadmap.Pipeline) (checked : Bool) (fuel : Nat) :=
  source_from_local (globals p) {F0 with checked := checked} fuel intSource .here 5 (by decide) rfl
def to_local_client (p : Roadmap.Pipeline) (checked : Bool) (fuel : Nat) :=
  source_to_local (globals p) {F0 with checked := checked} fuel (source a5 a17) .here a5 rfl
def from_transport_client (p : Roadmap.Pipeline) (checked : Bool) (fuel : Nat) :=
  from_local_transport (globals p) {F0 with checked := checked} fuel intSource tgt .here .here
    5 (by decide) rfl (integer_related ty _ _)
def to_transport_client (p : Roadmap.Pipeline) (checked : Bool) (fuel : Nat) :=
  to_local_transport (globals p) {F0 with checked := checked} fuel (source a5 a17) tgt .here .here
    a5 rfl (address_related false a5)
def from_source_assignment_client (p : Roadmap.Pipeline) (checked : Bool) (fuel : Nat) :=
  source_from_assignment (globals p) {F0 with checked := checked} fuel intSource .here (.there .here) 17 (by decide) rfl

def from_assignment_client (p : Roadmap.Pipeline) (checked : Bool) (fuel : Nat) :=
  from_assignment_transport (globals p) {F0 with checked := checked} fuel intSource tgt
    (WordCastControls.si ty) (WordCastControls.ti ty) (WordCastControls.initial ty 5 17 (by decide) (by decide))
    true false 17 (by decide) rfl
def from_self_client (p : Roadmap.Pipeline) (checked : Bool) (fuel : Nat) :=
  from_assignment_transport (globals p) {F0 with checked := checked} fuel intSource tgt
    (WordCastControls.si ty) (WordCastControls.ti ty) (WordCastControls.initial ty 5 17 (by decide) (by decide))
    true true 5 (by decide) rfl
def from_repeated_client (p : Roadmap.Pipeline) (checked : Bool) (fuel : Nat) :=
  from_assignment_transport (globals p) {F0 with checked := checked} fuel intSource tgt
    (fun k : Fin 3 => WordCastControls.si ty (decide (k.val ≠ 1)))
    (fun k : Fin 3 => WordCastControls.ti ty (decide (k.val ≠ 1)))
    ((WordCastControls.initial ty 5 17 (by decide) (by decide)).reindex (fun k : Fin 3 => decide (k.val ≠ 1)))
    0 1 17 (by decide) rfl

def to_source_assignment_client (p : Roadmap.Pipeline) (checked : Bool) (fuel : Nat) :=
  source_to_assignment (globals p) {F0 with checked := checked} fuel (source a5 a17) .here (.there .here) a17 rfl

def to_assignment_client (p : Roadmap.Pipeline) (checked : Bool) (fuel : Nat) :=
  to_assignment_transport (globals p) {F0 with checked := checked} fuel (source a5 a17) tgt
    mapping BindingRel (initial_addr a5 a17) reflect_addr .here (.there .here) .here (.there .here) rfl rfl a17 rfl
def to_self_client (p : Roadmap.Pipeline) (checked : Bool) (fuel : Nat) :=
  to_assignment_transport (globals p) {F0 with checked := checked} fuel (source a5 a17) tgt
    mapping BindingRel (initial_addr a5 a17) reflect_addr .here .here .here .here rfl rfl a5 rfl
def to_equal_values_client (p : Roadmap.Pipeline) (checked : Bool) (fuel : Nat) :=
  to_assignment_transport (globals p) {F0 with checked := checked} fuel (source a17 a17) (target a17 a17)
    mapping BindingRel (initial_addr a17 a17) reflect_addr .here (.there .here) .here (.there .here) rfl rfl a17 rfl

def extension_client := DeferredSource.Operand.run_wk (assignLocalOperand .here (.there .here))
  (Thin.drop (t := .val .bool) Thin.refl) tgt (true,tgt.env)
def binder_client (p : Roadmap.Pipeline) (checked : Bool) (fuel : Nat) :=
  to_assignment_transport (globals p) {F0 with checked := checked} fuel
    (Source.Locals.cons (.bool true) (source a5 a17).1,(source a5 a17).2) (tgt.push (t := .val .bool) true)
    (mapping.cons .bool (.val .bool)) BindingRel
    (ContextMap.related_cons mapping BindingRel (source a5 a17).1 tgt.env
      (initial_addr a5 a17) .bool (.val .bool) (.bool true) true rfl) reflect_addr
    (.there .here) (.there (.there .here)) (.there .here) (.there (.there .here)) rfl rfl a17 rfl

def live_client := P12Controls.live_memory_and_storage

def check (p : Roadmap.Pipeline) (checked : Bool) (old rhs : Roadmap.Address) : Bool :=
  let ints := WordCastControls.source ty old.val rhs.val (address_range old) (address_range rhs)
  let addresses := source old rhs
  let tgt := target old rhs
  let fr := (Source.evalE (globals p) {F0 with checked := checked} 3
    (.convExplicit (τ := .address false) (.assign (.local .here) (.local (.there .here))) (allowed_from E))).run ints
  let tr := (Source.evalE (globals p) {F0 with checked := checked} 3
    (.convExplicit (τ := .int ty) (.assign (.local .here) (.local (.there .here))) (allowed_to E))).run addresses
  match fr.1,tr.1,(assignLocalOperand .here (.there .here)).run tgt with
  | .ok (.val (.address a)),.ok (.val (.int x _)),.ok (out,.prim w) =>
      a.val == rhs.val && x == (rhs.val : Int) && w.val == x &&
      (fr.2.1.get .here).key == some x && (fr.2.1.get (.there .here)).key == some x &&
      (tr.2.1.get .here).key == some x && (tr.2.1.get (.there .here)).key == some x &&
      (TEnv.get .here out.st.env).val == x && (TEnv.get (.there .here) out.st.env).val == x
  | _,_,_ => false

/-- info: true -/
#guard_msgs in
#eval IO.println (reprStr ([Roadmap.Pipeline.legacy,.viaIR].all fun p => [false,true].all fun checked =>
  [0,1,5,17,2^159,2^160-1,2^160,2^160+17].all fun old =>
  [0,1,5,17,2^159,2^160-1,2^160,2^160+17].all fun rhs => check p checked (addr old) (addr rhs)))

-- Actual published typing refusals remain unchanged.
/-- info: true -/
#guard_msgs in
#eval IO.println (reprStr (
  !(Source.STy.int .u256).explicit E.isBase E.mapFree (.address false) &&
  !(Source.STy.int ty).explicit E.isBase E.mapFree (.address true) &&
  !(Source.STy.int ⟨true,160,by decide⟩).explicit E.isBase E.mapFree (.address false)))

-- Low bits alone do not establish the canonical address representation relation.
/-- info: true -/
#guard_msgs in
#eval IO.println (reprStr (
  (addressValue (addr 0)).val == 0 &&
  (PrimTy.num? (p := .uint) (⟨((2^160 : Nat) : Int),UnsignedNarrowing.modulus_range 160 (by decide)⟩ : PrimTy.uint.Denote)) !=
    (Source.Val.address (addr 0) : Source.Val E.layout (.address false)).key))

-- Intrinsic capture-lifetime control only: a later caller write must not rewrite a captured argument.
def captureThenWrite : Prog C TgtCtx (.val .uint :: TgtCtx) :=
  (assignLocalOperand .here (.there .here)).code.join
    (.cons (.assignLocal (.there .here) (.simple (.lit 0 (by decide)))) .nil)
def captured : DeferredSource.Operand C TgtCtx (.prim .uint) :=
  ⟨_,captureThenWrite,.val (.simple (.local .here))⟩
def stale : DeferredSource.Operand C TgtCtx (.prim .uint) :=
  ⟨_,captureThenWrite,.val (.simple (.local (.there .here)))⟩
/-- info: true -/
#guard_msgs in
#eval IO.println (reprStr (
  match captured.run tgt,stale.run tgt with
  | .ok (out,.prim v),.ok (wrong,.prim w) => v.val == 17 && w.val == 0 &&
      (TEnv.get .here out.st.env).val == 0 && (TEnv.get .here wrong.st.env).val == 0
  | _,_ => false))
end Solidity.Lowering.V07.AddressConversionControls

/-- info: 'Solidity.Lowering.V07.AddressConversionControls.initial_addr' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms Solidity.Lowering.V07.AddressConversionControls.initial_addr

/-- info: 'Solidity.Lowering.V07.AddressConversionControls.reflect_addr' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms Solidity.Lowering.V07.AddressConversionControls.reflect_addr

/-- info: 'Solidity.Lowering.V07.AddressConversionControls.range_client' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms Solidity.Lowering.V07.AddressConversionControls.range_client

/-- info: 'Solidity.Lowering.V07.AddressConversionControls.observe_client' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms Solidity.Lowering.V07.AddressConversionControls.observe_client

/-- info: 'Solidity.Lowering.V07.AddressConversionControls.related_client' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms Solidity.Lowering.V07.AddressConversionControls.related_client

/-- info: 'Solidity.Lowering.V07.AddressConversionControls.read_client' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Solidity.Lowering.V07.AddressConversionControls.read_client

/-- info: 'Solidity.Lowering.V07.AddressConversionControls.integer_read_client' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms Solidity.Lowering.V07.AddressConversionControls.integer_read_client

/-- info: 'Solidity.Lowering.V07.AddressConversionControls.from_related_client' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms Solidity.Lowering.V07.AddressConversionControls.from_related_client

/-- info: 'Solidity.Lowering.V07.AddressConversionControls.rule_client' does not depend on any axioms -/
#guard_msgs in
#print axioms Solidity.Lowering.V07.AddressConversionControls.rule_client

/-- info: 'Solidity.Lowering.V07.AddressConversionControls.allowed_from_client' does not depend on any axioms -/
#guard_msgs in
#print axioms Solidity.Lowering.V07.AddressConversionControls.allowed_from_client

/-- info: 'Solidity.Lowering.V07.AddressConversionControls.allowed_to_client' does not depend on any axioms -/
#guard_msgs in
#print axioms Solidity.Lowering.V07.AddressConversionControls.allowed_to_client

/-- info: 'Solidity.Lowering.V07.AddressConversionControls.from_value_client' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms Solidity.Lowering.V07.AddressConversionControls.from_value_client

/-- info: 'Solidity.Lowering.V07.AddressConversionControls.to_value_client' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms Solidity.Lowering.V07.AddressConversionControls.to_value_client

/-- info: 'Solidity.Lowering.V07.AddressConversionControls.injective_client' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms Solidity.Lowering.V07.AddressConversionControls.injective_client

/-- info: 'Solidity.Lowering.V07.AddressConversionControls.distinct_client' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms Solidity.Lowering.V07.AddressConversionControls.distinct_client

/-- info: 'Solidity.Lowering.V07.AddressConversionControls.from_run_client' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms Solidity.Lowering.V07.AddressConversionControls.from_run_client

/-- info: 'Solidity.Lowering.V07.AddressConversionControls.to_run_client' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms Solidity.Lowering.V07.AddressConversionControls.to_run_client

/-- info: 'Solidity.Lowering.V07.AddressConversionControls.from_local_client' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms Solidity.Lowering.V07.AddressConversionControls.from_local_client

/-- info: 'Solidity.Lowering.V07.AddressConversionControls.to_local_client' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms Solidity.Lowering.V07.AddressConversionControls.to_local_client

/-- info: 'Solidity.Lowering.V07.AddressConversionControls.from_transport_client' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms Solidity.Lowering.V07.AddressConversionControls.from_transport_client

/-- info: 'Solidity.Lowering.V07.AddressConversionControls.to_transport_client' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms Solidity.Lowering.V07.AddressConversionControls.to_transport_client

/-- info: 'Solidity.Lowering.V07.AddressConversionControls.from_source_assignment_client' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms Solidity.Lowering.V07.AddressConversionControls.from_source_assignment_client

/-- info: 'Solidity.Lowering.V07.AddressConversionControls.from_assignment_client' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms Solidity.Lowering.V07.AddressConversionControls.from_assignment_client

/-- info: 'Solidity.Lowering.V07.AddressConversionControls.from_self_client' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms Solidity.Lowering.V07.AddressConversionControls.from_self_client

/-- info: 'Solidity.Lowering.V07.AddressConversionControls.from_repeated_client' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms Solidity.Lowering.V07.AddressConversionControls.from_repeated_client

/-- info: 'Solidity.Lowering.V07.AddressConversionControls.to_source_assignment_client' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms Solidity.Lowering.V07.AddressConversionControls.to_source_assignment_client

/-- info: 'Solidity.Lowering.V07.AddressConversionControls.to_assignment_client' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms Solidity.Lowering.V07.AddressConversionControls.to_assignment_client

/-- info: 'Solidity.Lowering.V07.AddressConversionControls.to_self_client' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms Solidity.Lowering.V07.AddressConversionControls.to_self_client

/-- info: 'Solidity.Lowering.V07.AddressConversionControls.to_equal_values_client' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms Solidity.Lowering.V07.AddressConversionControls.to_equal_values_client

/-- info: 'Solidity.Lowering.V07.AddressConversionControls.extension_client' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms Solidity.Lowering.V07.AddressConversionControls.extension_client

/-- info: 'Solidity.Lowering.V07.AddressConversionControls.binder_client' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms Solidity.Lowering.V07.AddressConversionControls.binder_client

/-- info: 'Solidity.Lowering.V07.AddressConversionControls.live_client' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Solidity.Lowering.V07.AddressConversionControls.live_client
