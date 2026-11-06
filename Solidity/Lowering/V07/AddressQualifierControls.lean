import Solidity.Lowering.V07.AddressQualifiers
import Solidity.Lowering.V07.AddressConversionControls

namespace Solidity.Lowering.V07.AddressQualifierControls
open AddressQualifiers AddressConversions
open AddressConversionControls (addr a5 a17 TgtCtx target)
open Source.SemanticsExamples
open MixedAssignmentControls (C E globals)

abbrev SrcCtx (p : Bool) : Source.RCtx := [.address p,.address p,.bytes .memory,.bytes .storage]
def source (p : Bool) (old rhs : Roadmap.Address) : Source.EMState E (SrcCtx p) :=
  (.cons (.address old) (.cons (.address rhs) (.cons (.memRef rfl 0)
    (.cons (.storRef rfl MixedAssignmentControls.path) .nil))), (AddressConversionControls.source old rhs).2)
def mapping (p : Bool) : ContextMap (SrcCtx p) TgtCtx :=
  (((ContextMap.empty.cons (.bytes .storage) (.alias bytesR)).cons (.bytes .memory) (.mem bytesR)).cons
    (.address p) (.val .uint)).cons (.address p) (.val .uint)
def BindingRel : (τ : Source.STy) → (u : LTy) → Source.Val E.layout τ → u.TDenote C (target a5 a17).H → Prop
  | .address p,.val .uint,v,n => AddressRel p v n
  | τ,u,v,n => P12Controls.BindingRel τ u v n

theorem initial (p : Bool) (old rhs : Roadmap.Address) :
    (mapping p).Related BindingRel (source p old rhs).1 (target old rhs).env := by
  intro τ i
  cases i with
  | here => exact address_related p old
  | there i => cases i with
    | here => exact address_related p rhs
    | there i => cases i with
      | here => exact ⟨rfl,rfl⟩
      | there i => cases i with
        | here => exact ⟨rfl,rfl⟩
        | there i => nomatch i

theorem reflect (p : Bool) (v : Source.Val E.layout (.address p)) (n : PrimTy.uint.Denote)
    (related : BindingRel (.address p) (.val .uint) v n) : AddressRel p v n := related

def allowed_client (p : Bool) := allowed_erase E p
def value_client (p : Bool) := erase_value (D := E.layout) p a17

def payable_run_client (p : Bool) (pipeline : Roadmap.Pipeline) (checked : Bool) (fuel : Nat) :=
  payable_run (globals pipeline) {F0 with checked := checked} (fuel+1) (source p a5 a17)
    (source p a5 a17) p (.local .here) a5 rfl
def erase_run_client (p : Bool) (pipeline : Roadmap.Pipeline) (checked : Bool) (fuel : Nat) :=
  erase_run (globals pipeline) {F0 with checked := checked} (fuel+1) (source p a5 a17)
    (source p a5 a17) p (.local .here) a5 rfl

def payable_assignment_client (p : Bool) (pipeline : Roadmap.Pipeline) (checked : Bool) (fuel : Nat) :=
  payable_assignment (globals pipeline) {F0 with checked := checked} fuel (source p a5 a17)
    p .here (.there .here) a17 rfl
def erase_assignment_client (p : Bool) (pipeline : Roadmap.Pipeline) (checked : Bool) (fuel : Nat) :=
  erase_assignment (globals pipeline) {F0 with checked := checked} fuel (source p a5 a17)
    p .here (.there .here) a17 rfl

def copy_client (p : Bool) := copy_alignment (source p a5 a17) (target a5 a17) p
  (mapping p) BindingRel (initial p a5 a17) (reflect p) .here (.there .here)
  .here (.there .here) rfl rfl a17 rfl

def payable_transport_client (p : Bool) (pipeline : Roadmap.Pipeline) (checked : Bool) (fuel : Nat) :=
  payable_transport (globals pipeline) {F0 with checked := checked} fuel (source p a5 a17) (target a5 a17) p
    (mapping p) BindingRel (initial p a5 a17) (reflect p) .here (.there .here)
    .here (.there .here) rfl rfl a17 rfl

def erase_transport_client (p : Bool) (pipeline : Roadmap.Pipeline) (checked : Bool) (fuel : Nat) :=
  erase_transport (globals pipeline) {F0 with checked := checked} fuel (source p a5 a17) (target a5 a17) p
    (mapping p) BindingRel (initial p a5 a17) (reflect p) .here (.there .here)
    .here (.there .here) rfl rfl a17 rfl

def self_client (p : Bool) (pipeline : Roadmap.Pipeline) (checked : Bool) (fuel : Nat) :=
  payable_transport (globals pipeline) {F0 with checked := checked} fuel (source p a5 a17) (target a5 a17) p
    (mapping p) BindingRel (initial p a5 a17) (reflect p) .here .here
    .here .here rfl rfl a5 rfl

def equal_client (p : Bool) (pipeline : Roadmap.Pipeline) (checked : Bool) (fuel : Nat) :=
  erase_transport (globals pipeline) {F0 with checked := checked} fuel (source p a5 a5) (target a5 a5) p
    (mapping p) BindingRel (initial p a5 a5) (reflect p) .here (.there .here)
    .here (.there .here) rfl rfl a5 rfl

def extension_client := DeferredSource.Operand.run_wk (assignLocalOperand .here (.there .here))
  (Thin.drop (t := .val .bool) Thin.refl) (target a5 a17) (true,(target a5 a17).env)

-- The language's explicit conversion refusal is unchanged: payable(e) is a
-- separate Source constructor, not a proof that address(e) accepts true.
/-- info: true -/
#guard_msgs in
#eval IO.println (reprStr (!(Source.STy.address false).explicit E.isBase E.mapFree (.address true)))

-- Both conversions and their actual Source composition preserve the reached
-- assignment. Capture happens before the private native local is dropped.
def check (p : Bool) (pipeline : Roadmap.Pipeline) (checked : Bool)
    (old rhs : Roadmap.Address) : Bool := Id.run do
  let src := source p old rhs
  let tgt := target old rhs
  let ass : Source.RExpr E (SrcCtx p) (.address p) := .assign (.local .here) (.local (.there .here))
  let pay := Source.RExpr.payable ass
  let erase := Source.RExpr.convExplicit (τ := .address false) ass (allowed_erase E p)
  let round := Source.RExpr.convExplicit (τ := .address false) pay (allowed_erase E true)
  let pr := (Source.evalE (globals pipeline) {F0 with checked := checked} 3 pay).run src
  let er := (Source.evalE (globals pipeline) {F0 with checked := checked} 3 erase).run src
  let rr := (Source.evalE (globals pipeline) {F0 with checked := checked} 4 round).run src
  match pr.1,er.1,rr.1,(assignLocalOperand .here (.there .here)).code.run tgt,
    (assignLocalOperand .here (.there .here)).run tgt with
  | .ok (.val (.address a)),.ok (.val (.address b)),.ok (.val (.address c)),.ok cap,.ok (out,.prim v) =>
      return a.val == rhs.val && b.val == rhs.val && c.val == rhs.val && v.val == (rhs.val : Int) &&
        (pr.2.1.get .here).key == some (rhs.val : Int) &&
        (er.2.1.get .here).key == some (rhs.val : Int) &&
        (rr.2.1.get .here).key == some (rhs.val : Int) &&
        (TEnv.get .here cap.st.env).val == (rhs.val : Int) &&
        (TEnv.get (.there .here) cap.st.env).val == (rhs.val : Int) &&
        (TEnv.get .here out.st.env).val == (rhs.val : Int) &&
        (TEnv.get (.there .here) out.st.env).val == (rhs.val : Int)
  | _,_,_,_,_ => return false

/-- info: true -/
#guard_msgs in
#eval IO.println (reprStr ([false,true].all fun p => [Roadmap.Pipeline.legacy,.viaIR].all fun pipeline =>
  [false,true].all fun checked => [0,1,5,17,2^159,2^160-1].all fun old =>
    [0,1,5,17,2^159,2^160-1].all fun rhs => check p pipeline checked (addr old) (addr rhs)))

-- Intrinsic-only lifetime control: overwrite the RHS after capture. Reading
-- the captured value returns17; reloading the overwritten caller binding gives0.
def wrongCode : Prog C TgtCtx (.val .uint :: TgtCtx) :=
  (assignLocalOperand .here (.there .here)).code.join
    (.cons (.assignLocal (.there (.there .here)) (.simple (.lit 0 (by decide)))) .nil)
def correctCapture : DeferredSource.Operand C TgtCtx (.prim .uint) :=
  ⟨_,wrongCode,.val (.simple (.local .here))⟩
def uncaptured : DeferredSource.Operand C TgtCtx (.prim .uint) :=
  ⟨_,wrongCode,.val (.simple (.local (.there (.there .here))))⟩
/-- info: true -/
#guard_msgs in
#eval IO.println (reprStr (
  match correctCapture.run (target a5 a17),uncaptured.run (target a5 a17) with
  | .ok (_, .prim v),.ok (_, .prim wrong) => v.val == 17 && wrong.val == 0
  | _,_ => false))
end Solidity.Lowering.V07.AddressQualifierControls

/-- info: 'Solidity.Lowering.V07.AddressQualifierControls.initial' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Solidity.Lowering.V07.AddressQualifierControls.initial

/-- info: 'Solidity.Lowering.V07.AddressQualifierControls.reflect' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Solidity.Lowering.V07.AddressQualifierControls.reflect

/-- info: 'Solidity.Lowering.V07.AddressQualifierControls.allowed_client' does not depend on any axioms -/
#guard_msgs in
#print axioms Solidity.Lowering.V07.AddressQualifierControls.allowed_client

/-- info: 'Solidity.Lowering.V07.AddressQualifierControls.value_client' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Solidity.Lowering.V07.AddressQualifierControls.value_client

/-- info: 'Solidity.Lowering.V07.AddressQualifierControls.payable_run_client' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms Solidity.Lowering.V07.AddressQualifierControls.payable_run_client

/-- info: 'Solidity.Lowering.V07.AddressQualifierControls.erase_run_client' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms Solidity.Lowering.V07.AddressQualifierControls.erase_run_client

/-- info: 'Solidity.Lowering.V07.AddressQualifierControls.payable_assignment_client' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms Solidity.Lowering.V07.AddressQualifierControls.payable_assignment_client

/-- info: 'Solidity.Lowering.V07.AddressQualifierControls.erase_assignment_client' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms Solidity.Lowering.V07.AddressQualifierControls.erase_assignment_client

/-- info: 'Solidity.Lowering.V07.AddressQualifierControls.copy_client' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Solidity.Lowering.V07.AddressQualifierControls.copy_client

/-- info: 'Solidity.Lowering.V07.AddressQualifierControls.payable_transport_client' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms Solidity.Lowering.V07.AddressQualifierControls.payable_transport_client

/-- info: 'Solidity.Lowering.V07.AddressQualifierControls.erase_transport_client' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms Solidity.Lowering.V07.AddressQualifierControls.erase_transport_client

/-- info: 'Solidity.Lowering.V07.AddressQualifierControls.self_client' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Solidity.Lowering.V07.AddressQualifierControls.self_client

/-- info: 'Solidity.Lowering.V07.AddressQualifierControls.equal_client' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Solidity.Lowering.V07.AddressQualifierControls.equal_client

/-- info: 'Solidity.Lowering.V07.AddressQualifierControls.extension_client' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms Solidity.Lowering.V07.AddressQualifierControls.extension_client
