import Solidity.Lowering.V07.AddressComparisons
import Solidity.Lowering.V07.AddressConversionControls
import Solidity.Lowering.V07.NumericComparisonControls

namespace Solidity.Lowering.V07.AddressComparisonControls
open AddressComparisons AddressConversions AddressConversionControls
open Source.SemanticsExamples
open MixedAssignmentControls (C E globals)

def bridge_client := source_numeric (D := E.layout) false .ne a5 a17
def payable_bridge_client := source_numeric (D := E.layout) true .lt a5 a17
def value_client := value_run (D := E.layout) tgt false .lt rfl rfl a5 a17
  (.simple (.local .here)) (.simple (.local (.there .here))) rfl rfl

def operand_client (p : Roadmap.Pipeline) := operand_run (D := E.layout) tgt false .gt rfl rfl p
  .here (.there .here) a17 a5 rfl rfl

def pair_client := source_from_pair (globals .legacy) F0 3 (source a5 a17)
  ((source a5 a17).1.set .here (.address a17),(source a5 a17).2) false .gt
  (.assign (.local .here) (.local (.there .here))) (.local .here) a17 a5 true rfl
  (source_assign_read_pair (globals .legacy) F0 0 (source a5 a17)
    .here (.there .here) (.address a17) (.address a5) rfl rfl)

def assignment_client (p : Roadmap.Pipeline) (checked : Bool) (fuel : Nat) :=
  source_assignment (globals p) {F0 with checked := checked} fuel (source a5 a17) false .gt
    .here (.there .here) a17 a5 (decide ((a17.val : Int) > (rightAt p a17 a5).val))
    (by cases p <;> rfl) rfl rfl

def transport_client (p : Roadmap.Pipeline) (checked : Bool) (fuel : Nat)
    (op : {op : BinOp // op.accepts .uint = true ∧ op.ret .uint = .bool}) :=
  transport (globals p) {F0 with checked := checked} fuel (source a5 a17) tgt false
    mapping BindingRel (initial_addr a5 a17) reflect_addr .here (.there .here)
    .here (.there .here) rfl rfl a17 a5 rfl rfl op.val op.property.1 op.property.2

def self_client (p : Roadmap.Pipeline) (checked : Bool) (fuel : Nat) :=
  transport (globals p) {F0 with checked := checked} fuel (source a5 a17) tgt false
    mapping BindingRel (initial_addr a5 a17) reflect_addr .here .here
    .here .here rfl rfl a5 a5 rfl rfl .eqB rfl rfl

def equal_content_client (p : Roadmap.Pipeline) (checked : Bool) (fuel : Nat) :=
  transport (globals p) {F0 with checked := checked} fuel (source a5 a5) (target a5 a5) false
    mapping BindingRel (initial_addr a5 a5) reflect_addr .here (.there .here)
    .here (.there .here) rfl rfl a5 a5 rfl rfl .eqB rfl rfl

def extension_client (p : Roadmap.Pipeline) := DeferredSource.Operand.run_wk
  (NumericComparisons.operand ty .lt rfl rfl p .here (.there .here))
  (Thin.drop (t := .val .bool) Thin.refl) tgt (true,tgt.env)

def captureThin : Thin TgtCtx (.val .bool :: .val .uint :: .val .uint :: TgtCtx) :=
  Thin.drop (Thin.drop (Thin.drop Thin.refl))
def context_client : (mapping.wk captureThin).Related BindingRel (source a5 a17).1
    (tgt.lift captureThin (false,(addressValue a17,(addressValue a5,tgt.env)))).env :=
  ContextMap.related_wk mapping tgt BindingRel (source a5 a17).1
    (initial_addr a5 a17) captureThin (false,(addressValue a17,(addressValue a5,tgt.env)))

def pass_client (p : Roadmap.Pipeline) := NumericComparisons.pass_exact (C := C) ty .neB rfl rfl p
  (.here : Idx TgtCtx (.val .uint)) (.there .here)

def frame_client : (tgt.setLocal .here (addressValue a17)).glob = tgt.glob := rfl

-- Scalar observations and memory presence; exact global/reference framing follows
-- from transport's returned setLocal state and full mapped context relation.
def check (op : {op : BinOp // op.accepts .uint = true ∧ op.ret .uint = .bool})
    (p : Roadmap.Pipeline) (checked : Bool) (old rhs : Roadmap.Address) : Bool := Id.run do
  let src := source old rhs
  let tgt := target old rhs
  let right := rightAt p rhs old
  let expression : Source.RExpr E AddrCtx .bool := .compare (NumericComparisons.sourceOp op.val)
    (.assign (.local .here) (.local (.there .here))) (.local .here)
  let sr := (Source.evalE (globals p) {F0 with checked := checked} 4 expression).run src
  let code := NumericComparisons.code ty op.val op.property.1 op.property.2 p .here (.there .here)
  match sr.1,code.run tgt,(NumericComparisons.operand ty op.val op.property.1 op.property.2 p .here (.there .here)).run tgt,
    Source.cmpVal (NumericComparisons.sourceOp op.val) (.address rhs : Source.Val E.layout (.address false)) (.address right) with
  | .ok (.val (.bool v)),.ok captured,.ok (out,.prim w),.ok expected =>
      return v == expected && w == expected && TEnv.get .here captured.st.env == expected &&
        (TEnv.get (.there .here) captured.st.env).val == (rhs.val : Int) &&
        (TEnv.get (.there (.there .here)) captured.st.env).val == (right.val : Int) &&
        (TEnv.get (.there (.there (.there .here))) captured.st.env).val == (rhs.val : Int) &&
        (sr.2.1.get .here).key == some (rhs.val : Int) &&
        (sr.2.1.get (.there .here)).key == some (rhs.val : Int) &&
        (TEnv.get .here out.st.env).val == (rhs.val : Int) &&
        (TEnv.get (.there .here) out.st.env).val == (rhs.val : Int) &&
        (sr.2.1.get (.there (.there .here))).key == (src.1.get (.there (.there .here))).key &&
        (TEnv.get (.there (.there .here)) out.st.env).isSome == (TEnv.get (.there (.there .here)) tgt.env).isSome
  | _,_,_,_ => return false

/-- info: true -/
#guard_msgs in
#eval IO.println (reprStr (NumericComparisonControls.operators.all fun op =>
  [Roadmap.Pipeline.legacy,.viaIR].all fun p => [false,true].all fun checked =>
    [0,1,5,17,2^159,2^160-1].all fun old => [0,1,5,17,2^159,2^160-1].all fun rhs =>
      check op p checked (addr old) (addr rhs)))

-- The same assigned address is compared to old5 in legacy and reached17 viaIR.
/-- info: true -/
#guard_msgs in
#eval IO.println (reprStr (
  match (NumericComparisons.operand ty .eqB rfl rfl .legacy .here (.there .here)).run tgt,
        (NumericComparisons.operand ty .eqB rfl rfl .viaIR .here (.there .here)).run tgt with
  | .ok (_, .prim legacy),.ok (_, .prim viaIR) => !legacy && viaIR
  | _,_ => false))
-- Actual wrong programs: stale right reload and reversed captured operands.
def stale : DeferredSource.Operand C TgtCtx (.prim .bool) :=
  ⟨_,(assignReadPrefix .legacy .here (.there .here)).join
    (NumericComparisons.tail ty .eqB rfl rfl .here (.there (.there .here))),.val (.simple (.local .here))⟩
def reversed : DeferredSource.Operand C TgtCtx (.prim .bool) :=
  ⟨_,(assignReadPrefix .legacy .here (.there .here)).join
    (NumericComparisons.tail ty .gt rfl rfl (.there .here) .here),.val (.simple (.local .here))⟩
/-- info: true -/
#guard_msgs in
#eval IO.println (reprStr (
  match (NumericComparisons.operand ty .eqB rfl rfl .legacy .here (.there .here)).run tgt,
        stale.run tgt,(NumericComparisons.operand ty .gt rfl rfl .legacy .here (.there .here)).run tgt,
        reversed.run tgt with
  | .ok (_, .prim properEq),.ok (_, .prim wrongEq),.ok (_, .prim properGt),.ok (_, .prim wrongGt) =>
      !properEq && wrongEq && properGt && !wrongGt
  | _,_,_,_ => false))
end Solidity.Lowering.V07.AddressComparisonControls

/-- info: 'Solidity.Lowering.V07.AddressComparisonControls.bridge_client' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms Solidity.Lowering.V07.AddressComparisonControls.bridge_client

/-- info: 'Solidity.Lowering.V07.AddressComparisonControls.payable_bridge_client' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms Solidity.Lowering.V07.AddressComparisonControls.payable_bridge_client

/-- info: 'Solidity.Lowering.V07.AddressComparisonControls.value_client' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms Solidity.Lowering.V07.AddressComparisonControls.value_client

/-- info: 'Solidity.Lowering.V07.AddressComparisonControls.operand_client' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms Solidity.Lowering.V07.AddressComparisonControls.operand_client

/-- info: 'Solidity.Lowering.V07.AddressComparisonControls.pair_client' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Solidity.Lowering.V07.AddressComparisonControls.pair_client

/-- info: 'Solidity.Lowering.V07.AddressComparisonControls.assignment_client' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms Solidity.Lowering.V07.AddressComparisonControls.assignment_client

/-- info: 'Solidity.Lowering.V07.AddressComparisonControls.transport_client' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms Solidity.Lowering.V07.AddressComparisonControls.transport_client

/-- info: 'Solidity.Lowering.V07.AddressComparisonControls.self_client' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Solidity.Lowering.V07.AddressComparisonControls.self_client

/-- info: 'Solidity.Lowering.V07.AddressComparisonControls.equal_content_client' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms Solidity.Lowering.V07.AddressComparisonControls.equal_content_client

/-- info: 'Solidity.Lowering.V07.AddressComparisonControls.extension_client' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms Solidity.Lowering.V07.AddressComparisonControls.extension_client

/-- info: 'Solidity.Lowering.V07.AddressComparisonControls.context_client' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms Solidity.Lowering.V07.AddressComparisonControls.context_client

/-- info: 'Solidity.Lowering.V07.AddressComparisonControls.pass_client' depends on axioms: [propext] -/
#guard_msgs in
#print axioms Solidity.Lowering.V07.AddressComparisonControls.pass_client

/-- info: 'Solidity.Lowering.V07.AddressComparisonControls.frame_client' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms Solidity.Lowering.V07.AddressComparisonControls.frame_client
