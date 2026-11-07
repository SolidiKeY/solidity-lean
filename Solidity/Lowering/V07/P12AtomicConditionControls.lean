import Solidity.Lowering.V07.P12AtomicConditions
import Solidity.Lowering.V07.P12AssignedConditionControls
import Solidity.Lowering.V07.P12NegatedCondition

namespace Solidity.Lowering.V07.P12AtomicConditionControls
open Source.SemanticsExamples P12NextInterface P12AtomicConditions
open P12Controls (C E SrcCtx TgtCtx source target mapping)
open P12AssignedConditionControls (values worlds initial initial_pair srcPair tgtPair bool_reflect)
open MixedAssignmentControls (globals)

def literalProducer (p : Roadmap.Pipeline) (checked b : Bool) :=
  literal (globals p) {F0 with checked := checked} mapping values worlds b ⟨source,target,initial⟩
def localProducer (p : Roadmap.Pipeline) (checked : Bool) :=
  readLocal (globals p) {F0 with checked := checked} mapping values worlds bool_reflect
    ⟨source,target,initial⟩ (.there .here) (.there .here) rfl

def literal_success_client (p : Roadmap.Pipeline) (checked old rhs b : Bool) (n : Nat) :=
  (literalProducer p checked b).success (n+1) (srcPair old rhs) (srcPair old rhs) (tgtPair old rhs) b
    (initial_pair old rhs) (literal_source_run (globals p) {F0 with checked := checked} n (srcPair old rhs) b)
def local_success_client (p : Roadmap.Pipeline) (checked old rhs : Bool) (n : Nat) :=
  (localProducer p checked).success (n+1) (srcPair old rhs) (srcPair old rhs) (tgtPair old rhs) rhs
    (initial_pair old rhs) (source_local_value_run (globals p) {F0 with checked := checked} n (srcPair old rhs)
      (.there .here) (.bool rhs) (by rfl))
def negatedLocalProducer (p : Roadmap.Pipeline) (checked : Bool) :=
  P12NegatedCondition.negate (globals p) {F0 with checked := checked} mapping values worlds
    (.local (.there .here)) (localProducer p checked)
def negated_success_client (p : Roadmap.Pipeline) (checked old rhs : Bool) (n : Nat) :=
  (negatedLocalProducer p checked).success (n+2) (srcPair old rhs) (srcPair old rhs) (tgtPair old rhs) (!rhs)
    (initial_pair old rhs)
    (P12NegatedCondition.source_run (globals p) {F0 with checked := checked} (n+1)
      (srcPair old rhs) (srcPair old rhs) (.local (.there .here)) rhs
      (source_local_value_run (globals p) {F0 with checked := checked} n (srcPair old rhs)
        (.there .here) (.bool rhs) (by rfl)))
def negated_literal_client (p : Roadmap.Pipeline) (checked b : Bool) :=
  P12NegatedCondition.negate (globals p) {F0 with checked := checked} mapping values worlds
    (.bool b) (literalProducer p checked b)
def extension_client (p : Roadmap.Pipeline) (checked : Bool) :=
  DeferredSource.Operand.run_wk (localProducer p checked).operand
    (Thin.drop (t := .val .bool) .refl) target (false,target.env)
def live_refs_client := P12Controls.live_memory_and_storage

theorem local_frame (p : Roadmap.Pipeline) (checked old rhs : Bool) :
    (localProducer p checked).operand.run (tgtPair old rhs) =
      .ok (⟨tgtPair old rhs,List.prefix_refl _⟩,.prim rhs) := by
  rfl
theorem literal_frame (p : Roadmap.Pipeline) (checked old rhs b : Bool) :
    (literalProducer p checked b).operand.run (tgtPair old rhs) =
      .ok (⟨tgtPair old rhs,List.prefix_refl _⟩,.prim b) := by
  rfl

def observeSource (p : Roadmap.Pipeline) (checked : Bool) (n : Nat) (old rhs : Bool)
    (e : Source.RExpr E SrcCtx .bool) : Option (List Int) :=
  match (Source.evalE (globals p) {F0 with checked := checked} n e).run (srcPair old rhs) with
  | (.ok (.val (.bool value)),after) => match after.1.get .here,after.1.get (.there .here) with
    | .bool a,.bool b => some [1,Int.ofNat value.toNat,Int.ofNat a.toNat,Int.ofNat b.toNat]
    | _,_ => none
  | (.error .timeout,after) => match after.1.get .here,after.1.get (.there .here) with
    | .bool a,.bool b => some [-1,-1,Int.ofNat a.toNat,Int.ofNat b.toNat]
    | _,_ => none
  | _ => none

def observe (p : Roadmap.Pipeline) (checked old rhs b : Bool) (n : Nat) : Option (List Int) :=
  let t := tgtPair old rhs
  match observeSource p checked n old rhs (.bool b),observeSource p checked n old rhs (.local (.there .here)),
      (literalProducer p checked b).operand.run t,(localProducer p checked).operand.run t,
      (negatedLocalProducer p checked).operand.run t with
  | some xs,some ys,.ok (out,.prim lit),.ok (read,.prim value),.ok (neg,.prim inverse) =>
    some (xs ++ ys ++ [Int.ofNat lit.toNat,Int.ofNat out.st.env.1.toNat,Int.ofNat out.st.env.2.1.toNat,
      Int.ofNat value.toNat,Int.ofNat read.st.env.1.toNat,Int.ofNat read.st.env.2.1.toNat,
      Int.ofNat inverse.toNat,Int.ofNat neg.st.env.1.toNat,Int.ofNat neg.st.env.2.1.toNat])
  | _,_,_,_,_ => none

/-- info: true -/
#guard_msgs in
#eval IO.println (reprStr ([Roadmap.Pipeline.legacy,.viaIR].all fun p => [false,true].all fun checked =>
  [false,true].all fun old => [false,true].all fun rhs => [false,true].all fun b => (List.range 5).all fun n =>
    let o := Int.ofNat old.toNat
    let r := Int.ofNat rhs.toNat
    let v := Int.ofNat b.toNat
    let lit := if n=0 then [-1,-1,o,r] else [1,v,o,r]
    let read := if n=0 then [-1,-1,o,r] else [1,r,o,r]
    observe p checked old rhs b n == some (lit ++ read ++ [v,o,r,r,o,r,Int.ofNat (!rhs).toNat,o,r])))

/-- Actually wrong clauses: the other caller binding and the complement of
an emitted literal; neither may pass as the original source observation. -/
def wrongLocal := localOperand (C := C) (.here : Idx TgtCtx (.val .bool))
def wrongLiteral := literalOperand (C := C) (Γ := TgtCtx) false
def wrongResult : Option (Bool × Bool) :=
  match wrongLocal.run (tgtPair false true),wrongLiteral.run (tgtPair false true) with
  | .ok (_,.prim a),.ok (_,.prim b) => some (a,b)
  | _,_ => none
/-- info: some (false, false) -/
#guard_msgs in
#eval IO.println (reprStr wrongResult)
/-- info: some [1, 1, 0, 1, 1, 1, 0, 1, 1, 0, 1, 1, 0, 1, 0, 0, 1] -/
#guard_msgs in
#eval IO.println (reprStr (observe .viaIR false false true true 1))

/-- info: 'Solidity.Lowering.V07.P12AtomicConditionControls.local_frame' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms Solidity.Lowering.V07.P12AtomicConditionControls.local_frame

/-- info: 'Solidity.Lowering.V07.P12AtomicConditionControls.literal_frame' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms Solidity.Lowering.V07.P12AtomicConditionControls.literal_frame

/-- info: 'Solidity.Lowering.V07.P12AtomicConditionControls.literalProducer' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms Solidity.Lowering.V07.P12AtomicConditionControls.literalProducer

/-- info: 'Solidity.Lowering.V07.P12AtomicConditionControls.localProducer' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms Solidity.Lowering.V07.P12AtomicConditionControls.localProducer

/-- info: 'Solidity.Lowering.V07.P12AtomicConditionControls.literal_success_client' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms Solidity.Lowering.V07.P12AtomicConditionControls.literal_success_client

/-- info: 'Solidity.Lowering.V07.P12AtomicConditionControls.local_success_client' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms Solidity.Lowering.V07.P12AtomicConditionControls.local_success_client

/-- info: 'Solidity.Lowering.V07.P12AtomicConditionControls.negatedLocalProducer' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms Solidity.Lowering.V07.P12AtomicConditionControls.negatedLocalProducer

/-- info: 'Solidity.Lowering.V07.P12AtomicConditionControls.negated_success_client' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms Solidity.Lowering.V07.P12AtomicConditionControls.negated_success_client

/-- info: 'Solidity.Lowering.V07.P12AtomicConditionControls.negated_literal_client' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms Solidity.Lowering.V07.P12AtomicConditionControls.negated_literal_client

/-- info: 'Solidity.Lowering.V07.P12AtomicConditionControls.extension_client' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms Solidity.Lowering.V07.P12AtomicConditionControls.extension_client

/-- info: 'Solidity.Lowering.V07.P12AtomicConditionControls.live_refs_client' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms Solidity.Lowering.V07.P12AtomicConditionControls.live_refs_client

end Solidity.Lowering.V07.P12AtomicConditionControls
