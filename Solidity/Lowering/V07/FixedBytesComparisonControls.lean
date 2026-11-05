import Solidity.Lowering.V07.FixedBytesComparisons
import Solidity.Lowering.V07.FixedBytesAssignmentControls

namespace Solidity.Lowering.V07.FixedBytesComparisonControls
open FixedBytesComparisons
open Source.SemanticsExamples
open MixedAssignmentControls (C E globals)
open FixedBytesAssignmentControls (source target mapping BindingRel initial reflect)
def operators : List {op : BinOp // op.accepts .uint = true ∧ op.ret .uint = .bool} :=
  [⟨.lt,by decide⟩,⟨.gt,by decide⟩,⟨.le,by decide⟩,⟨.ge,by decide⟩,⟨.eqB,by decide⟩,⟨.neB,by decide⟩]
def xs : List UInt8 := [1,2]
def ys : List UInt8 := [2,1]
def src := source 2 (by decide) ys xs
def tgt := target 2 (by decide) ys xs

theorem pure_less_fixture {D : Source.Layout} :
    Source.cmpVal .lt (.fixedBytes xs (by decide) : Source.Val D (.fixedBytes 2 (by decide)))
      (.fixedBytes ys (by decide)) = .ok true := by
  simp only [Source.cmpVal,Source.Val.key,Source.bytesNat,Source.beValue,xs,ys,List.foldl_cons,List.foldl_nil,UInt8.toNat_ofNat]
  change (Except.ok (decide ((258 : Int) < 513)) : Source.R Bool) = .ok true
  have h : (258 : Int) < 513 := by omega
  simp only [h,decide_true]

theorem ordered_less_fixture {D : Source.Layout} (p : Roadmap.Pipeline) :
    Source.cmpVal .lt (.fixedBytes xs (by decide) : Source.Val D (.fixedBytes 2 (by decide)))
      (.fixedBytes (rightAt p xs ys) (right_length p 2 xs ys (by decide) (by decide))) =
      .ok (decide ((258 : Int) < if p = .legacy then 513 else 258)) := by
  cases p <;> simp only [rightAt,reduceCtorEq,if_true,if_false,Source.cmpVal,Source.Val.key,
    Source.bytesNat,Source.beValue,xs,ys,List.foldl_cons,List.foldl_nil,UInt8.toNat_ofNat] <;> rfl

def length_client (p : Roadmap.Pipeline) := right_length p 2 xs ys (by decide) (by decide)
def numeric_client := source_numeric (D := E.layout) 2 (by decide) .lt xs ys (by decide) (by decide)
def value_client := value_run (D := E.layout) tgt 2 (by decide) .lt rfl rfl xs ys (by decide) (by decide)
  (.simple (.local (.there .here))) (.simple (.local .here)) rfl rfl

def pair_client (p : Roadmap.Pipeline) (checked : Bool) (fuel : Nat) :=
  source_from_pair (globals p) {F0 with checked := checked} (fuel+2) src src 2 (by decide) .lt
    (.local (.there .here)) (.local .here) xs ys (by decide) (by decide) true pure_less_fixture
    (source_pure_pair (globals p) {F0 with checked := checked} (fuel+1) src
      (.local (.there .here)) (.local .here) (.val (.fixedBytes xs (by decide))) (.val (.fixedBytes ys (by decide)))
      (source_local_value_run (globals p) {F0 with checked := checked} fuel src (.there .here) (.fixedBytes xs (by decide)) rfl)
      (source_local_value_run (globals p) {F0 with checked := checked} fuel src .here (.fixedBytes ys (by decide)) rfl))

def assignment_client (p : Roadmap.Pipeline) (checked : Bool) (fuel : Nat) :=
  source_assignment (globals p) {F0 with checked := checked} fuel src 2 (by decide) .lt .here (.there .here)
    xs ys (by decide) (by decide) (decide ((258 : Int) < if p = .legacy then 513 else 258))
    (ordered_less_fixture p) rfl rfl

def operand_client (p : Roadmap.Pipeline) :=
  operand_run (D := E.layout) tgt 2 (by decide) .lt rfl rfl p .here (.there .here) xs ys (by decide) (by decide) rfl rfl

def transport_client (n : Nat) (w : 1 ≤ n ∧ n ≤ 32) (op : BinOp)
    (hu : op.accepts .uint = true) (hr : op.ret .uint = .bool)
    (p : Roadmap.Pipeline) (checked : Bool) (old rhs : List UInt8) :=
  transport (globals p) {F0 with checked := checked} 0 (source n w old rhs) (target n w old rhs)
    n w (mapping n w) BindingRel (initial n w old rhs) (reflect n w)
    .here (.there .here) .here (.there .here) rfl rfl
    (FixedBytesAssignmentControls.payload n rhs) (FixedBytesAssignmentControls.payload n old)
    (Source.fitBytes_length n rhs) (Source.fitBytes_length n old) rfl rfl op hu hr

def self_client (p : Roadmap.Pipeline) (checked : Bool) :=
  transport (globals p) {F0 with checked := checked} 0 src tgt 2 (by decide)
    (mapping 2 (by decide)) BindingRel (initial 2 (by decide) ys xs) (reflect 2 (by decide))
    .here .here .here .here rfl rfl ys ys (by decide) (by decide) rfl rfl .eqB rfl rfl

def extension_client := DeferredSource.Operand.run_wk
  (NumericComparisons.operand .u256 .lt rfl rfl .legacy (.here : Idx FixedBytesAssignmentControls.TgtCtx (.val .uint)) (.there .here))
  (Thin.drop (t := .val .bool) Thin.refl) tgt (true,tgt.env)
def code_client (p : Roadmap.Pipeline) := NumericComparisons.code_run (D := E.layout) tgt .u256 .lt rfl rfl p
  .here (.there .here) 258 513 (by decide) (by decide) rfl rfl
def pass_client (p : Roadmap.Pipeline) := NumericComparisons.pass_exact (C := C) .u256 .lt rfl rfl p
  (.here : Idx FixedBytesAssignmentControls.TgtCtx (.val .uint)) (.there .here)
def prefix_client (p : Roadmap.Pipeline) := assign_read_prefix_run p tgt .here (.there .here)
  (FixedBytesAssignment.value 2 (by decide) xs (by decide))
  (FixedBytesAssignment.value 2 (by decide) ys (by decide)) rfl rfl

def check (n : Nat) (w : 1 ≤ n ∧ n ≤ 32) (op : BinOp)
    (hu : op.accepts .uint = true) (hr : op.ret .uint = .bool) (p : Roadmap.Pipeline) (checked : Bool)
    (old rhs : List UInt8) : Bool :=
  let a := FixedBytesAssignmentControls.payload n rhs
  let b := FixedBytesAssignmentControls.payload n old
  let right := if p = .legacy then Source.bytesNat b else Source.bytesNat a
  match (Source.evalE (globals p) {F0 with checked := checked} 4
      (.compare (NumericComparisons.sourceOp op)
        (.assign (.local (.here : Source.Idx (FixedBytesAssignmentControls.SrcCtx n w) (.fixedBytes n w)))
          (.local (.there .here))) (.local .here))).run (source n w old rhs),
      (NumericComparisons.operand .u256 op hu hr p .here (.there .here)).run (target n w old rhs),
      (NumericComparisons.code .u256 op hu hr p .here (.there .here)).run (target n w old rhs) with
  | (.ok (.val (.bool s)),post),.ok (out,.prim r),.ok cap =>
      s == r && TEnv.get .here cap.st.env == r &&
      (post.1.get .here).key == some (Source.bytesNat a : Int) &&
      (post.1.get (.there .here)).key == some (Source.bytesNat a : Int) &&
      (TEnv.get .here out.st.env).val == (Source.bytesNat a : Int) &&
      (TEnv.get (.there .here) out.st.env).val == (Source.bytesNat a : Int) &&
      (TEnv.get (.there .here) cap.st.env).val == (Source.bytesNat a : Int) &&
      (TEnv.get (.there (.there .here)) cap.st.env).val == (right : Int) &&
      (TEnv.get (.there (.there (.there .here))) cap.st.env).val == (Source.bytesNat a : Int) &&
      (TEnv.get (.there (.there (.there (.there .here)))) cap.st.env).val == (Source.bytesNat a : Int)
  | _,_,_ => false

/-- info: true -/
#guard_msgs in
#eval IO.println (reprStr ((List.range 33).all fun n =>
  if w : 1 ≤ n ∧ n ≤ 32 then operators.all fun op =>
    [Roadmap.Pipeline.legacy,.viaIR].all fun p => [false,true].all fun checked =>
      [[],List.replicate (n-1) 0 ++ [1],List.replicate n 255,1 :: List.replicate (n-1) 0].all fun old =>
        [[],List.replicate (n-1) 0 ++ [1],List.replicate n 255,1 :: List.replicate (n-1) 0].all fun rhs =>
          check n w op.val op.property.1 op.property.2 p checked old rhs
  else true))

def observe (p : Roadmap.Pipeline) : List Int :=
  match (Source.evalE (globals p) F0 4 (.compare .lt
      (.assign (.local (.here : Source.Idx (FixedBytesAssignmentControls.SrcCtx 2 (by decide)) (.fixedBytes 2 (by decide))))
        (.local (.there .here))) (.local .here))).run src,
      (NumericComparisons.code .u256 .lt rfl rfl p .here (.there .here)).run tgt,
      (NumericComparisons.operand .u256 .lt rfl rfl p .here (.there .here)).run tgt with
  | (.ok (.val (.bool s)),post),.ok cap,.ok (out,.prim r) =>
      [if s then 1 else 0,(post.1.get .here).key.getD (-1),if (TEnv.get .here cap.st.env : Bool) = true then 1 else 0,
       (TEnv.get (.there .here) cap.st.env).val,(TEnv.get (.there (.there .here)) cap.st.env).val,
       (TEnv.get (.there (.there (.there .here))) cap.st.env).val,
       if (r : Bool) = true then 1 else 0,(TEnv.get .here out.st.env).val,(TEnv.get (.there .here) out.st.env).val]
  | _,_,_ => [-1]

/-- info: [1, 258, 1, 258, 513, 258, 1, 258, 258]
[0, 258, 0, 258, 258, 258, 0, 258, 258] -/
#guard_msgs in
#eval do IO.println (reprStr (observe .legacy)); IO.println (reprStr (observe .viaIR))

-- Initial-state stale and reversed-role value contrasts; composed capture mistakes follow below.
/-- info: true -/
#guard_msgs in
#eval IO.println (reprStr (
  match (NumericComparisons.value .u256 .lt rfl rfl (.simple (.local (.there .here))) (.simple (.local .here))).evalT tgt,
      (NumericComparisons.value .u256 .lt rfl rfl (.simple (.local .here)) (.simple (.local (.there .here)))).evalT tgt with
  | .ok stale,.ok reversed => stale && !reversed && observe .legacy != observe .viaIR &&
      (observe .viaIR).head? == some 0 && (observe .legacy).head? == some 1
  | _,_ => false))
-- Actual prefix-plus-tail programs: reloading the reached caller or reversing captured roles is wrong.
/-- info: true -/
#guard_msgs in
#eval IO.println (reprStr (
  let preludeCode := assignReadPrefix .legacy
    (.here : Idx FixedBytesAssignmentControls.TgtCtx (.val .uint)) (.there .here)
  match (preludeCode.join (NumericComparisons.tail .u256 .lt rfl rfl .here (.there .here))).run tgt,
      (preludeCode.join (NumericComparisons.tail .u256 .lt rfl rfl .here (.there (.there .here)))).run tgt,
      (preludeCode.join (NumericComparisons.tail .u256 .lt rfl rfl (.there .here) .here)).run tgt with
  | .ok good,.ok uncaptured,.ok reversed =>
      (TEnv.get .here good.st.env : Bool) && !(TEnv.get .here uncaptured.st.env : Bool) &&
      !(TEnv.get .here reversed.st.env : Bool) &&
      (TEnv.get (.there .here) good.st.env).val == 258 &&
      (TEnv.get (.there (.there .here)) good.st.env).val == 513 &&
      (TEnv.get (.there (.there (.there .here))) good.st.env).val == 258 &&
      (TEnv.get (.there (.there (.there .here))) uncaptured.st.env).val == 258 &&
      (TEnv.get (.there (.there (.there .here))) reversed.st.env).val == 258
  | _,_,_ => false))
/-- info: 'Solidity.Lowering.V07.FixedBytesComparisonControls.pure_less_fixture' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms Solidity.Lowering.V07.FixedBytesComparisonControls.pure_less_fixture

/-- info: 'Solidity.Lowering.V07.FixedBytesComparisonControls.ordered_less_fixture' depends on axioms: [propext] -/
#guard_msgs in
#print axioms Solidity.Lowering.V07.FixedBytesComparisonControls.ordered_less_fixture

/-- info: 'Solidity.Lowering.V07.FixedBytesComparisonControls.length_client' does not depend on any axioms -/
#guard_msgs in
#print axioms Solidity.Lowering.V07.FixedBytesComparisonControls.length_client

/-- info: 'Solidity.Lowering.V07.FixedBytesComparisonControls.numeric_client' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms Solidity.Lowering.V07.FixedBytesComparisonControls.numeric_client

/-- info: 'Solidity.Lowering.V07.FixedBytesComparisonControls.value_client' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms Solidity.Lowering.V07.FixedBytesComparisonControls.value_client

/-- info: 'Solidity.Lowering.V07.FixedBytesComparisonControls.pair_client' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms Solidity.Lowering.V07.FixedBytesComparisonControls.pair_client

/-- info: 'Solidity.Lowering.V07.FixedBytesComparisonControls.assignment_client' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms Solidity.Lowering.V07.FixedBytesComparisonControls.assignment_client

/-- info: 'Solidity.Lowering.V07.FixedBytesComparisonControls.operand_client' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms Solidity.Lowering.V07.FixedBytesComparisonControls.operand_client

/-- info: 'Solidity.Lowering.V07.FixedBytesComparisonControls.transport_client' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms Solidity.Lowering.V07.FixedBytesComparisonControls.transport_client

/-- info: 'Solidity.Lowering.V07.FixedBytesComparisonControls.self_client' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms Solidity.Lowering.V07.FixedBytesComparisonControls.self_client

/-- info: 'Solidity.Lowering.V07.FixedBytesComparisonControls.extension_client' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms Solidity.Lowering.V07.FixedBytesComparisonControls.extension_client

/-- info: 'Solidity.Lowering.V07.FixedBytesComparisonControls.code_client' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms Solidity.Lowering.V07.FixedBytesComparisonControls.code_client

/-- info: 'Solidity.Lowering.V07.FixedBytesComparisonControls.pass_client' depends on axioms: [propext] -/
#guard_msgs in
#print axioms Solidity.Lowering.V07.FixedBytesComparisonControls.pass_client

/-- info: 'Solidity.Lowering.V07.FixedBytesComparisonControls.prefix_client' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms Solidity.Lowering.V07.FixedBytesComparisonControls.prefix_client

end Solidity.Lowering.V07.FixedBytesComparisonControls
