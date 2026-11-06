import Solidity.Lowering.V07.P12AssignedCondition
import Solidity.Lowering.V07.P12Controls

namespace Solidity.Lowering.V07.P12AssignedConditionControls
open P12NextInterface Source.SemanticsExamples
open P12Controls (C E SrcCtx TgtCtx source target mapping)
open MixedAssignmentControls (globals)

/-- An adapter of the existing discriminating relation, not a new value model. -/
def values : ValueRelation E C := fun _ _ τ u sv tv =>
  ∃ original : u.TDenote C target.H, HEq tv original ∧ P12Controls.BindingRel τ u sv original
/-- Both complete worlds are anchored to the inhabited fixture. Local updates
may change callers; allocation and world mutation are outside this witness. -/
def worlds : WorldRelation E C := fun s t => s = source.2 ∧ t = target.glob

theorem initial : Aligned mapping values worlds source target := by
  refine ⟨⟨rfl,rfl⟩,?_⟩
  intro τ i
  exact ⟨_,HEq.rfl,P12Controls.initial i⟩

theorem bool_reflect (s : Source.St E) (t : State C []) (v : Source.Val E.layout .bool) (b : Bool)
    (related : values s t .bool (.val .bool) v b) : v = .bool b := by
  obtain ⟨original,same,linked⟩ := related
  have eq : b = original := eq_of_heq same
  subst original
  exact P12Controls.bool_reflect v b linked

def srcPair (old rhs : Bool) : Source.EMState E SrcCtx :=
  ((source.1.set .here (.bool old)).set (.there .here) (.bool rhs),source.2)
def tgtPair (old rhs : Bool) : State C TgtCtx :=
  (target.setLocal .here old).setLocal (.there .here) rhs

theorem initial_pair (old rhs : Bool) : Aligned mapping values worlds (srcPair old rhs) (tgtPair old rhs) := by
  have first : mapping.Related (values source.2 target.glob)
      (source.1.set .here (.bool old)) (TEnv.set .here old target.env) := ContextMap.related_write mapping (values source.2 target.glob)
    source.1 target.env initial.2 (Source.Idx.here) (Idx.here) rfl
    (.bool old) old (by exact ⟨old,HEq.rfl,rfl⟩)
  have second : mapping.Related (values source.2 target.glob)
      ((source.1.set .here (.bool old)).set (.there .here) (.bool rhs))
      (TEnv.set (.there .here) rhs (TEnv.set .here old target.env)) := ContextMap.related_write mapping (values source.2 target.glob)
    (source.1.set .here (.bool old)) (TEnv.set .here old target.env) first
    (Source.Idx.there .here) (Idx.there .here) rfl (.bool rhs) rhs (by exact ⟨rhs,HEq.rfl,rfl⟩)
  exact ⟨⟨rfl,rfl⟩,second⟩


def producer (p : Roadmap.Pipeline) (checked : Bool) :=
  P12AssignedCondition.assignment (globals p) {F0 with checked := checked} mapping values worlds
    bool_reflect ⟨source,target,initial⟩ .here (.there .here) .here (.there .here) rfl rfl

def source_zero_client (p : Roadmap.Pipeline) := P12AssignedCondition.source_zero (globals p) F0 source
  .here (.there .here)
def source_one_client (p : Roadmap.Pipeline) := P12AssignedCondition.source_one (globals p) F0 source
  .here (.there .here)
def source_success_client (p : Roadmap.Pipeline) (checked : Bool) (fuel : Nat) :=
  P12AssignedCondition.source_success (globals p) {F0 with checked := checked} (fuel+2) source
    (source.1.set .here (.bool true),source.2) .here (.there .here) true true rfl
    (source_assign_local_run (globals p) {F0 with checked := checked} fuel source .here (.there .here) _ rfl)
def source_not_revert_client (p : Roadmap.Pipeline) (fuel : Nat) (data : Roadmap.Bytes) :=
  P12AssignedCondition.source_not_revert (globals p) F0 fuel source source .here (.there .here) true rfl data

def success_client (p : Roadmap.Pipeline) (checked : Bool) (fuel : Nat) :=
  (producer p checked).success (fuel+2) source (source.1.set .here (.bool true),source.2) target true
    initial (source_assign_local_run (globals p) {F0 with checked := checked} fuel source
      .here (.there .here) _ rfl)
def pair_success_client (p : Roadmap.Pipeline) (checked : Bool) (fuel : Nat) (old rhs : Bool) :=
  (producer p checked).success (fuel+2) (srcPair old rhs)
    ((srcPair old rhs).1.set .here (.bool rhs),(srcPair old rhs).2) (tgtPair old rhs) rhs
    (initial_pair old rhs)
    (source_assign_local_run (globals p) {F0 with checked := checked} fuel (srcPair old rhs)
      .here (.there .here) _ rfl)
def operand_client := assigned_condition_operand_run target .here (.there .here)
def prefix_client := assigned_condition_prefix_run target .here (.there .here)
def extension_client (p : Roadmap.Pipeline) (checked : Bool) := DeferredSource.Operand.run_wk
  (producer p checked).operand (Thin.drop (t := .val .bool) .refl) target (true,target.env)
def live_reference_client := P12Controls.live_memory_and_storage
def self_producer (p : Roadmap.Pipeline) (checked : Bool) :=
  P12AssignedCondition.assignment (globals p) {F0 with checked := checked} mapping values worlds
    bool_reflect ⟨source,target,initial⟩ .here .here .here .here rfl rfl

def observe (p : Roadmap.Pipeline) (checked : Bool) (fuel : Nat) (old rhs : Bool) : Option (List Int) :=
  let s := srcPair old rhs
  let t := tgtPair old rhs
  let sourceObservation := match (Source.evalE (globals p) {F0 with checked := checked} fuel
      (.assign (.local .here) (.local (.there .here)))).run s with
    | (.ok (.val (.bool c)),post) => match post.1.get .here,post.1.get (.there .here) with
      | .bool a,.bool b => some [1,Int.ofNat c.toNat,Int.ofNat a.toNat,Int.ofNat b.toNat]
      | _,_ => none
    | (.error .timeout,post) => match post.1.get .here,post.1.get (.there .here) with
      | .bool a,.bool b => some [-1,-1,Int.ofNat a.toNat,Int.ofNat b.toNat]
      | _,_ => none
    | _ => none
  match sourceObservation,(producer p checked).operand.code.run t,(producer p checked).operand.run t with
  | some xs,.ok cap,.ok (out,.prim result) => some (xs ++
      [Int.ofNat (TEnv.get .here cap.st.env).toNat,
       Int.ofNat (TEnv.get (.there .here) cap.st.env).toNat,
       Int.ofNat (TEnv.get (.there (.there .here)) cap.st.env).toNat,
       Int.ofNat result.toNat,Int.ofNat (TEnv.get .here out.st.env).toNat,
       Int.ofNat (TEnv.get (.there .here) out.st.env).toNat])
  | _,_,_ => none

/-- info: [[some [-1, -1, 0, 1, 1, 1, 1, 1, 1, 1], some [-1, -1, 0, 1, 1, 1, 1, 1, 1, 1], some [1, 1, 1, 1, 1, 1, 1, 1, 1, 1]],
 [some [-1, -1, 0, 1, 1, 1, 1, 1, 1, 1], some [-1, -1, 0, 1, 1, 1, 1, 1, 1, 1], some [1, 1, 1, 1, 1, 1, 1, 1, 1, 1]]] -/
#guard_msgs in
#eval IO.println (reprStr ([Roadmap.Pipeline.legacy,.viaIR].map fun p =>
  [0,1,2].map fun n => observe p true n false true))

/-- info: true -/
#guard_msgs in
#eval IO.println (reprStr ([Roadmap.Pipeline.legacy,.viaIR].all fun p => [false,true].all fun checked =>
  [false,true].all fun old => [false,true].all fun rhs => (List.range 6).all fun fuel =>
    let o := Int.ofNat old.toNat
    let r := Int.ofNat rhs.toNat
    observe p checked fuel old rhs == some
      ((if fuel < 2 then [-1,-1,o,r] else [1,r,r,r]) ++ [r,r,r,r,r,r])))

-- Wrong code captures the old destination before it performs the real write.
def stale : DeferredSource.Operand C TgtCtx (.prim .bool) :=
  ⟨_,.cons (.declLocal .bool (.user "wrong_old_choice") (some (.simple (.local .here))))
    (.cons (.assignLocal (.there .here) (.simple (.local (.there (.there .here))))) .nil),
    .val (.simple (.local .here))⟩
def resultAndCaller (e : DeferredSource.Operand C TgtCtx (.prim .bool)) : Option (Bool × Bool) :=
  match e.run target with | .ok (out,.prim result) => some (result,TEnv.get .here out.st.env) | _ => none
/-- info: [some (true, true), some (true, false), some (false, true)] -/
#guard_msgs in
#eval IO.println (reprStr [resultAndCaller (producer .legacy true).operand,
  resultAndCaller (DeferredSource.Operand.ofSrc (.val (.simple (.local (.there .here))))),
  resultAndCaller stale])

/-- info: 'Solidity.Lowering.V07.P12AssignedConditionControls.initial' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Solidity.Lowering.V07.P12AssignedConditionControls.initial

/-- info: 'Solidity.Lowering.V07.P12AssignedConditionControls.bool_reflect' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms Solidity.Lowering.V07.P12AssignedConditionControls.bool_reflect

/-- info: 'Solidity.Lowering.V07.P12AssignedConditionControls.initial_pair' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms Solidity.Lowering.V07.P12AssignedConditionControls.initial_pair

/-- info: 'Solidity.Lowering.V07.P12AssignedConditionControls.producer' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Solidity.Lowering.V07.P12AssignedConditionControls.producer

/-- info: 'Solidity.Lowering.V07.P12AssignedConditionControls.source_zero_client' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms Solidity.Lowering.V07.P12AssignedConditionControls.source_zero_client

/-- info: 'Solidity.Lowering.V07.P12AssignedConditionControls.source_one_client' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms Solidity.Lowering.V07.P12AssignedConditionControls.source_one_client

/-- info: 'Solidity.Lowering.V07.P12AssignedConditionControls.source_success_client' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms Solidity.Lowering.V07.P12AssignedConditionControls.source_success_client

/-- info: 'Solidity.Lowering.V07.P12AssignedConditionControls.source_not_revert_client' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms Solidity.Lowering.V07.P12AssignedConditionControls.source_not_revert_client

/-- info: 'Solidity.Lowering.V07.P12AssignedConditionControls.success_client' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms Solidity.Lowering.V07.P12AssignedConditionControls.success_client

/-- info: 'Solidity.Lowering.V07.P12AssignedConditionControls.pair_success_client' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms Solidity.Lowering.V07.P12AssignedConditionControls.pair_success_client

/-- info: 'Solidity.Lowering.V07.P12AssignedConditionControls.operand_client' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms Solidity.Lowering.V07.P12AssignedConditionControls.operand_client

/-- info: 'Solidity.Lowering.V07.P12AssignedConditionControls.prefix_client' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms Solidity.Lowering.V07.P12AssignedConditionControls.prefix_client

/-- info: 'Solidity.Lowering.V07.P12AssignedConditionControls.extension_client' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms Solidity.Lowering.V07.P12AssignedConditionControls.extension_client

/-- info: 'Solidity.Lowering.V07.P12AssignedConditionControls.live_reference_client' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms Solidity.Lowering.V07.P12AssignedConditionControls.live_reference_client

/-- info: 'Solidity.Lowering.V07.P12AssignedConditionControls.self_producer' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms Solidity.Lowering.V07.P12AssignedConditionControls.self_producer

end Solidity.Lowering.V07.P12AssignedConditionControls
