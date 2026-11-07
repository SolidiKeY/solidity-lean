import Solidity.Lowering.V07.P12ContextExtension
import Solidity.Lowering.V07.P12AssignedConditionControls

namespace Solidity.Lowering.V07.P12ContextExtensionControls
open Source.SemanticsExamples P12NextInterface
open P12ContextExtension
open P12Controls (C E SrcCtx TgtCtx source target mapping)
open P12AssignedConditionControls (values worlds initial initial_pair srcPair tgtPair)
open MixedAssignmentControls (globals)

abbrev ExtraCtx : Ctx := .val .bool :: TgtCtx
abbrev MixedCtx : Ctx := .mem bytesR :: ExtraCtx

def boolThin : Thin TgtCtx ExtraCtx := .drop .refl
def memoryThin : Thin ExtraCtx MixedCtx := .drop .refl
/-- These typed initial backgrounds supply no semantic or preservation premise.
Nullable reference slots in the initial witness may be filled; runtime callers
below instead carry the existing *live* memory alias. -/
def boolBackground (H : HTy) : TEnv C H ExtraCtx := (false,(false,(false,(PrimTy.dflt .uint,(PrimTy.dflt .uint,(none,(none,())))))))
def memoryBackground (H : HTy) : TEnv C H MixedCtx := (none,boolBackground H)
def expr : Source.RExpr E SrcCtx .bool := .assign (.local .here) (.local (.there .here))
def producer (p : Roadmap.Pipeline) (checked : Bool) :=
  weaken (globals p) {F0 with checked := checked} mapping values worlds expr
    (P12AssignedConditionControls.producer p checked) boolThin boolBackground
def mixedProducer (p : Roadmap.Pipeline) (checked : Bool) :=
  weaken (globals p) {F0 with checked := checked} (mapping.wk boolThin) values worlds expr
    (producer p checked) memoryThin memoryBackground
def directProducer (p : Roadmap.Pipeline) (checked : Bool) :=
  weaken (globals p) {F0 with checked := checked} mapping values worlds expr
    (P12AssignedConditionControls.producer p checked) (boolThin.trans memoryThin) memoryBackground

def extended (old rhs sentinel : Bool) : State C ExtraCtx := (tgtPair old rhs).push (t := .val .bool) sentinel
def mixed (old rhs sentinel : Bool) : State C MixedCtx :=
  (extended old rhs sentinel).push (t := .mem bytesR) (some P12Controls.memoryRef)

theorem extension_initial (old rhs sentinel : Bool) :
    Aligned (mapping.wk boolThin) values worlds (srcPair old rhs) (extended old rhs sentinel) := by
  exact aligned_lift mapping values worlds (srcPair old rhs) (tgtPair old rhs) boolThin
    (sentinel,(tgtPair old rhs).env) (initial_pair old rhs)
theorem mixed_initial (old rhs sentinel : Bool) :
    Aligned ((mapping.wk boolThin).wk memoryThin) values worlds (srcPair old rhs) (mixed old rhs sentinel) := by
  exact aligned_lift (mapping.wk boolThin) values worlds (srcPair old rhs) (extended old rhs sentinel)
    memoryThin (some P12Controls.memoryRef,(extended old rhs sentinel).env) (extension_initial old rhs sentinel)

def success_client (p : Roadmap.Pipeline) (checked old rhs sentinel : Bool) (fuel : Nat) :=
  (producer p checked).success (fuel+2) (srcPair old rhs)
    ((srcPair old rhs).1.set .here (.bool rhs),(srcPair old rhs).2) (extended old rhs sentinel) rhs
    (extension_initial old rhs sentinel)
    (source_assign_local_run (globals p) {F0 with checked := checked} fuel (srcPair old rhs) .here (.there .here) _ rfl)
def mixed_success_client (p : Roadmap.Pipeline) (checked old rhs sentinel : Bool) (fuel : Nat) :=
  (mixedProducer p checked).success (fuel+2) (srcPair old rhs)
    ((srcPair old rhs).1.set .here (.bool rhs),(srcPair old rhs).2) (mixed old rhs sentinel) rhs
    (mixed_initial old rhs sentinel)
    (source_assign_local_run (globals p) {F0 with checked := checked} fuel (srcPair old rhs) .here (.there .here) _ rfl)
def projection_client (old rhs sentinel : Bool) := aligned_thin mapping values worlds
  (srcPair old rhs) (extended old rhs sentinel) boolThin (extension_initial old rhs sentinel)
def composition_client := ContextMap.wk_composition mapping boolThin memoryThin
def identity_client := ContextMap.wk_identity mapping

def failing : DeferredSource.Operand C TgtCtx (.prim .bool) :=
  ⟨_,.cons (.revertData [.bytes (Source.panicData .divZero)]) .nil,.val (.simple (.bool false))⟩
theorem extended_error : (failing.wk boolThin).run (extended false true true) =
    .error (THalt.ofData (Source.panicData .divZero)) := by
  rw [operand_thin]
  rfl

theorem mixed_run (p : Roadmap.Pipeline) (checked old rhs sentinel : Bool) :
    (mixedProducer p checked).operand.run (mixed old rhs sentinel) =
      .ok (⟨(mixed old rhs sentinel).setLocal (.there (.there .here)) rhs,List.prefix_refl _⟩,.prim rhs) := by
  rfl

/-- Ordered Source/result/caller observations plus extra locals; complete
world and untouched storage equality are proved by mixed_run. Successful conditions use their actual horizons.
Source timeout correspondence is deliberately not claimed. -/
def observe (p : Roadmap.Pipeline) (checked old rhs sentinel : Bool) (fuel : Nat) : Option (List Int) :=
  let s := srcPair old rhs
  let t := mixed old rhs sentinel
  let sourcePart := match (Source.evalE (globals p) {F0 with checked := checked} (fuel+2) expr).run s with
    | (.ok (.val (.bool value)),after) => match after.1.get .here, after.1.get (.there .here) with
      | .bool dest,.bool read => some [Int.ofNat value.toNat,Int.ofNat dest.toNat,Int.ofNat read.toNat]
      | _,_ => none
    | _ => none
  match sourcePart,(mixedProducer p checked).operand.run t,(directProducer p checked).operand.run t with
  | some xs,.ok (out,.prim value),.ok (direct,.prim value2) =>
    let env := out.st.env
    some (xs ++ [Int.ofNat value.toNat,Int.ofNat env.2.1.toNat,Int.ofNat env.2.2.1.toNat,
      Int.ofNat env.2.2.2.1.toNat,
      if env.1.map HRef.id == some P12Controls.memoryRef.id then 1 else 0,
      if env.2.2.2.2.2.2.1.map HRef.id == some P12Controls.memoryRef.id then 1 else 0,
      Int.ofNat value2.toNat,Int.ofNat direct.st.env.2.1.toNat,Int.ofNat direct.st.env.2.2.1.toNat])
  | _,_,_ => none

/-- info: true -/
#guard_msgs in
#eval IO.println (reprStr ([Roadmap.Pipeline.legacy,.viaIR].all fun p => [false,true].all fun checked =>
  [false,true].all fun old => [false,true].all fun rhs => [false,true].all fun sentinel => (List.range 4).all fun fuel =>
    let r := Int.ofNat rhs.toNat
    let b := Int.ofNat sentinel.toNat
    observe p checked old rhs sentinel fuel == some [r,r,r,r,b,r,r,1,1,r,b,r]))

/-- Deliberately stale target indices write the added sentinel and read the old
original destination. The correct weakened operand reaches the RHS instead. -/
def wrong : DeferredSource.Operand C ExtraCtx (.prim .bool) := assignLocalOperand .here (.there .here)
def wrongObservation : Option (Bool × Bool × Bool) :=
  match wrong.run (extended false true true) with
  | .ok (out,.prim value) => some (value,out.st.env.1,out.st.env.2.1)
  | _ => none
/-- info: some (false, false, false) -/
#guard_msgs in
#eval IO.println (reprStr wrongObservation)
/-- info: true -/
#guard_msgs in
#eval IO.println (reprStr (observe .legacy false false true true 0 == some [1,1,1,1,1,1,1,1,1,1,1,1]))

/-- info: 'Solidity.Lowering.V07.P12ContextExtensionControls.extension_initial' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms Solidity.Lowering.V07.P12ContextExtensionControls.extension_initial

/-- info: 'Solidity.Lowering.V07.P12ContextExtensionControls.mixed_initial' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms Solidity.Lowering.V07.P12ContextExtensionControls.mixed_initial

/-- info: 'Solidity.Lowering.V07.P12ContextExtensionControls.extended_error' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms Solidity.Lowering.V07.P12ContextExtensionControls.extended_error

/-- info: 'Solidity.Lowering.V07.P12ContextExtensionControls.mixed_run' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Solidity.Lowering.V07.P12ContextExtensionControls.mixed_run

/-- info: 'Solidity.Lowering.V07.P12ContextExtensionControls.producer' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Solidity.Lowering.V07.P12ContextExtensionControls.producer

/-- info: 'Solidity.Lowering.V07.P12ContextExtensionControls.mixedProducer' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms Solidity.Lowering.V07.P12ContextExtensionControls.mixedProducer

/-- info: 'Solidity.Lowering.V07.P12ContextExtensionControls.directProducer' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms Solidity.Lowering.V07.P12ContextExtensionControls.directProducer

/-- info: 'Solidity.Lowering.V07.P12ContextExtensionControls.success_client' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms Solidity.Lowering.V07.P12ContextExtensionControls.success_client

/-- info: 'Solidity.Lowering.V07.P12ContextExtensionControls.mixed_success_client' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms Solidity.Lowering.V07.P12ContextExtensionControls.mixed_success_client

/-- info: 'Solidity.Lowering.V07.P12ContextExtensionControls.projection_client' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms Solidity.Lowering.V07.P12ContextExtensionControls.projection_client

/-- info: 'Solidity.Lowering.V07.P12ContextExtensionControls.composition_client' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms Solidity.Lowering.V07.P12ContextExtensionControls.composition_client

/-- info: 'Solidity.Lowering.V07.P12ContextExtensionControls.identity_client' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms Solidity.Lowering.V07.P12ContextExtensionControls.identity_client

end Solidity.Lowering.V07.P12ContextExtensionControls
