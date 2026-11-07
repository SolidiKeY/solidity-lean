import Solidity.Lowering.V07.P12AssignedConditionControls

/-! A concrete producer of the published P12 StorageCapture contract over the
existing mixed caller fixture. This is not a general reference compiler or a
Source declaration/graph/path admission theorem. No copy or allocation occurs.
Initial alias identity is derived from the existing binding relation, never
from equal contents or a supplied desired execution/preservation result. -/
namespace Solidity.Lowering.V07.P12StorageCaptureControls
open Source.SemanticsExamples P12NextInterface
open P12Controls (C E SrcCtx TgtCtx source target mapping)
open P12AssignedConditionControls (values worlds initial initial_pair srcPair tgtPair)
open MixedAssignmentControls (globals path storageRef)

abbrev sourceSlot : Source.Idx SrcCtx (.bytes .storage) :=
  .there (.there (.there (.there (.there .here))))
abbrev targetSlot : Idx TgtCtx (.alias bytesR) :=
  .there (.there (.there (.there (.there .here))))

theorem binding (s : Source.EMState E SrcCtx) (t : State C TgtCtx)
    (aligned : Aligned mapping values worlds s t) :
    s.1.get sourceSlot = .storRef rfl path ∧ TEnv.get targetSlot t.env = some storageRef := by
  obtain ⟨original,same,sourceRead,targetRead⟩ := aligned.2 sourceSlot
  have eq : TEnv.get targetSlot t.env = original := eq_of_heq same
  exact ⟨sourceRead,eq.trans targetRead⟩

theorem storage_index {σ : Source.STy} (location : σ.loc? = some .storage) (i : Source.Idx SrcCtx σ) :
    σ = .bytes .storage ∧ HEq i sourceSlot := by
  cases i with
  | here => cases location
  | there i => cases i with
    | here => cases location
    | there i => cases i with
      | here => cases location
      | there i => cases i with
        | here => cases location
        | there i => cases i with
          | here => cases location
          | there i => cases i with
            | here => exact ⟨rfl,HEq.rfl⟩
            | there i => nomatch i

theorem initial_alias (s : Source.EMState E SrcCtx) (t : State C TgtCtx)
    (aligned : Aligned mapping values worlds s t)
    (σ : Source.STy) (location : σ.loc? = some .storage) (i : Source.Idx SrcCtx σ)
    (j : Idx TgtCtx (.alias bytesR)) (oldPath : Source.SPath) (oldRef : SRef C (.ref bytesR))
    (slot : mapping.slot i = ⟨.alias bytesR,j⟩)
    (sourceRead : s.1.get i = .storRef location oldPath)
    (targetRead : TEnv.get j t.env = some oldRef) : path = oldPath ↔ storageRef = oldRef := by
  obtain ⟨sameType,sameIndex⟩ := storage_index location i
  subst σ
  have sameIndex' : i = sourceSlot := eq_of_heq sameIndex
  subst i
  have sameTarget : targetSlot = j := eq_of_heq (Sigma.mk.inj slot).2
  subst j
  obtain ⟨knownSource,knownTarget⟩ := binding s t aligned
  have samePath : path = oldPath := by
    have observed : some path = some oldPath := congrArg
      (fun v : Source.Val E.layout (.bytes .storage) => match v with | .storRef _ p => some p | _ => none)
      (knownSource.symm.trans sourceRead)
    exact Option.some.inj observed
  have sameRef : storageRef = oldRef := Option.some.inj (knownTarget.symm.trans targetRead)
  exact ⟨fun _ => sameRef,fun _ => samePath⟩

theorem source_success (G : Source.Glob E) (F : Source.Fr) (n : Nat)
    (s after : Source.EMState E SrcCtx) (result : Source.SPath)
    (read : s.1.get sourceSlot = .storRef rfl path)
    (run : (Source.evalE G F n (.local sourceSlot)).run s = (.ok (.val (.storRef rfl result)),after)) :
    result = path ∧ after = s := by
  cases n with
  | zero => cases run
  | succ n =>
    rw [source_local_value_run G F n s sourceSlot (.storRef rfl path) read] at run
    have observed : some path = some result := congrArg
      (fun v : Source.R (Source.RVal E.layout (.bytes .storage)) =>
        match v with | .ok (.val (.storRef _ p)) => some p | _ => none) (congrArg Prod.fst run)
    exact ⟨(Option.some.inj observed).symm,(congrArg Prod.snd run).symm⟩

theorem source_not_revert (G : Source.Glob E) (F : Source.Fr) (n : Nat)
    (s after : Source.EMState E SrcCtx) (data : Roadmap.Bytes) :
    (Source.evalE G F n (.local sourceSlot)).run s ≠ (.error (.revert data),after) := by
  cases n <;> intro run <;> cases run

/-- An inhabited *fixture* producer for every G/F and every aligned caller,
not a producer of admitted-source coverage. It adds no initial alias premise. -/
def producer (G : Source.Glob E) (F : Source.Fr) :
    StorageCapture G F mapping values worlds (.bytes .storage) rfl bytesR (.local sourceSlot) where
  code := storageCapture targetSlot
  initial_nonempty := ⟨source,target,initial⟩
  success := by
    intro n s after t result aligned run
    obtain ⟨read,nativeRead⟩ := binding s t aligned
    obtain ⟨samePath,sameState⟩ := source_success G F n s after result read run
    subst result
    subst after
    have transport := related_storage_capture G F 0 s t mapping (values s.2 t.glob)
      aligned.2 sourceSlot targetSlot path storageRef rfl read nativeRead
    refine ⟨⟨t.push (t := .alias bytesR) (some storageRef),List.prefix_refl _⟩,storageRef,
      transport.2.1,rfl,transport.2.2.1,transport.2.2.2.2.1,aligned.1,?_⟩
    intro σ location i j oldPath oldRef slot sourceRead targetRead
    exact initial_alias s t aligned σ location i j oldPath oldRef slot sourceRead targetRead
  revert := by
    intro n s after t data _ run
    exact False.elim (source_not_revert G F n s after data run)

def success_client (p : Roadmap.Pipeline) (checked old rhs : Bool) (n : Nat) :=
  (producer (globals p) {F0 with checked := checked}).success (n+1) (srcPair old rhs) (srcPair old rhs)
    (tgtPair old rhs) path (initial_pair old rhs)
    (source_local_value_run (globals p) {F0 with checked := checked} n (srcPair old rhs)
      sourceSlot (.storRef rfl path) (by rfl))
def live_refs_client := P12Controls.live_memory_and_storage

theorem exact_capture (p : Roadmap.Pipeline) (checked old rhs : Bool) :
    (producer (globals p) {F0 with checked := checked}).code.run (tgtPair old rhs) =
      .ok (⟨(tgtPair old rhs).push (t := .alias bytesR) (some storageRef),List.prefix_refl _⟩) := by
  exact storage_capture_run (tgtPair old rhs) targetSlot storageRef rfl

theorem drop_capture (old rhs : Bool) :
    ((tgtPair old rhs).push (t := .alias bytesR) (some storageRef)).drop (.push .refl) = tgtPair old rhs := by
  rfl

theorem repeated_capture (old rhs : Bool) :
    (storageCapture (.here : Idx (.alias bytesR :: TgtCtx) (.alias bytesR))).run
      ((tgtPair old rhs).push (t := .alias bytesR) (some storageRef)) =
      .ok (⟨((tgtPair old rhs).push (t := .alias bytesR) (some storageRef)).push
        (t := .alias bytesR) (some storageRef),List.prefix_refl _⟩) := by
  exact storage_capture_run _ .here storageRef rfl

def alias_client (old rhs : Bool) := initial_alias (srcPair old rhs) (tgtPair old rhs)
  (initial_pair old rhs) (.bytes .storage) rfl sourceSlot targetSlot path storageRef rfl rfl rfl

def observe (p : Roadmap.Pipeline) (checked old rhs : Bool) (n : Nat) : Option (List Int) :=
  let src := match (Source.evalE (globals p) {F0 with checked := checked} n (.local sourceSlot)).run (srcPair old rhs) with
    | (.ok (.val (.storRef _ actual)),after) => match after.1.get .here,after.1.get (.there .here) with
      | .bool a,.bool b => some [1,if actual=path then 1 else 0,Int.ofNat a.toNat,Int.ofNat b.toNat]
      | _,_ => none
    | (.error .timeout,after) => match after.1.get .here,after.1.get (.there .here) with
      | .bool a,.bool b => some [-1,-1,Int.ofNat a.toNat,Int.ofNat b.toNat]
      | _,_ => none
    | _ => none
  match src,(producer (globals p) {F0 with checked := checked}).code.run (tgtPair old rhs) with
  | some xs,.ok out => match out.st.env.1,TEnv.get (.there targetSlot) out.st.env,
      (SPath.alias .here : SPath C (.alias bytesR :: TgtCtx) (.ref bytesR)).resolveT out.st with
    | some captured,some oldRef,.ok resolved => some (xs ++
      [if captured.root=storageRef.root then 1 else 0,if oldRef.root=captured.root then 1 else 0,
       if resolved.root=captured.root then 1 else 0,
       Int.ofNat out.st.env.2.1.toNat,Int.ofNat out.st.env.2.2.1.toNat,
       if out.st.env.2.2.2.2.2.1.map HRef.id == some P12Controls.memoryRef.id then 1 else 0])
    | _,_,_ => none
  | _,_ => none

/-- info: true -/
#guard_msgs in
#eval IO.println (reprStr ([Roadmap.Pipeline.legacy,.viaIR].all fun p => [false,true].all fun checked =>
  [false,true].all fun old => [false,true].all fun rhs => (List.range 5).all fun n =>
    let o := Int.ofNat old.toNat
    let r := Int.ofNat rhs.toNat
    let src := if n=0 then [-1,-1,o,r] else [1,1,o,r]
    observe p checked old rhs n == some (src ++ [1,1,1,o,r,1])))

def wrongCode : Prog C TgtCtx (.alias bytesR :: TgtCtx) :=
  .cons (.declStorage bytesR (.user "wrong_empty_capture") none) .nil

theorem wrong_run (old rhs : Bool) : wrongCode.run (tgtPair old rhs) =
    .ok (⟨(tgtPair old rhs).push (t := .alias bytesR) none,List.prefix_refl _⟩) := by
  rfl

theorem wrong_resolution (old rhs : Bool) :
    (SPath.alias .here : SPath C (.alias bytesR :: TgtCtx) (.ref bytesR)).resolveT
      ((tgtPair old rhs).push (t := .alias bytesR) none) = .error .revert := by
  rfl

def wrongObservation : Option (List Int) :=
  match wrongCode.run target with
  | .ok out => match (SPath.alias .here : SPath C (.alias bytesR :: TgtCtx) (.ref bytesR)).resolveT out.st with
    | .error .revert => some [-1,0]
    | .ok _ => some [1,0]
    | _ => none
  | _ => none
/-- info: some [-1, 0] -/
#guard_msgs in
#eval IO.println (reprStr wrongObservation)
/-- info: some [1, 1, 0, 1, 1, 1, 1, 0, 1, 1] -/
#guard_msgs in
#eval IO.println (reprStr (observe .viaIR false false true 1))

/-- info: 'Solidity.Lowering.V07.P12StorageCaptureControls.binding' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Solidity.Lowering.V07.P12StorageCaptureControls.binding

/-- info: 'Solidity.Lowering.V07.P12StorageCaptureControls.storage_index' does not depend on any axioms -/
#guard_msgs in
#print axioms Solidity.Lowering.V07.P12StorageCaptureControls.storage_index

/-- info: 'Solidity.Lowering.V07.P12StorageCaptureControls.initial_alias' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms Solidity.Lowering.V07.P12StorageCaptureControls.initial_alias

/-- info: 'Solidity.Lowering.V07.P12StorageCaptureControls.source_success' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms Solidity.Lowering.V07.P12StorageCaptureControls.source_success

/-- info: 'Solidity.Lowering.V07.P12StorageCaptureControls.source_not_revert' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms Solidity.Lowering.V07.P12StorageCaptureControls.source_not_revert

/-- info: 'Solidity.Lowering.V07.P12StorageCaptureControls.exact_capture' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms Solidity.Lowering.V07.P12StorageCaptureControls.exact_capture

/-- info: 'Solidity.Lowering.V07.P12StorageCaptureControls.drop_capture' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms Solidity.Lowering.V07.P12StorageCaptureControls.drop_capture

/-- info: 'Solidity.Lowering.V07.P12StorageCaptureControls.repeated_capture' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms Solidity.Lowering.V07.P12StorageCaptureControls.repeated_capture

/-- info: 'Solidity.Lowering.V07.P12StorageCaptureControls.wrong_run' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Solidity.Lowering.V07.P12StorageCaptureControls.wrong_run

/-- info: 'Solidity.Lowering.V07.P12StorageCaptureControls.wrong_resolution' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms Solidity.Lowering.V07.P12StorageCaptureControls.wrong_resolution

/-- info: 'Solidity.Lowering.V07.P12StorageCaptureControls.producer' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Solidity.Lowering.V07.P12StorageCaptureControls.producer

/-- info: 'Solidity.Lowering.V07.P12StorageCaptureControls.success_client' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms Solidity.Lowering.V07.P12StorageCaptureControls.success_client

/-- info: 'Solidity.Lowering.V07.P12StorageCaptureControls.live_refs_client' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms Solidity.Lowering.V07.P12StorageCaptureControls.live_refs_client

/-- info: 'Solidity.Lowering.V07.P12StorageCaptureControls.alias_client' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms Solidity.Lowering.V07.P12StorageCaptureControls.alias_client

end Solidity.Lowering.V07.P12StorageCaptureControls
