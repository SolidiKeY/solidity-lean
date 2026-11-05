import Solidity.Lowering.V07.P12AssignedConditionControls

/-! A concrete full P12 memory-reference capture producer over the published
mixed fixture. Initial identity and non-nullness are derived from its existing
binding/world relations. No general selector, declaration/graph admission,
allocation/copy correctness, lifetime or physical-memory theorem is supplied. -/
namespace Solidity.Lowering.V07.P12MemoryCaptureControls
open Source.SemanticsExamples P12NextInterface
open P12Controls (C E SrcCtx TgtCtx source target mapping)
open P12AssignedConditionControls (values worlds initial initial_pair srcPair tgtPair)
open MixedAssignmentControls (globals)

abbrev sourceSlot : Source.Idx SrcCtx (.bytes .memory) := .there (.there (.there (.there .here)))
abbrev targetSlot : Idx TgtCtx (.mem bytesR) := .there (.there (.there (.there .here)))

theorem binding (s : Source.EMState E SrcCtx) (t : State C TgtCtx)
    (aligned : Aligned mapping values worlds s t) :
    s.1.get sourceSlot = .memRef rfl 0 ∧ ∃ r : HRef t.H bytesR, TEnv.get targetSlot t.env = some r := by
  cases t with
  | mk storage H heap env net balance tx =>
    have sameH : H = target.H := congrArg State.H aligned.1.2
    subst H
    obtain ⟨original,same,sourceRead,targetRead⟩ := aligned.2 sourceSlot
    have eq : TEnv.get targetSlot env = original := eq_of_heq same
    exact ⟨sourceRead,P12Controls.memoryRef,eq.trans targetRead⟩

theorem memory_index {σ : Source.STy} (location : σ.loc? = some .memory) (i : Source.Idx SrcCtx σ) :
    σ = .bytes .memory ∧ HEq i sourceSlot := by
  cases i with
  | here => cases location
  | there i => cases i with
    | here => cases location
    | there i => cases i with
      | here => cases location
      | there i => cases i with
        | here => cases location
        | there i => cases i with
          | here => exact ⟨rfl,HEq.rfl⟩
          | there i => cases i with
            | here => cases location
            | there i => nomatch i

theorem initial_alias (s : Source.EMState E SrcCtx) (t : State C TgtCtx)
    (aligned : Aligned mapping values worlds s t) (r : HRef t.H bytesR)
    (nativeRead : TEnv.get targetSlot t.env = some r)
    (σ : Source.STy) (location : σ.loc? = some .memory) (i : Source.Idx SrcCtx σ)
    (oldR : RefTy) (j : Idx TgtCtx (.mem oldR)) (oldAddress : Nat) (oldRef : HRef t.H oldR)
    (slot : mapping.slot i = ⟨.mem oldR,j⟩)
    (sourceRead : s.1.get i = .memRef location oldAddress)
    (targetRead : TEnv.get j t.env = some oldRef) : 0 = oldAddress ↔ r.id = oldRef.id := by
  obtain ⟨sameType,sameIndex⟩ := memory_index location i
  subst σ
  have sameIndex' : i = sourceSlot := eq_of_heq sameIndex
  subst i
  have sameR : bytesR = oldR := LTy.mem.inj (Sigma.mk.inj slot).1
  subst oldR
  have sameTarget : targetSlot = j := eq_of_heq (Sigma.mk.inj slot).2
  subst j
  have sameAddress : 0 = oldAddress := by
    have observed : some 0 = some oldAddress := congrArg
      (fun v : Source.Val E.layout (.bytes .memory) => match v with | .memRef _ a => some a | _ => none)
      ((binding s t aligned).1.symm.trans sourceRead)
    exact Option.some.inj observed
  have sameRef : r = oldRef := Option.some.inj (nativeRead.symm.trans targetRead)
  exact ⟨fun _ => congrArg HRef.id sameRef,fun _ => sameAddress⟩

theorem source_success (G : Source.Glob E) (F : Source.Fr) (n : Nat)
    (s after : Source.EMState E SrcCtx) (address : Nat) (read : s.1.get sourceSlot = .memRef rfl 0)
    (run : (Source.evalE G F n (.local sourceSlot)).run s = (.ok (.val (.memRef rfl address)),after)) :
    address = 0 ∧ after = s := by
  cases n with
  | zero => cases run
  | succ n =>
    rw [source_local_value_run G F n s sourceSlot (.memRef rfl 0) read] at run
    have observed : some 0 = some address := congrArg
      (fun v : Source.R (Source.RVal E.layout (.bytes .memory)) =>
        match v with | .ok (.val (.memRef _ a)) => some a | _ => none) (congrArg Prod.fst run)
    exact ⟨(Option.some.inj observed).symm,(congrArg Prod.snd run).symm⟩

theorem source_not_revert (G : Source.Glob E) (F : Source.Fr) (n : Nat)
    (s after : Source.EMState E SrcCtx) (data : Roadmap.Bytes) :
    (Source.evalE G F n (.local sourceSlot)).run s ≠ (.error (.revert data),after) := by
  cases n <;> intro run <;> cases run

/-- This fixture constructor supplies every frozen field without an extra
alias, non-null, execution or postrelation premise. -/
def producer (G : Source.Glob E) (F : Source.Fr) :
    MemoryCapture G F mapping values worlds (.bytes .memory) rfl bytesR rfl (.local sourceSlot) where
  code := memoryCapture targetSlot rfl
  initial_nonempty := ⟨source,target,initial⟩
  success := by
    intro n s after t address aligned run
    obtain ⟨read,r,nativeRead⟩ := binding s t aligned
    obtain ⟨sameAddress,sameState⟩ := source_success G F n s after address read run
    subst address
    subst after
    have transport := related_memory_capture G F 0 s t mapping (values s.2 t.glob)
      aligned.2 sourceSlot targetSlot 0 r rfl read nativeRead
    refine ⟨⟨t.push (t := .mem bytesR) (some r),List.prefix_refl _⟩,r,
      transport.2.1,rfl,transport.2.2.1,transport.2.2.2.2.1,aligned.1,?_⟩
    intro σ location i oldR j oldAddress oldRef slot sourceRead targetRead
    exact initial_alias s t aligned r nativeRead σ location i oldR j oldAddress oldRef slot sourceRead targetRead
  revert := by
    intro n s after t data _ run
    exact False.elim (source_not_revert G F n s after data run)

def success_client (p : Roadmap.Pipeline) (checked old rhs : Bool) (n : Nat) :=
  (producer (globals p) {F0 with checked := checked}).success (n+1) (srcPair old rhs) (srcPair old rhs)
    (tgtPair old rhs) 0 (initial_pair old rhs)
    (source_local_value_run (globals p) {F0 with checked := checked} n (srcPair old rhs)
      sourceSlot (.memRef rfl 0) (by rfl))
def live_refs_client := P12Controls.live_memory_and_storage

theorem exact_capture (p : Roadmap.Pipeline) (checked old rhs : Bool) :
    (producer (globals p) {F0 with checked := checked}).code.run (tgtPair old rhs) =
      .ok (⟨(tgtPair old rhs).push (t := .mem bytesR) (some P12Controls.memoryRef),List.prefix_refl _⟩) := by
  exact memory_capture_run (tgtPair old rhs) targetSlot rfl P12Controls.memoryRef rfl

theorem drop_capture (old rhs : Bool) :
    ((tgtPair old rhs).push (t := .mem bytesR) (some P12Controls.memoryRef)).drop (.push .refl) = tgtPair old rhs := by
  rfl

theorem repeated_capture (old rhs : Bool) :
    (memoryCapture (.here : Idx (.mem bytesR :: TgtCtx) (.mem bytesR)) rfl).run
      ((tgtPair old rhs).push (t := .mem bytesR) (some P12Controls.memoryRef)) =
      .ok (⟨((tgtPair old rhs).push (t := .mem bytesR) (some P12Controls.memoryRef)).push
        (t := .mem bytesR) (some P12Controls.memoryRef),List.prefix_refl _⟩) := by
  exact memory_capture_run ((tgtPair old rhs).push (t := .mem bytesR) (some P12Controls.memoryRef))
    .here rfl P12Controls.memoryRef rfl

def alias_client (old rhs : Bool) := initial_alias (srcPair old rhs) (tgtPair old rhs)
  (initial_pair old rhs) P12Controls.memoryRef rfl (.bytes .memory) rfl sourceSlot bytesR targetSlot
  0 P12Controls.memoryRef rfl rfl rfl

def observe (p : Roadmap.Pipeline) (checked old rhs : Bool) (n : Nat) : Option (List Int) :=
  let src := match (Source.evalE (globals p) {F0 with checked := checked} n (.local sourceSlot)).run (srcPair old rhs) with
    | (.ok (.val (.memRef _ address)),after) => match after.1.get .here,after.1.get (.there .here) with
      | .bool a,.bool b => some [1,Int.ofNat address,Int.ofNat a.toNat,Int.ofNat b.toNat]
      | _,_ => none
    | (.error .timeout,after) => match after.1.get .here,after.1.get (.there .here) with
      | .bool a,.bool b => some [-1,-1,Int.ofNat a.toNat,Int.ofNat b.toNat]
      | _,_ => none
    | _ => none
  match src,(producer (globals p) {F0 with checked := checked}).code.run (tgtPair old rhs) with
  | some xs,.ok out => match out.st.env.1,TEnv.get (.there targetSlot) out.st.env,
      (MPath.var .here rfl : MPath C (.mem bytesR :: TgtCtx) (.ref bytesR)).mvalT out.st,
      out.st.env.2.2.2.2.2.2.1 with
    | some captured,some oldRef,.ok resolved,some storage => some (xs ++
      [Int.ofNat captured.id,Int.ofNat oldRef.id,Int.ofNat (out.st.heap.len captured .dyn),Int.ofNat resolved.id,
       Int.ofNat out.st.env.2.1.toNat,Int.ofNat out.st.env.2.2.1.toNat,
       if storage.root=MixedAssignmentControls.storageRef.root then 1 else 0,Int.ofNat out.st.H.length])
    | _,_,_,_ => none
  | _,_ => none

/-- info: true -/
#guard_msgs in
#eval IO.println (reprStr ([Roadmap.Pipeline.legacy,.viaIR].all fun p => [false,true].all fun checked =>
  [false,true].all fun old => [false,true].all fun rhs => (List.range 5).all fun n =>
    let o := Int.ofNat old.toNat
    let r := Int.ofNat rhs.toNat
    let src := if n=0 then [-1,-1,o,r] else [1,0,o,r]
    observe p checked old rhs n == some (src ++ [0,0,2,0,o,r,1,1])))

/-- Actually wrong: a fresh zero array has equal contents but a different
identity. It cannot replace an alias capture even in this small fixture. -/
def wrongFresh : Prog C TgtCtx (.mem bytesR :: TgtCtx) :=
  .cons (.declMem bytesR (.user "wrong_fresh_capture")
    (some (.newArr (.lit 2 (by decide)) rfl)) rfl rfl) .nil

theorem wrong_run (old rhs : Bool) : wrongFresh.run (tgtPair old rhs) =
    .ok (⟨(tgtPair old rhs).allocPush (zerosObj (tgtPair old rhs).H 2 (by decide)),List.prefix_append _ _⟩) := by
  have step : (Stmt.declMem bytesR (.user "wrong_fresh_capture")
      (some (.newArr (.lit 2 (by decide)) rfl)) rfl rfl).run (tgtPair old rhs) =
      .ok (⟨(tgtPair old rhs).allocPush (zerosObj (tgtPair old rhs).H 2 (by decide)),List.prefix_append _ _⟩) :=
    TRun.declMem_newArr_bytes (tgtPair old rhs) 2 (by decide)
  unfold wrongFresh
  rw [Prog.run_cons_ok step,Prog.run_nil]
  rfl

def wrongObservation : Option (List Nat) :=
  match wrongFresh.run (tgtPair false true) with
  | .ok out => match out.st.env.1,TEnv.get (.there targetSlot) out.st.env with
    | some fresh,some old => some [fresh.id,old.id,out.st.heap.len fresh .dyn,out.st.heap.len old .dyn,
      out.st.H.length,out.st.env.2.1.toNat,out.st.env.2.2.1.toNat]
    | _,_ => none
  | _ => none
/-- info: some [1, 0, 2, 2, 2, 0, 1] -/
#guard_msgs in
#eval IO.println (reprStr wrongObservation)
/-- info: some [1, 0, 0, 1, 0, 0, 2, 0, 0, 1, 1, 1] -/
#guard_msgs in
#eval IO.println (reprStr (observe .viaIR false false true 1))

def wrongContents : Option (List (Option Int) × List (Option Int)) :=
  match wrongFresh.run (tgtPair false true) with
  | .ok out => match out.st.env.1,TEnv.get (.there targetSlot) out.st.env with
    | some fresh,some old => some
      ((MObj.elems .dyn (out.st.heap.get fresh)).map (fun v => PrimTy.num? (p := .uint) v),
       (MObj.elems .dyn (out.st.heap.get old)).map (fun v => PrimTy.num? (p := .uint) v))
    | _,_ => none
  | _ => none

theorem wrong_contents_equal : wrongContents = some ([some 0,some 0],[some 0,some 0]) := by
  unfold wrongContents
  rw [wrong_run]
  with_unfolding_all rfl

theorem wrong_fresh_identity : wrongObservation = some [1,0,2,2,2,0,1] := by
  unfold wrongObservation
  rw [wrong_run]
  with_unfolding_all rfl

/-- info: some ([some 0, some 0], [some 0, some 0]) -/
#guard_msgs in
#eval IO.println (reprStr wrongContents)

/-- info: 'Solidity.Lowering.V07.P12MemoryCaptureControls.binding' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Solidity.Lowering.V07.P12MemoryCaptureControls.binding

/-- info: 'Solidity.Lowering.V07.P12MemoryCaptureControls.memory_index' does not depend on any axioms -/
#guard_msgs in
#print axioms Solidity.Lowering.V07.P12MemoryCaptureControls.memory_index

/-- info: 'Solidity.Lowering.V07.P12MemoryCaptureControls.initial_alias' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms Solidity.Lowering.V07.P12MemoryCaptureControls.initial_alias

/-- info: 'Solidity.Lowering.V07.P12MemoryCaptureControls.source_success' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms Solidity.Lowering.V07.P12MemoryCaptureControls.source_success

/-- info: 'Solidity.Lowering.V07.P12MemoryCaptureControls.source_not_revert' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms Solidity.Lowering.V07.P12MemoryCaptureControls.source_not_revert

/-- info: 'Solidity.Lowering.V07.P12MemoryCaptureControls.exact_capture' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms Solidity.Lowering.V07.P12MemoryCaptureControls.exact_capture

/-- info: 'Solidity.Lowering.V07.P12MemoryCaptureControls.drop_capture' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Solidity.Lowering.V07.P12MemoryCaptureControls.drop_capture

/-- info: 'Solidity.Lowering.V07.P12MemoryCaptureControls.repeated_capture' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms Solidity.Lowering.V07.P12MemoryCaptureControls.repeated_capture

/-- info: 'Solidity.Lowering.V07.P12MemoryCaptureControls.wrong_run' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Solidity.Lowering.V07.P12MemoryCaptureControls.wrong_run

/-- info: 'Solidity.Lowering.V07.P12MemoryCaptureControls.wrong_contents_equal' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms Solidity.Lowering.V07.P12MemoryCaptureControls.wrong_contents_equal

/-- info: 'Solidity.Lowering.V07.P12MemoryCaptureControls.wrong_fresh_identity' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms Solidity.Lowering.V07.P12MemoryCaptureControls.wrong_fresh_identity

/-- info: 'Solidity.Lowering.V07.P12MemoryCaptureControls.producer' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Solidity.Lowering.V07.P12MemoryCaptureControls.producer

/-- info: 'Solidity.Lowering.V07.P12MemoryCaptureControls.success_client' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms Solidity.Lowering.V07.P12MemoryCaptureControls.success_client

/-- info: 'Solidity.Lowering.V07.P12MemoryCaptureControls.live_refs_client' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms Solidity.Lowering.V07.P12MemoryCaptureControls.live_refs_client

/-- info: 'Solidity.Lowering.V07.P12MemoryCaptureControls.alias_client' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Solidity.Lowering.V07.P12MemoryCaptureControls.alias_client

end Solidity.Lowering.V07.P12MemoryCaptureControls
