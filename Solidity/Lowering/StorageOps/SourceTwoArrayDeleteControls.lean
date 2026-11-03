import Solidity.Lowering.StorageOps.SourceTwoArrayDeletes
import Solidity.Source.Eval

/-! Inhabited captured operation clients. Raw retained/default observations are
separate from fresh Source index expressions and from physical storage garbage. -/
namespace Solidity.Backend.StorageOps.SourceTwoArrayDeleteControls
open SourceTwoArrayDeletes SourceArrayDeleteTarget SourceScalarDeleteLog

private def uintSyntax : Source.Syn .typeName := .elem (.int false 256 (by decide))
private def unit : Source.Syn .unit := .unit (.cons (.contract false "C" .none .nil
  (.cons (.stateVar (.array uintSyntax .none) none none none false "left" .none)
    (.cons (.stateVar (.array uintSyntax .none) none none none false "right" .none)
      (.cons (.stateVar (.elem .bool) none none none false "bad" .none)
        (.cons (.stateVar uintSyntax none none none true "scratch" .none)
          (.cons (.stateVar uintSyntax none none none false "sentinel" .none) .nil)))))) .nil)
private def env : Source.Env := unit.env
private def left : Source.SPath := ⟨⟨some "C","left"⟩,[]⟩
private def right : Source.SPath := ⟨⟨some "C","right"⟩,[]⟩
private def bad : Source.SPath := ⟨⟨some "C","bad"⟩,[]⟩
private def scratch : Source.SPath := ⟨⟨some "C","scratch"⟩,[]⟩
private def sentinel : Source.SPath := ⟨⟨some "C","sentinel"⟩,[]⟩
private def missing : Source.SPath := ⟨⟨some "C","missing"⟩,[]⟩
private def elem (p : Source.SPath) (i : Nat) : Source.SPath := p.go (.index i)
private def address : Roadmap.Address := ⟨7,by decide⟩
private def storage : Source.Storage env.layout env.cellTy :=
  let s := (Source.Storage.empty : Source.Storage env.layout env.cellTy).write left (.int 2 (by decide))
  let s := s.write (elem left 0) (.int 53 (by decide))
  let s := s.write (elem left 1) (.int 59 (by decide))
  let s := s.write (elem left 2) (.int 61 (by decide))
  let s := s.write right (.int 3 (by decide))
  let s := s.write (elem right 0) (.int 7 (by decide))
  let s := s.write (elem right 1) (.int 17 (by decide))
  let s := s.write (elem right 2) (.int 23 (by decide))
  let s := s.write (elem right 3) (.int 71 (by decide))
  let s := s.write bad (.bool true)
  s.write sentinel (.int 99 (by decide))
private def state : Source.St env :=
  { ex :=
      { world := ⟨fun a => if a = address then
          { balance := ⟨19,by decide⟩, nonce := 3, code := some 0, storage := storage }
          else Source.Account.empty _⟩
        transient := Source.Transient.empty.set address
          ((Source.Storage.empty : Source.Storage env.layout env.cellTy).write scratch (.int 5 (by decide)))
        journal := [] }
    heap := Source.Heap.empty
    events := []
    logs := []
    fnLocals := ⟨[],.nil⟩ }
private def frame : Source.Fr :=
  {this := address,sender := ⟨13,by decide⟩,value := ⟨0,by decide⟩,static := false,contract := "C"}
private def initial : Source.Locals env.layout [] × Source.St env := (.nil,state)
private def sourceOut := (program (E := env) (Γ := []) frame Source.IntTy.u256 Source.IntTy.u256 left right 2 3).run initial
private def first : Evm.Slot := .root 0
private def second : Evm.Slot := .root 1
private def liveAlias : Evm.Slot := .data first 0
private def retainedAlias : Evm.Slot := .data first 2
private def store : Evm.WordStore := .ofFn fun s =>
  if s = first then 2 else if s = .data first 0 then 53 else if s = .data first 1 then 59 else
  if s = .data first 2 then 61 else if s = .data first 4 then 93 else
  if s = second then 3 else if s = .data second 0 then 7 else if s = .data second 1 then 17 else
  if s = .data second 2 then 23 else if s = .data second 3 then 71 else if s = .data second 5 then 97 else
  if s = .root 8 then 1 else if s = .root 9 then 99 else if s = .root 77 then 87 else
  if s = .data liveAlias 0 then 77 else if s = .data retainedAlias 0 then 79 else 0
private def tail : List Evm.Word := [.val ⟨23,by decide⟩,.slot (.root 9)]
private def targetAddress : Fin Evm.W := Source.toWord address.val
private def target : Evm.Machine :=
  {stack := tail,store := store,mem := fun _ => .val ⟨31,by decide⟩,
   bal := fun a => if a = targetAddress then 19 else 0,
   bal₀ := fun a => if a = targetAddress then 19 else 0,
   self := targetAddress,caller := Source.toWord frame.sender.val,callvalue := frame.value,
   timestamp := ⟨53,by decide⟩,accepts := fun _ _ => false}
private def targetOut := TargetArrayDeleteSequence.after target tail first second
private def paths := [left,elem left 0,elem left 1,elem left 2,elem left 4,
  right,elem right 0,elem right 1,elem right 2,elem right 3,elem right 5,bad,sentinel,missing]
private def slots : List Evm.Slot := [first,.data first 0,.data first 1,.data first 2,.data first 4,
  second,.data second 0,.data second 1,.data second 2,.data second 3,.data second 5,
  .root 8,.root 9,.root 77,.data liveAlias 0,.data retainedAlias 0]
private def sourceView (s : Source.St env) := paths.map (wordAt frame s.ex)
private def targetView (s : Evm.Machine) := slots.map (fun q => s.store q)
private def sourceContext (s : Source.St env) :=
  ((s.ex.world.accounts frame.this).balance,(s.ex.world.accounts frame.this).nonce,
   (s.ex.world.accounts frame.this).code,((s.ex.transient.cells frame.this).read scratch).bind Source.Val.word,
   s.heap,s.events,s.logs,s.fnLocals)
private def targetContext (m : Evm.Machine) :=
  (m.stack,m.mem 3,m.bal m.self,m.bal₀ m.self,m.self,m.caller,m.callvalue,m.timestamp,m.accepts m.self m.self)

private theorem right_no_left (i : Nat) : right ≠ elem left i := by
  intro same
  have roots := congrArg Source.SPath.root same
  exact (by decide : right.root ≠ left.root) roots
private theorem left_index_no_right (i : Nat) : elem left i ≠ right := by
  intro same
  have roots := congrArg Source.SPath.root same
  exact (by decide : left.root ≠ right.root) roots
private theorem source_data_apart (i j : Nat) : elem left i ≠ elem right j := by
  intro same
  have roots := congrArg Source.SPath.root same
  exact (by decide : left.root ≠ right.root) roots
private theorem target_data_apart (i j : Nat) : Evm.Slot.data first i ≠ .data second j := by
  intro same
  exact (by decide : first ≠ second) (Evm.Slot.data.inj same).1

theorem executions : sourceOut.1 = .ok () ∧
    Evm.run (TargetArrayDeleteSequence.code second) {target with stack := .slot first :: tail} = .ok targetOut 0 := by
  have actual := source_run frame rfl Source.IntTy.u256 Source.IntTy.u256 left right 2 3 .nil state rfl rfl
    (by decide) (by intro i _; exact right_no_left i)
  exact ⟨congrArg Prod.fst actual,TargetArrayDeleteSequence.run_current target tail first second⟩

/-- Every recorded word, context observation and journal count is pinned. -/
theorem ordered_observations :
    (sourceView state,sourceView sourceOut.2.2,sourceOut.2.2.ex.journal.length,
      targetView target,targetView targetOut,sourceContext sourceOut.2.2,targetContext targetOut) =
    ([some 2,some 53,some 59,some 61,some 0,some 3,some 7,some 17,some 23,some 71,some 0,some 1,some 99,none],
     [some 0,some 0,some 0,some 61,some 0,some 0,some 0,some 0,some 0,some 71,some 0,some 1,some 99,none],7,
     [2,53,59,61,93,3,7,17,23,71,97,1,99,87,77,79],
     [0,0,0,61,93,0,0,0,0,71,97,1,99,87,77,79],sourceContext state,targetContext target) := by rfl

/-- Canonical Source defaults and unknown None are not arbitrary raw words. -/
theorem observation_boundaries :
    (wordAt frame sourceOut.2.2.ex (elem left 4),targetOut.store (.data first 4),
      wordAt frame sourceOut.2.2.ex (elem right 5),targetOut.store (.data second 5),
      wordAt frame sourceOut.2.2.ex missing,targetOut.store (.root 77)) =
      (some 0,93,some 0,97,none,87) := by rfl

/-- Real nonempty reordered/duplicate clients instantiate BOTH word laws. -/
theorem selected_correspondences :
    (∀ j ∈ [2,0,1,2], wordAt frame sourceOut.2.2.ex (elem left j) = some (targetOut.store (.data first j))) ∧
    (∀ j ∈ [3,1,0,2,3], wordAt frame sourceOut.2.2.ex (elem right j) = some (targetOut.store (.data second j))) := by
  constructor
  · intro j member
    exact first_correspondence frame rfl left right 2 3 j .nil state rfl rfl rfl rfl
      (by decide) (by intro i _; exact right_no_left i) (left_index_no_right j)
      (by intro k _; exact source_data_apart j k) target tail first second rfl
      (by decide) (by intro k _ same; cases same) (by intro same; cases same)
      (by intro k _; exact target_data_apart j k)
      (by intro unvisited
          simp only [List.mem_cons,List.not_mem_nil,or_false] at member
          rcases member with rfl | rfl | rfl | rfl
          · rfl
          · omega
          · omega
          · rfl)
  · intro j member
    exact second_correspondence frame rfl left right 2 3 j .nil state rfl rfl rfl rfl
      (by decide) (by intro i _; exact right_no_left i)
      (by intro _; constructor
          · intro same
            have roots := congrArg Source.SPath.root same
            exact (by decide : right.root ≠ left.root) roots
          · intro i _; exact Ne.symm (source_data_apart i j))
      target tail first second rfl (by decide) (by intro k _ same; cases same)
      (by intro _; constructor
          · intro same; cases same
          · intro k _; exact Ne.symm (target_data_apart k j))
      (by intro unvisited
          simp only [List.mem_cons,List.not_mem_nil,or_false] at member
          rcases member with rfl | rfl | rfl | rfl | rfl
          · rfl
          · omega
          · omega
          · omega
          · rfl)

theorem selected_headers :
    wordAt frame sourceOut.2.2.ex left = some (targetOut.store first) ∧
    wordAt frame sourceOut.2.2.ex right = some (targetOut.store second) := by
  have sourceHeaders := source_headers frame rfl left right 2 3 .nil state rfl rfl rfl rfl rfl rfl
    (by decide) (by intro i _; exact right_no_left i)
    (by intro i _ same
        have roots := congrArg Source.SPath.root same
        exact (by decide : left.root ≠ right.root) roots)
  have targetHeaders := TargetArrayDeleteSequence.headers_zero target tail first second
  unfold sourceOut initial targetOut
  rw [sourceHeaders.1,sourceHeaders.2,targetHeaders.1,targetHeaders.2]
  exact ⟨rfl,rfl⟩

private def sameSource := (program (E := env) (Γ := []) frame Source.IntTy.u256 Source.IntTy.u256 left left 2 2).run initial
private def sameTarget := TargetArrayDeleteSequence.after target tail first first

/-- Same captured array: the second actual header read is zero; Source still
journals one header clear. This is not full Source-state idempotence. -/
theorem same_slot_control :
    Evm.run (TargetArrayDeleteSequence.code first) {target with stack := .slot first :: tail} = .ok sameTarget 0 ∧
    (sameSource.1,sourceView sameSource.2.2,sameSource.2.2.ex.journal.length,targetView sameTarget,
      sourceContext sameSource.2.2,targetContext sameTarget) =
      (.ok (),[some 0,some 0,some 0,some 61,some 0,some 3,some 7,some 17,some 23,some 71,some 0,some 1,some 99,none],4,
       [0,0,0,61,93,3,7,17,23,71,97,1,99,87,77,79],sourceContext state,targetContext target) := by
  exact ⟨TargetArrayDeleteSequence.run_current target tail first first,rfl⟩

/-- An actual wrong captured SECOND operand leaves the required right array
unchanged, despite using the same genuine clearing loop twice. -/
theorem wrong_capture_control :
    Evm.run (TargetArrayDeleteSequence.code first) {target with stack := .slot first :: tail} = .ok sameTarget 0 ∧
    wordAt frame sourceOut.2.2.ex right ≠ some (sameTarget.store second) := by
  refine ⟨TargetArrayDeleteSequence.run_current target tail first first,?_⟩
  change some (0 : Nat) ≠ some 3
  decide

private def emptyInput := (Source.setCell (E := env) (Γ := []) frame left none).run initial
private def emptySource := (program (E := env) (Γ := []) frame Source.IntTy.u256 Source.IntTy.u256 left right 0 3).run emptyInput.2
private def emptyTarget : Evm.Machine := {target with store := Evm.WordStore.write target.store first 0}
private def emptyOut := TargetArrayDeleteSequence.after emptyTarget tail first second

/-- Deleting an empty retained array preserves every older shadow. -/
theorem empty_control :
    Evm.run (TargetArrayDeleteSequence.code second) {emptyTarget with stack := .slot first :: tail} = .ok emptyOut 0 ∧
    (emptySource.1,sourceView emptySource.2.2,emptySource.2.2.ex.journal.length,targetView emptyOut,
      sourceContext emptySource.2.2,targetContext emptyOut) =
      (.ok (),[some 0,some 53,some 59,some 61,some 0,some 0,some 0,some 0,some 0,some 71,some 0,some 1,some 99,none],6,
       [0,53,59,61,93,0,0,0,0,71,97,1,99,87,77,79],sourceContext state,targetContext target) := by
  exact ⟨TargetArrayDeleteSequence.run_current emptyTarget tail first second,rfl⟩

private def failedSource := (program (E := env) (Γ := []) frame Source.IntTy.u256 Source.IntTy.u256 left right 2 0).run initial

/-- Insufficient SECOND fuel preserves all first-operation writes; no automatic
world rollback follows from the Source halt. -/
theorem second_failure_control :
    (failedSource.1,sourceView failedSource.2.2,failedSource.2.2.ex.journal.length,sourceContext failedSource.2.2) =
      (.error .timeout,[some 0,some 0,some 0,some 61,some 0,some 3,some 7,some 17,some 23,some 71,some 0,some 1,some 99,none],3,sourceContext state) ∧
    failedSource.2.2 ≠ state := by
  refine ⟨rfl,?_⟩
  intro same
  have journals := congrArg (fun s : Source.St env => s.ex.journal.length) same
  change 3 = 0 at journals
  omega

/-- Explicit public outer-frame rollback restores that actual failed sequence. -/
theorem explicit_failed_restore :
    (failedSource.2.1,{failedSource.2.2 with ex :=
      (state.ex.enter frame.this frame.sender frame.value [] frame.static).rollback failedSource.2.2.ex}) = initial := by
  change (Source.Locals.nil,{state with ex := (state.ex.enter frame.this frame.sender frame.value [] frame.static).rollback (state.ex.run [clearOp env frame (elem left 0),clearOp env frame (elem left 1),clearOp env frame left])}) = initial
  rw [Source.rollback_run]
  rfl

private def liveAliasOut := TargetArrayDeleteSequence.after target tail first liveAlias
private def retainedAliasOut := TargetArrayDeleteSequence.after target tail first retainedAlias

/-- TARGET-ONLY symbolic aliases, with no Source array-typing claim. A live
second header is cleared by the first loop, so the second loop reads zero. -/
theorem live_alias_control :
    Evm.run (TargetArrayDeleteSequence.code liveAlias) {target with stack := .slot first :: tail} = .ok liveAliasOut 0 ∧
    (target.store liveAlias,(TargetArrayClear.afterClear target tail first).store liveAlias,
      targetView liveAliasOut,targetContext liveAliasOut) =
      (53,0,[0,0,0,61,93,3,7,17,23,71,97,1,99,87,77,79],targetContext target) := by
  exact ⟨TargetArrayDeleteSequence.run_current target tail first liveAlias,rfl⟩

/-- The retained observer IS the second header. Dropping its header-exclusion
premise would wrongly preserve61; its nested raw79 is also genuinely cleared. -/
theorem retained_alias_control :
    Evm.run (TargetArrayDeleteSequence.code retainedAlias) {target with stack := .slot first :: tail} = .ok retainedAliasOut 0 ∧
    (target.store retainedAlias,(TargetArrayClear.afterClear target tail first).store retainedAlias,
      targetView retainedAliasOut,targetContext retainedAliasOut) =
      (61,61,[0,0,0,0,93,3,7,17,23,71,97,1,99,87,77,0],targetContext target) ∧
    retainedAliasOut.store (.data first 2) ≠ target.store (.data first 2) := by
  refine ⟨TargetArrayDeleteSequence.run_current target tail first retainedAlias,rfl,?_⟩
  change (0 : Nat) ≠ 61
  decide

private def wrongOldCode : List Evm.Instr := TargetArrayClear.code ++
  ([.push (.val ⟨53,by decide⟩),.push (.slot liveAlias),.sstore,.push (.slot liveAlias)] ++ TargetArrayClear.code)
private def reset : Evm.Machine :=
  {TargetArrayClear.afterClear target tail first with store := Evm.WordStore.write (TargetArrayClear.afterClear target tail first).store liveAlias 53}
private def wrongOldOut := TargetArrayClear.afterClear reset tail liveAlias

/-- A REAL wrong program reinstates the OLD second header before its loop.
It destroys nested77 that the correct evolving-header program preserves. -/
theorem wrong_old_header_control :
    Evm.run wrongOldCode {target with stack := .slot first :: tail} = .ok wrongOldOut 0 ∧
    (targetView wrongOldOut,targetContext wrongOldOut) =
      ([0,0,0,61,93,3,7,17,23,71,97,1,99,87,0,79],targetContext target) ∧
    liveAliasOut.store (.data liveAlias 0) ≠ wrongOldOut.store (.data liveAlias 0) := by
  have resetRun : Evm.run [.push (.val ⟨53,by decide⟩),.push (.slot liveAlias),.sstore,.push (.slot liveAlias)]
      (TargetArrayClear.afterClear target tail first) = .ok {reset with stack := .slot liveAlias :: tail} 0 := by rfl
  refine ⟨?_,rfl,?_⟩
  · unfold wrongOldCode
    rw [Evm.run_append_ok (TargetArrayClear.run_current target tail first),Evm.run_append_ok resetRun]
    exact TargetArrayClear.run_current reset tail liveAlias
  · change (77 : Nat) ≠ 0
    decide

private def arrayRef : Source.Val env.layout (.array .storage (.int Source.IntTy.u256) none) := .storRef rfl left
private def capturedAlias : Source.Loc env.layout [] (.int Source.IntTy.u256) := .stor (elem left 2)
private def grownInput := (Source.writeLen (E := env) (Γ := []) frame left 3).run initial
private def captured := (Source.indexLoc (E := env) (Γ := []) frame arrayRef 2).run grownInput.2
private def shrunk := (Source.writeLen (E := env) (Γ := []) frame left 2).run captured.2
private def aliasSource := (program (E := env) (Γ := []) frame Source.IntTy.u256 Source.IntTy.u256 left right 2 3).run shrunk.2
private def capturedRead := (Source.readLoc (E := env) (Γ := []) frame capturedAlias).run aliasSource.2
private def freshAfter := (Source.indexLoc (E := env) (Γ := []) frame arrayRef 2).run aliasSource.2
private def regrown := (Source.writeLen (E := env) (Γ := []) frame left 3).run aliasSource.2
private def freshRegrown := (Source.indexLoc (E := env) (Γ := []) frame arrayRef 2).run regrown.2

/-- Actual Source index capture when live, then header shrink, two deletions,
retained alias read, fresh-index refusal, and header regrowth. writeLen is ONLY
header writing: no push/allocation/default/identity-generation claim follows. -/
theorem captured_alias_control :
    captured = (.ok capturedAlias,grownInput.2) ∧
    capturedRead = (.ok (.int 61 (by decide)),aliasSource.2) ∧
    freshAfter = (.error (.revert (Source.panicData .index)),aliasSource.2) ∧
    freshRegrown = (.ok capturedAlias,regrown.2) ∧
    (sourceView shrunk.2.2,sourceView aliasSource.2.2,sourceView regrown.2.2,
      shrunk.2.2.ex.journal.length,aliasSource.2.2.ex.journal.length,regrown.2.2.ex.journal.length,
      sourceContext aliasSource.2.2,sourceContext regrown.2.2) =
      ([some 2,some 53,some 59,some 61,some 0,some 3,some 7,some 17,some 23,some 71,some 0,some 1,some 99,none],
       [some 0,some 0,some 0,some 61,some 0,some 0,some 0,some 0,some 0,some 71,some 0,some 1,some 99,none],
       [some 3,some 0,some 0,some 61,some 0,some 0,some 0,some 0,some 0,some 71,some 0,some 1,some 99,none],2,9,10,
       sourceContext state,sourceContext state) := by
  exact ⟨rfl,rfl,rfl,rfl,rfl⟩

/-- Pin actual panic bytes, not just an arbitrary refusal label. -/
theorem index_panic_bytes :
    Source.panicData .index = ([0x4e,0x48,0x7b,0x71] ++ List.replicate 31 0 ++ [0x32]) := by rfl

/-- Instantiate the GENERIC all-index Source law after the real shrink prefix. -/
theorem generic_index_control (j : Nat) :
    (Source.indexLoc (E := env) (Γ := []) frame arrayRef j).run aliasSource.2 =
      (.error (.revert (Source.panicData .index)),aliasSource.2) := by
  exact source_index_refusal frame rfl left right 2 3 j shrunk.2.1 shrunk.2.2 rfl rfl rfl rfl rfl rfl
    (by decide) (by intro i _; exact right_no_left i)
    (by intro i _ same
        have roots := congrArg Source.SPath.root same
        exact (by decide : left.root ≠ right.root) roots)

/-- Actual captured SLOAD succeeds while fresh indexed target code reverts.
Source pins the exact panic bytes; Evm.Out.revert alone has no byte-data/world
rollback relation, and this theorem does not manufacture one. -/
theorem alias_source_target_reads :
    capturedRead.1 = .ok (.int 61 (by decide)) ∧
    freshAfter.1 = .error (.revert (Source.panicData .index)) ∧
    Evm.run [.sload] {targetOut with stack := .slot (.data first 2) :: tail} =
      .ok {targetOut with stack := .val ⟨61,by decide⟩ :: tail} 0 ∧
    Evm.run TargetArrayRead.code {targetOut with stack := .val ⟨2,by decide⟩ :: .slot first :: tail} = .revert := by
  exact ⟨rfl,rfl,rfl,TargetArrayDeleteSequence.fresh_read_reverts target tail first second 2 (by decide)⟩

/-- info: 'Solidity.Backend.StorageOps.SourceTwoArrayDeleteControls.executions' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in #print axioms executions

/-- info: 'Solidity.Backend.StorageOps.SourceTwoArrayDeleteControls.ordered_observations' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in #print axioms ordered_observations

/-- info: 'Solidity.Backend.StorageOps.SourceTwoArrayDeleteControls.observation_boundaries' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in #print axioms observation_boundaries

/-- info: 'Solidity.Backend.StorageOps.SourceTwoArrayDeleteControls.selected_correspondences' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in #print axioms selected_correspondences

/-- info: 'Solidity.Backend.StorageOps.SourceTwoArrayDeleteControls.selected_headers' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in #print axioms selected_headers

/-- info: 'Solidity.Backend.StorageOps.SourceTwoArrayDeleteControls.same_slot_control' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in #print axioms same_slot_control

/-- info: 'Solidity.Backend.StorageOps.SourceTwoArrayDeleteControls.wrong_capture_control' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in #print axioms wrong_capture_control

/-- info: 'Solidity.Backend.StorageOps.SourceTwoArrayDeleteControls.empty_control' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in #print axioms empty_control

/-- info: 'Solidity.Backend.StorageOps.SourceTwoArrayDeleteControls.second_failure_control' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in #print axioms second_failure_control

/-- info: 'Solidity.Backend.StorageOps.SourceTwoArrayDeleteControls.explicit_failed_restore' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in #print axioms explicit_failed_restore

/-- info: 'Solidity.Backend.StorageOps.SourceTwoArrayDeleteControls.live_alias_control' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in #print axioms live_alias_control

/-- info: 'Solidity.Backend.StorageOps.SourceTwoArrayDeleteControls.retained_alias_control' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in #print axioms retained_alias_control

/-- info: 'Solidity.Backend.StorageOps.SourceTwoArrayDeleteControls.wrong_old_header_control' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in #print axioms wrong_old_header_control

/-- info: 'Solidity.Backend.StorageOps.SourceTwoArrayDeleteControls.captured_alias_control' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in #print axioms captured_alias_control

/-- info: 'Solidity.Backend.StorageOps.SourceTwoArrayDeleteControls.index_panic_bytes' does not depend on any axioms -/
#guard_msgs in #print axioms index_panic_bytes

/-- info: 'Solidity.Backend.StorageOps.SourceTwoArrayDeleteControls.generic_index_control' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in #print axioms generic_index_control

/-- info: 'Solidity.Backend.StorageOps.SourceTwoArrayDeleteControls.alias_source_target_reads' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in #print axioms alias_source_target_reads

end Solidity.Backend.StorageOps.SourceTwoArrayDeleteControls
