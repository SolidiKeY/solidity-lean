import Solidity.Backend.InternalFlow.EvaluatedRevert
import Solidity.Backend.InternalFlow.MixedLoopPrefixes

/-! Inhabited actual typed payload evaluation and nested/scoped calls wired to
checked emission. Explicit slice machines remain representation hooks, not
intrinsic heaps or a reconstruction of a failed State. -/
namespace Solidity.Backend.InternalFlow.EvaluatedRevertChecks
open Backend.Failure
open Controls (contract arrayType persistent transient)
open AllocationFrameChecks (CallerCtx contents)

def prepared : State contract CallerCtx := MixedLoopPrefixes.first.st

def args : Args contract CallerCtx CallerCtx :=
  .snocMemory (.snocMemory
    (.snoc (.snoc .nil .uint (.user "other") (.simple (.local (.there (.there (.there .here))))))
      .uint (.user "counter") (.simple (.local (.there (.there .here)))))
    arrayType (.user "aliasB") (.var (.there .here) rfl))
    arrayType (.user "aliasA") (.var .here rfl)

@[irreducible] def arguments : TEnv contract prepared.H CallerCtx :=
  match args.evalT prepared with
  | .ok env => env
  | .error _ => (none, none, PrimTy.dflt .uint, PrimTy.dflt .uint, ())

def entered : State contract CallerCtx := ((CallRet.none (Γ := CallerCtx)).enterT (prepared.withEnv arguments)).st

def parts : List (RevPart contract CallerCtx) :=
  [.bytes [0xde,0], .word (.simple (.local (.there (.there .here)))), .mem .raw .here,
    .bytes [], .word (.simple (.local (.there (.there (.there .here))))),
    .word (.read (.root "p" rfl)), .word (.read (.root "t" rfl)), .mem .raw (.there .here)]
def chunks : List (List UInt8) :=
  [[0xde,0], Semantics.wordBytes 10, [7,11], [], Semantics.wordBytes 17,
    Semantics.wordBytes 8, Semantics.wordBytes 11, [7,11]]
def bytes : List UInt8 := chunks.flatten

private def resultEq {α : Type} [DecidableEq α] : DecidableEq (TRes α)
  | .ok a, .ok b => if h : a = b then isTrue (h ▸ rfl) else isFalse (fun e => h (Except.ok.inj e))
  | .error a, .error b => if h : a = b then isTrue (h ▸ rfl) else isFalse (fun e => h (Except.error.inj e))
  | .ok _, .error _ => isFalse (by intro h; cases h)
  | .error _, .ok _ => isFalse (by intro h; cases h)

theorem arguments_execute : args.evalT prepared = .ok arguments := by
  have success : (match args.evalT prepared with | .ok _ => true | .error _ => false) = true := by decide +kernel
  cases h : args.evalT prepared with
  | ok env => simp only [arguments, h]
  | error halt => rw [h] at success; cases success

theorem arguments_observed : (args.evalT prepared).map (fun env =>
    (env.1.map HRef.id, env.2.1.map HRef.id, env.2.2.1.1, env.2.2.2.1.1)) =
      .ok (some 0, some 0, 10, 17) := by
  apply @of_decide_eq_true _ (resultEq _ _)
  decide +kernel

theorem parts_evaluate : parts.mapM (·.evalT entered) = .ok chunks := by
  apply @of_decide_eq_true _ (resultEq _ _)
  decide +kernel

theorem chunks_complete : chunks.map List.length = [2,32,2,0,32,32,32,2] ∧ bytes.length = 134 ∧
    [bytes[0]!, bytes[1]!, bytes[33]!, bytes[34]!, bytes[35]!, bytes[67]!, bytes[99]!, bytes[131]!, bytes[132]!, bytes[133]!] =
      [0xde,0,10,7,11,17,8,11,7,11] := by decide +kernel

/-- Actual prefix statement, including storage shrink/allocation/local unwind. -/
theorem successful_prefix : (Stmt.block MixedLoopPrefixes.body).runR MixedLoopPrefixes.initial =
    .ok MixedLoopPrefixes.first := by
  change (MixedLoopPrefixes.body.runR MixedLoopPrefixes.initial).map _ = _
  rw [MixedLoopPrefixes.first_execution]
  rfl

theorem ordered_prefix_observations :
    [MixedLoopPrefixes.observe MixedLoopPrefixes.start, MixedLoopPrefixes.observe MixedLoopPrefixes.first] =
      [MixedLoopPrefixes.zeroObservation, MixedLoopPrefixes.oneObservation] := by
  rw [MixedLoopPrefixes.every_state_observed.1, MixedLoopPrefixes.every_state_observed.2.1]

theorem entered_observations :
    (contents entered .here, contents entered (.there .here), entered.env.2.2.1.1, entered.env.2.2.2.1.1,
      (entered.storage.get persistent.declared).view.1, (entered.storage.get transient.declared).view.1) =
      (some [7,11], some [7,11], 10,17,8,11) := by decide +kernel

abbrev Scoped : Ctx := .val .uint :: CallerCtx
def innerArgs : Args contract Scoped CallerCtx :=
  .snocMemory (.snocMemory
    (.snoc (.snoc .nil .uint (.user "other") (.simple (.local (.there (.there (.there (.there .here)))))))
      .uint (.user "counter") (.simple (.local (.there (.there (.there .here))))))
    arrayType (.user "aliasB") (.var (.there (.there .here)) rfl))
    arrayType (.user "aliasA") (.var (.there .here) rfl)
def innerBody : Prog contract CallerCtx CallerCtx := .cons (.revertData parts) .nil
def outerBody : Prog contract CallerCtx CallerCtx :=
  .cons (.block (.cons (.declLocal .uint (.user "scoped55") (some (.simple (.lit 55 rfl))))
    (.cons (.call "inner" innerArgs .none innerBody) .nil))) .nil
def program : Prog contract CallerCtx CallerCtx :=
  .cons (.block MixedLoopPrefixes.body) (.cons (.call "outer" args .none outerBody) .nil)

theorem nested_failure : program.runR MixedLoopPrefixes.initial = .error (THalt.ofData bytes) := by
  have certificate : (match program.runR MixedLoopPrefixes.initial with
    | .error halt => decide (halt = THalt.ofData bytes) | .ok _ => false) = true := by decide +kernel
  cases h : program.runR MixedLoopPrefixes.initial with
  | ok out => rw [h] at certificate; cases certificate
  | error halt =>
    rw [h] at certificate
    have hh : halt = THalt.ofData bytes := of_decide_eq_true certificate
    rw [hh]

theorem original_halt_class : program.runR MixedLoopPrefixes.initial = .error (.revertWith bytes) := by
  rw [nested_failure]
  rfl

def offset : Nat := 31
def suffix : Program := [.op .ADD]
def machine : Slice.Machine :=
  ⟨[Slice.pushed [0x41], Slice.pushed [0x52], Slice.pushed [0x63]],
    fun x => if x = 30 then 0x95 else if x = 165 then 0x96 else 0x73⟩
def callerMachine : Slice.Machine := ⟨[Slice.pushed [0x10], Slice.pushed [0x11]], fun _ => 0x11⟩
def emitted : Slice.Machine := { machine with memory := Slice.putBytes machine.memory offset bytes }

theorem fits : Fits offset bytes := by unfold Fits; decide +kernel

theorem headroom : machine.stack.length + 2 ≤ 1024 := by decide +kernel

/-- Actual nested runtime result selects the checked emitted payload. -/
theorem checked_execution : checkedRuntimeRevert (program.runR MixedLoopPrefixes.initial) offset suffix machine =
    some (emitted, some (.revert bytes)) :=
  checked_runtime_revert _ bytes nested_failure offset suffix machine fits headroom

/-- The generic dependent call/parts consumer has both premises discharged. -/
theorem checked_direct_call :
    checkedRuntimeRevert (TRun.call args CallRet.none .refl (TRun.revertData parts) prepared) offset suffix machine =
      some (emitted, some (.revert bytes)) :=
  checked_call_evaluated_revert prepared args .none arguments arguments_execute parts chunks parts_evaluate
    offset suffix machine fits headroom

theorem full_emitted_bytes : Slice.getBytes emitted.memory offset bytes.length = bytes :=
  Slice.getBytes_putBytes machine.memory offset bytes

theorem protected_stack : emitted.stack = machine.stack := rfl

theorem outside_interval (x : Nat) (hx : x < offset ∨ offset + bytes.length ≤ x) :
    emitted.memory x = machine.memory x := Slice.putBytes_frame machine.memory offset x bytes hx

theorem interval_boundary : (emitted.memory 30, emitted.memory 31, emitted.memory 32,
    emitted.memory 164, emitted.memory 165) = (0x95,0xde,0,11,0x96) := by decide +kernel

theorem complete_checked_observation :
    (checkedRuntimeRevert (program.runR MixedLoopPrefixes.initial) offset suffix machine).map
      (fun result => (result.1.stack, Slice.getBytes result.1.memory offset bytes.length,
        result.2, result.1.memory 30, result.1.memory 165)) =
      some (machine.stack, bytes, some (.revert bytes), 0x95,0x96) := by
  rw [checked_execution]
  change some (emitted.stack, Slice.getBytes emitted.memory offset bytes.length,
    some (Roadmap.Outcome.revert bytes), emitted.memory 30, emitted.memory 165) = _
  rw [full_emitted_bytes, outside_interval 30 (by left; decide), outside_interval 165 (by right; decide +kernel)]
  rfl

def saved : Local.Journal (SVal (.prim .uint)) (SVal (.prim .uint)) := rootJournal persistent transient MixedLoopPrefixes.initial.storage callerMachine
def live : Local.Journal (SVal (.prim .uint)) (SVal (.prim .uint)) := rootJournal persistent transient prepared.storage machine
def checkpoint : Local.Checkpoint (SVal (.prim .uint)) (SVal (.prim .uint)) := Local.save saved

theorem roots_populated : (saved.persistent.view.1, saved.transient.view.1,
    live.persistent.view.1, live.transient.view.1) = (7,9,8,11) := by decide +kernel

/-- This restores explicit projections, not a lost whole-State execution. -/
theorem local_execution : localRuntimeRevert (program.runR MixedLoopPrefixes.initial) checkpoint offset live =
    some (saved, .revert bytes) :=
  local_runtime_revert _ bytes nested_failure checkpoint offset live fits headroom

theorem local_parts_execution : localRuntimeRevert (TRun.revertData parts entered) checkpoint offset
    (rootJournal persistent transient entered.storage machine) = some (saved, .revert bytes) :=
  local_evaluated_revert persistent transient entered parts chunks parts_evaluate
    MixedLoopPrefixes.initial.storage callerMachine machine offset fits headroom

theorem immutable_bytes_after_restore :
    (localRuntimeRevert (program.runR MixedLoopPrefixes.initial) checkpoint offset live).map
      (fun result => (result.1.persistent.view.1, result.1.transient.view.1,
        result.1.machine.stack, result.1.machine.memory 31, result.2)) =
      some (7,9,callerMachine.stack,0x11,.revert bytes) := by
  rw [local_execution]
  rfl

/-- RETURN of these same evaluated bytes is a distinct component control,
not a claim about intrinsic ABI return lowering. -/
theorem component_return : Local.execute checkpoint offset (.returned bytes) live =
    some ({ live with machine := emitted }, .success bytes) :=
  Local.execute_return checkpoint offset bytes live fits headroom

def emptyParts : List (RevPart contract CallerCtx) := [.bytes [], .bytes []]

theorem empty_parts_evaluate : emptyParts.mapM (·.evalT entered) = .ok [[],[]] := rfl

theorem empty_actual_halt : TRun.revertData emptyParts entered = .error .revert := rfl

theorem empty_checked : checkedRuntimeRevert (TRun.revertData emptyParts entered) offset suffix machine =
    some (machine, some (.revert [])) := by
  exact checked_evaluated_revert entered emptyParts [[],[]] empty_parts_evaluate offset suffix machine
    (by unfold Fits; decide +kernel) headroom

theorem wrong_order :
    (checkedRuntimeRevert (program.runR MixedLoopPrefixes.initial) offset suffix machine).map Prod.snd ≠
      some (some (.revert chunks.reverse.flatten)) := by
  rw [checked_execution]
  intro h
  have eqBytes : bytes = chunks.reverse.flatten :=
    Roadmap.Outcome.revert.inj (Option.some.inj (Option.some.inj h))
  have bad : (0xde : UInt8) = 7 := congrArg (fun bs => bs[0]!) eqBytes
  exact (by decide +kernel : (0xde : UInt8) ≠ 7) bad

theorem wrong_length :
    (checkedRuntimeRevert (program.runR MixedLoopPrefixes.initial) offset suffix machine).map
      (fun result => match result.2 with | some (.revert bs) => bs.length | _ => 0) ≠ some 133 := by
  rw [checked_execution]
  intro h
  have bad : bytes.length = 133 := Option.some.inj h
  have actual : bytes.length = 134 := chunks_complete.2.1
  omega

theorem wrong_offset :
    (checkedRuntimeRevert (program.runR MixedLoopPrefixes.initial) (offset + 1) suffix machine).map
      (fun result => result.1.memory offset) ≠ some 0xde := by
  have shifted : checkedRuntimeRevert (program.runR MixedLoopPrefixes.initial) (offset + 1) suffix machine =
      some ({ machine with memory := Slice.putBytes machine.memory (offset + 1) bytes }, some (.revert bytes)) :=
    checked_runtime_revert _ bytes nested_failure (offset + 1) suffix machine
      (by unfold Fits; decide +kernel) headroom
  rw [shifted]
  simp only [Option.map_some]
  rw [Slice.putBytes_frame machine.memory (offset + 1) offset bytes (Or.inl (by omega))]
  intro h
  have bad : (0x73 : UInt8) = 0xde := Option.some.inj h
  exact (by decide +kernel : (0x73 : UInt8) ≠ 0xde) bad

def resetPayload : List UInt8 :=
  ([[0xde,0], Semantics.wordBytes 10, [7,11], [], Semantics.wordBytes 17,
    Semantics.wordBytes 8, Semantics.wordBytes 0, [7,11]] : List (List UInt8)).flatten

theorem wrong_payload :
    (checkedRuntimeRevert (program.runR MixedLoopPrefixes.initial) offset suffix machine).map Prod.snd ≠
      some (some (.revert resetPayload)) := by
  rw [checked_execution]
  intro h
  have eqBytes : bytes = resetPayload :=
    Roadmap.Outcome.revert.inj (Option.some.inj (Option.some.inj h))
  have actual : bytes[131]! = (11 : UInt8) := by decide +kernel
  have wrong : resetPayload[131]! = (0 : UInt8) := by decide +kernel
  have bad : (11 : UInt8) = 0 := actual.symm.trans ((congrArg (fun bs => bs[131]!) eqBytes).trans wrong)
  exact (by decide +kernel : (11 : UInt8) ≠ 0) bad

theorem wrong_class :
    (checkedRuntimeRevert (program.runR MixedLoopPrefixes.initial) offset suffix machine).map Prod.snd ≠
      some (some (.success bytes)) := by
  rw [checked_execution]
  intro h
  cases h

theorem early_reset :
    (localRuntimeRevert (program.runR MixedLoopPrefixes.initial) checkpoint offset live).map
      (fun result => result.1.transient.view.1) ≠ some 0 := by
  rw [local_execution]
  intro h
  have actual : saved.transient.view.1 = (9 : Int) := by decide +kernel
  have bad : (9 : Int) = 0 := actual.symm.trans (Option.some.inj h)
  cases bad

/-- Empty data does not identify the original class. No panic code is chosen. -/
theorem empty_data_is_lossy : THalt.revert.data = [] ∧ THalt.panic.data = [] ∧
    THalt.exhausted.data = [] ∧ THalt.diverge.data = [] := ⟨rfl,rfl,rfl,rfl⟩

theorem actual_assert_panic : TRun.assert (.simple (.bool false)) entered = .error .panic := rfl

theorem assert_not_reinterpreted : checkedRuntimeRevert
    (TRun.assert (.simple (.bool false)) entered) offset suffix machine = none := rfl

theorem actual_exhaustion_refused : checkedRuntimeRevert
    ((Prog.recBase : Prog contract CallerCtx CallerCtx).runR entered) offset suffix machine = none := rfl

def badValue : Val contract CallerCtx .uint :=
  .binop .div rfl rfl (.simple (.lit 1 rfl)) (.simple (.lit 0 rfl))
def goodValue : Val contract CallerCtx .uint :=
  .binop .div rfl rfl (.simple (.local (.there (.there .here)))) (.simple (.lit 2 rfl))
def badParts : List (RevPart contract CallerCtx) := [.bytes [0xde,0xad], .word badValue, .bytes [0xef]]

theorem division_positive : (RevPart.word goodValue).evalT entered = .ok (Semantics.wordBytes 5) := by
  apply @of_decide_eq_true _ (resultEq _ _)
  decide +kernel

/-- Existing intrinsic arithmetic failure is bare revert, not an invented
panic code; preceding partial payload chunks are discarded by mapM. -/
theorem evaluation_failure : badParts.mapM (·.evalT entered) = .error .revert ∧
    TRun.revertData badParts entered = .error .revert := ⟨rfl,rfl⟩

theorem no_partial_payload : checkedRuntimeRevert (TRun.revertData badParts entered) offset suffix machine =
    some (machine, some (.revert [])) :=
  checked_runtime_revert _ [] evaluation_failure.2 offset suffix machine
    (by unfold Fits; decide +kernel) headroom

def capacityMachine : Slice.Machine := { machine with stack := List.replicate 1022 (Slice.pushed [7]) }
def overCapacityMachine : Slice.Machine := { machine with stack := List.replicate 1023 (Slice.pushed [7]) }

theorem capacity_baseline : checkedRuntimeRevert (TRun.revertData emptyParts entered) offset [] capacityMachine =
    some (capacityMachine, some (.revert [])) :=
  checked_evaluated_revert entered emptyParts [[],[]] empty_parts_evaluate offset [] capacityMachine
    (by unfold Fits; decide +kernel) (by simp only [capacityMachine, List.length_replicate]; omega)

theorem over_capacity_reason : overCapacityMachine.stack.length = 1023 ∧
    overCapacityMachine.stack.length ≤ 1024 ∧ ¬ overCapacityMachine.stack.length + 2 ≤ 1024 := by
  simp only [overCapacityMachine, List.length_replicate]
  decide

theorem over_capacity_rejected : checkedRuntimeRevert (TRun.revertData emptyParts entered) offset [] overCapacityMachine = none := by
  have notSafe : Slice.stackSafe (emit offset .empty) overCapacityMachine ≠ true := by
    intro safe
    have impossible : overCapacityMachine.stack.length + 2 ≤ 1024 :=
      (empty_stack_boundary offset (by decide) overCapacityMachine).mp safe
    exact over_capacity_reason.2.2 impossible
  have guardFalse : Slice.stackSafe (emit offset .empty) overCapacityMachine = false := by
    cases h : Slice.stackSafe (emit offset .empty) overCapacityMachine with
    | false => rfl
    | true => exact False.elim (notSafe h)
  have emptyCode : emit offset (.custom []) = emit offset .empty := rfl
  rw [empty_actual_halt]
  simp only [checkedRuntimeRevert, canonicalRevertInput, Option.bind_some, List.append_nil,
    emptyCode, Slice.checkedRun, guardFalse, Bool.false_eq_true, if_false]

/-- The scoped temporary is distinct from both transported scalar arguments. -/
def scopedState : State contract Scoped := entered.push (t := .val .uint) ⟨55, rfl⟩

theorem scoped_arguments_observed : (innerArgs.evalT scopedState).map (fun env =>
    (env.1.map HRef.id, env.2.1.map HRef.id, env.2.2.1.1, env.2.2.2.1.1)) =
      .ok (some 0, some 0, 10,17) ∧ scopedState.env.1.1 = 55 := by
  constructor
  · apply @of_decide_eq_true _ (resultEq _ _)
    decide +kernel
  · rfl

theorem successful_runtime_refused : checkedRuntimeRevert
    ((Prog.nil : Prog contract CallerCtx CallerCtx).runR entered) offset suffix machine = none := rfl

theorem actual_require_checked : checkedRuntimeRevert
    (TRun.require (.simple (.bool false)) entered) offset suffix machine =
      some (machine, some (.revert [])) :=
  checked_runtime_revert _ [] (by rfl) offset suffix machine (by unfold Fits; decide +kernel) headroom

/-- info: 'Solidity.Backend.InternalFlow.EvaluatedRevertChecks.arguments_execute' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms arguments_execute
/-- info: 'Solidity.Backend.InternalFlow.EvaluatedRevertChecks.arguments_observed' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms arguments_observed
/-- info: 'Solidity.Backend.InternalFlow.EvaluatedRevertChecks.parts_evaluate' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms parts_evaluate
/-- info: 'Solidity.Backend.InternalFlow.EvaluatedRevertChecks.chunks_complete' does not depend on any axioms -/
#guard_msgs in
#print axioms chunks_complete
/-- info: 'Solidity.Backend.InternalFlow.EvaluatedRevertChecks.successful_prefix' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms successful_prefix
/-- info: 'Solidity.Backend.InternalFlow.EvaluatedRevertChecks.ordered_prefix_observations' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms ordered_prefix_observations
/-- info: 'Solidity.Backend.InternalFlow.EvaluatedRevertChecks.entered_observations' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms entered_observations
/-- info: 'Solidity.Backend.InternalFlow.EvaluatedRevertChecks.nested_failure' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms nested_failure
/-- info: 'Solidity.Backend.InternalFlow.EvaluatedRevertChecks.original_halt_class' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms original_halt_class
/-- info: 'Solidity.Backend.InternalFlow.EvaluatedRevertChecks.fits' does not depend on any axioms -/
#guard_msgs in
#print axioms fits
/-- info: 'Solidity.Backend.InternalFlow.EvaluatedRevertChecks.headroom' does not depend on any axioms -/
#guard_msgs in
#print axioms headroom
/-- info: 'Solidity.Backend.InternalFlow.EvaluatedRevertChecks.checked_execution' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms checked_execution
/-- info: 'Solidity.Backend.InternalFlow.EvaluatedRevertChecks.checked_direct_call' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms checked_direct_call
/-- info: 'Solidity.Backend.InternalFlow.EvaluatedRevertChecks.full_emitted_bytes' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms full_emitted_bytes
/-- info: 'Solidity.Backend.InternalFlow.EvaluatedRevertChecks.protected_stack' does not depend on any axioms -/
#guard_msgs in
#print axioms protected_stack
/-- info: 'Solidity.Backend.InternalFlow.EvaluatedRevertChecks.outside_interval' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms outside_interval
/-- info: 'Solidity.Backend.InternalFlow.EvaluatedRevertChecks.interval_boundary' does not depend on any axioms -/
#guard_msgs in
#print axioms interval_boundary
/-- info: 'Solidity.Backend.InternalFlow.EvaluatedRevertChecks.complete_checked_observation' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms complete_checked_observation
/-- info: 'Solidity.Backend.InternalFlow.EvaluatedRevertChecks.roots_populated' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms roots_populated
/-- info: 'Solidity.Backend.InternalFlow.EvaluatedRevertChecks.local_execution' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms local_execution
/-- info: 'Solidity.Backend.InternalFlow.EvaluatedRevertChecks.local_parts_execution' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms local_parts_execution
/-- info: 'Solidity.Backend.InternalFlow.EvaluatedRevertChecks.immutable_bytes_after_restore' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms immutable_bytes_after_restore
/-- info: 'Solidity.Backend.InternalFlow.EvaluatedRevertChecks.component_return' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms component_return
/-- info: 'Solidity.Backend.InternalFlow.EvaluatedRevertChecks.empty_parts_evaluate' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms empty_parts_evaluate
/-- info: 'Solidity.Backend.InternalFlow.EvaluatedRevertChecks.empty_actual_halt' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms empty_actual_halt
/-- info: 'Solidity.Backend.InternalFlow.EvaluatedRevertChecks.empty_checked' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms empty_checked
/-- info: 'Solidity.Backend.InternalFlow.EvaluatedRevertChecks.wrong_order' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms wrong_order
/-- info: 'Solidity.Backend.InternalFlow.EvaluatedRevertChecks.wrong_length' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms wrong_length
/-- info: 'Solidity.Backend.InternalFlow.EvaluatedRevertChecks.wrong_offset' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms wrong_offset
/-- info: 'Solidity.Backend.InternalFlow.EvaluatedRevertChecks.wrong_payload' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms wrong_payload
/-- info: 'Solidity.Backend.InternalFlow.EvaluatedRevertChecks.wrong_class' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms wrong_class
/-- info: 'Solidity.Backend.InternalFlow.EvaluatedRevertChecks.early_reset' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms early_reset
/-- info: 'Solidity.Backend.InternalFlow.EvaluatedRevertChecks.empty_data_is_lossy' does not depend on any axioms -/
#guard_msgs in
#print axioms empty_data_is_lossy
/-- info: 'Solidity.Backend.InternalFlow.EvaluatedRevertChecks.actual_assert_panic' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms actual_assert_panic
/-- info: 'Solidity.Backend.InternalFlow.EvaluatedRevertChecks.assert_not_reinterpreted' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms assert_not_reinterpreted
/-- info: 'Solidity.Backend.InternalFlow.EvaluatedRevertChecks.actual_exhaustion_refused' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms actual_exhaustion_refused
/-- info: 'Solidity.Backend.InternalFlow.EvaluatedRevertChecks.division_positive' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms division_positive
/-- info: 'Solidity.Backend.InternalFlow.EvaluatedRevertChecks.evaluation_failure' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms evaluation_failure
/-- info: 'Solidity.Backend.InternalFlow.EvaluatedRevertChecks.no_partial_payload' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms no_partial_payload
/-- info: 'Solidity.Backend.InternalFlow.EvaluatedRevertChecks.capacity_baseline' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms capacity_baseline
/-- info: 'Solidity.Backend.InternalFlow.EvaluatedRevertChecks.over_capacity_reason' depends on axioms: [propext] -/
#guard_msgs in
#print axioms over_capacity_reason
/-- info: 'Solidity.Backend.InternalFlow.EvaluatedRevertChecks.over_capacity_rejected' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms over_capacity_rejected
/-- info: 'Solidity.Backend.InternalFlow.EvaluatedRevertChecks.scoped_arguments_observed' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms scoped_arguments_observed
/-- info: 'Solidity.Backend.InternalFlow.EvaluatedRevertChecks.successful_runtime_refused' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms successful_runtime_refused
/-- info: 'Solidity.Backend.InternalFlow.EvaluatedRevertChecks.actual_require_checked' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms actual_require_checked

end Solidity.Backend.InternalFlow.EvaluatedRevertChecks
