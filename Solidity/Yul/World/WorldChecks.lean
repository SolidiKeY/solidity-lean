import Solidity.Yul.World.Lifecycle
import Solidity.Source.StateExamples

/-! # Inhabited, negative and combined preparation controls
These are kernel proofs of independent laws, not Yul frontend admission or
concrete VY2/G42 integration tests. No native_decide is used.
-/
namespace Solidity.Yul.World.Checks
open Solidity.Roadmap (Address Word Bytes Fixed)
open Solidity.Source
open Solidity.Source.StateExamples

/-- LOG0 and LOG4, with a nonempty payload and ordered distinct topics. -/
def l0 : Log := ⟨addr 1, ⟨0, by decide⟩, #v[], [0, 255, 17]⟩
def l4 : Log := ⟨addr 2, ⟨4, by decide⟩,
  #v[toWord 11, toWord 22, toWord 33, toWord 44], [128, 0]⟩

/-- Nonempty data, boundary endpoints, and out-of-bounds zero-size refusal. -/
theorem windows :
    returnWindow [17, 34, 51] 1 2 = some [34, 51] ∧
    returnWindow [17, 34, 51] 3 0 = some [] ∧
    returnWindow [17, 34, 51] 4 0 = none ∧
    returnWindow [17, 34, 51] 2 2 = none ∧
    callOutput [17, 34, 51] 2 = [17, 34] := by decide

/-- Revert overwrites rather than restores an earlier call's data. -/
theorem overwritten : overwrite (overwrite [9] (.success [1, 2, 3])) (.revert [254, 0]) = [254, 0] := rfl

/-- CREATE success discards runtime code from returndata; failure retains bytes. -/
theorem creation_data : createReturnData (.success [96, 0]) = [] ∧
    createReturnData (.revert [255, 0]) = [255, 0] := ⟨rfl, rfl⟩

/-- All five legal topic counts are inhabited. -/
def logs : Vector Log 5 := #v[
  l0,
  ⟨addr 1, ⟨1, by decide⟩, #v[toWord 1], [11]⟩,
  ⟨addr 1, ⟨2, by decide⟩, #v[toWord 1, toWord 2], [22]⟩,
  ⟨addr 1, ⟨3, by decide⟩, #v[toWord 1, toWord 2, toWord 3], [33]⟩,
  l4]

/-- Distinct topics, origins and bytes are not erased. -/
theorem observations_exact : observeEmit l4 = observeYul l4 ∧
    observeYul l0 ≠ observeYul l4 := by decide

/-- A caller already has a write, log and stale returndata. -/
def callerEntry : Effects D₀ LW LW := ⟨s₀.run callOps, [l0], [9, 8, 7]⟩

/-- Environment-supplied caller-storage havoc, explicitly supplied as an
operation, is reversible. No claim that all such operations are reachable. -/
def havoc : List (Op D₀ LW LW) :=
  [.account (addr 1) (fun a => { a with storage := Storage.empty.write countPath seven })]

/-- A failing nested callee keeps the caller's earlier writes/logs, removes
its own log, and exposes nonempty revert data. -/
theorem rollback_control :
    let done := complete callerEntry (addr 1) (addr 2) (toWord 0) [42] false havoc [l4] (.revert [254, 0])
    done.execution = callerEntry.execution ∧ done.logs = [l0] ∧
    done.returndata = [254, 0] ∧
    (done.execution.world.accounts (addr 1)).storage.read countPath = some eight := by
  dsimp only
  rw [complete_revert]
  exact ⟨rfl, rfl, rfl, rfl⟩

/-- The same havoc on success actually changes caller storage and keeps logs. -/
theorem success_control :
    let done := complete callerEntry (addr 1) (addr 2) (toWord 0) [42] false havoc [l4] (.success [12])
    (done.execution.world.accounts (addr 1)).storage.read countPath = some seven ∧
      done.logs = [l0, l4] ∧ done.returndata = [12] := ⟨rfl, rfl, rfl⟩

/-- Nested staticcall then delegatecall preserves static, caller address,
sender and inherited value (the static call's zero). -/
theorem nested_context :
    let p := s₀.enter (addr 1) (addr 2) (toWord 99) [] false
    let s := childContext s₀ p .staticcall (addr 3) (toWord 88) [1]
    let d := childContext s₀ s .delegatecall (addr 4) (toWord 77) [2]
    d.static = true ∧ d.this = addr 3 ∧ d.caller = addr 1 ∧ d.value = toWord 0 :=
  ⟨rfl, rfl, rfl, rfl⟩

/-- Existing and fresh accounts are distinguished by transaction metadata. -/
def life : Lifecycle D₀ LW LW :=
  let old : Account D₀ L₀ := { acc₁ with nonce := 3, code := some 7 }
  let fresh : Account D₀ L₀ :=
    ⟨toWord 23, 1, some 8, Storage.empty.write countPath eight⟩
  ⟨⟨(s₀.run callOps).world.set (addr 1) old |>.set (addr 2) fresh,
      (s₀.run callOps).transient, (s₀.run callOps).journal⟩,
    fun a => a == addr 2, fun _ => true⟩

/-- Old code/storage persists; new scheduled account is deleted; transient,
metadata and journal are cleared at the transaction boundary. -/
theorem lifecycle_control :
    life.finish.execution.world.accounts (addr 1) = life.execution.world.accounts (addr 1) ∧
    life.finish.execution.world.accounts (addr 2) = Account.empty (LW (addr 2)) ∧
    life.finish.execution.journal = [] ∧ life.finish.created (addr 2) = false := by
  exact ⟨finish_old life _ (by decide), finish_created_doomed life _ (by decide) rfl, rfl, rfl⟩

/-- Deletion really removes a funded account with code, nonce and storage;
an old account's nonempty code survives EIP-6780. -/
theorem nontrivial_deletion :
    (life.execution.world.accounts (addr 2)).code = some 8 ∧
    (life.execution.world.accounts (addr 2)).nonce = 1 ∧
    (life.execution.world.accounts (addr 2)).balance = toWord 23 ∧
    (life.execution.world.accounts (addr 2)).storage.read countPath = some eight ∧
    (life.finish.execution.world.accounts (addr 2)).code = none ∧
    (life.finish.execution.world.accounts (addr 2)).nonce = 0 ∧
    (life.finish.execution.world.accounts (addr 1)).code = some 7 := by
  exact ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩

/-- The fresh child cannot inherit the caller's stale buffer. -/
theorem child_buffer : (freshChild callerEntry).returndata = [] ∧
    (freshChild callerEntry).execution = callerEntry.execution := ⟨rfl, rfl⟩

/-- Static mode refuses destruction; old self-beneficiary leaves funds;
fresh self-beneficiary burns funds before deferred deletion. -/
theorem destruction_controls :
    (life.schedule true (addr 1)).isNone = true ∧
    (selfBeneficiary s₀ false (addr 1)).world.accounts (addr 1) = s₀.world.accounts (addr 1) ∧
    ((selfBeneficiary s₀ true (addr 1)).world.accounts (addr 1)).balance = toWord 0 :=
  ⟨rfl, rfl, by decide⟩

/-- Destruction's balance transfer changes both known accounts. -/
theorem destruction_transfer :
    (destructTransfer s₀ false (addr 1) (addr 2)).map (fun s =>
      ((s.world.accounts (addr 1)).balance.val, (s.world.accounts (addr 2)).balance.val)) =
      some (0, 100) := by decide

/-- Nonempty prefix, two callee outcomes and a later bounds failure combine. -/
theorem combined :
    let first := complete callerEntry (addr 1) (addr 2) (toWord 0) [] false havoc [l4] (.success [1, 2, 3])
    let last := complete first (addr 1) (addr 2) (toWord 0) [] false callOps [l0] (.revert [254])
    last.logs = [l0, l4] ∧ last.returndata = [254] ∧
      returnWindow last.returndata 0 2 = none := by
  dsimp only
  rw [complete_revert]
  exact ⟨rfl, rfl, by decide⟩

/-- G01 fixed Keccak; no new hash/address primitive. -/
def fixed : Fixed := ⟨Solidity.Roadmap.Evm.withKeccak, fun bal _ a => bal a, 1, 0⟩

/-- Concrete CREATE2 sender/salt boundaries in the actual 85-byte input. -/
theorem create2_input_control :
    (create2Input fixed (addr 1) (toWord 2) [0]).take 21 =
      [255] ++ beBytes 20 1 ∧
    ((create2Input fixed (addr 1) (toWord 2) [0]).drop 21).take 32 = wordBytes (toWord 2) := by
  decide

-- EIP-1014 example 0, actual Keccak computation. This #guard is an executable
-- control, not a universal kernel theorem about the external hash primitive.
#guard (create2Address fixed (addr 0) (toWord 0) [0]).val ==
  0x4d1a2e2bb4f88f0250f26ffff098b0b30b26bf38

/-- An inhabited extension agreement keeps old events as well as logs. -/
def identityAgreement : ObservationAgreement (List Observation) (List Observation) where
  source := id
  target := id
  related := Eq
  exact_observations := fun _ _ h => h

/-- Erasing logs cannot satisfy exact observations, even for a mixed trace. -/
theorem no_log_erasure :
    [Observation.event (.credit (addr 1) (toWord 3)), .log l4] ≠
      [Observation.event (.credit (addr 1) (toWord 3))] := by decide

/-- Mixed caller observations, retained verbatim on an inner revert. -/
def callerTrace : List Observation :=
  [.event (.credit (addr 1) (toWord 3)), .log l0,
   .event (.call (addr 3) (toWord 0) [17] false), .log l4]

/-- Multiple distinct interactions interleaved with distinct emitter/topic/data
logs. This is a trace-transformation control, not a reachable G42 session. -/
def calleeTrace : List Observation :=
  [.log ⟨addr 3, ⟨1, by decide⟩, #v[toWord 51], [61]⟩,
   .event (.credit (addr 5) (toWord 8)),
   .log ⟨addr 4, ⟨2, by decide⟩, #v[toWord 52, toWord 53], [62, 63]⟩,
   .event (.answer (.success [170]) none),
   .log ⟨addr 6, ⟨3, by decide⟩, #v[toWord 54, toWord 55, toWord 56], [64]⟩,
   .event (.credit (addr 7) (toWord 9))]

/-- The FULL ordered observation list, not just either projection. -/
theorem mixed_rollback_exact : rollbackTrace callerTrace calleeTrace =
    [.event (.credit (addr 1) (toWord 3)), .log l0,
     .event (.call (addr 3) (toWord 0) [17] false), .log l4,
     .event (.credit (addr 5) (toWord 8)),
     .event (.answer (.success [170]) none),
     .event (.credit (addr 7) (toWord 9))] := rfl

/-- Success retains every interleaved log; subsequent inner revert retains
that complete successful prefix, and removes only the new failed-frame logs. -/
theorem success_then_revert_trace :
    rollbackTrace (callerTrace ++ calleeTrace) [.log l0, .event (.credit (addr 8) (toWord 10)), .log l4] =
      callerTrace ++ calleeTrace ++ [.event (.credit (addr 8) (toWord 10))] := rfl

/-- A committed child's logs are still removed by an enclosing frame revert;
every interaction from both completed children remains in order. -/
theorem enclosing_revert_trace : rollbackTrace callerTrace (calleeTrace ++ [.log l4,
    .event (.credit (addr 8) (toWord 10))]) =
    callerTrace ++ [.event (.credit (addr 5) (toWord 8)),
      .event (.answer (.success [170]) none), .event (.credit (addr 7) (toWord 9)),
      .event (.credit (addr 8) (toWord 10))] := rfl

/-- A successful trace has strictly more observations than its reverted form;
keeping the failed-frame logs or reordering interactions is observably wrong. -/
theorem mixed_negative :
    rollbackTrace callerTrace calleeTrace ≠ callerTrace ++ calleeTrace ∧
    rollbackTrace callerTrace calleeTrace ≠ callerTrace ++
      [.event (.answer (.success [170]) none), .event (.credit (addr 5) (toWord 8)),
       .event (.credit (addr 7) (toWord 9))] := by decide

/-! ## Funded multi-account lifecycle/journal controls -/

/-- Three funded accounts with distinct code/nonce and nonempty typed storage. -/
def fundedBase : ExecState D₀ LW LW :=
  ⟨s₀.world.set (addr 1) { acc₁ with nonce := 3, code := some 7 }
    |>.set (addr 2) ⟨toWord 23, 1, some 8, Storage.empty.write countPath eight⟩
    |>.set (addr 3) ⟨toWord 41, 9, some 10, Storage.empty.write countPath seven⟩,
    Transient.empty, []⟩

def fundedPrefix : ExecState D₀ LW LW := fundedBase.run callOps

def paid : ExecState D₀ LW LW :=
  (fundedPrefix.apply (.account (addr 1) (fun old => { old with balance := toWord 0 }))).apply
    (.account (addr 2) (fun old => { old with balance := toWord 123 }))

theorem funded_prefix_nonempty : fundedPrefix.journal.length = 2 ∧
    (fundedPrefix.world.accounts (addr 1)).balance = toWord 100 ∧
    (fundedPrefix.world.accounts (addr 2)).balance = toWord 23 ∧
    (fundedPrefix.world.accounts (addr 3)).balance = toWord 41 := ⟨rfl, rfl, rfl, rfl⟩

theorem paid_actual : destructTransfer fundedPrefix true (addr 1) (addr 2) = some paid := rfl

/-- Both actual self-beneficiary branches restore exactly the caller journal
and full state; the fresh branch really burned a nonzero balance first. -/
theorem funded_self_rollback :
    (selfBeneficiary fundedPrefix false (addr 1)).world.accounts (addr 1) =
      fundedPrefix.world.accounts (addr 1) ∧
    ((selfBeneficiary fundedPrefix true (addr 1)).world.accounts (addr 1)).balance = toWord 0 ∧
    ((selfBeneficiary fundedPrefix true (addr 1)).world.accounts (addr 1)).code = some 7 ∧
    ((selfBeneficiary fundedPrefix true (addr 1)).world.accounts (addr 1)).nonce = 3 ∧
    ((selfBeneficiary fundedPrefix true (addr 1)).world.accounts (addr 1)).storage.read countPath = some eight ∧
    (fundedPrefix.enter (addr 1) (addr 2) (toWord 999) [1, 2] false).rollback
      (selfBeneficiary fundedPrefix true (addr 1)) = fundedPrefix ∧
    (fundedPrefix.enter (addr 1) (addr 2) (toWord 999) [1, 2] false).rollback
      (selfBeneficiary fundedPrefix false (addr 1)) = fundedPrefix := by
  exact ⟨rfl, rfl, rfl, rfl, rfl, rollback_selfBeneficiary _ _ _ _ _ _ _ _,
    rollback_selfBeneficiary _ _ _ _ _ _ _ _⟩

/-- Known distinct transfer pays the funded beneficiary; the third account's
entire typed record is unchanged. Rollback keeps the two-entry caller prefix. -/
theorem funded_transfer_rollback :
    (paid.world.accounts (addr 1)).balance = toWord 0 ∧
    (paid.world.accounts (addr 2)).balance = toWord 123 ∧
    paid.world.accounts (addr 3) = fundedPrefix.world.accounts (addr 3) ∧
    (fundedPrefix.enter (addr 1) (addr 2) (toWord 999) [3] false).rollback paid = fundedPrefix := by
  exact ⟨rfl, rfl, destructTransfer_other _ _ _ _ _ _ paid_actual (by decide) (by decide),
    rollback_destructTransfer _ _ _ _ _ paid_actual _ _ _ _ _⟩

/-- An actual successful child's payment, followed by more caller writes,
remains undoable by the enclosing frame. No empty journal is assumed. -/
theorem funded_enclosing_rollback :
    (fundedBase.enter (addr 1) (addr 2) (toWord 999) [4] false).rollback
      (((fundedPrefix.enter (addr 2) (addr 1) (toWord 23) [5] false).commit paid).run havoc) = fundedBase := by
  change (fundedBase.enter (addr 1) (addr 2) (toWord 999) [4] false).rollback (paid.run havoc) = fundedBase
  exact destructTransfer_outer_revert fundedBase paid callOps havoc true (addr 1) (addr 2)
    paid_actual _ _ _ _ _

/-- Fresh but unscheduled accounts survive finalization. A later scheduling
attempt without a new creation cannot resurrect the transaction-local flag. -/
def unscheduledLife : Lifecycle D₀ LW LW :=
  ⟨fundedPrefix, fun a => a == addr 2, fun _ => false⟩

theorem fresh_unscheduled_reset :
    unscheduledLife.finish.execution.world.accounts (addr 2) = fundedPrefix.world.accounts (addr 2) ∧
    (unscheduledLife.finish.execution.world.accounts (addr 2)).balance = toWord 23 ∧
    (unscheduledLife.finish.execution.world.accounts (addr 2)).nonce = 1 ∧
    (unscheduledLife.finish.execution.world.accounts (addr 2)).code = some 8 ∧
    (unscheduledLife.finish.execution.world.accounts (addr 2)).storage.read countPath = some eight ∧
    unscheduledLife.finish.execution.journal = [] ∧
    unscheduledLife.finish.finish = unscheduledLife.finish := by
  exact ⟨finish_not_doomed _ _ rfl, rfl, rfl, rfl, rfl, rfl, finish_idempotent _⟩

theorem second_transaction_control :
    (unscheduledLife.finish.schedule false (addr 2)).map (fun t =>
      (t.created (addr 2), t.doomed (addr 2), (t.execution.world.accounts (addr 2)).balance)) =
      some (false, false, toWord 23) ∧
    (unscheduledLife.finish.execution.transient.cells (addr 1)).read countPath =
      Val.default D₀ (LW (addr 1) countPath) := ⟨rfl, rfl⟩

/-- Metadata changes exactly the named account, and scheduling refuses static
mode even for a funded newly recorded account. -/
theorem metadata_controls :
    (unscheduledLife.recordCreation (addr 1)).created (addr 1) = true ∧
    (unscheduledLife.recordCreation (addr 1)).created (addr 2) = true ∧
    (unscheduledLife.recordCreation (addr 1)).doomed (addr 1) = false ∧
    ((unscheduledLife.recordCreation (addr 1)).schedule false (addr 1)).map
      (fun t => (t.created (addr 1), t.doomed (addr 1), t.doomed (addr 2))) = some (true, true, false) ∧
    (unscheduledLife.recordCreation (addr 1)).schedule true (addr 1) = none :=
  ⟨rfl, rfl, rfl, rfl, rfl⟩

/-- Wrongly preserving a burned balance, deleting an unscheduled fresh account,
or crediting the untouched third account would change observations. -/
theorem lifecycle_negative_controls :
    ((selfBeneficiary fundedPrefix true (addr 1)).world.accounts (addr 1)).balance ≠ toWord 100 ∧
    (unscheduledLife.finish.execution.world.accounts (addr 2)).code ≠ none ∧
    (paid.world.accounts (addr 3)).balance ≠ toWord 141 := by decide

/-! ## General byte-window and ordered-trace laws instantiated -/

def windowBytes : Bytes := [17, 34, 51, 68, 85, 102]

theorem window_composition_control : returnWindow windowBytes 2 2 = some [51, 68] :=
  returnWindow_compose windowBytes [34, 51, 68, 85] [51, 68] 1 4 1 2 (by decide) (by decide)

theorem window_index_control :
    ([51, 68] : Bytes)[1]'(by decide) = windowBytes[3]'(by decide) :=
  returnWindow_byte windowBytes [51, 68] 2 2 1 window_composition_control (by decide)

/-- Exact outer/source end permits zero bytes; one byte beyond either end
refuses even zero bytes. A positive-size crossing refuses as well. -/
theorem window_boundary_control :
    returnWindow windowBytes 6 0 = some [] ∧
    returnWindow windowBytes 0 0 = some [] ∧
    returnWindow ([51, 68, 85, 102] : Bytes) 5 0 = none ∧
    returnWindow windowBytes 7 0 = none ∧ returnWindow windowBytes 5 2 = none := by
  exact ⟨returnWindow_compose windowBytes [51, 68, 85, 102] [] 2 4 4 0 (by decide) (by decide),
    returnWindow_zero _ _ (by decide),
    (returnWindow_none_iff _ _ _).mpr (by decide),
    (returnWindow_none_iff _ _ _).mpr (by decide),
    (returnWindow_none_iff _ _ _).mpr (by decide)⟩

/-- A successful call followed by revert exposes the last complete buffer;
its nested source window is unaffected by the previous success's bytes. -/
theorem overwrite_window_control :
    returnWindow (overwrite (overwrite [9, 8] (.success [255, 254, 253]))
      (.revert windowBytes)) 2 2 = some [51, 68] := by
  rw [overwrite_last]
  exact window_composition_control

theorem output_prefix_control :
    callOutput (callOutput windowBytes 4) 2 = callOutput windowBytes 2 ∧
    callOutput windowBytes 2 ++ windowBytes.drop 2 = windowBytes ∧
    callOutput windowBytes 9 = windowBytes ∧
    callOutput windowBytes (2 + 3) = callOutput windowBytes 2 ++ callOutput (windowBytes.drop 2) 3 :=
  ⟨callOutput_truncate _ _ _, callOutput_prefix _ _, callOutput_full _ _ (by decide),
    callOutput_append _ _ _⟩

/-- Uses the general nested identity to recover the FULL expected list. -/
theorem nested_trace_law_control :
    rollbackTrace callerTrace (rollbackTrace calleeTrace [.log l4, .event (.credit (addr 8) (toWord 10))]) =
      callerTrace ++ [.event (.credit (addr 5) (toWord 8)),
        .event (.answer (.success [170]) none), .event (.credit (addr 7) (toWord 9)),
        .event (.credit (addr 8) (toWord 10))] := by
  rw [rollbackTrace_nested]
  exact enclosing_revert_trace

theorem committed_enclosing_law_control :
    rollbackTrace callerTrace ((calleeTrace ++ [.log l0]) ++ [.event (.credit (addr 8) (toWord 10)), .log l4]) =
      rollbackTrace (rollbackTrace (rollbackTrace callerTrace calleeTrace) [.log l0])
        [.event (.credit (addr 8) (toWord 10)), .log l4] :=
  rollbackTrace_enclosing _ _ _ _

theorem successful_prefix_law_control :
    rollbackTrace (callerTrace ++ calleeTrace) [.log l0, .event (.credit (addr 8) (toWord 10)), .log l4] =
      callerTrace ++ (calleeTrace ++ [.event (.credit (addr 8) (toWord 10))]) :=
  rollbackTrace_success_then_revert _ _ _

theorem discard_idempotent_control :
    discardLogs (discardLogs (callerTrace ++ calleeTrace)) =
      discardLogs callerTrace ++ discardLogs calleeTrace := by
  rw [discardLogs_idempotent, discardLogs_append]

/-- Neither wrong bytes, reordered interactions nor erasure of the full
caller's logs can pass the exact ordered observation contract. -/
theorem window_trace_negative_controls :
    returnWindow windowBytes 2 2 ≠ some [68, 51] ∧
    rollbackTrace callerTrace calleeTrace ≠ rollbackTrace (discardLogs callerTrace) calleeTrace ∧
    rollbackTrace callerTrace calleeTrace ≠ callerTrace ++
      [.event (.answer (.success [170]) none), .event (.credit (addr 5) (toWord 8)),
       .event (.credit (addr 7) (toWord 9))] := by decide

end Solidity.Yul.World.Checks

#print axioms Solidity.Yul.World.returnWindow_length
#print axioms Solidity.Yul.World.create2Input_length
#print axioms Solidity.Yul.World.complete_revert
#print axioms Solidity.Yul.World.nested_revert
#print axioms Solidity.Yul.World.rollback_events
#print axioms Solidity.Yul.World.rollback_logs
#print axioms Solidity.Yul.World.lifecycle_revert
#print axioms Solidity.Yul.World.Checks.mixed_rollback_exact
#print axioms Solidity.Yul.World.Checks.success_then_revert_trace
#print axioms Solidity.Yul.World.Checks.enclosing_revert_trace
#print axioms Solidity.Yul.World.Checks.mixed_negative

#print axioms Solidity.Yul.World.schedule_exact
#print axioms Solidity.Yul.World.finish_idempotent
#print axioms Solidity.Yul.World.rollback_destructTransfer
#print axioms Solidity.Yul.World.destructTransfer_outer_revert
#print axioms Solidity.Yul.World.Checks.funded_self_rollback
#print axioms Solidity.Yul.World.Checks.funded_transfer_rollback
#print axioms Solidity.Yul.World.Checks.funded_enclosing_rollback

#print axioms Solidity.Yul.World.returnWindow_byte
#print axioms Solidity.Yul.World.returnWindow_compose
#print axioms Solidity.Yul.World.rollbackTrace_nested
#print axioms Solidity.Yul.World.rollbackTrace_enclosing
#print axioms Solidity.Yul.World.Checks.nested_trace_law_control
