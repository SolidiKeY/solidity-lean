import Solidity.Backend.WorldCalls.SourceCallHistory
import Solidity.Lowering.Readonly.SourceEnvironmentControls

/-! Actual Source calls at known nonself and unknown receivers. Caller states
already contain a prior write; capture provenance and native/compiler adequacy
are not inferred. -/
namespace Solidity.Backend.WorldCalls.SourceCallHistoryControls
open Solidity.Source Solidity.Source.SemanticsExamples
open Solidity.Lowering.Readonly
open Solidity.Roadmap (Word Outcome)
def other := addr 2
def callerAccount := (sB.ex.world.accounts thisC).withBalance (word 10)
def callerWorld := sB.ex.world.set thisC callerAccount
def two : St EB := {sB with ex := {sB.ex with world := callerWorld.set other acctC}}
def global := GB (fun _ => .answer (.success []))
def knownCall (requested : Bool) (value : Word := word 0)
    (pipeline : Solidity.Roadmap.Pipeline := .legacy) :=
  (callAddr {global with pipeline := pipeline} FC 30 other value (selOf "cb()") requested).run (L0 EB, two)
def nameAt (a : Solidity.Roadmap.Address) :=
  match (instanceAt global a : EM EB [] _).run (L0 EB, two) with
  | (.ok name, _) => name
  | _ => none
def otherX (s : St EB) : Option Int :=
  match (s.ex.world.accounts other).storage.read dX.path with
  | some (.int k _) => some k
  | _ => none
def callee (out : Outcome) : Solidity.Roadmap.Strategy :=
  fun events => if events.length = 1 then .reenter thisC user (word 0) (selOf "cb()") false else .answer out
def unknownCall (requested readonly : Bool) (out : Outcome := .success [1,2])
    (pipeline : Solidity.Roadmap.Pipeline := .legacy) :=
  let base := GB (callee out)
  let program := if readonly then SourceEnvironmentControls.readProgram else PB
  (callAddr {base with prog := program, pipeline := pipeline} FC 30 ext (word 0) [4,5] requested).run
    (L0 EB, HistoryRollbackControls.entry)
def changedKnown := knownCall false
def nonpayable := knownCall false (word 3)
def funded := (SourceHistory.CallPrefix.fund (E := EB) FC other (word 3)).run (L0 EB,two)
def refusedKnown := knownCall true
def ordinaryUnknown := unknownCall false false
def staticUnknown := unknownCall true false
def readingUnknown := unknownCall true true
theorem known_nonself : other ≠ FC.this := by decide
theorem actual_code : nameAt other = some "C" := by decide
theorem spoofed_code_rejected : nameAt other ≠ some "Fake" := by decide
theorem known_zero_success : changedKnown.1 = .ok (.success []) := by rfl
theorem known_zero_caller_kept : readX changedKnown.2.2 = some 3 := by decide
theorem known_zero_callee_written : otherX changedKnown.2.2 = some 4 := by decide
theorem funding_success : funded.1 = .ok true := by rfl
theorem funding_balances : (funded.2.2.ex.world.accounts thisC).balance = 7 ∧
    (funded.2.2.ex.world.accounts other).balance = 3 := by decide
theorem nonpayable_reverts : nonpayable.1 = .ok (.revert []) := by rfl
theorem nonpayable_balance_rollback : (nonpayable.2.2.ex.world.accounts thisC).balance = 10 ∧
    (nonpayable.2.2.ex.world.accounts other).balance = 0 := by decide
theorem nonpayable_storage_kept : otherX nonpayable.2.2 = some 3 := by decide
theorem known_static_revert : refusedKnown.1 = .ok (.revert []) := by rfl
theorem known_static_storage : otherX refusedKnown.2.2 = some 3 := by decide
theorem static_value_outer_halt :
    ((callAddr global {FC with static := true} 30 other (word 1) [] false).run (L0 EB,two)).1 =
      .error (.revert []) := by rfl
theorem unknown_nonself : ext ≠ FC.this := by decide
theorem unknown_success : ordinaryUnknown.1 = .ok (.success [1,2]) := by rfl
theorem ordinary_reentry_changes : readX ordinaryUnknown.2.2 = some 5 := by decide
theorem ordinary_false_preservation : readX ordinaryUnknown.2.2 ≠ some 4 := by decide
theorem static_unknown_success : staticUnknown.1 = .ok (.success [1,2]) := by rfl
theorem static_prefix_kept : readX staticUnknown.2.2 = some 4 := by decide
theorem static_child_refused : staticUnknown.2.2.events.contains (.reentered (.revert [])) = true := by decide
theorem readonly_reentry_succeeds : readingUnknown.2.2.events.contains (.reentered (.success [])) = true := by decide
theorem readonly_prefix_kept : readX readingUnknown.2.2 = some 4 := by decide
theorem outer_revert_bytes : (unknownCall false false (.revert [7,9])).1 = .ok (.revert [7,9]) := by rfl
theorem outer_revert_prefix : readX (unknownCall false false (.revert [7,9])).2.2 = some 4 := by decide
def returned (result : Except Halt Outcome) : Option Solidity.Roadmap.Bytes :=
  match result with | .ok (.success bytes) => some bytes | _ => none
theorem both_pipelines : ∀ pipeline : Solidity.Roadmap.Pipeline,
    readX (unknownCall true true (pipeline := pipeline)).2.2 = some 4 ∧
    otherX (knownCall false (pipeline := pipeline)).2.2 = some 4 ∧
    returned (unknownCall true true (pipeline := pipeline)).1 = some [1,2] ∧
    returned (knownCall false (pipeline := pipeline)).1 = some [] ∧
    (unknownCall true true (pipeline := pipeline)).2.2.events.contains (.reentered (.success [])) = true := by
  intro pipeline
  cases pipeline <;> decide
theorem actual_unknown_client :
    StaticJournal.SameStorage
      ((callAddr global FC 1 ext (word 0) [4,5] true).run (L0 EB,HistoryRollbackControls.entry)).2.2.ex
      HistoryRollbackControls.entry.ex := by
  exact SourceCallHistory.unknown_static_storage global FC 0 (SourceHistory.at_zero global)
    ext [4,5] true HistoryRollbackControls.entry (by decide) (by rfl) (by rfl)
end Solidity.Backend.WorldCalls.SourceCallHistoryControls
