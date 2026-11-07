import Solidity.Source.MemoryLocalDelete
import Solidity.Backend.Aggregates.CalldataCopyControls

/-! G18.05 actual copy/conversion/branch-local deletion and alias clients.
These observe Source identities and budgets, not physical EVM allocation. -/
namespace Solidity.Backend.Aggregates.MemoryLocalDeleteControls
open Solidity ByteParameterControls NestedCalldataControls CalldataCopyControls

abbrev arrayTy : Source.STy := .array .memory .bool none
abbrev branchCtx : Source.RCtx := arrayTy :: arrayTy :: caller

def contents : Source.Data E.layout arrayTy :=
  .array 2 (fun _ h => nomatch h) (fun k => .val ([Source.Val.bool true,.bool false].get k))
def emptyContents : Source.Data E.layout arrayTy :=
  .array 0 (fun _ h => nomatch h) Fin.elim0
def copiedState : Source.St E :=
  {sourceState with heap := (sourceHeap.alloc ⟨arrayTy,contents⟩).1}
def branchLocals : Source.Locals E.layout branchCtx :=
  .cons (.memRef rfl 2) (.cons (.memRef rfl 2) sourceLocals)
def branchBefore : Source.EMState E branchCtx := (branchLocals,copiedState)
def deletedState : Source.St E :=
  {copiedState with heap := (copiedState.heap.alloc ⟨arrayTy,emptyContents⟩).1}
def finishedLocals : Source.Locals E.layout branchCtx :=
  .cons (.memRef rfl 3) (.cons (.memRef rfl 2) sourceLocals)

def body (budget : Nat) : Source.EM E branchCtx (Source.Val E.layout .bool) := do
  Source.deleteLoc copyFrame budget (.local .here)
  let alias ← Source.readLoc copyFrame (.local (.there .here))
  let location ← Source.indexLoc copyFrame alias 1
  Source.readLoc copyFrame location

/-- Actual copy and same-memory conversion produce both alias locals; sub
uses the real copied state and drops only its branch-local extensions. -/
def client (budget : Nat) : Source.EM E caller
    (Source.Val E.layout .bool × Source.Locals E.layout branchCtx) := do
  let value ← Source.getV (← copied)
  let alias ← Source.getV (← Source.convRV copyFrame 0 arrayTy (.val value))
  let tail ← Source.EM.locals
  Source.EM.sub (.cons value (.cons alias tail)) (body budget)

theorem delete_selected_local :
    (Source.deleteLoc copyFrame 2 (.local (.here : Source.Idx branchCtx arrayTy))).run branchBefore =
      (.ok (), (finishedLocals,deletedState)) :=
  Source.deleteLocal_array_run copyFrame 2 .bool .here branchBefore

theorem branch_success : (body 2).run branchBefore =
    (.ok (.bool false),(finishedLocals,deletedState)) := by
  unfold body
  rw [Source.Hoare.run_bind,delete_selected_local]
  rfl

theorem branch_timeout : (body 1).run branchBefore = (.error .timeout,branchBefore) := by
  unfold body
  rw [Source.Hoare.run_bind,Source.deleteLocal_array_run]

theorem client_success : (client 2).run sourceBefore =
    (.ok (.bool false,finishedLocals),(sourceLocals,deletedState)) := by
  unfold client
  rw [Source.Hoare.run_bind,copy_success]
  change (Source.EM.sub branchLocals (body 2)).run (sourceLocals,copiedState) = _
  unfold Source.EM.sub
  change (match (body 2).run branchBefore with
    | (.ok result,(locals,state)) => (Except.ok (ε := Source.Halt) (result,locals),(sourceLocals,state))
    | (.error halt,(_,state)) => (Except.error (α := Source.Val E.layout .bool × Source.Locals E.layout branchCtx) halt,(sourceLocals,state))) = _
  rw [branch_success]

theorem client_timeout : (client 1).run sourceBefore =
    (.error .timeout,(sourceLocals,copiedState)) := by
  unfold client
  rw [Source.Hoare.run_bind,copy_success]
  change (Source.EM.sub branchLocals (body 1)).run (sourceLocals,copiedState) = _
  unfold Source.EM.sub
  change (match (body 1).run branchBefore with
    | (.ok result,(locals,state)) => (Except.ok (ε := Source.Halt) (result,locals),(sourceLocals,state))
    | (.error halt,(_,state)) => (Except.error (α := Source.Val E.layout .bool × Source.Locals E.layout branchCtx) halt,(sourceLocals,state))) = _
  rw [branch_timeout]
  rfl

theorem retained_copy_contents :
    ((client 2).run sourceBefore).2.2.heap.get 2 = some ⟨arrayTy,contents⟩ := by
  rw [client_success]
  rfl

theorem fresh_empty_contents :
    ((client 2).run sourceBefore).2.2.heap.get 3 = some ⟨arrayTy,emptyContents⟩ := by
  rw [client_success]
  rfl

theorem protected_old_objects :
    ((client 2).run sourceBefore).2.2.heap.get 0 = sourceHeap.get 0 ∧
    ((client 2).run sourceBefore).2.2.heap.get 1 = sourceHeap.get 1 := by
  rw [client_success]
  exact ⟨rfl,rfl⟩

theorem deleted_local_empty_length :
    (Source.lengthOf copyFrame (finishedLocals.get .here)).run (finishedLocals,deletedState) =
      (.ok 0,(finishedLocals,deletedState)) := rfl

theorem alias_old_length :
    (Source.lengthOf copyFrame (finishedLocals.get (.there .here))).run (finishedLocals,deletedState) =
      (.ok 2,(finishedLocals,deletedState)) := rfl

theorem timeout_keeps_completed_copy : ((client 1).run sourceBefore).2.2.heap.next = 3 := by
  rw [client_timeout]
  rfl

theorem success_grows_once_more : ((client 2).run sourceBefore).2.2.heap.next = 4 := by
  rw [client_success]
  rfl

theorem wrong_timeout_rollback :
    ((client 1).run sourceBefore).2.2.heap.next ≠ sourceBefore.2.heap.next := by
  rw [timeout_keeps_completed_copy]
  decide

theorem zero_budget_delete :
    (Source.deleteLoc copyFrame 0 (.local (.here : Source.Idx branchCtx arrayTy))).run branchBefore =
      (.error .timeout,branchBefore) :=
  Source.deleteLocal_array_run copyFrame 0 .bool .here branchBefore

theorem bytes_local_delete :
    (Source.deleteLoc copyFrame 2 (.local (.here : Source.Idx caller (.bytes .memory)))).run sourceBefore =
      (.ok (),(.cons (.memRef rfl 2) (.cons (.memRef rfl 0) .nil),
        {sourceState with heap := (sourceHeap.alloc ⟨.bytes .memory,.bytes []⟩).1})) :=
  Source.deleteLocal_bytes_run copyFrame 2 .here sourceBefore

theorem wrong_alias_clear : ((body 2).run branchBefore).1 ≠
    .error (.revert (Source.panicData .index)) := by
  rw [branch_success]
  intro impossible
  cases impossible

theorem wrong_timeout_fresh_delete : ((client 1).run sourceBefore).2.2.heap.next ≠ 4 := by
  rw [timeout_keeps_completed_copy]
  decide

def deleteExpr : Source.RExpr E branchCtx (.tuple []) := .delete (.local .here)

theorem typed_delete_success :
    (Source.evalE ByteSliceControls.G copyFrame 3 deleteExpr).run branchBefore =
      (.ok Source.RVal.unit,(finishedLocals,deletedState)) := by
  unfold deleteExpr
  change ((do let location ← (pure (.local (.here : Source.Idx branchCtx arrayTy)) :
      Source.EM E branchCtx (Source.Loc E.layout branchCtx arrayTy))
              Source.deleteLoc copyFrame 2 location
              pure Source.RVal.unit) : Source.EM E branchCtx _).run branchBefore = _
  rw [pure_bind,Source.Hoare.run_bind,delete_selected_local]
  rfl

theorem typed_delete_exhausted :
    (Source.evalE ByteSliceControls.G copyFrame 2 deleteExpr).run branchBefore =
      (.error .timeout,branchBefore) := by
  unfold deleteExpr
  change ((do let location ← (pure (.local (.here : Source.Idx branchCtx arrayTy)) :
      Source.EM E branchCtx (Source.Loc E.layout branchCtx arrayTy))
              Source.deleteLoc copyFrame 1 location
              pure Source.RVal.unit) : Source.EM E branchCtx _).run branchBefore = _
  rw [pure_bind,Source.Hoare.run_bind,Source.deleteLocal_array_run]

end Solidity.Backend.Aggregates.MemoryLocalDeleteControls
