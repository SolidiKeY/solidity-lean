import tests.«internal-flow».LoopTargetFacts
/-! Projections of actual finite target executions. These are not a new
machine evaluator; the unbounded endpoint is linked with loopRun_of_iterN. -/
namespace Solidity.Backend.InternalFlow.LoopTargetChecks
open Evm Evm.Memory
private theorem prefix_ok : (match run (storageCode ++ before.code) machine with
    | .ok _ 0 => true | _ => false) = true := by decide +kernel
def prefixMachine : Evm.Machine := match run (storageCode ++ before.code) machine with
  | .ok m _ => m | _ => machine

theorem prefix_actual : run (storageCode ++ before.code) machine = .ok prefixMachine 0 := by
  have valid := prefix_ok
  cases h : run (storageCode ++ before.code) machine with
  | revert => rw [h] at valid; cases valid
  | fault => rw [h] at valid; cases valid
  | ok m k => cases k with
    | zero => simp only [prefixMachine,h]
    | succ k => rw [h] at valid; cases valid

private theorem first_ok : (match loopIterN (fun m => exec conditionCompiled.code 0 m)
    (fun m => exec bodyCompiled.code 0 m) 1 prefixMachine with
    | .inl _ => true | _ => false) = true := by decide +kernel

def firstMachine : Evm.Machine := match loopIterN (fun m => exec conditionCompiled.code 0 m)
    (fun m => exec bodyCompiled.code 0 m) 1 prefixMachine with
  | .inl m => m | _ => prefixMachine

theorem first_target_horizon : loopIterN (fun m => exec conditionCompiled.code 0 m)
    (fun m => exec bodyCompiled.code 0 m) 1 prefixMachine = .inl firstMachine := by
  have valid := first_ok
  cases h : loopIterN (fun m => exec conditionCompiled.code 0 m)
    (fun m => exec bodyCompiled.code 0 m) 1 prefixMachine with
  | inl m => simp only [firstMachine,h]
  | inr r => rw [h] at valid; cases valid

private theorem final_ok : (match loopIterN (fun m => exec conditionCompiled.code 0 m)
    (fun m => exec bodyCompiled.code 0 m) 3 prefixMachine with
    | .inr (.ok _ 0) => true | _ => false) = true := by decide +kernel

def finalMachine : Evm.Machine := match loopIterN (fun m => exec conditionCompiled.code 0 m)
    (fun m => exec bodyCompiled.code 0 m) 3 prefixMachine with
  | .inr (.ok m _) => m | _ => prefixMachine

theorem final_target_horizon : loopIterN (fun m => exec conditionCompiled.code 0 m)
    (fun m => exec bodyCompiled.code 0 m) 3 prefixMachine = .inr (.ok finalMachine 0) := by
  have valid := final_ok
  cases h : loopIterN (fun m => exec conditionCompiled.code 0 m)
    (fun m => exec bodyCompiled.code 0 m) 3 prefixMachine with
  | inl m => rw [h] at valid; cases valid
  | inr r => cases r with
    | revert => rw [h] at valid; cases valid
    | fault => rw [h] at valid; cases valid
    | ok m k => cases k with
      | zero => simp only [finalMachine,h]
      | succ k => rw [h] at valid; cases valid

theorem loop_target_actual : run selected.code prefixMachine = .ok finalMachine 0 := by
  rw [selector_code]
  have h := loopRun_of_iterN final_target_horizon
  change ((Instr.step (.loop conditionCompiled.code bodyCompiled.code) prefixMachine).bind
    (fun m k => exec [] k m)) = _
  simp only [Instr.step,h,Out.ok_bind]
  rfl

def addresses : List Nat := [0,127,1,2,3,4,5,6,256,257,258,259,260,261,262]
def words (m : Evm.Machine) : List Evm.Word := m.stack ++ addresses.map m.mem
def slots : List Evm.Slot := [.root 0,.root 1,.root 2,.data (.root 2) 0,.data (.root 2) 1,.root 3]
def stores (m : Evm.Machine) : List Nat := slots.map m.store

theorem ordered_target_words : (words prefixMachine,words firstMachine,words finalMachine) =
    ([w[77],w[259],w[99],w[17],w[9],w[256],w[256],w[0],w[0],w[2],w[7],w[11],w[0],w[0],w[0],w[0]],
     [w[77],w[261],w[99],w[17],w[10],w[256],w[256],w[259],w[77],w[2],w[9],w[11],w[1],w[10],w[0],w[0]],
     [w[77],w[263],w[99],w[17],w[11],w[256],w[256],w[261],w[77],w[2],w[10],w[11],w[1],w[10],w[1],w[11]]) := by decide +kernel

theorem ordered_target_roots : (stores prefixMachine,stores firstMachine,stores finalMachine) =
    ([7,9,2,13,17,0],[8,11,2,13,17,0],[9,13,2,13,17,0]) := by decide +kernel

private theorem split_snapshot (m : Evm.Machine) (cells : List Evm.Word)
    (lengths : cells.length = addresses.length) (h : words m = w[77] :: cells) :
    m.stack = [w[77]] ∧ addresses.map m.mem = cells := by
  have raw : m.stack ++ addresses.map m.mem = [w[77]] ++ cells := h
  have same : m.stack.length = ([w[77]] : List Evm.Word).length := by
    have size := congrArg List.length raw
    simp only [List.length_append,List.length_map] at size ⊢
    omega
  exact List.append_inj raw same

theorem final_cells : finalMachine.stack = [w[77]] ∧ addresses.map finalMachine.mem =
    [w[263],w[99],w[17],w[11],w[256],w[256],w[261],w[77],w[2],w[10],w[11],w[1],w[10],w[1],w[11]] :=
  split_snapshot finalMachine _ rfl (congrArg (fun p => p.2.2) ordered_target_words)

theorem final_cursor : finalMachine.mem 0 = w[263] :=
  congrArg (fun xs : List Evm.Word => xs[0]!) final_cells.2

theorem wrong_cursor : finalMachine.mem 0 ≠ w[259] := by
  rw [final_cursor]
  decide +kernel

theorem wrong_alias_identity : finalMachine.mem 3 ≠ w[261] := by
  have good : finalMachine.mem 3 = w[256] := congrArg (fun xs : List Evm.Word => xs[4]!) final_cells.2
  rw [good]
  decide +kernel

theorem wrong_private_frame : finalMachine.mem 5 ≠ w[259] := by
  have good : finalMachine.mem 5 = w[261] := congrArg (fun xs : List Evm.Word => xs[6]!) final_cells.2
  rw [good]
  decide +kernel

theorem omitted_old_mutation : finalMachine.mem 257 ≠ w[7] := by
  have good : finalMachine.mem 257 = w[10] := congrArg (fun xs : List Evm.Word => xs[9]!) final_cells.2
  rw [good]
  decide +kernel

theorem premature_reset : finalMachine.store (.root 1) ≠ 0 := by
  have good : finalMachine.store (.root 1) = 13 :=
    congrArg (fun triple => triple.2.2[1]!) ordered_target_roots
  rw [good]
  decide +kernel

theorem wrong_scalar_destination : finalMachine.mem 1 ≠ w[11] := by
  have good : finalMachine.mem 1 = w[17] := congrArg (fun xs : List Evm.Word => xs[2]!) final_cells.2
  rw [good]
  decide +kernel

theorem wrong_fresh_order : (finalMachine.mem 260,finalMachine.mem 262) ≠ (w[11],w[10]) := by
  have good : finalMachine.mem 260 = w[10] := congrArg (fun xs : List Evm.Word => xs[12]!) final_cells.2
  intro bad
  have impossible := good.symm.trans (congrArg Prod.fst bad)
  exact (by decide +kernel : (w[10] : Evm.Word) ≠ w[11]) impossible

theorem pointer_not_slot : finalMachine.mem 3 ≠ .slot (.root 2) := by
  have good : finalMachine.mem 3 = w[256] := congrArg (fun xs : List Evm.Word => xs[4]!) final_cells.2
  rw [good]
  intro bad; cases bad

attribute [irreducible] prefixMachine firstMachine finalMachine
end Solidity.Backend.InternalFlow.LoopTargetChecks

#print axioms Solidity.Backend.InternalFlow.LoopTargetChecks.prefix_actual
#print axioms Solidity.Backend.InternalFlow.LoopTargetChecks.first_target_horizon
#print axioms Solidity.Backend.InternalFlow.LoopTargetChecks.final_target_horizon
#print axioms Solidity.Backend.InternalFlow.LoopTargetChecks.loop_target_actual
#print axioms Solidity.Backend.InternalFlow.LoopTargetChecks.ordered_target_words
#print axioms Solidity.Backend.InternalFlow.LoopTargetChecks.ordered_target_roots
#print axioms Solidity.Backend.InternalFlow.LoopTargetChecks.final_cells
#print axioms Solidity.Backend.InternalFlow.LoopTargetChecks.final_cursor
#print axioms Solidity.Backend.InternalFlow.LoopTargetChecks.wrong_cursor
#print axioms Solidity.Backend.InternalFlow.LoopTargetChecks.wrong_alias_identity
#print axioms Solidity.Backend.InternalFlow.LoopTargetChecks.wrong_private_frame
#print axioms Solidity.Backend.InternalFlow.LoopTargetChecks.omitted_old_mutation
#print axioms Solidity.Backend.InternalFlow.LoopTargetChecks.premature_reset
#print axioms Solidity.Backend.InternalFlow.LoopTargetChecks.wrong_scalar_destination
#print axioms Solidity.Backend.InternalFlow.LoopTargetChecks.wrong_fresh_order
#print axioms Solidity.Backend.InternalFlow.LoopTargetChecks.pointer_not_slot
