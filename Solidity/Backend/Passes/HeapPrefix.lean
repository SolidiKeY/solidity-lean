import Solidity.Backend.Passes.HeapBoundaryControls

/-! Strong concrete prefix observations from the published allocation theorems,
including the independent cell outside all actually allocated objects. -/
namespace Solidity.Backend.Passes.HeapPrefix
open Evm Evm.Memory Evm.Compiler
open HeapBoundaryControls
open Backend.Passes.Controls.Fixture (C)

private theorem noRefs {R : RefTy} (r : HRef initial.H R) : False := by
  simpa only [initial, State.init, List.getElem?_nil, reduceCtorEq] using r.get?

private theorem heap16 : Objects.HeapRepr initial.heap base 16 machine :=
  ⟨⟨fun r => (noRefs r).elim, fun r => (noRefs r).elim, fun r _ _ => (noRefs r).elim⟩,
    (fun _ r => (noRefs r).elim), (fun r => (noRefs r).elim), (fun r _ => (noRefs r).elim)⟩
private theorem physical16 : Objects.StateRepr 1 1 16 (Frag.init []) initial base machine := by
  have hc := Sim.init C 0 W_pos (fun _ => 0) ⟨0,W_pos⟩ rfl
  refine ⟨⟨hc.store, ?_, ?_, hc.net, hc.netSelf, hc.bound, ?_, hc.env, hc.funds, hc.oracle⟩,
    heap16, ?_, by decide⟩
  all_goals intro p i; nomatch i
private theorem allocator16 : Objects.AllocatorRepr initial.heap base 16 ⟨16,by decide⟩ machine := by
  refine ⟨heap16, ⟨by decide, by decide, rfl, ?_⟩, fun r => (noRefs r).elim⟩
  intro addr ha
  change 16 ≤ addr at ha
  simp only [machine, if_neg (show addr ≠ 0 by omega), if_neg (show addr ≠ 15 by omega)]

def childMachine : Machine :=
  writeMachine (allocateMachine machine ⟨16,by decide⟩ ⟨1,by decide⟩) 1 w[16]
def childState : State C [.mem Child] := initial.allocPush (defaultArray .uint ⟨1,by decide⟩)
def childBase : Nat → Fin W := upd base 0 ⟨16,by decide⟩

theorem allocation_code : allocation.code =
    declareNewCode (C := C) (Γ := []) 1 (.lit 1 rfl) ++
      ([.push w[2]] ++ Objects.nestedCode ++ [.mstore 2]) := rfl

/-- No unrolling or second loop semantics: use the owner's finite construction
simulation, exact old-reference map extension and actual frame preservation. -/
theorem allocation_observations :
    ∃ mid, run allocation.code machine = .ok mid 0 ∧
      mid.mem 0 = w[23] ∧ mid.mem 1 = w[16] ∧ mid.mem 2 = w[18] ∧ mid.mem 15 = w[99] := by
  have hp := Objects.primitiveDeclare_correct physical16 allocator16 (by decide)
    .uint (.lit 1 rfl) rfl (⟨1,by decide⟩ : Fin W) rfl (by decide) (by decide)
  have hrun : run (declareNewCode (C := C) (Γ := []) 1 (.lit 1 rfl)) machine = .ok childMachine 0 := hp.2.1
  have hal : Objects.AllocatorRepr childState.heap childBase 16 ⟨18,by decide⟩ childMachine := hp.2.2.2.1
  obtain ⟨selected, rest, hr, ha, _, _, _, _, hf⟩ :=
    Objects.nested_correct childState.heap (.prim .uint) rfl (⟨2,by decide⟩ : Fin W)
      childBase 16 childMachine (⟨18,by decide⟩ : Fin W) hal (by decide)
  let final := writeMachine rest 2 w[18]
  have hs : run ([.push w[2]] ++ Objects.nestedCode ++ [.mstore 2]) childMachine = .ok final 0 := by
    rw [List.append_assoc, run_append_ok (m' := childMachine.push w[2]) rfl,
      run_append_ok hr]
    rfl
  refine ⟨final, ?_, ?_, ?_, ?_, ?_⟩
  · rw [allocation_code, run_append_ok hrun]
    exact hs
  · change upd rest.mem 2 w[18] 0 = w[23]
    rw [upd_other _ _ (by decide)]
    exact ha.free.cell
  · change upd rest.mem 2 w[18] 1 = w[16]
    rw [upd_other _ _ (by decide), hf 1 (by decide) (by decide)]
    rfl
  · change upd rest.mem 2 w[18] 2 = w[18]
    exact upd_same _ _ _
  · change upd rest.mem 2 w[18] 15 = w[99]
    rw [upd_other _ _ (by decide), hf 15 (by decide) (by decide)]
    rfl

end Solidity.Backend.Passes.HeapPrefix
