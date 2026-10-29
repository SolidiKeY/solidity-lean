import Solidity.Evm.MemoryDefaultBuilder
import Solidity.Evm.MemoryObjectChildLoop

/-! Generic typed child-default copying and target pointer stores. -/
namespace Solidity.Evm.Memory.Objects

def defaultChildrenCopy {H : HTy} (hp : Heap H) (R : RefTy)
    (hm : (Ty.ref R).mapFree = true) (n : Nat) :=
  (SVec.replicate (SVal.dflt (.ref R)) n).copyStToM hp hm

theorem defaultChildrenCopy_zero {H : HTy} (hp : Heap H) (R : RefTy)
    (hm : (Ty.ref R).mapFree = true) :
    defaultChildrenCopy hp R hm 0 = ⟨List.prefix_refl H, hp, ⟨[], rfl⟩⟩ := by
  simp only [defaultChildrenCopy, SVec.replicate, SVec.copyStToM_nil]

theorem defaultChildrenCopy_succ {H : HTy} (hp : Heap H) (R : RefTy)
    (hm : (Ty.ref R).mapFree = true) (n : Nat) :
    defaultChildrenCopy hp R hm (n + 1) =
      let g₁ := hp.allocDefault R hm
      let g₂ := defaultChildrenCopy g₁.heap R hm n
      ⟨g₁.ext.trans g₂.ext, g₂.heap,
        ⟨g₁.val.wk g₂.ext :: g₂.val.1, congrArg Nat.succ g₂.val.2⟩⟩ := by
  simp only [defaultChildrenCopy, SVec.replicate, SVec.copyStToM_cons, Heap.allocDefault]

def defaultStoreStep (offset : Nat) : List Instr :=
  [.dup 4, .dup 3, .add, .push (.val (wmod offset)), .add, .mstoreAt, .push w[1], .add]
def defaultStoreMachine (m : Machine) (parent index child : Fin W) (offset : Nat) : Machine :=
  writeMachine m (wmod (parent.val + index.val + offset)).val (.val child)
def defaultChildrenBody (offset : Nat) (childCode : List Instr) : List Instr :=
  childCode ++ defaultStoreStep offset

theorem defaultStoreStep_run (m : Machine) (parent total index child : Fin W) (offset : Nat) :
    run (defaultStoreStep offset) ((control m parent total index).push (.val child)) =
      .ok (control (defaultStoreMachine m parent index child offset) parent total
        (wmod (index.val + 1))) 0 := by
  simp only [run, defaultStoreStep, control, defaultStoreMachine, writeMachine, Machine.push,
    exec_cons_zero, Instr.step, Machine.next, Out.ok_bind,
    List.getElem?_cons_succ, List.getElem?_cons_zero, exec_nil,
    wmod_def, Nat.add_mod, Nat.mod_mod, Nat.add_comm]

theorem defaultStoreMachine_eq (m : Machine) (parent index child : Fin W) (offset : Nat)
    (hs : parent.val + offset + index.val < W) :
    defaultStoreMachine m parent index child offset =
      writeMachine m (parent.val + offset + index.val) (.val child) := by
  unfold defaultStoreMachine
  have ha : parent.val + index.val + offset < W := by omega
  rw [wmod_of_lt ha]
  congr 1
  change parent.val + index.val + offset = parent.val + offset + index.val
  omega

private theorem loopTurn_true (rc rb : Machine → Out) (m m' : Machine)
    (hc : rc m = .ok (m.push w[1]) 0) (hb : rb m = .ok m' 0) :
    loopTurn rc rb m = .inl m' := by
  rw [loopTurn, hc]
  change (match rb m with
    | .ok m₂ 0 => Sum.inl m₂
    | .ok _ (_ + 1) => Sum.inr Out.fault
    | r => .inr r) = _
  rw [hb]

theorem defaultTurn_more {m m' : Machine} {parent total index : Fin W}
    {offset : Nat} {childCode : List Instr} (hi : index.val < total.val)
    (hb : run (defaultChildrenBody offset childCode) (control m parent total index) = .ok m' 0) :
    loopTurn (run childrenCondition) (run (defaultChildrenBody offset childCode))
      (control m parent total index) = .inl m' := by
  have hc : run childrenCondition (control m parent total index) =
      .ok ((control m parent total index).push w[1]) 0 := by
    simpa only [hi, decide_true, bword, if_true] using childrenCondition_run m parent total index
  exact loopTurn_true _ _ _ _ hc hb

theorem defaultTurn_done (m : Machine) (parent total : Fin W) (offset : Nat) (childCode : List Instr) :
    loopTurn (run childrenCondition) (run (defaultChildrenBody offset childCode))
      (control m parent total total) = .inr (.ok (control m parent total total) 0) := by
  have hc : run childrenCondition (control m parent total total) =
      .ok ((control m parent total total).push w[0]) 0 := by
    simpa only [Nat.lt_irrefl, decide_false, bword, Bool.false_eq_true, if_false] using
      childrenCondition_run m parent total total
  rw [loopTurn, hc]
  rfl

end Solidity.Evm.Memory.Objects
