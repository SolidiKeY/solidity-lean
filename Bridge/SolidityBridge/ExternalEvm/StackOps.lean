import SolidityBridge.ExternalEvm.Dispatch
import EvmYul.EVM.Semantics
import Mathlib.Tactic.FinCases
import Mathlib.Data.Fin.VecNotation

namespace Solidity.Evm.External

def dupCode : Fin 16 → EvmYul.Operation .EVM :=
  ![.DUP1, .DUP2, .DUP3, .DUP4, .DUP5, .DUP6, .DUP7, .DUP8,
    .DUP9, .DUP10, .DUP11, .DUP12, .DUP13, .DUP14, .DUP15, .DUP16]

def swapCode : Fin 16 → EvmYul.Operation .EVM :=
  ![.SWAP1, .SWAP2, .SWAP3, .SWAP4, .SWAP5, .SWAP6, .SWAP7, .SWAP8,
    .SWAP9, .SWAP10, .SWAP11, .SWAP12, .SWAP13, .SWAP14, .SWAP15, .SWAP16]

theorem dup_dispatch (n : Fin 16) (s : EvmYul.EVM.State) (fuel : Nat) :
    EvmYul.EVM.step (fuel + 1) 0 (some (dupCode n, none)) s =
      EvmYul.dup (n.val + 1) (prepare s) := by
  fin_cases n <;> rfl

theorem swap_dispatch (n : Fin 16) (s : EvmYul.EVM.State) (fuel : Nat) :
    EvmYul.EVM.step (fuel + 1) 0 (some (swapCode n, none)) s =
      EvmYul.swap (n.val + 1) (prepare s) := by
  fin_cases n <;> rfl

private theorem take_pre {α : Type} (pre suffix : List α) (a : α) :
    (pre ++ a :: suffix).take (pre.length + 1) = pre ++ [a] := by
  rw [List.take_append, List.take_of_length_le (by omega)]
  simp only [Nat.add_sub_cancel_left, List.take_succ_cons, List.take_zero]

theorem reference_dup_pre (s : EvmYul.EVM.State)
    (pre suffix : List EvmYul.UInt256) (a : EvmYul.UInt256) :
    EvmYul.dup (pre.length + 1) {s with stack := pre ++ a :: suffix} =
      .ok (s.replaceStackAndIncrPC (a :: (pre ++ a :: suffix))) := by
  unfold EvmYul.dup
  rw [take_pre]
  simp only [List.length_append, List.length_singleton, ↓reduceIte,
    List.getLast!_eq_getLast?_getD, List.getLast?_concat, Option.getD_some]
  rfl

theorem core_dup_pre (m : Machine)
    (pre suffix : List EvmYul.UInt256) (a : EvmYul.UInt256) :
    (Instr.dup (pre.length + 1)).step
      {m with stack := (pre ++ a :: suffix).map (fun x => .val (decode x))} =
      m.next (.val (decode a) :: (pre ++ a :: suffix).map (fun x => .val (decode x))) := by
  simp only [Instr.step, Nat.add_sub_cancel, List.getElem?_map,
    List.getElem?_append_right (Nat.le_refl pre.length), Nat.sub_self,
    List.getElem?_cons_zero, Option.map_some]
  rfl

theorem reference_swap_pre (s : EvmYul.EVM.State)
    (middle suffix : List EvmYul.UInt256) (a b : EvmYul.UInt256) :
    EvmYul.swap (middle.length + 1) {s with stack := a :: (middle ++ b :: suffix)} =
      .ok (s.replaceStackAndIncrPC (b :: (middle ++ a :: suffix))) := by
  unfold EvmYul.swap
  rw [show (a :: (middle ++ b :: suffix)).take (middle.length + 1 + 1) =
      a :: (middle ++ [b]) by rw [Nat.add_assoc, List.take_succ_cons, take_pre]]
  simp only [List.length_cons, List.length_append, List.length_nil,
    Nat.add_assoc, ↓reduceIte, List.getLast!_cons_eq_getLastD, List.getLastD_concat,
    List.tail!_cons, List.dropLast_concat, List.head!_cons]
  have hd : (a :: (middle ++ b :: suffix)).drop (middle.length + 1 + 1) = suffix := by
    rw [Nat.add_assoc, List.drop_succ_cons, List.drop_append]
    simp only [List.drop_of_length_le (by omega : middle.length ≤ middle.length + 1),
      Nat.add_sub_cancel_left, List.drop_succ_cons, List.drop_zero, List.nil_append]
  rw [hd]
  simp only [List.append_assoc, List.cons_append, List.nil_append]
  rfl

theorem core_swap_pre (m : Machine)
    (middle suffix : List EvmYul.UInt256) (a b : EvmYul.UInt256) :
    (Instr.swap (middle.length + 1)).step
      {m with stack := (a :: (middle ++ b :: suffix)).map (fun x => .val (decode x))} =
      m.next ((b :: (middle ++ a :: suffix)).map (fun x => .val (decode x))) := by
  have hi : ((middle ++ b :: suffix).map (fun x => Word.val (decode x)))[middle.length]? =
      some (.val (decode b)) := by
    rw [List.getElem?_map, List.getElem?_append_right (Nat.le_refl middle.length), Nat.sub_self]
    rfl
  simp only [Instr.step, List.map_cons]
  rw [hi]
  simp only [List.map_append, List.map_cons]
  rw [List.set_append_right _ _ (by simp only [List.length_map]; omega)]
  simp only [List.length_map, Nat.sub_self, List.set_cons_zero]
  rfl

/-- Successful legal DUP opcodes preserve the complete shared observation.
The split stack makes the required operand and its depth explicit. -/
theorem dup_agrees (n : Fin 16) (m : Machine) (s : EvmYul.EVM.State)
    (h : EnvironmentAgrees m s) (pre suffix : List EvmYul.UInt256)
    (a : EvmYul.UInt256) (hlen : pre.length = n.val)
    (hs : s.stack = pre ++ a :: suffix) (fuel : Nat) :
    ResultAgrees ((Instr.dup (n.val + 1)).step m)
      (EvmYul.EVM.step (fuel + 1) 0 (some (dupCode n, none)) s) := by
  have hm : m.stack = (pre ++ a :: suffix).map (fun x => .val (decode x)) := by
    rw [h.stack, hs]
  have hc := core_dup_pre m pre suffix a
  rw [← hm, hlen] at hc
  rw [hc, dup_dispatch, ← hlen]
  have hr : EvmYul.dup (pre.length + 1) (prepare s) =
      .ok ((prepare s).replaceStackAndIncrPC (a :: (pre ++ a :: suffix))) := by
    have ht := reference_dup_pre (prepare s) pre suffix a
    have he : {prepare s with stack := pre ++ a :: suffix} = prepare s := by
      rw [← hs]
      rfl
    rw [he] at ht
    exact ht
  rw [hr]
  refine .ok ⟨?_, h.self, h.caller, h.value, h.time, h.balances⟩
  change .val (decode a) :: m.stack =
    .val (decode a) :: (pre ++ a :: suffix).map (fun x => .val (decode x))
  rw [hm]

/-- Successful SWAP1 through SWAP16, against the actual EVM dispatcher. -/
theorem swap_agrees (n : Fin 16) (m : Machine) (s : EvmYul.EVM.State)
    (h : EnvironmentAgrees m s) (middle suffix : List EvmYul.UInt256)
    (a b : EvmYul.UInt256) (hlen : middle.length = n.val)
    (hs : s.stack = a :: (middle ++ b :: suffix)) (fuel : Nat) :
    ResultAgrees ((Instr.swap (n.val + 1)).step m)
      (EvmYul.EVM.step (fuel + 1) 0 (some (swapCode n, none)) s) := by
  have hm : m.stack = (a :: (middle ++ b :: suffix)).map (fun x => .val (decode x)) := by
    rw [h.stack, hs]
  have hc := core_swap_pre m middle suffix a b
  rw [← hm, hlen] at hc
  rw [hc, swap_dispatch, ← hlen]
  have hr : EvmYul.swap (middle.length + 1) (prepare s) =
      .ok ((prepare s).replaceStackAndIncrPC (b :: (middle ++ a :: suffix))) := by
    have ht := reference_swap_pre (prepare s) middle suffix a b
    have he : {prepare s with stack := a :: (middle ++ b :: suffix)} = prepare s := by
      rw [← hs]
      rfl
    rw [he] at ht
    exact ht
  rw [hr]
  exact .ok ⟨rfl, h.self, h.caller, h.value, h.time, h.balances⟩

end Solidity.Evm.External

/-- info: 'Solidity.Evm.External.dup_agrees' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Solidity.Evm.External.dup_agrees

/-- info: 'Solidity.Evm.External.swap_agrees' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Solidity.Evm.External.swap_agrees
