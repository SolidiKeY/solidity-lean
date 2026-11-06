import Solidity.Backend.FunctionValues.Representation

/-! Actual Evm.run observations for the backend low-192-bit convention.
Whole-word storage is used; packed neighbouring fields require the existing
Yul layout/packing agreement. No world-call or STATICCALL claim is made. -/
namespace Solidity.Backend.FunctionValues
open Solidity.Source Solidity.Roadmap Evm

def construct (value : Source.Val D (.fn true ps rs m)) : List Instr :=
  [.push (.val (encode value))]

theorem construction (value : Source.Val D (.fn true ps rs m)) (machine : Machine) :
    run (construct value) machine = .ok { machine with stack := .val (encode value) :: machine.stack } 0 := by
  rfl

theorem memory_roundtrip (value : Source.Val D (.fn true ps rs m))
    (machine : Machine) (location : Nat) :
    run (construct value ++ [.mstore location, .mload location]) machine =
      .ok { machine with
        stack := .val (encode value) :: machine.stack
        mem := upd machine.mem location (.val (encode value)) } 0 := by
  simp only [construct, List.cons_append, List.nil_append, run, exec, Instr.step,
    Machine.next, Out.bind, upd_same]

theorem storage_roundtrip (value : Source.Val D (.fn true ps rs m))
    (machine : Machine) (slot : Slot) :
    run (construct value ++ [.push (.slot slot), .sstore, .push (.slot slot), .sload]) machine =
      .ok { machine with
        stack := .val (encode value) :: machine.stack
        store := WordStore.write machine.store slot (encode value).val } 0 := by
  simp only [construct, List.cons_append, List.nil_append, run, exec, Instr.step,
    Machine.next, Out.bind, WordStore.write_cells_same]

theorem comparison (a b : ExternalValue D ps rs m) (machine : Machine) :
    run (construct b.source ++ construct a.source ++ [.eq]) machine =
      .ok { machine with stack := .val (bword (decide (a.number = b.number))) :: machine.stack } 0 := by
  simp only [construct, List.cons_append, List.nil_append, run, exec, Instr.step,
    Machine.next, Out.bind]
  rfl

theorem source_comparison (a b : ExternalValue D ps rs m) :
    Source.cmpVal .eq a.source b.source = .ok (decide (a.number = b.number)) := by
  simp only [Source.cmpVal, source_key]
  change Except.ok (decide ((a.number : Int) = (b.number : Int))) = _
  simp only [Int.ofNat_inj]

def addressWord (value : ExternalValue D ps rs m) : Fin W :=
  ⟨(encode value.source).val / 2 ^ 32,
    Nat.lt_of_le_of_lt (Nat.div_le_self _ _) (encode value.source).isLt⟩

def selectorWord (value : ExternalValue D ps rs m) : Fin W :=
  ⟨(encode value.source).val % 2 ^ 32,
    Nat.lt_trans (Nat.mod_lt _ (by decide)) (by decide)⟩

theorem address_execution (value : ExternalValue D ps rs m) (machine : Machine) :
    run (construct value.source ++ [.push (.val ⟨32, by decide⟩), .shr]) machine =
      .ok { machine with stack := .val (addressWord value) :: machine.stack } 0 := by
  simp only [construct, List.cons_append, List.nil_append, run, exec, Instr.step,
    Machine.next, Out.bind]
  rfl

theorem selector_execution (value : ExternalValue D ps rs m) (machine : Machine) :
    run ([.push (.val ⟨2 ^ 32, by decide⟩)] ++ construct value.source ++ [.mod]) machine =
      .ok { machine with stack := .val (selectorWord value) :: machine.stack } 0 := by
  have nonzero : ¬ (2 ^ 32 : Nat) = 0 := by decide
  simp only [construct, List.cons_append, List.nil_append, run, exec, Instr.step,
    Machine.next, Out.bind, if_neg nonzero, selectorWord]

theorem address_word (value : ExternalValue D ps rs m) :
    (addressWord value).val = value.address.val := address_projection value

theorem selector_word (value : ExternalValue D ps rs m) :
    Source.beBytes 4 (selectorWord value).val = value.selector := selector_projection value

/-- Failure is a genuine EVM stack fault, not an invented Source revert. -/
theorem empty_store_fault (machine : Machine) (empty : machine.stack = []) (location : Nat) :
    run [.mstore location] machine = .fault := by
  simp only [run, exec, Instr.step, empty, Out.bind]

end Solidity.Backend.FunctionValues
