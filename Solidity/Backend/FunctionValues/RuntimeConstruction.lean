import Solidity.Backend.FunctionValues.Controls

/-! Runtime packing from two operands, as distinct from pushing a preencoded
constant. This is a source-value representation theorem, not Source expression
lowering, ABI alignment, or dynamic external-call admission. -/
namespace Solidity.Backend.FunctionValues
open Solidity.Source Solidity.Roadmap Evm

def runtimeAddress (value : ExternalValue D ps rs m) : Fin W :=
  ⟨value.address.val, Nat.lt_of_lt_of_le value.address.isLt (by decide)⟩

def runtimeSelector (value : ExternalValue D ps rs m) : Fin W :=
  ⟨Source.bytesNat value.selector, by
    have bound := Yul.Views.scalar_beValue_bound value.selector
    rw [value.selector_length] at bound
    exact Nat.lt_trans bound (by decide)⟩

/-- Address on top, selector beneath; code is independent of both inputs. -/
def packCode : List Instr := [.push (.val ⟨2 ^ 32, by decide⟩), .mul, .add]

private theorem pack_words (address selector : Fin W) (machine : Machine)
    (tail : List Evm.Word)
    (inputs : machine.stack = .val address :: .val selector :: tail) :
    run packCode machine = .ok { machine with
      stack := .val (wmod ((wmod (2 ^ 32 * address.val)).val + selector.val)) :: tail } 0 := by
  simp only [packCode, run, exec, Instr.step, Machine.next, Out.bind, inputs]

theorem pack_run (value : ExternalValue D ps rs m) (machine : Machine)
    (tail : List Evm.Word)
    (inputs : machine.stack = .val (runtimeAddress value) :: .val (runtimeSelector value) :: tail) :
    run packCode machine =
      .ok { machine with stack := .val (encode value.source) :: tail } 0 := by
  have total : value.address.val * 2 ^ 32 + Source.bytesNat value.selector < W :=
    (encode value.source).isLt
  have shifted : 2 ^ 32 * value.address.val < W := by omega
  have packed : wmod ((wmod (2 ^ 32 * (runtimeAddress value).val)).val +
      (runtimeSelector value).val) = encode value.source := by
    apply Fin.ext
    change (2 ^ 32 * value.address.val % W + Source.bytesNat value.selector) % W = _
    rw [Nat.mod_eq_of_lt shifted, Nat.mul_comm (2 ^ 32), Nat.mod_eq_of_lt total]
    rfl
  rw [pack_words _ _ machine tail inputs, packed]

theorem runtime_inputs_canonical (value : ExternalValue D ps rs m) :
    (runtimeAddress value).val < 2 ^ 160 ∧ (runtimeSelector value).val < 2 ^ 32 := by
  constructor
  · exact value.address.isLt
  · have bound := Yul.Views.scalar_beValue_bound value.selector
    rw [value.selector_length] at bound
    exact bound

namespace Controls

def runtimeInputs : Machine := { Machine.init with
  stack := [.val (runtimeAddress sample), .val (runtimeSelector sample)] }

theorem runtime_positive : run packCode runtimeInputs =
    .ok { runtimeInputs with stack := [.val (encode sample.source)] } 0 :=
  pack_run sample runtimeInputs [] rfl

theorem runtime_source_value : Represents sample.source (encode sample.source) :=
  encode_represents sample

/-- Missing selector is an actual target stack fault, not a Source revert. -/
theorem runtime_underflow : run packCode { Machine.init with
    stack := [.val (runtimeAddress sample)] } = .fault := by
  simp only [packCode, run, exec, Instr.step, Machine.next, Out.bind]

end Controls
end Solidity.Backend.FunctionValues
