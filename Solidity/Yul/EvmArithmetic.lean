import Solidity.Yul.EvmSigned

/-! Unsigned Yul arithmetic agrees with the existing target-machine steps.
Each theorem preserves every other machine field and an arbitrary stack tail.
This is word-level correspondence, not compiler lowering or external EVM adequacy. -/
namespace Solidity.Yul.EvmArithmetic

theorem step_add : ∀ (machine : Solidity.Evm.Machine) (x y : Solidity.Yul.Word) (tail : List Solidity.Evm.Word),
 Solidity.Evm.Instr.step .add { machine with stack := .val x :: .val y :: tail } =
 .ok { machine with stack := .val (Solidity.Yul.Pure.eval .add
   (Solidity.Yul.EvmSigned.args x y)) :: tail } 0 := by
  intro machine x y tail
  rfl

theorem step_sub : ∀ (machine : Solidity.Evm.Machine) (x y : Solidity.Yul.Word) (tail : List Solidity.Evm.Word),
 Solidity.Evm.Instr.step .sub { machine with stack := .val x :: .val y :: tail } =
 .ok { machine with stack := .val (Solidity.Yul.Pure.eval .sub
   (Solidity.Yul.EvmSigned.args x y)) :: tail } 0 := by
  intro machine x y tail
  apply congrArg (fun result : Solidity.Yul.Word => Solidity.Evm.Out.ok { machine with stack := .val result :: tail } 0)
  apply Fin.ext
  change (x.val + (Solidity.Evm.W - y.val)) % Solidity.Evm.W = (x.val + Solidity.Evm.W - y.val) % Solidity.Evm.W
  have low : y.val ≤ Solidity.Evm.W := Nat.le_of_lt y.isLt
  rw [Nat.add_sub_assoc low]

theorem step_mul : ∀ (machine : Solidity.Evm.Machine) (x y : Solidity.Yul.Word) (tail : List Solidity.Evm.Word),
 Solidity.Evm.Instr.step .mul { machine with stack := .val x :: .val y :: tail } =
 .ok { machine with stack := .val (Solidity.Yul.Pure.eval .mul
   (Solidity.Yul.EvmSigned.args x y)) :: tail } 0 := by
  intro machine x y tail
  rfl

theorem step_div : ∀ (machine : Solidity.Evm.Machine) (x y : Solidity.Yul.Word) (tail : List Solidity.Evm.Word),
 Solidity.Evm.Instr.step .div { machine with stack := .val x :: .val y :: tail } =
 .ok { machine with stack := .val (Solidity.Yul.Pure.eval .div
   (Solidity.Yul.EvmSigned.args x y)) :: tail } 0 := by
  intro machine x y tail
  apply congrArg (fun result : Solidity.Yul.Word => Solidity.Evm.Out.ok { machine with stack := .val result :: tail } 0)
  apply Fin.ext
  change (if y.val = 0 then 0 else x.val / y.val) = (x.val / y.val) % Solidity.Evm.W
  by_cases zero : y.val = 0
  · simp only [zero, if_pos, Nat.div_zero, Nat.zero_mod]
  · simp only [if_neg zero]
    have bound : x.val / y.val < Solidity.Evm.W := Nat.lt_of_le_of_lt (Nat.div_le_self _ _) x.isLt
    exact (Nat.mod_eq_of_lt bound).symm

theorem step_mod : ∀ (machine : Solidity.Evm.Machine) (x y : Solidity.Yul.Word) (tail : List Solidity.Evm.Word),
 Solidity.Evm.Instr.step .mod { machine with stack := .val x :: .val y :: tail } =
 .ok { machine with stack := .val (Solidity.Yul.Pure.eval .mod
   (Solidity.Yul.EvmSigned.args x y)) :: tail } 0 := by
  intro machine x y tail
  apply congrArg (fun result : Solidity.Yul.Word => Solidity.Evm.Out.ok { machine with stack := .val result :: tail } 0)
  apply Fin.ext
  change (if y.val = 0 then 0 else x.val % y.val) = ((if y.val = 0 then Solidity.Yul.word 0 else Solidity.Yul.word (x.val % y.val))).val
  by_cases zero : y.val = 0
  · simp only [if_pos zero]; rfl
  · simp only [if_neg zero]
    exact (Nat.mod_eq_of_lt (Nat.lt_of_le_of_lt (Nat.mod_le _ _) x.isLt)).symm

/-- Two target steps with word-wrapped multiplication before division. -/
def mulDiv (machine : Solidity.Evm.Machine) (x y divisor : Word)
    (tail : List Solidity.Evm.Word) : Solidity.Evm.Out :=
  match Solidity.Evm.Instr.step .mul
      { machine with stack := .val x :: .val y :: .val divisor :: tail } with
  | .ok next 0 => Solidity.Evm.Instr.step .div next
  | _ => .fault

/-- Universal two-step correspondence, including a zero divisor. The product
is wrapped before division; this does not specify full-precision mulDiv. -/
theorem mulDiv_agrees : ∀ (machine : Solidity.Evm.Machine) (x y divisor : Solidity.Yul.Word) (tail : List Solidity.Evm.Word),
 Solidity.Yul.EvmArithmetic.mulDiv machine x y divisor tail =
 .ok { machine with stack := .val (Solidity.Yul.Pure.eval .div
   (Solidity.Yul.EvmSigned.args (Solidity.Yul.Pure.eval .mul
     (Solidity.Yul.EvmSigned.args x y)) divisor)) :: tail } 0 := by
  intro machine x y divisor tail
  simp only [Solidity.Yul.EvmArithmetic.mulDiv,
    Solidity.Yul.EvmArithmetic.step_mul, Solidity.Yul.EvmArithmetic.step_div]

end Solidity.Yul.EvmArithmetic
