import Solidity.Yul.Words
import Solidity.Evm.Signed

/-! Agreement with the existing target machine for signed word operations.
No compiler lowering, byte-memory or external EVM agreement is claimed. -/
namespace Solidity.Yul.EvmSigned

/-- EVM.toWord uses one wrap for negative inputs, so its real lower bound
is required. Pure signed operations below discharge it from word ranges. -/
theorem iword_eq_sword : ∀ (n : Int), -(Solidity.Evm.W : Int) ≤ n → Solidity.Yul.iword n = Solidity.Evm.sword n := by
  intro n low
  apply Fin.ext
  change ((n % (2^256 : Int)).toNat % Solidity.Evm.W) =
    (Solidity.Evm.toWord n % Solidity.Evm.W)
  have power : (2^256 : Int) = (Solidity.Evm.W : Int) := by
    simpa only [Solidity.Evm.W] using (Int.natCast_pow 2 256).symm
  rw [power]
  change ((n % (Solidity.Evm.W : Int)).toNat % Solidity.Evm.W) =
    (Solidity.Evm.toWord n % Solidity.Evm.W)
  unfold Solidity.Evm.toWord
  split
  · next nonneg =>
      rw [Int.toNat_emod nonneg (Int.natCast_nonneg _)]
      simp only [Int.toNat_natCast,Nat.mod_mod]
  · next neg =>
      have shifted : 0 ≤ n + (Solidity.Evm.W : Int) := by omega
      rw [Int.emod_eq_add_self_emod,Int.toNat_emod shifted (Int.natCast_nonneg _)]
      simp only [Int.toNat_natCast,Nat.mod_mod]


theorem signed_eq_sgn : ∀ (x : Solidity.Yul.Word), Solidity.Yul.signed x = Solidity.Evm.sgn x.val := by
  intro x
  unfold Solidity.Yul.signed Solidity.Evm.sgn Solidity.Evm.H
  have power : (2^256 : Int) = (Solidity.Evm.W : Int) := by
    simpa only [Solidity.Evm.W] using (Int.natCast_pow 2 256).symm
  rw [power]

def args (x y : Word) (i : Fin 2) : Word := if i = 0 then x else y


theorem eval_sdiv : ∀ (x y : Solidity.Yul.Word),
 Solidity.Yul.Pure.eval .sdiv (Solidity.Yul.EvmSigned.args x y) =
 if y.val = 0 then Solidity.Yul.word 0 else
 Solidity.Evm.sword ((Solidity.Evm.sgn x.val).tdiv (Solidity.Evm.sgn y.val)) := by
  intro x y
  change (if y.val = 0 then Solidity.Yul.word 0 else
    Solidity.Yul.iword ((Solidity.Yul.signed x).tdiv (Solidity.Yul.signed y))) = _
  by_cases zero : y.val = 0
  · simp only [if_pos zero]
  · simp only [if_neg zero,Solidity.Yul.EvmSigned.signed_eq_sgn]
    exact Solidity.Yul.EvmSigned.iword_eq_sword _
      (Solidity.Evm.tdiv_sgn_range x.isLt (Solidity.Evm.sgn y.val)).1

theorem eval_smod : ∀ (x y : Solidity.Yul.Word),
 Solidity.Yul.Pure.eval .smod (Solidity.Yul.EvmSigned.args x y) =
 if y.val = 0 then Solidity.Yul.word 0 else
 Solidity.Evm.sword ((Solidity.Evm.sgn x.val).tmod (Solidity.Evm.sgn y.val)) := by
  intro x y
  change (if y.val = 0 then Solidity.Yul.word 0 else
    Solidity.Yul.iword ((Solidity.Yul.signed x).tmod (Solidity.Yul.signed y))) = _
  by_cases zero : y.val = 0
  · simp only [if_pos zero]
  · simp only [if_neg zero,Solidity.Yul.EvmSigned.signed_eq_sgn]
    apply Solidity.Yul.EvmSigned.iword_eq_sword
    have nonzero : Solidity.Evm.sgn y.val ≠ 0 :=
      fun bad => zero ((Solidity.Evm.sgn_eq_zero y.isLt).mp bad)
    have bound := Solidity.Evm.tmod_range (x := Solidity.Evm.sgn x.val) (Solidity.Evm.sgn_range y.isLt) nonzero
    have halves := Solidity.Evm.W_eq
    omega

theorem eval_slt : ∀ (x y : Solidity.Yul.Word),
 Solidity.Yul.Pure.eval .slt (Solidity.Yul.EvmSigned.args x y) =
 Solidity.Evm.bword (decide (Solidity.Evm.sgn x.val < Solidity.Evm.sgn y.val)) := by
  intro x y
  change Solidity.Yul.truth (decide (Solidity.Yul.signed x < Solidity.Yul.signed y)) = _
  rw [Solidity.Yul.EvmSigned.signed_eq_sgn x,Solidity.Yul.EvmSigned.signed_eq_sgn y]
  generalize decide (Solidity.Evm.sgn x.val < Solidity.Evm.sgn y.val) = choice
  cases choice <;> rfl

theorem eval_sgt : ∀ (x y : Solidity.Yul.Word),
 Solidity.Yul.Pure.eval .sgt (Solidity.Yul.EvmSigned.args x y) =
 Solidity.Evm.bword (decide (Solidity.Evm.sgn y.val < Solidity.Evm.sgn x.val)) := by
  intro x y
  change Solidity.Yul.truth (decide (Solidity.Yul.signed y < Solidity.Yul.signed x)) = _
  rw [Solidity.Yul.EvmSigned.signed_eq_sgn y,Solidity.Yul.EvmSigned.signed_eq_sgn x]
  generalize decide (Solidity.Evm.sgn y.val < Solidity.Evm.sgn x.val) = choice
  cases choice <;> rfl


/-- Two typed operands on top; every other machine field and tail is preserved. -/
theorem step_sdiv : ∀ (machine : Solidity.Evm.Machine) (x y : Solidity.Yul.Word) (tail : List Solidity.Evm.Word),
 Solidity.Evm.Instr.step .sdiv { machine with stack := .val x :: .val y :: tail } =
 .ok { machine with stack := .val (Solidity.Yul.Pure.eval .sdiv
   (Solidity.Yul.EvmSigned.args x y)) :: tail } 0 := by
  intro machine x y tail
  change (Solidity.Evm.Out.ok { machine with stack := .val (if y.val = 0 then Solidity.Yul.word 0 else Solidity.Evm.sword ((Solidity.Evm.sgn x.val).tdiv (Solidity.Evm.sgn y.val))) :: tail } 0) = _
  rw [Solidity.Yul.EvmSigned.eval_sdiv]

/-- Two typed operands on top; every other machine field and tail is preserved. -/
theorem step_smod : ∀ (machine : Solidity.Evm.Machine) (x y : Solidity.Yul.Word) (tail : List Solidity.Evm.Word),
 Solidity.Evm.Instr.step .smod { machine with stack := .val x :: .val y :: tail } =
 .ok { machine with stack := .val (Solidity.Yul.Pure.eval .smod
   (Solidity.Yul.EvmSigned.args x y)) :: tail } 0 := by
  intro machine x y tail
  change (Solidity.Evm.Out.ok { machine with stack := .val (if y.val = 0 then Solidity.Yul.word 0 else Solidity.Evm.sword ((Solidity.Evm.sgn x.val).tmod (Solidity.Evm.sgn y.val))) :: tail } 0) = _
  rw [Solidity.Yul.EvmSigned.eval_smod]

/-- Two typed operands on top; every other machine field and tail is preserved. -/
theorem step_slt : ∀ (machine : Solidity.Evm.Machine) (x y : Solidity.Yul.Word) (tail : List Solidity.Evm.Word),
 Solidity.Evm.Instr.step .slt { machine with stack := .val x :: .val y :: tail } =
 .ok { machine with stack := .val (Solidity.Yul.Pure.eval .slt
   (Solidity.Yul.EvmSigned.args x y)) :: tail } 0 := by
  intro machine x y tail
  change (Solidity.Evm.Out.ok { machine with stack := .val (Solidity.Evm.bword (decide (Solidity.Evm.sgn x.val < Solidity.Evm.sgn y.val))) :: tail } 0) = _
  rw [Solidity.Yul.EvmSigned.eval_slt]

/-- Two typed operands on top; every other machine field and tail is preserved. -/
theorem step_sgt : ∀ (machine : Solidity.Evm.Machine) (x y : Solidity.Yul.Word) (tail : List Solidity.Evm.Word),
 Solidity.Evm.Instr.step .sgt { machine with stack := .val x :: .val y :: tail } =
 .ok { machine with stack := .val (Solidity.Yul.Pure.eval .sgt
   (Solidity.Yul.EvmSigned.args x y)) :: tail } 0 := by
  intro machine x y tail
  change (Solidity.Evm.Out.ok { machine with stack := .val (Solidity.Evm.bword (decide (Solidity.Evm.sgn y.val < Solidity.Evm.sgn x.val))) :: tail } 0) = _
  rw [Solidity.Yul.EvmSigned.eval_sgt]

end Solidity.Yul.EvmSigned
