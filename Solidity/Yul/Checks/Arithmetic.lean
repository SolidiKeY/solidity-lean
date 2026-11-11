import Solidity.Yul.Checks.Arithmetic.Part00
import Solidity.Yul.Checks.Arithmetic.Part01
import Solidity.Yul.Checks.Arithmetic.Part02
import Solidity.Yul.Checks.Shifts
import Solidity.Yul.Checks.Bytes

/-! # Arithmetic opcodes: universal contract and vector table

The 20 clause theorems state each opcode's exact meaning over arbitrary
operands; `universal` is `OpcodeSpec.arithmetic`, and
`Solidity.Yul.opcode_eval_universal` joins it with the Shifts and Bytes proofs.
The 2,008 literal vectors of `Part00`–`Part02` form one table checked by one
aggregate kernel decision. -/

namespace Solidity.Yul.Checks.Arithmetic

/-- The family's single literal table: all 2,008 former vectors, in order. -/
noncomputable def table : List Row := rows00 ++ rows01 ++ rows02

theorem table_length : table.length = 2008 := by decide +kernel

/-- The one aggregate kernel decision for the whole family. -/
theorem table_checked : table.all Row.check = true := by decide +kernel

/-- Every row of the table evaluates to its literal expected word. -/
theorem table_holds : ∀ r ∈ table, (Pure.eval r.op (operands r.args)).val = r.out :=
  Row.holds table_checked

/-! ## Universal clauses

One theorem per clause of `OpcodeSpec.arithmetic`, in its order (`OpcodeSpec.modulus`
and `OpcodeSpec.residue` unfolded); each is definitionally that clause, and
`universal` is their conjunction. -/

theorem word_val (n : Nat) : (word n).val = n % 2 ^ 256 := rfl

theorem iword_val (z : Int) : (iword z).val = (z % 2 ^ 256).toNat := by
  unfold iword
  rw [word_val]
  apply Nat.mod_eq_of_lt
  omega

theorem truth_val (p : Prop) [Decidable p] :
    (truth (decide p)).val = (if p then 1 else 0) % 2 ^ 256 := by
  by_cases h : p <;> simp [h, truth, word_val]

theorem add_spec (xs : Fin 2 → Word) :
    (Pure.eval .«add» xs).val = ((xs 0).val + (xs 1).val) % 2 ^ 256 := rfl

theorem sub_spec (xs : Fin 2 → Word) :
    (Pure.eval .«sub» xs).val = ((xs 0).val + 2 ^ 256 - (xs 1).val) % 2 ^ 256 := rfl

theorem mul_spec (xs : Fin 2 → Word) :
    (Pure.eval .«mul» xs).val = ((xs 0).val * (xs 1).val) % 2 ^ 256 := rfl

theorem div_spec (xs : Fin 2 → Word) :
    (Pure.eval .«div» xs).val =
      (if (xs 1).val = 0 then 0 else (xs 0).val / (xs 1).val) % 2 ^ 256 := by
  change ((xs 0).val / (xs 1).val) % 2 ^ 256 = _
  split <;> simp_all

theorem mod_spec (xs : Fin 2 → Word) :
    (Pure.eval .«mod» xs).val =
      (if (xs 1).val = 0 then 0 else (xs 0).val % (xs 1).val) % 2 ^ 256 := by
  change (if (xs 1).val = 0 then word 0 else word _).val = _
  split <;> rfl

theorem sdiv_spec (xs : Fin 2 → Word) :
    (Pure.eval .«sdiv» xs).val =
      ((if (xs 1).val = 0 then 0 else (signed (xs 0)).tdiv (signed (xs 1))) % 2 ^ 256).toNat := by
  change (if (xs 1).val = 0 then word 0 else iword _).val = _
  split
  · simp [word_val]
  · exact iword_val _

theorem smod_spec (xs : Fin 2 → Word) :
    (Pure.eval .«smod» xs).val =
      ((if (xs 1).val = 0 then 0 else (signed (xs 0)).tmod (signed (xs 1))) % 2 ^ 256).toNat := by
  change (if (xs 1).val = 0 then word 0 else iword _).val = _
  split
  · simp [word_val]
  · exact iword_val _

theorem addmod_spec (xs : Fin 3 → Word) :
    (Pure.eval .«addmod» xs).val =
      (if (xs 2).val = 0 then 0 else ((xs 0).val + (xs 1).val) % (xs 2).val) % 2 ^ 256 := by
  change (if (xs 2).val = 0 then word 0 else word _).val = _
  split <;> rfl

theorem mulmod_spec (xs : Fin 3 → Word) :
    (Pure.eval .«mulmod» xs).val =
      (if (xs 2).val = 0 then 0 else ((xs 0).val * (xs 1).val) % (xs 2).val) % 2 ^ 256 := by
  change (if (xs 2).val = 0 then word 0 else word _).val = _
  split <;> rfl

theorem lt_spec (xs : Fin 2 → Word) :
    (Pure.eval .«lt» xs).val = (if (xs 0).val < (xs 1).val then 1 else 0) % 2 ^ 256 :=
  truth_val _

theorem gt_spec (xs : Fin 2 → Word) :
    (Pure.eval .«gt» xs).val = (if (xs 1).val < (xs 0).val then 1 else 0) % 2 ^ 256 :=
  truth_val _

theorem slt_spec (xs : Fin 2 → Word) :
    (Pure.eval .«slt» xs).val = (if signed (xs 0) < signed (xs 1) then 1 else 0) % 2 ^ 256 :=
  truth_val _

theorem sgt_spec (xs : Fin 2 → Word) :
    (Pure.eval .«sgt» xs).val = (if signed (xs 1) < signed (xs 0) then 1 else 0) % 2 ^ 256 :=
  truth_val _

theorem eq_spec (xs : Fin 2 → Word) :
    (Pure.eval .«eq» xs).val = (if (xs 0).val = (xs 1).val then 1 else 0) % 2 ^ 256 := by
  change (truth ((xs 0).val == (xs 1).val)).val = _
  by_cases h : (xs 0).val = (xs 1).val <;> simp [h, truth, word_val]

theorem iszero_spec (xs : Fin 1 → Word) :
    (Pure.eval .«iszero» xs).val = (if (xs 0).val = 0 then 1 else 0) % 2 ^ 256 := by
  change (truth ((xs 0).val == 0)).val = _
  by_cases h : (xs 0).val = 0 <;> simp [h, truth, word_val]

theorem not_spec (xs : Fin 1 → Word) :
    (Pure.eval .«not» xs).val = (2 ^ 256 - 1 - (xs 0).val) % 2 ^ 256 := rfl

theorem and_spec (xs : Fin 2 → Word) :
    (Pure.eval .«and» xs).val = ((xs 0).val &&& (xs 1).val) % 2 ^ 256 := rfl

theorem or_spec (xs : Fin 2 → Word) :
    (Pure.eval .«or» xs).val = ((xs 0).val ||| (xs 1).val) % 2 ^ 256 := rfl

theorem xor_spec (xs : Fin 2 → Word) :
    (Pure.eval .«xor» xs).val = ((xs 0).val ^^^ (xs 1).val) % 2 ^ 256 := rfl

theorem clz_spec (xs : Fin 1 → Word) :
    (Pure.eval .«clz» xs).val =
      (if (xs 0).val = 0 then 256 else 255 - (xs 0).val.log2) % 2 ^ 256 := rfl

/-- The whole arithmetic contract, for every input
(`Solidity.Goals.opcodeArithmetic` is a definitional wrapper of it). -/
theorem universal : OpcodeSpec.arithmetic :=
  ⟨add_spec, sub_spec, mul_spec, div_spec, mod_spec, sdiv_spec, smod_spec, addmod_spec,
    mulmod_spec, lt_spec, gt_spec, slt_spec, sgt_spec, eq_spec, iszero_spec, not_spec,
    and_spec, or_spec, xor_spec, clz_spec⟩

end Solidity.Yul.Checks.Arithmetic

/-- Every opcode of the Shifts, Arithmetic and Bytes/Powers families agrees with
its arithmetic specification on every input: `Solidity.Goals.opcodeEvalUniversal`
up to its definitional wrappers. -/
theorem Solidity.Yul.opcode_eval_universal : Solidity.Yul.OpcodeSpec.evalUniversal :=
  ⟨Checks.Shifts.universal, Checks.Arithmetic.universal, Checks.Bytes.universal⟩
