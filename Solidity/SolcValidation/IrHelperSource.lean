import Solidity.SolcValidation.IrHelperSteps
import Solidity.SolcValidation.IrExpSim
import Solidity.Semantics.Ops

/-!
# solc's checked helpers against the source operators

The runtime definition of a checked `uint256` operator in the source semantics
is `Solidity.BinOp.evalNum .uint … op` (`Semantics/Ops.lean`): the integer result,
or `none` (a revert) when it leaves the type's range. Here the imported solc
helpers (`SolcValidation/IrHelperSim.lean`) are matched to it: the helper
returns exactly the source value when the source operator succeeds, and runs
solc's `Panic(0x11)` sequence exactly when the source operator reverts. This is
the helper-level simulation of T02; the relation of the source's revert to the
panic's return data is G01's (not yet frozen) and is not asserted here.

Covered: `checked_add_t_uint256`, `checked_sub_t_uint256` and
`checked_mul_t_uint256` at their call sites (`uint` `+`, `-`, `*`), and the body
of `checked_div_t_int256` (`int` `/`, words read as two's complement by
`Yul.signed`; `tdiv_inRange` is the source's range fact behind solc's
`min / -1` test), and the body of `checked_exp_t_uint256_t_uint256` (`uint` `**`).
-/
namespace Solidity.SolcValidation.IrSyntax
open Solidity.SolcValidation

/-- The source's checked `uint` addition on two words. -/
def sourceAdd (x y : Word) : Option Int :=
  (Solidity.BinOp.evalNum .uint rfl (x.val : Int) (y.val : Int) .add rfl).map Subtype.val

/-- The source's checked `uint` multiplication on two words. -/
def sourceMul (x y : Word) : Option Int :=
  (Solidity.BinOp.evalNum .uint rfl (x.val : Int) (y.val : Int) .mul rfl).map Subtype.val

/-- Stated by `rw`, not `rfl`, so the kernel never unfolds `ofInt?`'s `2^256`
range test (Gate G0's pitfall; `Evm/SimLemmas.lean` does the same). -/
private theorem some_bind' {α β : Type} (a : α) (f : α → Option β) : (some a).bind f = f a := by
  rw [Option.bind]

private theorem ofInt_uint_in {n : Int} (h : PrimTy.uint.inRange n = true) :
    (PrimTy.uint.ofInt? n).map Subtype.val = some n := by
  simp only [PrimTy.ofInt?, dif_pos h, Option.map_some]

private theorem ofInt_uint_out {n : Int} (h : ¬ PrimTy.uint.inRange n = true) :
    (PrimTy.uint.ofInt? n).map Subtype.val = none := by
  simp only [PrimTy.ofInt?, dif_neg h, Option.map_none]

private theorem uint_inRange (n : Nat) : PrimTy.uint.inRange (n : Int) = true ↔ n < 2 ^ 256 := by
  simp only [PrimTy.inRange, decide_eq_true_eq]
  omega

theorem sourceAdd_eq (x y : Word) :
    sourceAdd x y = if x.val + y.val < 2 ^ 256 then some ((x.val + y.val : Nat) : Int) else none := by
  simp only [sourceAdd, Solidity.BinOp.evalNum, Solidity.BinOp.arithInt, some_bind', ← Int.natCast_add]
  by_cases fits : x.val + y.val < 2 ^ 256
  · rw [if_pos fits, ofInt_uint_in ((uint_inRange _).mpr fits)]
  · rw [if_neg fits, ofInt_uint_out (fun h => fits ((uint_inRange _).mp h))]

theorem sourceMul_eq (x y : Word) :
    sourceMul x y = if x.val * y.val < 2 ^ 256 then some ((x.val * y.val : Nat) : Int) else none := by
  simp only [sourceMul, Solidity.BinOp.evalNum, Solidity.BinOp.arithInt, some_bind', ← Int.natCast_mul]
  by_cases fits : x.val * y.val < 2 ^ 256
  · rw [if_pos fits, ofInt_uint_in ((uint_inRange _).mpr fits)]
  · rw [if_neg fits, ofInt_uint_out (fun h => fits ((uint_inRange _).mp h))]

/-- The source's checked `uint` subtraction on two words. -/
def sourceSub (x y : Word) : Option Int :=
  (Solidity.BinOp.evalNum .uint rfl (x.val : Int) (y.val : Int) .sub rfl).map Subtype.val

theorem sourceSub_eq (x y : Word) :
    sourceSub x y = if y.val ≤ x.val then some ((x.val - y.val : Nat) : Int) else none := by
  simp only [sourceSub, Solidity.BinOp.evalNum, Solidity.BinOp.arithInt, some_bind']
  by_cases le : y.val ≤ x.val
  · rw [if_pos le, ← Int.ofNat_sub le, ofInt_uint_in ((uint_inRange _).mpr (by omega))]
  · rw [if_neg le, ofInt_uint_out]
    simp only [PrimTy.inRange, decide_eq_true_eq]
    omega

/-- Truncated division of two `int256` values stays in range except for `min / -1`. -/
theorem tdiv_inRange (a b : Int) (ha : -((2 ^ 255 : Nat) : Int) ≤ a ∧ a < ((2 ^ 255 : Nat) : Int))
    (b0 : b ≠ 0) :
    PrimTy.int.inRange (a.tdiv b) = true ↔ ¬ (a = -((2 ^ 255 : Nat) : Int) ∧ b = -1) := by
  simp only [PrimTy.inRange, decide_eq_true_eq]
  have hb : b = (b.natAbs : Int) ∨ b = -(b.natAbs : Int) := Int.natAbs_eq b
  by_cases one : b.natAbs = 1
  · rw [one] at hb
    rcases hb with h | h
    · rw [h, Int.ofNat_one, Int.tdiv_one]
      omega
    · rw [h, Int.ofNat_one, Int.tdiv_neg, Int.tdiv_one]
      omega
  · have two : 2 ≤ b.natAbs := by
      have : b.natAbs ≠ 0 := fun z => b0 (Int.natAbs_eq_zero.mp z)
      omega
    have q : (a.tdiv b).natAbs ≤ a.natAbs / 2 := by
      rw [Int.natAbs_tdiv]
      exact Nat.div_le_div_left two (by decide)
    have aa : a.natAbs ≤ 2 ^ 255 := by
      rcases Int.natAbs_eq a with h | h <;> omega
    have qq : (a.tdiv b).natAbs ≤ 2 ^ 254 := by omega
    constructor
    · intro _ ⟨am, bm⟩
      rw [bm] at one
      exact one rfl
    · intro _
      rcases Int.natAbs_eq (a.tdiv b) with h | h <;> omega

section Signed
open Solidity.Yul

theorem signed_range (x : Word) :
    -((2 ^ 255 : Nat) : Int) ≤ signed x ∧ signed x < ((2 ^ 255 : Nat) : Int) := by
  have hx : x.val < 2 ^ 256 := x.isLt
  simp only [signed]
  split <;> omega

theorem signed_zero (x : Word) : signed x = 0 ↔ x.val = 0 := by
  have hx : x.val < 2 ^ 256 := x.isLt
  simp only [signed]
  split <;> omega

theorem signed_min (x : Word) : signed x = -((2 ^ 255 : Nat) : Int) ↔ x.val = 2 ^ 255 := by
  have hx : x.val < 2 ^ 256 := x.isLt
  simp only [signed]
  split <;> omega

theorem signed_neg_one (x : Word) : signed x = -1 ↔ x.val = 2 ^ 256 - 1 := by
  have hx : x.val < 2 ^ 256 := x.isLt
  simp only [signed]
  split <;> omega

/-- The owner's `sdiv` (stated by `rfl` on its definition). -/
theorem pure_sdiv (xs : Fin 2 → Word) :
    Pure.eval .«sdiv» xs = if (xs 1).val = 0 then word 0 else iword ((signed (xs 0)).tdiv (signed (xs 1))) := rfl
end Signed

private theorem none_bind' {α β : Type} (f : α → Option β) : (none : Option α).bind f = none := by
  rw [Option.bind]

private theorem ofInt_int_in {n : Int} (h : PrimTy.int.inRange n = true) :
    (PrimTy.int.ofInt? n).map Subtype.val = some n := by
  simp only [PrimTy.ofInt?, dif_pos h, Option.map_some]

private theorem ofInt_int_out {n : Int} (h : ¬ PrimTy.int.inRange n = true) :
    (PrimTy.int.ofInt? n).map Subtype.val = none := by
  simp only [PrimTy.ofInt?, dif_neg h, Option.map_none]

/-- The source's checked `int` division on two words (read as two's complement). The
reading of a word as a source value (`x.val` for `uint`, `Yul.signed` for `int`) is
chosen here; the source↔word relation itself is G01's. -/
def sourceDiv (x y : Word) : Option Int :=
  (Solidity.BinOp.evalNum .int rfl (Solidity.Yul.signed x) (Solidity.Yul.signed y) .div rfl).map Subtype.val

theorem sourceDiv_eq (x y : Word) :
    sourceDiv x y = if y.val = 0 ∨ (x.val = 2 ^ 255 ∧ y.val = 2 ^ 256 - 1) then none
      else some ((Solidity.Yul.signed x).tdiv (Solidity.Yul.signed y)) := by
  simp only [sourceDiv, Solidity.BinOp.evalNum, Solidity.BinOp.arithInt]
  by_cases y0 : y.val = 0
  · rw [if_pos ((signed_zero y).mpr y0), none_bind', Option.map_none, if_pos (Or.inl y0)]
  · have sy : ¬ Solidity.Yul.signed y = 0 := fun h => y0 ((signed_zero y).mp h)
    rw [if_neg sy, some_bind']
    by_cases m : x.val = 2 ^ 255 ∧ y.val = 2 ^ 256 - 1
    · rw [if_pos (Or.inr m), ofInt_int_out]
      rw [tdiv_inRange _ _ (signed_range x) sy]
      exact fun h => h ⟨(signed_min x).mpr m.1, (signed_neg_one y).mpr m.2⟩
    · have nm : ¬ (y.val = 0 ∨ (x.val = 2 ^ 255 ∧ y.val = 2 ^ 256 - 1)) := fun h => h.elim y0 m
      rw [if_neg nm, ofInt_int_in]
      rw [tdiv_inRange _ _ (signed_range x) sy]
      exact fun h => m ⟨(signed_min x).mp h.1, (signed_neg_one y).mp h.2⟩

/-- The source's checked `uint` exponentiation on two words. -/
def sourceExp (x y : Word) : Option Int :=
  (Solidity.BinOp.evalNum .uint rfl (x.val : Int) (y.val : Int) .pow rfl).map Subtype.val

theorem sourceExp_eq (x y : Word) :
    sourceExp x y = if x.val ^ y.val < 2 ^ 256 then some ((x.val ^ y.val : Nat) : Int) else none := by
  simp only [sourceExp, Solidity.BinOp.evalNum, Solidity.BinOp.arithInt]
  rw [if_neg (by omega), some_bind', Int.toNat_natCast, ← Int.natCast_pow]
  by_cases fits : x.val ^ y.val < 2 ^ 256
  · rw [if_pos fits, ofInt_uint_in ((uint_inRange _).mpr fits)]
  · rw [if_neg fits, ofInt_uint_out (fun h => fits ((uint_inRange _).mp h))]

section
variable {σ : Type} (M : Machine σ) (ctx : ObjectCtx)

/-- Simulation of `checked_add_t_uint256` by the source's checked `+` at
`uint`: a source value is returned as that word; a source revert is solc's
`Panic(0x11)` sequence. For every machine, state and pair of words. -/
theorem checked_add_matches_source (k : Nat) (x y : Word) (s : σ) :
    match sourceAdd x y with
    | some v => evalExpr M ctx (k + 20) helperEnv addCall (argVals x y) s =
        .ok (s, fun _ => Solidity.Yul.word v.toNat)
    | none => evalExpr M ctx (k + 20) helperEnv addCall (argVals x y) s =
        (fun s => (s, fun _ => Solidity.Yul.word (x.val + y.val))) <$> panicRun M 0x11 s := by
  rw [sourceAdd_eq, checked_add_sim]
  by_cases fits : x.val + y.val < 2 ^ 256
  · simp only [fits, if_true, Int.toNat_natCast]
  · simp only [fits, if_false]

/-- Simulation of `checked_mul_t_uint256`'s body by the source's checked `*`
at `uint`, from the body's entry values. -/
theorem checked_mul_matches_source (k : Nat) (x y : Word) (s : σ) :
    match sourceMul x y with
    | some v => evalBlock M ctx (k + 30) helperEnv bodyMul (.cons x (.cons y (.cons 0 .nil))) s =
        .ok (s, .cons x (.cons y (.cons (Solidity.Yul.word v.toNat) .nil)), .normal)
    | none => evalBlock M ctx (k + 30) helperEnv bodyMul (.cons x (.cons y (.cons 0 .nil))) s =
        (fun s => (s, .cons x (.cons y (.cons (Solidity.Yul.word (x.val * y.val)) .nil)), .normal)) <$>
          panicRun M 0x11 s := by
  rw [sourceMul_eq, checked_mul_body]
  by_cases fits : x.val * y.val < 2 ^ 256
  · simp only [fits, if_true, Int.toNat_natCast]
  · simp only [fits, if_false]

/-- Simulation of `checked_sub_t_uint256` by the source's checked `-` at `uint`. -/
theorem checked_sub_matches_source (k : Nat) (x y : Word) (s : σ) :
    match sourceSub x y with
    | some v => evalExpr M ctx (k + 34) helperEnv subCall (argVals x y) s =
        .ok (s, fun _ => Solidity.Yul.word v.toNat)
    | none => evalExpr M ctx (k + 34) helperEnv subCall (argVals x y) s =
        (fun s => (s, fun _ => Solidity.Yul.Pure.eval .«sub» (word2 x y))) <$> panicRun M 0x11 s := by
  rw [sourceSub_eq, checked_sub_sim]
  by_cases le : y.val ≤ x.val
  · simp only [le, if_true, Int.toNat_natCast]
  · simp only [le, if_false]

/-- Simulation of `checked_mul_t_uint256` at its call site by the source's checked `*` at `uint`. -/
theorem checked_mul_call_matches_source (k : Nat) (x y : Word) (s : σ) :
    match sourceMul x y with
    | some v => evalExpr M ctx (k + 34) helperEnv mulCall (argVals x y) s =
        .ok (s, fun _ => Solidity.Yul.word v.toNat)
    | none => evalExpr M ctx (k + 34) helperEnv mulCall (argVals x y) s =
        (fun s => (s, fun _ => Solidity.Yul.word (x.val * y.val))) <$> panicRun M 0x11 s := by
  rw [sourceMul_eq, checked_mul_sim]
  by_cases fits : x.val * y.val < 2 ^ 256
  · simp only [fits, if_true, Int.toNat_natCast]
  · simp only [fits, if_false]

/-- Simulation of `checked_div_t_int256`'s body by the source's checked `/` at
`int`: a source value is returned (as its two's-complement word); a source
revert is solc's panic sequence, `Panic(0x12)` for a zero divisor and
`Panic(0x11)` for `min / -1`, after which (on a machine whose `revert` returns)
the body finishes with `sdiv`. -/
theorem checked_div_matches_source (k : Nat) (x y : Word) (s : σ) :
    match sourceDiv x y with
    | some v => evalBlock M ctx (k + 60) helperEnv bodyDiv (.cons x (.cons y (.cons 0 .nil))) s =
        .ok (s, .cons x (.cons y (.cons (Solidity.Yul.iword v) .nil)), .normal)
    | none => evalBlock M ctx (k + 60) helperEnv bodyDiv (.cons x (.cons y (.cons 0 .nil))) s =
        panicRun M (if y.val = 0 then 0x12 else 0x11) s >>= fun s =>
          .ok (s, .cons x (.cons y (.cons (Solidity.Yul.Pure.eval .«sdiv» (word2 x y)) .nil)), .normal) := by
  rw [sourceDiv_eq, checked_div_body]
  by_cases y0 : y.val = 0
  · have c1 : (y.val == 0) = true := beq_iff_eq.mpr y0
    have c2 : (x.val == 2 ^ 255 && y.val == 2 ^ 256 - 1) = false := by
      rw [Bool.and_eq_false_iff]
      exact Or.inr (beq_eq_false_iff_ne.mpr (by rw [y0]; decide))
    rw [if_pos (Or.inl y0)]
    dsimp only
    rw [if_pos y0, panicIf, if_pos c1]
    simp only [panicIf, c2, Bool.false_eq_true, ↓reduceIte, run_ok_bind]
  · have c1 : (y.val == 0) = false := beq_eq_false_iff_ne.mpr y0
    by_cases m : x.val = 2 ^ 255 ∧ y.val = 2 ^ 256 - 1
    · have c2 : (x.val == 2 ^ 255 && y.val == 2 ^ 256 - 1) = true := by
        rw [Bool.and_eq_true, beq_iff_eq, beq_iff_eq]
        exact m
      rw [if_pos (Or.inr m)]
      dsimp only
      rw [if_neg y0, panicIf, c1, if_neg Bool.false_ne_true, run_ok_bind, panicIf, if_pos c2]
    · have c2 : (x.val == 2 ^ 255 && y.val == 2 ^ 256 - 1) = false := by
        rw [Bool.and_eq_false_iff, beq_eq_false_iff_ne, beq_eq_false_iff_ne]
        exact Classical.byCases (fun h : x.val = 2 ^ 255 => Or.inr fun h' => m ⟨h, h'⟩) Or.inl
      have nm : ¬ (y.val = 0 ∨ (x.val = 2 ^ 255 ∧ y.val = 2 ^ 256 - 1)) := fun h => h.elim y0 m
      rw [if_neg nm]
      dsimp only
      rw [panicIf, c1, if_neg Bool.false_ne_true, run_ok_bind, panicIf, c2, if_neg Bool.false_ne_true,
        run_ok_bind, pure_sdiv, word2_one, word2_zero, if_neg y0]


/-- Simulation of `checked_exp_t_uint256_t_uint256`'s body by the source's checked `**`
at `uint`: a source value is returned as that word with no machine effect; on a source
revert the result factors through solc's `Panic(0x11)` sequence from the entry state
(on a `RevertHalts` machine it is exactly that fault: `checked_exp_overflow_halts`). -/
theorem checked_exp_matches_source (k : Nat) (x y : Word) (s : σ) :
    match sourceExp x y with
    | some v => evalBlock M ctx (k + 420) expEnv expExpU256 (.cons x (.cons y (.cons 0 .nil))) s =
        .ok (s, .cons x (.cons y (.cons (Solidity.Yul.word v.toNat) .nil)), .normal)
    | none => ∃ cont, evalBlock M ctx (k + 420) expEnv expExpU256 (.cons x (.cons y (.cons 0 .nil))) s =
        panicRun M 0x11 s >>= cont := by
  rw [sourceExp_eq]
  have h := checked_exp_body M ctx k x y s
  by_cases fits : x.val ^ y.val < 2 ^ 256
  · rw [if_pos fits]
    dsimp only
    rw [Int.toNat_natCast]
    exact h.1 fits
  · rw [if_neg fits]
    exact h.2 fits
end

end Solidity.SolcValidation.IrSyntax
