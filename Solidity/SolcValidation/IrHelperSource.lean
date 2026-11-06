import Solidity.SolcValidation.IrHelperSim
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
end

end Solidity.SolcValidation.IrSyntax
