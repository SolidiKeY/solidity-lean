import Solidity.Backend.CompilerOptimizerDomain.StmtFold
import Solidity.Optimizer.Simplify

/-! Accepted-domain preservation for the existing simplification pass. -/
namespace Solidity.Backend.CompilerOptimizerDomain
open Solidity Solidity.Optimizer.ConstFold
open Solidity.Backend.AbiWorld.PublicCompilerTotal
variable {C : Contract} {Γ : Ctx}

theorem castV_ok {p q : PrimTy} (h : p = q) {v : Val C Γ p}
    (hv : ValOk v) : ValOk (castV h v) := by
  cases h
  exact hv

theorem simpBin_ok (op : BinOp) (p : PrimTy) {q : PrimTy}
    (h : op.accepts p = true) (hq : op.ret p = q)
    {a b : Val C Γ p} (ha : ValOk a) (hb : ValOk b) :
    ValOk (simpBin op p h hq a b) := by
  cases op <;> cases p <;> simp only [simpBin] <;>
    repeat first | exact ha | exact hb | exact .binop _ _ _ ha hb |
      apply castV_ok | exact .lit _ _ | exact .bool _ | split

theorem val_simp_ok : {p : PrimTy} → {v : Val C Γ p} → ValOk v → ValOk v.simp
  | _, _, .lit n h => .lit n h
  | _, _, .bool b => .bool b
  | _, _, .local i => .local i
  | _, _, .env k hp hk => .env k hp hk
  | _, _, .read h => .read h
  | _, _, .binop op h hq ha hb => simpBin_ok op _ h hq (val_simp_ok ha) (val_simp_ok hb)
  | _, _, .unop op h hq ha => .unop op h hq (val_simp_ok ha)
  | _, _, .ternary hc ha hb => .ternary (val_simp_ok hc) (val_simp_ok ha) (val_simp_ok hb)
  | _, _, .len hp hb => .len hp hb

theorem prog_simplify_ok {Δ : Ctx} {K : Kinds} {P : Solidity.Prog C Γ Δ}
    (h : ProgOk K P) : ProgOk K P.simplify :=
  prog_vopt_ok simpFoldPass (fun hv => val_cfold_ok (val_simp_ok hv)) h

end Solidity.Backend.CompilerOptimizerDomain
