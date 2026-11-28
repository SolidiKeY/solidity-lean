import Solidity.Backend.AbiWorld.PublicCompilerTotal
import Solidity.Optimizer.CSE

/-! Common-subexpression elimination preserves the accepted domain for any table. -/
namespace Solidity.Backend.CompilerOptimizerDomain
open Solidity Solidity.Optimizer.ConstFold
open Solidity.Backend.AbiWorld.PublicCompilerTotal
variable {C : Contract}

theorem val_cse_ok {Γ : Ctx} (A : List (Avail C Γ)) :
    {p : PrimTy} → {v : Val C Γ p} → ValOk v → ValOk (v.cse A)
  | _, _, h@(.lit ..) => h
  | _, _, h@(.bool ..) => h
  | _, _, h@(.local ..) => h
  | _, _, h@(.env ..) => h
  | _, _, h@(.read ..) => h
  | _, _, h@(.len ..) => h
  | _, _, .binop op h hq ha hb => by
      simp only [Val.cse]
      split
      · exact .local _
      · exact .binop op h hq (val_cse_ok A ha) (val_cse_ok A hb)
  | _, _, .unop op h hq ha => by
      simp only [Val.cse]
      split
      · exact .local _
      · exact .unop op h hq (val_cse_ok A ha)
  | _, _, .ternary hc ha hb => by
      simp only [Val.cse]
      split
      · exact .local _
      · exact .ternary (val_cse_ok A hc) (val_cse_ok A ha) (val_cse_ok A hb)

mutual
theorem stmt_cse_ok : {Γ Γ' : Ctx} → {K K' : Kinds} → {s : Solidity.Stmt C Γ Γ'} →
    StmtOk K s K' → (A : List (Avail C Γ)) → StmtOk K (Stmt.cse A s).1 K'
  | _, _, _, _, _, .assign hl hv, A => .assign hl (val_cse_ok A hv)
  | _, _, _, _, _, .assignLocal i hv, A => .assignLocal i (val_cse_ok A hv)
  | _, _, _, _, _, .declNone p x, _ => .declNone p x
  | _, _, _, _, _, .declSome p x hv, A => .declSome p x (val_cse_ok A hv)
  | _, _, _, _, _, h@(.declStorage ..), _ => h
  | _, _, _, _, _, h@(.declIndexed ..), _ => h
  | _, _, _, _, _, h@(.rebind ..), _ => h
  | _, _, _, _, _, h@(.rebindIndexed ..), _ => h
  | _, _, _, _, _, h@(.opAssign ..), _ => h
  | _, _, _, _, _, h@(.incDec ..), _ => h
  | _, _, _, _, _, .require hc, A => .require (val_cse_ok A hc)
  | _, _, _, _, _, .assert hc, A => .assert (val_cse_ok A hc)
  | _, _, _, _, _, h@(.revert), _ => h
  | _, _, _, _, _, h@(.callNone ..), _ => h
  | _, _, _, _, _, h@(.callVal ..), _ => h
  | _, _, _, _, _, .ite hc ht he, A => .ite (val_cse_ok A hc) (prog_cse_ok ht A) (prog_cse_ok he A)
  | _, _, _, _, _, .block hb, A => .block (prog_cse_ok hb A)
  | _, _, _, _, _, .loop a hc hb, _ => .loop a hc (prog_cse_ok hb [])

theorem prog_cse_ok : {Γ Δ : Ctx} → {K : Kinds} → {P : Solidity.Prog C Γ Δ} →
    ProgOk K P → (A : List (Avail C Γ)) → ProgOk K (Prog.cse A P)
  | _, _, _, _, .nil, _ => .nil
  | _, _, _, _, .cons hs hp, A => .cons (stmt_cse_ok hs A) (prog_cse_ok hp _)
end

end Solidity.Backend.CompilerOptimizerDomain
