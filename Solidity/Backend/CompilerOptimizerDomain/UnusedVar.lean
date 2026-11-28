import Solidity.Backend.CompilerOptimizerDomain.Strengthening

/-! The actual unused-variable removal preserves the public compiler domain. -/
namespace Solidity.Backend.CompilerOptimizerDomain
open Solidity Solidity.Optimizer.ConstFold
open Solidity.Backend.AbiWorld.PublicCompilerTotal
variable {C : Contract}

theorem blockCons_ok {Γ Γ₁ Δ : Ctx} {K K₁ : Kinds} {s : Solidity.Stmt C Γ Γ₁}
    {P : Solidity.Prog C Γ₁ Δ} (hs : StmtOk K s K₁) (hp : ProgOk K₁ P) :
    StmtOk K (blockCons s P) K := by
  have original := hs
  cases hs <;> simp only [blockCons] <;> try exact .block (.cons original hp)
  all_goals
    split
    · split
      · exact .block (prog_str_ok hp _ ‹_› K)
      · exact .block (.cons original hp)
    · exact .block (.cons original hp)

theorem blockUve_ok {Γ Δ : Ctx} {K : Kinds} {P : Solidity.Prog C Γ Δ}
    (hp : ProgOk K P) : StmtOk K (blockUve P) K := by
  cases hp with
  | nil => exact .block .nil
  | cons hs hp => exact blockCons_ok hs hp

mutual
theorem stmt_uve_ok : {Γ Γ' : Ctx} → {K K' : Kinds} → {s : Solidity.Stmt C Γ Γ'} →
    StmtOk K s K' → StmtOk K (Stmt.uve s) K'
  | _, _, _, _, _, h@(.assign ..) => h
  | _, _, _, _, _, h@(.assignLocal ..) => h
  | _, _, _, _, _, h@(.declNone ..) => h
  | _, _, _, _, _, h@(.declSome ..) => h
  | _, _, _, _, _, h@(.declStorage ..) => h
  | _, _, _, _, _, h@(.declIndexed ..) => h
  | _, _, _, _, _, h@(.rebind ..) => h
  | _, _, _, _, _, h@(.rebindIndexed ..) => h
  | _, _, _, _, _, h@(.opAssign ..) => h
  | _, _, _, _, _, h@(.incDec ..) => h
  | _, _, _, _, _, h@(.require ..) => h
  | _, _, _, _, _, h@(.assert ..) => h
  | _, _, _, _, _, h@(.revert) => h
  | _, _, _, _, _, h@(.callNone ..) => h
  | _, _, _, _, _, h@(.callVal ..) => h
  | _, _, _, _, _, .ite hc ht he => .ite hc (prog_uve_ok ht) (prog_uve_ok he)
  | _, _, _, _, _, .block hb => blockUve_ok (prog_uve_ok hb)
  | _, _, _, _, _, .loop a hc hb => .loop a hc (prog_uve_ok hb)

theorem prog_uve_ok : {Γ Δ : Ctx} → {K : Kinds} → {P : Solidity.Prog C Γ Δ} →
    ProgOk K P → ProgOk K (Prog.uve P)
  | _, _, _, _, .nil => .nil
  | _, _, _, _, .cons hs hp => .cons (stmt_uve_ok hs) (prog_uve_ok hp)
end

end Solidity.Backend.CompilerOptimizerDomain
