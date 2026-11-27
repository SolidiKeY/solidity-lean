import Solidity.Backend.AbiWorld.PublicCompilerTotal
import Solidity.Optimizer.DeadCode

/-! Domain preservation by the actual code and local-store removal passes,
for `Solidity.Goals.compilerOptimizedEndpoint`. No semantic premise is added. -/
namespace Solidity.Backend.CompilerOptimizerDomain
open Solidity Solidity.Optimizer.ConstFold
open Solidity.Backend.AbiWorld.PublicCompilerTotal
variable {C : Contract}

theorem cut_ok : {Γ Δ : Ctx} → {K : Kinds} → {P : Solidity.Prog C Γ Δ} →
    ProgOk K P → ProgOk K (Prog.cut P).2
  | _, _, _, _, .nil => .nil
  | _, _, _, .cons s _, .cons hs hp => by
    simp only [Prog.cut]
    by_cases h : alwaysHalts s = true
    · rw [if_pos h]
      exact .cons hs .nil
    · rw [if_neg h]
      exact .cons hs (cut_ok hp)

mutual
theorem stmt_dce_ok : {Γ Γ' : Ctx} → {K K' : Kinds} → {s : Solidity.Stmt C Γ Γ'} →
    StmtOk K s K' → StmtOk K (Stmt.dce s) K'
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
  | _, _, _, _, _, .ite hc ht he => .ite hc (cut_ok (prog_dce_ok ht)) (cut_ok (prog_dce_ok he))
  | _, _, _, _, _, .block hb => .block (cut_ok (prog_dce_ok hb))
  | _, _, _, _, _, .loop a hc hb => .loop a hc (cut_ok (prog_dce_ok hb))

theorem prog_dce_ok : {Γ Δ : Ctx} → {K : Kinds} → {P : Solidity.Prog C Γ Δ} →
    ProgOk K P → ProgOk K (Prog.dce P)
  | _, _, _, _, .nil => .nil
  | _, _, _, _, .cons hs hp => .cons (stmt_dce_ok hs) (prog_dce_ok hp)
end

theorem dseCons_ok {Γ Γ₁ Δ : Ctx} {K K₁ : Kinds} {s : Solidity.Stmt C Γ Γ₁}
    {P : Solidity.Prog C Γ₁ Δ} (hs : StmtOk K s K₁) (hp : ProgOk K₁ P) :
    ProgOk K (dseCons s P) := by
  have original := hs
  cases hs <;> simp only [dseCons] <;> try exact .cons original hp
  split
  · split
    · exact hp
    · exact .cons original hp
  · exact .cons original hp

mutual
theorem stmt_dse_ok : {Γ Γ' : Ctx} → {K K' : Kinds} → {s : Solidity.Stmt C Γ Γ'} →
    StmtOk K s K' → StmtOk K (Stmt.dse s) K'
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
  | _, _, _, _, _, .ite hc ht he => .ite hc (prog_dse_ok ht) (prog_dse_ok he)
  | _, _, _, _, _, .block hb => .block (prog_dse_ok hb)
  | _, _, _, _, _, .loop a hc hb => .loop a hc (prog_dse_ok hb)

theorem prog_dse_ok : {Γ Δ : Ctx} → {K : Kinds} → {P : Solidity.Prog C Γ Δ} →
    ProgOk K P → ProgOk K (Prog.dse P)
  | _, _, _, _, .nil => .nil
  | _, _, _, _, .cons hs hp => dseCons_ok (stmt_dse_ok hs) (prog_dse_ok hp)
end

end Solidity.Backend.CompilerOptimizerDomain
