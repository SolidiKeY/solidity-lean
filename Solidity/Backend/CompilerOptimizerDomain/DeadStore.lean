import Solidity.Backend.AbiWorld.PublicCompilerTotal
import Solidity.Optimizer.DeadStore

/-! Preserve the unchanged public compiler domain through actual store removal,
a prerequisite of `Solidity.Goals.compilerOptimizedEndpoint`. -/
namespace Solidity.Backend.CompilerOptimizerDomain
open Solidity Solidity.Optimizer.ConstFold
open Solidity.Backend.AbiWorld.PublicCompilerTotal
variable {C : Contract}

theorem dstoreCons_ok {Γ Γ₁ Δ : Ctx} {K K₁ : Kinds} {s : Solidity.Stmt C Γ Γ₁}
    {P : Solidity.Prog C Γ₁ Δ} (hs : StmtOk K s K₁) (hp : ProgOk K₁ P) :
    ProgOk K (dstoreCons s P) := by
  have original := hs
  cases hs <;> simp only [dstoreCons] <;> try exact .cons original hp
  split
  · exact hp
  · exact .cons original hp

mutual
theorem stmt_dstore_ok : {Γ Γ' : Ctx} → {K K' : Kinds} → {s : Solidity.Stmt C Γ Γ'} →
    StmtOk K s K' → StmtOk K (Stmt.dstore s) K'
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
  | _, _, _, _, _, .ite hc ht he => .ite hc (prog_dstore_ok ht) (prog_dstore_ok he)
  | _, _, _, _, _, .block hb => .block (prog_dstore_ok hb)
  | _, _, _, _, _, .loop a hc hb => .loop a hc (prog_dstore_ok hb)

theorem prog_dstore_ok : {Γ Δ : Ctx} → {K : Kinds} → {P : Solidity.Prog C Γ Δ} →
    ProgOk K P → ProgOk K (Prog.dstore P)
  | _, _, _, _, .nil => .nil
  | _, _, _, _, .cons hs hp => dstoreCons_ok (stmt_dstore_ok hs) (prog_dstore_ok hp)
end

end Solidity.Backend.CompilerOptimizerDomain
