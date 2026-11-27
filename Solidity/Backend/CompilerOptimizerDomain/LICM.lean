import Solidity.Backend.AbiWorld.PublicCompilerTotal
import Solidity.Optimizer.LICM

/-! Accepted-domain preservation for the actual loop-invariant code-motion pass,
a prerequisite of `Solidity.Goals.compilerOptimizedEndpoint`. -/
namespace Solidity.Backend.CompilerOptimizerDomain
open Solidity Solidity.Optimizer.ConstFold
open Solidity.Backend.AbiWorld.PublicCompilerTotal
variable {C : Contract}

theorem hoist_ok {Γ Δ : Ctx} {K : Kinds} (a : LoopAnn C Γ)
    {c : Val C Γ .bool} {body : Solidity.Prog C Γ Δ}
    (hc : ValOk c) (hb : ProgOk K body) : StmtOk K (hoist a c body) K := by
  unfold hoist
  split
  · next q x e rest hs =>
    split
    · rw [splitAssign?_eq hs] at hb
      cases hb with
      | cons ha hr =>
        cases ha with
        | assignLocal _ he =>
          exact .ite hc (.cons (.assignLocal x he) (.cons (.loop a hc hr) .nil)) .nil
    · exact .loop a hc hb
  · exact .loop a hc hb

mutual
theorem stmt_licm_ok : {Γ Γ' : Ctx} → {K K' : Kinds} → {s : Solidity.Stmt C Γ Γ'} →
    StmtOk K s K' → StmtOk K (Stmt.licm s) K'
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
  | _, _, _, _, _, .ite hc ht he => .ite hc (prog_licm_ok ht) (prog_licm_ok he)
  | _, _, _, _, _, .block hb => .block (prog_licm_ok hb)
  | _, _, _, _, _, .loop a hc hb => hoist_ok a hc (prog_licm_ok hb)

theorem prog_licm_ok : {Γ Δ : Ctx} → {K : Kinds} → {P : Solidity.Prog C Γ Δ} →
    ProgOk K P → ProgOk K (Prog.licm P)
  | _, _, _, _, .nil => .nil
  | _, _, _, _, .cons hs hp => .cons (stmt_licm_ok hs) (prog_licm_ok hp)
end

end Solidity.Backend.CompilerOptimizerDomain
