import Solidity.Backend.CompilerOptimizerDomain.Weakening
import Solidity.Optimizer.Inline

/-! Accepted-domain preservation for the actual inlining pass. -/
namespace Solidity.Backend.CompilerOptimizerDomain
open Solidity Solidity.Optimizer.ConstFold
open Solidity.Backend.AbiWorld.PublicCompilerTotal
variable {C : Contract}

/-- The original frame occupies the all-plain prefix of the enlarged frame. -/
theorem kindsWk_top (Γ ps : Ctx) (K : Kinds) :
    KindsWk (thinTop Γ ps) [] (List.replicate ps.length false ++ K) := by
  induction ps with
  | nil => intro R i; cases i
  | cons t ps ih =>
      intro R i
      cases i with
      | here => rfl
      | there i =>
          simpa only [thinTop, Idx.wk, Kinds.at, Idx.toNat, List.length_cons,
            List.replicate_succ, List.cons_append, List.getD_cons_succ, List.getD_nil] using ih R i

/-- Accepted value arguments introduce plain locals before the continuation. -/
theorem bindArgs_ok {Γ Δ : Ctx} {K : Kinds} : {ps : Ctx} → {as : Args C Γ ps} →
    ArgsOk as → {P : Solidity.Prog C (ps ++ Γ) Δ} →
    ProgOk (List.replicate ps.length false ++ K) P → ProgOk K (bindArgs as P)
  | _, _, .nil, _, hP => hP
  | _, _, .snoc p x ha he, _, hP =>
      bindArgs_ok ha (.cons (.declSome p x (val_wk_ok _ he)) hP)

theorem inlineBlock_ok {Γ ps Γf : Ctx} {K : Kinds} {as : Args C Γ ps}
    {body : Solidity.Prog C ps Γf} (ha : ArgsOk as) (hb : ProgOk [] body) :
    StmtOk K (inlineBlock as body) K :=
  .block (bindArgs_ok ha (prog_wk_ok hb _ (kindsWk_top Γ ps K)))

theorem retTail_ok {Γ qs : Ctx} {p : PrimTy} {K : Kinds} (res : Option (Idx Γ (.val p))) :
    ProgOk K (retTail (C := C) (qs := qs) res) := by
  cases res with
  | none => exact .nil
  | some i => exact .cons (.assignLocal _ (.local .here)) .nil

theorem inlineBlockVal_ok {Γ ps Γf : Ctx} {K : Kinds} {as : Args C Γ ps}
    (p : PrimTy) (r : Var) (res : Option (Idx Γ (.val p)))
    {body : Solidity.Prog C ([.val p] ++ ps) Γf} (ha : ArgsOk as) (hb : ProgOk [] body) :
    StmtOk K (inlineBlockVal as p r res body) K :=
  .block (bindArgs_ok ha (.cons (.declNone p r)
    (.cons (.block (prog_wk_ok hb _ (kindsWk_top Γ (.val p :: ps) K))) (retTail_ok res))))

mutual
theorem stmt_inl_ok : {Γ Γ' : Ctx} → {K K' : Kinds} → {s : Solidity.Stmt C Γ Γ'} →
    StmtOk K s K' → StmtOk K (Stmt.inl s) K'
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
  | _, _, _, _, _, .callNone _ ha hb => inlineBlock_ok ha hb
  | _, _, _, _, _, .callVal _ p r res ha hb => inlineBlockVal_ok p r res ha hb
  | _, _, _, _, _, .ite hc ht he => .ite hc (prog_inl_ok ht) (prog_inl_ok he)
  | _, _, _, _, _, .block hb => .block (prog_inl_ok hb)
  | _, _, _, _, _, .loop a hc hb => .loop a hc (prog_inl_ok hb)

theorem prog_inl_ok : {Γ Δ : Ctx} → {K : Kinds} → {P : Solidity.Prog C Γ Δ} →
    ProgOk K P → ProgOk K (Prog.inl P)
  | _, _, _, _, .nil => .nil
  | _, _, _, _, .cons hs hp => .cons (stmt_inl_ok hs) (prog_inl_ok hp)
end

end Solidity.Backend.CompilerOptimizerDomain
