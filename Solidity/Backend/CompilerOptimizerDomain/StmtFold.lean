import Solidity.Backend.CompilerOptimizerDomain.ConstFold
import Solidity.Optimizer.StmtFold

/-! Lift expression-domain preservation through the existing statement folder.
This advances `Solidity.Goals.compilerOptimizedEndpoint` without altering its domain. -/
namespace Solidity.Backend.CompilerOptimizerDomain
open Solidity Solidity.Optimizer.ConstFold
open Solidity.Backend.AbiWorld.PublicCompilerTotal
variable {C : Contract}


mutual
theorem path_vmap_ok (V : ValPass C)
    (hv : ∀ {Γ : Ctx} {p : PrimTy} {v : Val C Γ p}, ValOk v → ValOk (V.run v)) {Γ : Ctx} : {T : Ty} → {b : SPath C Γ T} →
    PathOk b → PathOk (b.vmap V)
  | _, _, .alias i => .alias i
  | _, _, .loc h => .loc (loc_vmap_ok V hv h)

theorem loc_vmap_ok (V : ValPass C)
    (hv : ∀ {Γ : Ctx} {p : PrimTy} {v : Val C Γ p}, ValOk v → ValOk (V.run v)) {Γ : Ctx} : {T : Ty} → {l : Loc C Γ T} →
    LocOk l → LocOk (l.vmap V)
  | _, _, .root r h => .root r h
  | _, _, .field f h fits hb => .field f h fits (path_vmap_ok V hv hb)
  | _, _, .map hb hi => .map (path_vmap_ok V hv hb) (hv hi)
  | _, _, .dyn hb hi => .dyn (path_vmap_ok V hv hb) (hv hi)
  | _, _, .fixed fits hb hi => .fixed fits (path_vmap_ok V hv hb) (hv hi)
end

theorem foldIte_ok {Γ Γ₁ Γ₂ : Ctx} {K : Kinds} {c : Val C Γ .bool}
    {t : Prog C Γ Γ₁} {e : Prog C Γ Γ₂} (hc : ValOk c)
    (ht : ProgOk K t) (he : ProgOk K e) : StmtOk K (foldIte c t e) K := by
  unfold foldIte
  split
  · split
    · exact .block ht
    · exact .block he
  · exact .ite hc ht he

theorem consDrop_ok {Γ Γ₁ Γ₂ : Ctx} {K K₁ : Kinds} {s : Stmt C Γ Γ₁}
    {P : Prog C Γ₁ Γ₂} (hs : StmtOk K s K₁) (hP : ProgOk K₁ P) :
    ProgOk K (consDrop s P) := by
  have original := hs
  cases hs <;> simp only [consDrop] <;>
    first | exact .cons original hP | (split <;> first | exact hP | exact .cons original hP)


mutual
theorem stmt_vopt_ok (V : ValPass C)
    (hv : ∀ {Γ : Ctx} {p : PrimTy} {v : Val C Γ p}, ValOk v → ValOk (V.run v)) : {Γ Γ' : Ctx} → {K K' : Kinds} → {s : Stmt C Γ Γ'} →
    StmtOk K s K' → StmtOk K (s.vopt V) K'
  | _, _, _, _, _, .assign hl hv' => .assign (loc_vmap_ok V hv hl) (hv hv')
  | _, _, _, _, _, .assignLocal i h => .assignLocal i (hv h)
  | _, _, _, _, _, .declNone p x => .declNone p x
  | _, _, _, _, _, .declSome p x h => .declSome p x (hv h)
  | _, _, _, _, _, .declStorage r x h => .declStorage r x h
  | _, _, _, _, _, .declIndexed r x hp hi => .declIndexed r x hp hi
  | _, _, _, _, _, .rebind i plain h => .rebind i plain h
  | _, _, _, _, _, .rebindIndexed i indexed hp hi => .rebindIndexed i indexed hp hi
  | _, _, _, _, _, .opAssign op hop hp hl h => .opAssign op hop hp hl (hv h)
  | _, _, _, _, _, .incDec op hp hl => .incDec op hp hl
  | _, _, _, _, _, .require h => .require (hv h)
  | _, _, _, _, _, .assert h => .assert (hv h)
  | _, _, _, _, _, .revert => .revert
  | _, _, _, _, _, .ite hc ht he => foldIte_ok (hv hc) (prog_vopt_ok V hv ht) (prog_vopt_ok V hv he)
  | _, _, _, _, _, .block h => .block (prog_vopt_ok V hv h)
  | _, _, _, _, _, .loop a hc hb => .loop a (hv hc) (prog_vopt_ok V hv hb)
  | _, _, _, _, _, .callNone f ha hb => .callNone f ha hb
  | _, _, _, _, _, .callVal f p r res ha hb => .callVal f p r res ha hb

theorem prog_vopt_ok (V : ValPass C)
    (hv : ∀ {Γ : Ctx} {p : PrimTy} {v : Val C Γ p}, ValOk v → ValOk (V.run v)) : {Γ Γ' : Ctx} → {K : Kinds} → {P : Prog C Γ Γ'} →
    ProgOk K P → ProgOk K (P.vopt V)
  | _, _, _, _, .nil => .nil
  | _, _, _, _, .cons hs hp => consDrop_ok (stmt_vopt_ok V hv hs) (prog_vopt_ok V hv hp)
end

theorem prog_cfold_ok {Γ Γ' : Ctx} {K : Kinds} {P : Prog C Γ Γ'}
    (h : ProgOk K P) : ProgOk K P.cfold := prog_vopt_ok cfoldPass val_cfold_ok h

end Solidity.Backend.CompilerOptimizerDomain
