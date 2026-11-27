import Solidity.Backend.AbiWorld.PublicCompilerTotal

/-! Context weakening preserves the original accepted expression domain. -/
namespace Solidity.Backend.CompilerOptimizerDomain
open Solidity
open Solidity.Backend.AbiWorld.PublicCompilerTotal
variable {C : Contract} {Γ Δ : Ctx}

mutual
theorem path_wk_ok (w : Thin Γ Δ) :
    {T : Ty} → {b : SPath C Γ T} → PathOk b → PathOk (b.wk w)
  | _, _, .alias i => .alias (i.wk w)
  | _, _, .loc h => .loc (loc_wk_ok w h)

theorem loc_wk_ok (w : Thin Γ Δ) :
    {T : Ty} → {l : Loc C Γ T} → LocOk l → LocOk (l.wk w)
  | _, _, .root r h => .root r h
  | _, _, .field f h fits hb => .field f h fits (path_wk_ok w hb)
  | _, _, .map hb hi => .map (path_wk_ok w hb) (val_wk_ok w hi)
  | _, _, .dyn hb hi => .dyn (path_wk_ok w hb) (val_wk_ok w hi)
  | _, _, .fixed fits hb hi => .fixed fits (path_wk_ok w hb) (val_wk_ok w hi)

theorem val_wk_ok (w : Thin Γ Δ) :
    {p : PrimTy} → {v : Val C Γ p} → ValOk v → ValOk (v.wk w)
  | _, _, .lit n h => .lit n h
  | _, _, .bool b => .bool b
  | _, _, .local i => .local (i.wk w)
  | _, _, .env k hp hk => .env k hp hk
  | _, _, .read h => .read (loc_wk_ok w h)
  | _, _, .binop op h hq ha hb => .binop op h hq (val_wk_ok w ha) (val_wk_ok w hb)
  | _, _, .unop op h hq ha => .unop op h hq (val_wk_ok w ha)
  | _, _, .ternary hc ha hb => .ternary (val_wk_ok w hc) (val_wk_ok w ha) (val_wk_ok w hb)
  | _, _, .len hp hb => .len hp (path_wk_ok w hb)
end

theorem args_wk_ok (w : Thin Γ Δ) :
    {ps : Ctx} → {as : Args C Γ ps} → ArgsOk as → ArgsOk (as.wk w)
  | _, _, .nil => .nil
  | _, _, .snoc p x ha he => .snoc p x (args_wk_ok w ha) (val_wk_ok w he)

theorem opLoc_wk_ok (w : Thin Γ Δ) {p : PrimTy} {l : OpLoc C Γ p}
    (h : OpLocOk l) : OpLocOk (l.wk w) := by
  cases h <;> constructor <;> first | assumption | exact path_wk_ok w ‹_› | exact loc_wk_ok w ‹_›
end Solidity.Backend.CompilerOptimizerDomain
