import Solidity.Backend.AbiWorld.PublicCompilerTotal
import Solidity.Optimizer.ConstFold

/-! Expression-domain preservation for `Solidity.Goals.compilerOptimizedEndpoint`.
These lemmas retain the existing accepted domain and the actual constant folder. -/
namespace Solidity.Backend.CompilerOptimizerDomain

open Solidity Solidity.Optimizer.ConstFold
open Solidity.Backend.AbiWorld.PublicCompilerTotal

variable {C : Contract} {Γ : Ctx}

theorem litV_ok (p : PrimTy) (x : p.Denote) :
    ValOk (litV (C := C) (Γ := Γ) p x) := by
  cases p with
  | bool => exact .bool x
  | uint => exact .lit x.1 x.2
  | int => exact .lit x.1 x.2

theorem foldBin_ok {p q : PrimTy} (op : BinOp) (h : op.accepts p = true)
    (hq : op.ret p = q) {a b : Val C Γ p} (ha : ValOk a) (hb : ValOk b) :
    ValOk (foldBin op h hq a b) := by
  unfold foldBin
  split
  · exact .binop op h hq ha hb
  · split
    · exact litV_ok _ _
    · split
      · exact .binop op h hq ha hb
      · split
        · exact litV_ok _ _
        · exact .binop op h hq ha hb

theorem foldUn_ok {p q : PrimTy} (op : UnOp) (h : op.accepts p = true)
    (hq : op.ret p = q) {a : Val C Γ p} (ha : ValOk a) :
    ValOk (foldUn op h hq a) := by
  unfold foldUn
  split
  · exact .unop op h hq ha
  · split
    · exact litV_ok _ _
    · exact .unop op h hq ha

theorem foldTern_ok {p : PrimTy} {c : Val C Γ .bool} {a b : Val C Γ p}
    (hc : ValOk c) (ha : ValOk a) (hb : ValOk b) :
    ValOk (foldTern c a b) := by
  unfold foldTern
  split
  · exact .ternary hc ha hb
  · split
    · exact ha
    · exact hb

mutual
theorem path_cfold_ok : {T : Ty} → {b : SPath C Γ T} → PathOk b → PathOk b.cfold
  | _, _, .alias i => .alias i
  | _, _, .loc h => .loc (loc_cfold_ok h)

theorem loc_cfold_ok : {T : Ty} → {l : Loc C Γ T} → LocOk l → LocOk l.cfold
  | _, _, .root r h => .root r h
  | _, _, .field f h fits hb => .field f h fits (path_cfold_ok hb)
  | _, _, .map hb hi => .map (path_cfold_ok hb) (val_cfold_ok hi)
  | _, _, .dyn hb hi => .dyn (path_cfold_ok hb) (val_cfold_ok hi)
  | _, _, .fixed fits hb hi => .fixed fits (path_cfold_ok hb) (val_cfold_ok hi)

theorem val_cfold_ok : {p : PrimTy} → {v : Val C Γ p} → ValOk v → ValOk v.cfold
  | _, _, .lit n h => .lit n h
  | _, _, .bool b => .bool b
  | _, _, .local i => .local i
  | _, _, .env k hp hk => .env k hp hk
  | _, _, .read h => .read (loc_cfold_ok h)
  | _, _, .binop op h hq ha hb => foldBin_ok op h hq (val_cfold_ok ha) (val_cfold_ok hb)
  | _, _, .unop op h hq ha => foldUn_ok op h hq (val_cfold_ok ha)
  | _, _, .ternary hc ha hb => foldTern_ok (val_cfold_ok hc) (val_cfold_ok ha) (val_cfold_ok hb)
  | _, _, .len hp hb => .len hp (path_cfold_ok hb)
end

end Solidity.Backend.CompilerOptimizerDomain
