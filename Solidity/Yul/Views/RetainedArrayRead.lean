import Solidity.Yul.Views.RetainedLocationProducers

/-! Factoring actual mutable-array value reads through the identical actual
location producer. Evaluation order, index checks, horizons and readLoc remain
unchanged. This is computation equality, not assumed view or coverage adequacy. -/
namespace Solidity.Yul.Views

theorem evalArray_readLoc {E Γ l τ σ size} (G : Source.Glob E) (F : Source.Fr) (n : Nat)
    (array : Source.RExpr E Γ (.array l τ size)) (mutable : l ≠ .calldata)
    (index : Source.RExpr E Γ σ) (valid : σ.isIndex = true) :
    Source.evalE G F (n+1) (.indexArray array index valid)=
      (do let loc ← Source.evalLoc G F (n+1) (.indexArray array mutable index valid)
          return .val (← Source.readLoc F loc)) := by
  first | (simp only;done) | decide | omega | rfl | skip
  simp only [Source.evalE,Source.evalLoc,bind_assoc]

theorem evalArray_readLoc_run {E Γ l τ σ size} (G : Source.Glob E) (F : Source.Fr) (n : Nat)
    (array : Source.RExpr E Γ (.array l τ size)) (mutable : l ≠ .calldata)
    (index : Source.RExpr E Γ σ) (valid : σ.isIndex = true)
    (s mid after : Source.EMState E Γ) (loc : Source.Loc E.layout Γ τ) (value : Source.Val E.layout τ)
    (location : (Source.evalLoc G F (n+1) (.indexArray array mutable index valid)).run s=(.ok loc,mid))
    (read : (Source.readLoc F loc).run mid=(.ok value,after)) :
    (Source.evalE G F (n+1) (.indexArray array index valid)).run s=(.ok (.val value),after) := by
  first | (simp only;done) | decide | omega | rfl | skip
  rw [evalArray_readLoc G F n array mutable index valid,Source.Hoare.run_bind,location]
  dsimp only
  rw [Source.Hoare.run_bind,read]
  rfl
end Solidity.Yul.Views
