import Solidity.Backend.Passes.ValueCertificate

/-! Syntactic fresh-local transport for existing intrinsic code/fragment
functions. Code equality alone is not an acceptance/correctness claim. -/
namespace Solidity.Backend.Passes
open Solidity.Evm
variable {C : Contract} {Γ : Ctx}

theorem simple_fresh_code (b : Nat) (fresh : LTy) {p : PrimTy} (s : Simple C Γ p) :
    compileSimple b (s.wk (Thin.drop (t := fresh) .refl)) = compileSimple b s := by
  cases s <;> simp only [Simple.wk, compileSimple, Idx.wk, cellOf, lvl_there]

mutual

theorem spath_fresh_code (b : Nat) (fresh : LTy) : {T : Ty} → (q : SPath C Γ T) →
    compileSPath b (q.wk (Thin.drop (t := fresh) .refl)) = compileSPath b q
  | _, .alias i => by simp only [SPath.wk, compileSPath, Idx.wk, cellOf, lvl_there]
  | _, .loc l => by simp only [SPath.wk, compileSPath, loc_fresh_code b fresh l]

theorem loc_fresh_code (b : Nat) (fresh : LTy) : {T : Ty} → (l : Loc C Γ T) →
    compileLoc b (l.wk (Thin.drop (t := fresh) .refl)) = compileLoc b l
  | _, .root r h => rfl
  | _, .field q f hf => by simp only [Loc.wk, compileLoc, spath_fresh_code b fresh q]
  | _, .index .map q i => by
      simp only [Loc.wk, compileLoc, spath_fresh_code b fresh q, core_val_fresh_code b fresh i]
  | _, .index (.arr .dyn) q i => by
      simp only [Loc.wk, compileLoc, spath_fresh_code b fresh q, core_val_fresh_code b fresh i]
  | _, .index (.arr .fixed) q i => by
      simp only [Loc.wk, compileLoc, spath_fresh_code b fresh q, core_val_fresh_code b fresh i]

theorem core_val_fresh_code (b : Nat) (fresh : LTy) : {p : PrimTy} → (v : Val C Γ p) →
    Evm.compileVal b (v.wk (Thin.drop (t := fresh) .refl)) = Evm.compileVal b v
  | _, .simple s => by simp only [Val.wk, Evm.compileVal, simple_fresh_code b fresh s]
  | _, .read l => by simp only [Val.wk, Evm.compileVal, loc_fresh_code b fresh l]
  | _, .binop op ha hq x y => by
      simp only [Val.wk, Evm.compileVal, core_val_fresh_code b fresh x, core_val_fresh_code b fresh y]
  | _, .unop op ha hq x => by simp only [Val.wk, Evm.compileVal, core_val_fresh_code b fresh x]
  | _, .ternary c x y => by
      simp only [Val.wk, Evm.compileVal, core_val_fresh_code b fresh c,
        core_val_fresh_code b fresh x, core_val_fresh_code b fresh y]
  | _, .len q h => by simp only [Val.wk, Evm.compileVal, spath_fresh_code b fresh q]
  | _, .readMem _ => rfl
  | _, .mlen .. => rfl
  | _, .modular .. => rfl
  | _, .hash .. => rfl
end

/-- The actual core fragment predicate is preserved, including refusals. -/
theorem simple_fresh_in (fresh : LTy) {p : PrimTy} (s : Simple C Γ p) :
    simpleIn (s.wk (Thin.drop (t := fresh) .refl)) = simpleIn s := by
  cases s <;> rfl

mutual

theorem spath_fresh_in (fresh : LTy) (F : Frag Γ) (free : Bool) :
    {T : Ty} → (q : SPath C Γ T) →
    spathIn (F.push fresh .ok) free (q.wk (Thin.drop (t := fresh) .refl)) = spathIn F free q
  | _, .alias i => by simp only [SPath.wk, spathIn, Frag.get, Frag.push, Idx.wk,
      Idx.toNat, List.getD_cons_succ]
  | _, .loc l => by simp only [SPath.wk, spathIn, loc_fresh_in fresh F free l]

theorem loc_fresh_in (fresh : LTy) (F : Frag Γ) (free : Bool) :
    {T : Ty} → (l : Loc C Γ T) →
    locIn (F.push fresh .ok) free (l.wk (Thin.drop (t := fresh) .refl)) = locIn F free l
  | _, .root .. => rfl
  | _, .field q f hf => by simp only [Loc.wk, locIn, spath_fresh_in fresh F free q]
  | _, .index .map q i => by
      simp only [Loc.wk, locIn, spath_fresh_in fresh F free q, core_val_fresh_in fresh F i]
  | _, .index (.arr .dyn) q i => by
      simp only [Loc.wk, locIn, spath_fresh_in fresh F free q, core_val_fresh_in fresh F i]
  | _, .index (.arr .fixed) q i => by
      simp only [Loc.wk, locIn, spath_fresh_in fresh F free q, core_val_fresh_in fresh F i]

theorem core_val_fresh_in (fresh : LTy) (F : Frag Γ) : {p : PrimTy} → (v : Val C Γ p) →
    valIn (F.push fresh .ok) (v.wk (Thin.drop (t := fresh) .refl)) = valIn F v
  | _, .simple s => by simp only [Val.wk, valIn, simple_fresh_in fresh s]
  | _, .read l => by simp only [Val.wk, valIn, loc_fresh_in fresh F false l]
  | _, .binop op ha hq x y => by
      simp only [Val.wk, valIn, core_val_fresh_in fresh F x, core_val_fresh_in fresh F y]
  | _, .unop op ha hq x => by simp only [Val.wk, valIn, core_val_fresh_in fresh F x]
  | _, .ternary c x y => by simp only [Val.wk, valIn, core_val_fresh_in fresh F c,
      core_val_fresh_in fresh F x, core_val_fresh_in fresh F y]
  | _, .len q h => by simp only [Val.wk, valIn, spath_fresh_in fresh F false q]
  | _, .readMem _ => rfl
  | _, .mlen .. => rfl
  | _, .modular .. => rfl
  | _, .hash .. => rfl
end


end Solidity.Backend.Passes
