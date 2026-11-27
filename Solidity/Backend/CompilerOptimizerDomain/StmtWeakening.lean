import Solidity.Backend.CompilerOptimizerDomain.Weakening

/-! Alias-kind transport and accepted statement/program weakening. -/
namespace Solidity.Backend.CompilerOptimizerDomain
open Solidity
open Solidity.Backend.AbiWorld.PublicCompilerTotal
variable {C : Contract} {Γ Δ : Ctx}

/-- A thinning preserves the plain/indexed flag of every existing storage alias. -/
def KindsWk (w : Thin Γ Δ) (K L : Kinds) : Prop :=
  ∀ (R : RefTy) (i : Idx Γ (.alias R)), L.at (i.wk w) = K.at i

theorem KindsWk.keep {w : Thin Γ Δ} {K L : Kinds} (h : KindsWk w K L)
    (t : LTy) (k : Bool) : KindsWk (.keep (t := t) w) (k :: K) (k :: L) := by
  intro R i
  cases i with
  | here => rfl
  | there i => simpa only [Idx.wk, Kinds.at, Idx.toNat, List.getD_cons_succ] using h R i

theorem KindsWk.empty (w : Thin Γ Δ) : KindsWk w [] [] := by
  intro R i
  simp only [Kinds.at, List.getD_nil]

theorem freePath_wk_ok (w : Thin Γ Δ) {K L : Kinds} (hK : KindsWk w K L) :
    {T : Ty} → {b : SPath C Γ T} → FreePath K b → FreePath L (b.wk w)
  | _, _, .alias i hi => .alias (i.wk w) ((hK _ i).trans hi)
  | _, _, .root r h => .root r h
  | _, _, .field f h fits hb => .field f h fits (freePath_wk_ok w hK hb)
  | _, _, .map hb hi => .map (freePath_wk_ok w hK hb) (val_wk_ok w hi)

theorem indexedPath_wk_ok (w : Thin Γ Δ) {K L : Kinds} (hK : KindsWk w K L) :
    {T : Ty} → {b : SPath C Γ T} → IndexedPath K b → IndexedPath L (b.wk w)
  | _, _, .alias i hi => .alias (i.wk w) ((hK _ i).trans hi)
  | _, _, .dyn => .dyn
  | _, _, .fixed => .fixed
  | _, _, .field f h hb => .field f h (indexedPath_wk_ok w hK hb)
  | _, _, .map hb => .map (indexedPath_wk_ok w hK hb)

mutual
/-- Accepted statements transport to a larger context and preserve output alias kinds. -/
theorem stmt_wk_ok : {Γ Γ' Δ : Ctx} → {K K' L : Kinds} → {s : Stmt C Γ Γ'} →
    (h : StmtOk K s K') → (w : Thin Γ Δ) → KindsWk w K L →
    ∃ L', StmtOk L (s.wk w).2.2 L' ∧ KindsWk (s.wk w).2.1 K' L'
  | _, _, _, _, _, L, _, .assign hl hv, w, hK => ⟨L, .assign (loc_wk_ok w hl) (val_wk_ok w hv), hK⟩
  | _, _, _, _, _, L, _, .assignLocal i hv, w, hK => ⟨L, .assignLocal (i.wk w) (val_wk_ok w hv), hK⟩
  | _, _, _, _, _, L, _, .declNone p x, w, hK => ⟨false :: L, .declNone p x, hK.keep _ false⟩
  | _, _, _, _, _, L, _, .declSome p x hv, w, hK => ⟨false :: L, .declSome p x (val_wk_ok w hv), hK.keep _ false⟩
  | _, _, _, _, _, L, _, .declStorage R x hb, w, hK =>
      ⟨false :: L, .declStorage R x (freePath_wk_ok w hK hb), hK.keep _ false⟩
  | _, _, _, _, _, L, _, .declIndexed R x hb hi, w, hK =>
      ⟨true :: L, .declIndexed R x (path_wk_ok w hb) (indexedPath_wk_ok w hK hi), hK.keep _ true⟩
  | _, _, _, _, _, L, _, .rebind i plain hb, w, hK =>
      ⟨L, .rebind (i.wk w) ((hK _ i).trans plain) (freePath_wk_ok w hK hb), hK⟩
  | _, _, _, _, _, L, _, .rebindIndexed i indexed hb hi, w, hK =>
      ⟨L, .rebindIndexed (i.wk w) ((hK _ i).trans indexed)
        (path_wk_ok w hb) (indexedPath_wk_ok w hK hi), hK⟩
  | _, _, _, _, _, L, _, .opAssign op hop hp hl hv, w, hK =>
      ⟨L, .opAssign op hop hp (opLoc_wk_ok w hl) (val_wk_ok w hv), hK⟩
  | _, _, _, _, _, L, _, .incDec op hp hl, w, hK => ⟨L, .incDec op hp (opLoc_wk_ok w hl), hK⟩
  | _, _, _, _, _, L, _, .require hc, w, hK => ⟨L, .require (val_wk_ok w hc), hK⟩
  | _, _, _, _, _, L, _, .assert hc, w, hK => ⟨L, .assert (val_wk_ok w hc), hK⟩
  | _, _, _, _, _, L, _, .revert, w, hK => ⟨L, .revert, hK⟩
  | _, _, _, _, _, L, _, .ite hc ht he, w, hK =>
      ⟨L, .ite (val_wk_ok w hc) (prog_wk_ok ht w hK) (prog_wk_ok he w hK), hK⟩
  | _, _, _, _, _, L, _, .block hb, w, hK => ⟨L, .block (prog_wk_ok hb w hK), hK⟩
  | _, _, _, _, _, L, _, .loop a hc hb, w, hK => ⟨L, .loop (a.wk w) (val_wk_ok w hc) (prog_wk_ok hb w hK), hK⟩
  | _, _, _, _, _, L, _, .callNone f ha hb, w, hK => ⟨L, .callNone f (args_wk_ok w ha) hb, hK⟩
  | _, _, _, _, _, L, _, .callVal f p r res ha hb, w, hK =>
      ⟨L, .callVal f p r (res.map (·.wk w)) (args_wk_ok w ha) hb, hK⟩


/-- Program weakening preserves the complete original accepted domain. -/
theorem prog_wk_ok : {Γ Γ' Δ : Ctx} → {K L : Kinds} → {P : Prog C Γ Γ'} →
    (h : ProgOk K P) → (w : Thin Γ Δ) → KindsWk w K L → ProgOk L (P.wk w).2.2
  | _, _, _, _, _, _, .nil, _, _ => .nil
  | _, _, _, _, _, _, .cons hs hp, w, hK => by
      obtain ⟨L', hs', hK'⟩ := stmt_wk_ok hs w hK
      exact .cons hs' (prog_wk_ok hp _ hK')
end

end Solidity.Backend.CompilerOptimizerDomain
