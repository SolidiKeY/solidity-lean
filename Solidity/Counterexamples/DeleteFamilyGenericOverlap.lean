import Solidity.KeySort


namespace Solidity
namespace Counterexamples
namespace DeleteFamilyGenericOverlap


example : KeySort.struct.le KeySort.stValue = true := by decide
example : KeySort.struct.le KeySort.prim = false := by decide
example : KeySort.mapField.le KeySort.field = true := by decide
example : KeySort.stValue.le KeySort.prim = false := by decide
example : KeySort.stValue = KeySort.struct <-> False := by decide


theorem delValue_overlap_inconsistent
    {St SV Fld : Type}
    (injS : St -> SV) (injI : Int -> SV)
    (mt : St)
    (delValueS : St -> St)
    (delNode : St -> St)
    (dvStruct : St)
    (selS : St -> Fld -> St)
    (selI : St -> Fld -> Int)
    (storeSt : St -> Fld -> SV -> St)
    (castS : SV -> St) (castI : SV -> Int)
    (mf at0 : Fld)
    (hDelStruct : ∀ st, delValueS st = delNode st)
    (hDelDefault : ∀ st, delValueS st = dvStruct)
    (hDv : dvStruct = mt)
    (hMap : ∀ st, selS (delNode st) mf = selS st mf)
    (hStoreS : ∀ st f v, selS (storeSt st f v) f = castS v)
    (hStoreI : ∀ st f v, selI (storeSt st f v) f = castI v)
    (hCastS : ∀ s, castS (injS s) = s)
    (hCastI : ∀ n, castI (injI n) = n) : False := by
  have hdn : ∀ st, delNode st = mt := fun st =>
    (hDelStruct st).symm.trans ((hDelDefault st).trans hDv)
  have hconst : ∀ st, selS st mf = selS mt mf := by
    intro st
    have h := hMap st
    rw [hdn st] at h
    exact h.symm
  have habs : ∀ s : St, s = selS mt mf := by
    intro s
    have h := hconst (storeSt mt mf (injS s))
    rw [hStoreS, hCastS] at h
    exact h
  have hcollapse : storeSt mt at0 (injI 5) = storeSt mt at0 (injI 7) :=
    (habs _).trans (habs _).symm
  have : (5 : Int) = 7 := by
    have h := congrArg (fun st => selI st at0) hcollapse
    simpa [hStoreI, hCastI] using h
  omega

theorem selectStDelNode_overlap_inconsistent
    {St SV Fld : Type}
    (injS : St -> SV) (injI : Int -> SV)
    (mt : St)
    (delNode : St -> St)
    (dvStruct : St)
    (selS : St -> Fld -> St)
    (selI : St -> Fld -> Int)
    (storeSt : St -> Fld -> SV -> St)
    (castS : SV -> St) (castI : SV -> Int)
    (mf at0 : Fld)
    (hDefault : ∀ st, selS (delNode st) mf = dvStruct)
    (hDv : dvStruct = mt)
    (hMap : ∀ st, selS (delNode st) mf = selS st mf)
    (hStoreS : ∀ st f v, selS (storeSt st f v) f = castS v)
    (hStoreI : ∀ st f v, selI (storeSt st f v) f = castI v)
    (hCastS : ∀ s, castS (injS s) = s)
    (hCastI : ∀ n, castI (injI n) = n) : False := by
  have hconst : ∀ st, selS st mf = mt := fun st =>
    (hMap st).symm.trans ((hDefault st).trans hDv)
  have habs : ∀ s : St, s = mt := by
    intro s
    have h := hconst (storeSt mt mf (injS s))
    rw [hStoreS, hCastS] at h
    exact h
  have hcollapse : storeSt mt at0 (injI 5) = storeSt mt at0 (injI 7) :=
    (habs _).trans (habs _).symm
  have : (5 : Int) = 7 := by
    have h := congrArg (fun st => selI st at0) hcollapse
    simpa [hStoreI, hCastI] using h
  omega

end DeleteFamilyGenericOverlap
end Counterexamples
end Solidity
