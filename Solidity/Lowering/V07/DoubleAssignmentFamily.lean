import Solidity.Lowering.V07.DoubleAssignment

namespace Solidity.Lowering.V07.IntegerLocalFamily
variable {D : Source.Layout} {srcΓ : Source.RCtx} {C : Contract} {H : HTy} {Γ : Ctx}
  {ι : Type} {t : Source.IntTy} {si : ι → Source.Idx srcΓ (.int t)}
  {ti : ι → Idx Γ (.val (integerPrim t))} {source : Source.Locals D srcΓ} {target : TEnv C H Γ}

/-- Both ordered writes preserve every selected value/alias. Reached reads
are computed by the actual write laws; the postfamily is not a premise.
Destinations i/a may alias, including aliases repeated arbitrarily in ι. -/
theorem assign_pair (h : IntegerLocalFamily t si ti source target)
    (pipeline : Roadmap.Pipeline) (i a b : ι) (x z : Int)
    (hx : t.lo ≤ x ∧ x ≤ t.hi) (hz : t.lo ≤ z ∧ z ≤ t.hi)
    (readA : source.get (si a) = .int x hx) (readB : source.get (si b) = .int z hz)
    (different : (si i).toNat ≠ (si b).toNat) :
    IntegerLocalFamily t si ti
      (if pipeline = .legacy then (source.set (si a) (.int z hz)).set (si i) (.int z hz)
        else (source.set (si i) (.int x hx)).set (si a) (.int z hz))
      (if pipeline = .legacy then
        TEnv.set (ti i) (integerValue t z hz) (TEnv.set (ti a) (integerValue t z hz) target)
        else TEnv.set (ti a) (integerValue t z hz) (TEnv.set (ti i) (integerValue t x hx) target)) := by
  have targetA := h.read a x hx readA
  have targetB := h.read b z hz readB
  by_cases order : pipeline = .legacy
  · simp only [order,if_true]
    simpa only [readB,targetB,source_locals_get_set,TEnv.get_set] using
      (h.write a b).write i a
  · simp only [order,if_false]
    simpa only [readA,targetA,
      source_locals_get_set_ne source (si i) (si b) (.int x hx) different,
      TEnv.get_set_ne (ti i) (ti b) (integerValue t x hx) target (h.separate i b different),
      readB,targetB] using (h.write i a).write a b

end Solidity.Lowering.V07.IntegerLocalFamily
