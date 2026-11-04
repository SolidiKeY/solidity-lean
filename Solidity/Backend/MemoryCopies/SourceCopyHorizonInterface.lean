import Solidity.Source.Hoare

/-! Exact non-timeout observation preservation when existing Source copy
traversals receive additional interpreter fuel. Fuel is not EVM gas. -/
namespace Solidity.Backend.MemoryCopies

def CopyHorizonExtends {E : Source.Env} {Γ : Source.RCtx} {α : Type}
    (lower upper : Source.EM E Γ α) : Prop :=
  ∀ before : Source.EMState E Γ, (lower.run before).1 ≠ .error .timeout →
    upper.run before = lower.run before

structure SourceCopyHorizonCertificate (E : Source.Env) (Γ : Source.RCtx) (frame : Source.Fr) : Prop where
  memory : ∀ fuel slack type path,
    CopyHorizonExtends (Source.loadMem (E := E) (Γ := Γ) frame fuel type path)
      (Source.loadMem frame (fuel + slack) type path)
  element : ∀ fuel slack type path,
    CopyHorizonExtends (Source.loadElem (E := E) (Γ := Γ) frame fuel type path)
      (Source.loadElem frame (fuel + slack) type path)
  elements : ∀ fuel slack type path start count,
    CopyHorizonExtends (Source.loadElems (E := E) (Γ := Γ) frame fuel type path start count)
      (Source.loadElems frame (fuel + slack) type path start count)
  fields : ∀ fuel slack types path start,
    CopyHorizonExtends (Source.loadFields (E := E) (Γ := Γ) frame fuel types path start)
      (Source.loadFields frame (fuel + slack) types path start)
  bytes : ∀ fuel slack path start count,
    CopyHorizonExtends (Source.loadBytes (E := E) (Γ := Γ) frame fuel path start count)
      (Source.loadBytes frame (fuel + slack) path start count)
end Solidity.Backend.MemoryCopies
