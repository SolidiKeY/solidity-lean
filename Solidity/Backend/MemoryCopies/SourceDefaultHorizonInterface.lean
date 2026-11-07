import Solidity.Backend.MemoryCopies.SourceCopyHorizonInterface

/-! Exact non-timeout observations of existing default traversals under added
interpreter fuel. This does not assert termination or physical allocation room. -/
namespace Solidity.Backend.MemoryCopies

structure SourceDefaultHorizonCertificate (E : Source.Env) (Γ : Source.RCtx) : Prop where
  data : ∀ (fuel slack : Nat) (type : Source.STy),
    CopyHorizonExtends (Source.zeroData (E := E) (Γ := Γ) fuel type)
      (Source.zeroData (fuel + slack) type)
  value : ∀ (fuel slack : Nat) (type : Source.STy),
    CopyHorizonExtends (Source.zeroVal (E := E) (Γ := Γ) fuel type)
      (Source.zeroVal (fuel + slack) type)
  elements : ∀ (fuel slack : Nat) (type : Source.STy) (count : Nat),
    CopyHorizonExtends (Source.zeroElems (E := E) (Γ := Γ) fuel type count)
      (Source.zeroElems (fuel + slack) type count)
  fields : ∀ (fuel slack : Nat) (types : List Source.STy),
    CopyHorizonExtends (Source.zeroFields (E := E) (Γ := Γ) fuel types)
      (Source.zeroFields (fuel + slack) types)
end Solidity.Backend.MemoryCopies
