import Solidity.Lowering.Readonly.PrimitiveLocals
import Solidity.Source.Eval

/-! Actual primitive return-slot initialisation for typed source calls.
The source horizon/refusal behaviour is retained, including the distinct empty
return-list case. No source body, memory allocation or ABI execution is assumed. -/
namespace Solidity.Lowering.Readonly.PrimitiveInitialization
open Solidity.Source PrimitiveValues
variable {E : Env} {Γ : RCtx}

def defaults (D : Layout) : (ps : List PrimTy) → Vals D (ps.map sourceTy)
  | [] => .nil
  | p :: ps => .cons (toSource D p (PrimTy.dflt p)) (defaults D ps)

theorem zero_value (n : Nat) (p : PrimTy) :
    (zeroVal (E := E) (Γ := Γ) (n + 1) (sourceTy p)) = pure (toSource E.layout p (PrimTy.dflt p)) := by
  rw [zeroVal, default_value]

theorem zero_values (n : Nat) (ps : List PrimTy) :
    (zeroVals (E := E) (Γ := Γ) (n + 1) (ps.map sourceTy)) = pure (defaults E.layout ps) := by
  induction ps with
  | nil => rfl
  | cons p ps ih =>
    simp only [List.map_cons, zeroVals, zero_value, ih, pure_bind, defaults]

theorem exhausted_nonempty (p : PrimTy) (ps : List PrimTy) :
    (zeroVals (E := E) (Γ := Γ) 0 ((p :: ps).map sourceTy)) = EM.halt .timeout := by
  rw [List.map_cons, zeroVals, zeroVal]
  rfl

theorem exhausted_empty : (zeroVals (E := E) (Γ := Γ) 0 []) = pure (Vals.nil : Vals E.layout []) := rfl

end Solidity.Lowering.Readonly.PrimitiveInitialization
