import Solidity.Lowering.Readonly.PrimitiveValues
import Solidity.Source.Machine
import Solidity.Semantics.State

/-! Primitive caller/callee locals correspondence. Context order is preserved
exactly; function parameter order is the reverse-context order already computed
by Source.Vals.onto. These maps neither decode ABI bytes nor select a body. -/
namespace Solidity.Lowering.Readonly.PrimitiveLocals
open Solidity.Source PrimitiveValues
variable {C : Contract} {H : HTy}

def targetCtx (ps : List PrimTy) : Ctx := ps.map LTy.val

def toLocals (D : Layout) : (ps : List PrimTy) →
    TEnv C H (targetCtx ps) → Locals D (ps.map sourceTy)
  | [], _ => .nil
  | p :: ps, values => .cons (toSource D p values.1) (toLocals D ps values.2)

def fromLocals (D : Layout) : (ps : List PrimTy) →
    Locals D (ps.map sourceTy) → TEnv C H (targetCtx ps)
  | [], _ => ()
  | p :: ps, values => by
    cases values with
    | cons value rest => exact (fromSource D p value, fromLocals D ps rest)

def sourceIndex : {ps : List PrimTy} → {p : PrimTy} →
    Solidity.Idx (targetCtx ps) (.val p) → Solidity.Source.Idx (ps.map sourceTy) (sourceTy p)
  | [], _, index => nomatch index
  | _ :: ps, _, index => by
    cases index with
    | here => exact .here
    | there index => exact .there (sourceIndex (ps := ps) index)

theorem from_to {D : Layout} (ps : List PrimTy) (values : TEnv C H (targetCtx ps)) :
    fromLocals D ps (toLocals D ps values) = values := by
  induction ps with
  | nil => cases values; rfl
  | cons p ps ih =>
    rcases values with ⟨head, rest⟩
    change (fromSource D p (toSource D p head), fromLocals D ps (toLocals D ps rest)) = (head, rest)
    rw [PrimitiveValues.from_to, ih]

theorem to_from {D : Layout} (ps : List PrimTy) (values : Locals D (ps.map sourceTy)) :
    toLocals (C := C) (H := H) D ps (fromLocals D ps values) = values := by
  induction ps with
  | nil => cases values; rfl
  | cons p ps ih =>
    cases values with
    | cons head rest =>
      change Locals.cons (toSource D p (fromSource D p head))
        (toLocals D ps (fromLocals D ps rest)) = .cons head rest
      rw [PrimitiveValues.to_from, ih]

/-- Every typed variable position reads the exact represented value. -/
theorem get_toLocals {D : Layout} (ps : List PrimTy) (values : TEnv C H (targetCtx ps))
    {p : PrimTy} (index : Solidity.Idx (targetCtx ps) (.val p)) :
    (toLocals D ps values).get (sourceIndex index) = toSource D p (TEnv.get index values) := by
  induction ps with
  | nil => cases index
  | cons head ps ih =>
    cases index with
    | here => rfl
    | there index => exact ih values.2 index

/-- Reading a real source local transports to the corresponding typed target
variable; no binder permutation or re-evaluation is introduced. -/
theorem get_fromLocals {D : Layout} (ps : List PrimTy) (values : Locals D (ps.map sourceTy))
    {p : PrimTy} (index : Solidity.Idx (targetCtx ps) (.val p)) :
    fromSource D p (values.get (sourceIndex index)) =
      TEnv.get index (fromLocals (C := C) (H := H) D ps values) := by
  have represented := get_toLocals (D := D) ps (fromLocals (C := C) (H := H) D ps values) index
  rw [to_from] at represented
  have transported := congrArg (fromSource D p) represented
  rw [PrimitiveValues.from_to] at transported
  exact transported

end Solidity.Lowering.Readonly.PrimitiveLocals
