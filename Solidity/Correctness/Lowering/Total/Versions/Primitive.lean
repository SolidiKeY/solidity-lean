import Solidity.Correctness.Lowering.Total.Decode.Widths

namespace Solidity.Correctness.Lowering.Total.Version

/-! ## The decoder's primitive types -/


/-- A primitive slot: a model primitive and a Source type a decoder version
may give it. A `bool` is a `bool`; a `uint` is an unsigned integer of any
width, an address or fixed bytes; an `int` is a signed integer of any width. -/
inductive Prim : PrimTy → Source.STy → Prop where
  | bool : Prim .bool .bool
  | uint (t : Source.IntTy) (unsigned : t.signed = false) : Prim .uint (.int t)
  | int (t : Source.IntTy) (signed : t.signed = true) : Prim .int (.int t)
  | address (payable : Bool) : Prim .uint (.address payable)
  | bytes (n : Nat) (h : 1 ≤ n ∧ n ≤ 32) : Prim .uint (.fixedBytes n h)

/-- The Source type of an elementary type the decoders use is a primitive
slot's type, and a storage cell of it holds a value of it. -/
theorem prim_of_primElem {p : PrimTy} {bits : Nat} {e : Source.Elem}
    (he : Decode.primElem p bits = some e) :
    Prim p (e.ty .storage) ∧ (e.ty .storage).cell = e.ty .storage ∧
      e.ty .memory = e.ty .storage := by
  cases p <;> simp only [Decode.primElem] at he <;> split at he <;>
    first
    | (cases he; exact ⟨.bool, rfl, rfl⟩)
    | (cases he; exact ⟨.uint _ rfl, rfl, rfl⟩)
    | (cases he; exact ⟨.int _ rfl, rfl, rfl⟩)
    | cases he

/-- The decoders' type of a primitive at a width is a primitive slot's type. -/
theorem prim_of_primTy {p : PrimTy} {bits : Nat} {τ : Source.STy}
    (h : Decode.primTy p bits = some τ) : Prim p τ := by
  simp only [Decode.primTy, Option.map_eq_some_iff] at h
  obtain ⟨e, he, rfl⟩ := h
  obtain ⟨prim, _, same⟩ := prim_of_primElem he
  rw [same]
  exact prim

end Solidity.Correctness.Lowering.Total.Version
