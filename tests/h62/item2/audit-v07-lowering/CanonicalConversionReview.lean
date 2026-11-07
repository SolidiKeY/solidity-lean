import tests.«primitive-packets-1105».Constants.H57ConversionTransport

/-!
Guarded regression: the mapFree API migration must preserve all scalar conversion
observations used by the nineteen frozen V07 headers, without asserting global
old/new conversion equality. Reuse the existing complete implicitV0 and retain
the complete frozen explicit body under a versioned name. Frozen interfaces,
width/range/nominal premises, and strict original fidelity remain unchanged.
-/
namespace Solidity.H62.AuditV07.CanonicalConversionReview
open Solidity.Source
open Solidity.Backend.PrimitivePackets.Constants.H57ConversionTransport
  (implicitV0 struct_copy_differs)

def explicitV0 (isBase : DeclName → DeclName → Bool) (s t : STy) : Bool :=
  implicitV0 isBase s t ||
  match s, t with
  | .int a, .int b => a.signed == b.signed || a.bits == b.bits
  | .int a, .fixedBytes n _ | .fixedBytes n _, .int a => !a.signed && a.bits == 8 * n
  | .int a, .address p | .address p, .int a => !p && !a.signed && a.bits == 160
  | .fixedBytes n _, .address false | .address _, .fixedBytes n _ => n == 20
  | .fixedBytes _ _, .fixedBytes _ _ => true
  | .address _, .address false => true
  | .contract _, .address false | .address _, .contract _ => true
  | .int _, .enum _ | .enum _, .int _ => true
  | .fixed _, .fixed _ | .fixed _, .int _ => true
  | .int a, .fixed f => a.signed == f.signed && a.bits == f.bits
  | .fixed f, .fixedBytes n _ | .fixedBytes n _, .fixed f => f.bits == 8 * n
  | .bytes l, .string l' | .string l, .bytes l' => l == l'
  | .bytes _, .fixedBytes _ _ => true
  | .rational q, .int a => (q.toIntExplicit? a).isSome
  | .rational q, .fixed f => (q.toFixedExplicit? f).isSome
  | .rational q, .address false => decide (q.FitsInt IntTy.u160)
  | .rational q, .enum _ => q.isInt && decide (0 ≤ q.toInt)
  | .hexConst q _, .int a => (q.toIntExplicit? a).isSome
  | .hexConst q _, .fixed f => (q.toFixedExplicit? f).isSome
  | .hexConst q _, .address false => decide (q.FitsInt IntTy.u160)
  | .hexConst q _, .enum _ => q.isInt && decide (0 ≤ q.toInt)
  | _, _ => false

inductive Scalar where
  | int (t : IntTy)
  | address (payable : Bool)
  | enum (d : DeclName)
  | udvt (d : DeclName)
  | rational (q : Q)

def Scalar.ty : Scalar → STy
  | .int t => .int t
  | .address p => .address p
  | .enum d => .enum d
  | .udvt d => .udvt d
  | .rational q => .rational q

/-- Equality holds for all scalar inputs and arbitrary base/mapFree functions. -/
theorem implicit_scalar_agrees (B : DeclName → DeclName → Bool)
    (M : DeclName → Bool) (s t : Scalar) :
    implicitV0 B s.ty t.ty = STy.implicit B M s.ty t.ty := by
  cases s <;> cases t <;> rfl

/-- The same total scalar family covers every explicit-conversion header. -/
theorem explicit_scalar_agrees (B : DeclName → DeclName → Bool)
    (M : DeclName → Bool) (s t : Scalar) :
    explicitV0 B s.ty t.ty = STy.explicit B M s.ty t.ty := by
  cases s <;> cases t <;> rfl

/-- Struct-copy behavior differs, so no unrestricted equivalence is inferred. -/
theorem explicit_struct_copy_differs (B : DeclName → DeclName → Bool) (d : DeclName) :
    explicitV0 B (.struct .storage d) (.struct .memory d) = true ∧
      STy.explicit B (fun _ => false) (.struct .storage d) (.struct .memory d) = false := by
  change (implicitV0 B (.struct .storage d) (.struct .memory d) || false) = true ∧
    (STy.implicit B (fun _ => false) (.struct .storage d) (.struct .memory d) || false) = false
  simpa only [Bool.or_false] using struct_copy_differs B d

#print axioms explicitV0
#print axioms implicit_scalar_agrees
#print axioms explicit_scalar_agrees
#print axioms explicit_struct_copy_differs
end Solidity.H62.AuditV07.CanonicalConversionReview
