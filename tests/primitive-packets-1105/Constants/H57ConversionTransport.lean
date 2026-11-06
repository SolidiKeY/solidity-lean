import Solidity.Backend.PrimitivePackets.Constants.Source

/-!
Guarded regression: the added mapFree argument must not hide the frozen
Constants.conversion_refused statement or change its universal rational/integer
domain. implicitV0 preserves the complete original conversion definition under
an explicit versioned name. Transport is proved for rational-to-integer inputs,
for arbitrary base/mapFree functions; global conversion equivalence is false.
The strict original source inventory remains failed and is not re-pinned here.
-/
namespace Solidity.Backend.PrimitivePackets.Constants.H57ConversionTransport
open Solidity.Source

/-- Complete frozen implicit definition, with only its declaration name changed. -/
def implicitV0 (isBase : DeclName → DeclName → Bool) : STy → STy → Bool
  | .int t, .int t' => t.implicit t'
  | .bool, .bool => true
  | .address p, .address p' => p || !p'
  | .fixedBytes n _, .fixedBytes m _ => decide (n ≤ m)
  | .fixed t, .fixed t' => t.implicitOK t'
  | .int t, .fixed f => f.intImplicit t.lo t.hi
  | .enum d, .enum d' | .udvt d, .udvt d' => d == d'
  | .contract d, .contract d' => isBase d d'
  | .bytes l, .bytes l' | .string l, .string l' => l.implicit l'
  | .array l τ n, .array l' τ' n' => τ.same τ' && n == n' && l.implicit l'
  | .struct l d, .struct l' d' => d == d' && l.implicit l'
  | .mapping k v, .mapping k' v' => k.same k' && v.same v'
  | .fn e ps rs m, .fn e' ps' rs' m' => e == e' && STy.sameList ps ps' && STy.sameList rs rs' && m == m'
  | .rational q, .int t => decide (q.FitsInt t)
  | .rational q, .fixed f => (q.toFixed? f).isSome
  | .rational q, .fixedBytes _ _ => q.num == 0
  | .hexConst q _, .int t => decide (q.FitsInt t)
  | .hexConst q _, .fixed f => (q.toFixed? f).isSome
  | .hexConst q n, .fixedBytes m _ => n == m || q.num == 0
  | .stringLit _, .bytes .memory | .stringLit _, .string .memory => true
  | .stringLit s, .fixedBytes n _ => decide (s.length ≤ n)
  | _, _ => false

/-- The rational/integer branch agrees even across different inheritance tests. -/
theorem rational_integer_agrees (oldBase newBase : DeclName → DeclName → Bool)
    (mapFree : DeclName → Bool) (q : Q) (t : IntTy) :
    implicitV0 oldBase (.rational q) (.int t) =
      STy.implicit newBase mapFree (.rational q) (.int t) := rfl

namespace V0

/-- Frozen statement domain, with its conversion function explicitly versioned. -/
theorem conversion_refused (E : Source.Env) (t : Source.IntTy) (z : Int)
    (outside : ¬ (t.lo ≤ z ∧ z ≤ t.hi)) :
    implicitV0 E.isBase (Source.STy.rational (Source.Q.ofInt z)) (.int t) = false :=
  (rational_integer_agrees E.isBase E.isBase E.mapFree (Q.ofInt z) t).trans
    (Solidity.Backend.PrimitivePackets.Constants.conversion_refused E t z outside)

end V0

namespace V1

/-- Exact current statement; no premise on the new environment function is added. -/
theorem conversion_refused (E : Source.Env) (t : Source.IntTy) (z : Int)
    (outside : ¬ (t.lo ≤ z ∧ z ≤ t.hi)) :
    (Source.STy.rational (Source.Q.ofInt z)).implicit E.isBase E.mapFree (.int t) = false :=
  Solidity.Backend.PrimitivePackets.Constants.conversion_refused E t z outside

end V1

/-- Both versions retain the same out-of-range hypothesis for every legal type. -/
theorem refusal_pair (E : Source.Env) (t : IntTy) (z : Int)
    (outside : ¬ (t.lo ≤ z ∧ z ≤ t.hi)) :
    implicitV0 E.isBase (.rational (Q.ofInt z)) (.int t) = false ∧
      STy.implicit E.isBase E.mapFree (.rational (Q.ofInt z)) (.int t) = false :=
  ⟨V0.conversion_refused E t z outside, V1.conversion_refused E t z outside⟩

/-- In-range constants are admitted by both versions; an always-false adapter fails. -/
theorem admission_pair (E : Source.Env) (t : IntTy) (z : Int)
    (inside : t.lo ≤ z ∧ z ≤ t.hi) :
    implicitV0 E.isBase (.rational (Q.ofInt z)) (.int t) = true ∧
      STy.implicit E.isBase E.mapFree (.rational (Q.ofInt z)) (.int t) = true := by
  have h := Solidity.Lowering.V07.IntegerConstants.allowed E t z inside
  exact ⟨(rational_integer_agrees E.isBase E.isBase E.mapFree (Q.ofInt z) t).trans h, h⟩

/-- Every environment/type has a joint refusal witness, not separate premises. -/
theorem refusal_inputs (E : Source.Env) (t : IntTy) :
    ∃ z : Int, ¬ (t.lo ≤ z ∧ z ≤ t.hi) ∧
      implicitV0 E.isBase (.rational (Q.ofInt z)) (.int t) = false ∧
      STy.implicit E.isBase E.mapFree (.rational (Q.ofInt z)) (.int t) = false := by
  have outside : ¬ (t.lo ≤ t.hi + 1 ∧ t.hi + 1 ≤ t.hi) := by omega
  exact ⟨t.hi + 1, outside, refusal_pair E t (t.hi + 1) outside⟩

/-- A completed joint positive certificate inhabits the original input domain. -/
theorem admission_inputs :
    ∃ (E : Source.Env) (t : IntTy) (z : Int), (t.lo ≤ z ∧ z ≤ t.hi) ∧
      implicitV0 E.isBase (.rational (Q.ofInt z)) (.int t) = true ∧
      STy.implicit E.isBase E.mapFree (.rational (Q.ofInt z)) (.int t) = true :=
  ⟨⟨[]⟩, IntTy.u8, 0, by decide, admission_pair ⟨[]⟩ IntTy.u8 0 (by decide)⟩

/-- The migration changes other branches: no global old/new equality is asserted. -/
theorem struct_copy_differs (B : DeclName → DeclName → Bool) (d : DeclName) :
    implicitV0 B (.struct .storage d) (.struct .memory d) = true ∧
      STy.implicit B (fun _ => false) (.struct .storage d) (.struct .memory d) = false := by
  have hd : (d == d) = true := BEq.rfl
  constructor
  · change ((d == d) && true) = true
    rw [hd]
    rfl
  · change (((d == d) && true) && false) = false
    rw [hd]
    rfl

#print axioms implicitV0
#print axioms rational_integer_agrees
#print axioms V0.conversion_refused
#print axioms V1.conversion_refused
#print axioms refusal_pair
#print axioms admission_pair
#print axioms refusal_inputs
#print axioms admission_inputs
#print axioms struct_copy_differs
end Solidity.Backend.PrimitivePackets.Constants.H57ConversionTransport
