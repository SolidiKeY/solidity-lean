import Solidity.Calculus.DecisionFixedArrayPath

/-! # Simultaneous reconstruction at two disjoint intrinsic array prefixes
This is an additive value/path component. It does not alter array collection,
source profiles, observations, defaults or the decision pipeline.
-/
namespace Solidity

/-- Typed path divergence is symmetric. -/
theorem Path.Diverges.symm {T U W : Ty} {p : Path T U} {q : Path T W}
    (h : Path.Diverges p q) : Path.Diverges q p := by
  induction h with
  | field h h' p q hn => exact .field h' h q p (Ne.symm hn)
  | fieldIn h hd ih => exact .fieldIn h ih
  | «at» p q hn => exact .«at» q p (Ne.symm hn)
  | atIn i hd ih => exact .atIn i ih
  | atF p q hn => exact .atF q p (Ne.symm hn)
  | atFIn i hd ih => exact .atFIn i ih
  | key p q hn => exact .key q p (Ne.symm hn)
  | keyIn k hd ih => exact .keyIn k ih

/-- Extending a diverging query stays disjoint, at every intrinsic result type. -/
theorem Path.Diverges.append_right {T U W V : Ty} {p : Path T U} {q : Path T W}
    (h : Path.Diverges p q) (r : Path W V) : Path.Diverges p (q.append r) := by
  induction h with
  | field h h' p q hn => rw [Path.append_field]; exact .field h h' p (q.append r) hn
  | fieldIn h hd ih => rw [Path.append_field]; exact .fieldIn h (ih r)
  | «at» p q hn => rw [Path.append_at]; exact .«at» p (q.append r) hn
  | atIn i hd ih => rw [Path.append_at]; exact .atIn i (ih r)
  | atF p q hn => rw [Path.append_atF]; exact .atF p (q.append r) hn
  | atFIn i hd ih => rw [Path.append_atF]; exact .atFIn i (ih r)
  | key p q hn => rw [Path.append_key]; exact .key p (q.append r) hn
  | keyIn k hd ih => rw [Path.append_key]; exact .keyIn k (ih r)

namespace Decide

/-- Rebuild the two actual selected arrays in sequence, preserving optional absence. -/
def fixedFloorPair {T E F : Ty} {n m : Nat}
    (p : Path T (.ref (.fixed E n))) (B : List Int)
    (q : Path T (.ref (.fixed F m))) (D : List Int) (x : SVal T) : Option (SVal T) := do
  let y ← fixedFloorAtPath p B x
  fixedFloorAtPath q D y

theorem fixedFloorPair_saved {T E F : Ty} {n m : Nat}
    (p : Path T (.ref (.fixed E n))) (B : List Int)
    (q : Path T (.ref (.fixed F m))) (D : List Int) (x : SVal T) {z : SVal T}
    (h : fixedFloorPair p B q D x = some z) :
    ∃ y : SVal T, fixedFloorAtPath p B x = some y ∧ fixedFloorAtPath q D y = some z :=
  Option.bind_eq_some_iff.mp h

/-- Both actual prefixes present plus divergence construct the second save too. -/
theorem fixedFloorPair_exists {T E F : Ty} {n m : Nat}
    (p : Path T (.ref (.fixed E n))) (B : List Int)
    (q : Path T (.ref (.fixed F m))) (D : List Int) (x : SVal T)
    (hd : Path.Diverges p q) {a : SVal (.ref (.fixed E n))} {b : SVal (.ref (.fixed F m))}
    (ha : x.findM p = some a) (hb : x.findM q = some b) :
    ∃ z : SVal T, fixedFloorPair p B q D x = some z := by
  obtain ⟨y, hy⟩ := fixedFloorAtPath_exists p B x ha
  have hq : y.findM q = some b := (fixedFloorAtPath_diverges p B x hy q hd).trans hb
  obtain ⟨z, hz⟩ := fixedFloorAtPath_exists q D y hq
  exact ⟨z, by simp only [fixedFloorPair, hy, Option.bind_eq_bind, Option.bind_some, hz]⟩

/-- The second disjoint save preserves every first-array continuation. -/
theorem fixedFloorPair_find_left {T E F U : Ty} {n m : Nat}
    (p : Path T (.ref (.fixed E n))) (B : List Int)
    (q : Path T (.ref (.fixed F m))) (D : List Int) (x : SVal T) {z : SVal T}
    (h : fixedFloorPair p B q D x = some z) (hd : Path.Diverges p q)
    (hn : (n : Int) ∈ B) (i : PrimTy.uint.Denote) (r : Path E U) :
    z.findM (p.append (.atF i r)) = x.findM (p.append (.atF (fixedFloorIndex B i) r)) := by
  obtain ⟨y, hy, hz⟩ := fixedFloorPair_saved p B q D x h
  exact (fixedFloorAtPath_diverges q D y hz _ (hd.symm.append_right (.atF i r))).trans
    (fixedFloorAtPath_find p B x hy hn i r)

/-- The first disjoint save preserves every original second-array continuation. -/
theorem fixedFloorPair_find_right {T E F U : Ty} {n m : Nat}
    (p : Path T (.ref (.fixed E n))) (B : List Int)
    (q : Path T (.ref (.fixed F m))) (D : List Int) (x : SVal T) {z : SVal T}
    (h : fixedFloorPair p B q D x = some z) (hd : Path.Diverges p q)
    (hm : (m : Int) ∈ D) (i : PrimTy.uint.Denote) (r : Path F U) :
    z.findM (q.append (.atF i r)) = x.findM (q.append (.atF (fixedFloorIndex D i) r)) := by
  obtain ⟨y, hy, hz⟩ := fixedFloorPair_saved p B q D x h
  exact (fixedFloorAtPath_find q D y hz hm i r).trans
    (fixedFloorAtPath_diverges p B x hy _ (hd.append_right (.atF (fixedFloorIndex D i) r)))

/-- Observations at a path diverging from both prefixes are unchanged. -/
theorem fixedFloorPair_frame {T E F U : Ty} {n m : Nat}
    (p : Path T (.ref (.fixed E n))) (B : List Int)
    (q : Path T (.ref (.fixed F m))) (D : List Int) (x : SVal T) {z : SVal T}
    (h : fixedFloorPair p B q D x = some z) (r : Path T U)
    (hp : Path.Diverges p r) (hq : Path.Diverges q r) : z.findM r = x.findM r := by
  obtain ⟨y, hy, hz⟩ := fixedFloorPair_saved p B q D x h
  exact (fixedFloorAtPath_diverges q D y hz r hq).trans (fixedFloorAtPath_diverges p B x hy r hp)

/-- A missing second disjoint prefix stays absent after the first rebuild. -/
theorem fixedFloorPair_second_absent {T E F : Ty} {n m : Nat}
    (p : Path T (.ref (.fixed E n))) (B : List Int)
    (q : Path T (.ref (.fixed F m))) (D : List Int) (x : SVal T)
    (hd : Path.Diverges p q) (hq : x.findM q = none) : fixedFloorPair p B q D x = none := by
  cases hp : fixedFloorAtPath p B x with
  | none => simp only [fixedFloorPair, hp, Option.bind_eq_bind, Option.bind_none]
  | some y =>
    have hyq : y.findM q = none := (fixedFloorAtPath_diverges p B x hp q hd).trans hq
    simp only [fixedFloorPair, hp, Option.bind_eq_bind, Option.bind_some,
      fixedFloorAtPath_absent q D y hyq]

/-- Simultaneously construct both lookup equations and the full disjoint frame.
Element types, fixed lengths and query result types stay intrinsic and independent. -/
theorem fixedFloorPair_reconstruction {T E F : Ty} {n m : Nat}
    (p : Path T (.ref (.fixed E n))) (B : List Int)
    (q : Path T (.ref (.fixed F m))) (D : List Int) (x : SVal T)
    (hd : Path.Diverges p q) {a : SVal (.ref (.fixed E n))} {b : SVal (.ref (.fixed F m))}
    (ha : x.findM p = some a) (hb : x.findM q = some b)
    (hn : (n : Int) ∈ B) (hm : (m : Int) ∈ D) :
    ∃ z : SVal T, fixedFloorPair p B q D x = some z ∧
      (∀ {U : Ty} (i : PrimTy.uint.Denote) (r : Path E U),
        z.findM (p.append (.atF i r)) = x.findM (p.append (.atF (fixedFloorIndex B i) r))) ∧
      (∀ {U : Ty} (i : PrimTy.uint.Denote) (r : Path F U),
        z.findM (q.append (.atF i r)) = x.findM (q.append (.atF (fixedFloorIndex D i) r))) ∧
      (∀ {U : Ty} (r : Path T U), Path.Diverges p r → Path.Diverges q r →
        z.findM r = x.findM r) := by
  obtain ⟨z, hz⟩ := fixedFloorPair_exists p B q D x hd ha hb
  exact ⟨z, hz, fun i r => fixedFloorPair_find_left p B q D x hz hd hn i r,
    fun i r => fixedFloorPair_find_right p B q D x hz hd hm i r,
    fun r hp hq => fixedFloorPair_frame p B q D x hz r hp hq⟩

end Decide
end Solidity
