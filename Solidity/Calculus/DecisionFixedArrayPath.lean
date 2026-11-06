import Solidity.Calculus.FixedArrayRoot

/-!
# Fixed-array flooring below an intrinsic path

Rebuild a fixed array reached through fields, mapping keys or array indices.
The existing optional lookup/save APIs preserve absence. This additive component
does not change the source classifier, finite-set collector or decision route.
-/
namespace Solidity.Decide

/-- Read the selected fixed array, rebuild its same-length vector and save it
back through the original typed prefix. An absent prefix returns none. -/
def fixedFloorAtPath {T E : Ty} {n : Nat} (p : Path T (.ref (.fixed E n)))
    (B : List Int) (x : SVal T) : Option (SVal T) := do
  let v ← x.findM p
  x.saveM p (fixedFloorValue B v)

/-- An absent prefix is preserved as a refusal; no default object is installed. -/
theorem fixedFloorAtPath_absent {T E : Ty} {n : Nat} (p : Path T (.ref (.fixed E n)))
    (B : List Int) (x : SVal T) (hx : x.findM p = none) : fixedFloorAtPath p B x = none := by
  simp only [fixedFloorAtPath, hx, Option.bind_eq_bind, Option.bind_none]

/-- Actual prefix presence suffices for the save; no future save-success premise is needed. -/
theorem fixedFloorAtPath_exists {T E : Ty} {n : Nat} (p : Path T (.ref (.fixed E n)))
    (B : List Int) (x : SVal T) {v : SVal (.ref (.fixed E n))} (hx : x.findM p = some v) :
    ∃ x' : SVal T, fixedFloorAtPath p B x = some x' := by
  obtain ⟨x', hs⟩ := SVal.saveM_of_findM x p hx (fixedFloorValue B v)
  exact ⟨x', by simp only [fixedFloorAtPath, hx, Option.bind_eq_bind, Option.bind_some, hs]⟩

/-- A successful reconstruction gives the actual typed save and selected old value. -/
theorem fixedFloorAtPath_saved {T E : Ty} {n : Nat} (p : Path T (.ref (.fixed E n)))
    (B : List Int) (x : SVal T) {x' : SVal T} (h : fixedFloorAtPath p B x = some x') :
    ∃ v : SVal (.ref (.fixed E n)), x.findM p = some v ∧
      x.saveM p (fixedFloorValue B v) = some x' := by
  exact Option.bind_eq_some_iff.mp h

/-- Every typed continuation through a selected element reads its original floored index,
including absent element continuations and indices outside the fixed length. -/
theorem fixedFloorAtPath_find {T E U : Ty} {n : Nat} (p : Path T (.ref (.fixed E n)))
    (B : List Int) (x : SVal T) {x' : SVal T} (h : fixedFloorAtPath p B x = some x')
    (hn : (n : Int) ∈ B) (i : PrimTy.uint.Denote) (q : Path E U) :
    x'.findM (p.append (.atF i q)) =
      x.findM (p.append (.atF (fixedFloorIndex B i) q)) := by
  obtain ⟨v, hv, hs⟩ := fixedFloorAtPath_saved p B x h
  rw [SVal.findM_append, SVal.findM_saveM x p _ hs, Option.bind_some,
    fixedFloorValue_find B v hn, SVal.findM_append, hv, Option.bind_some]

/-- A path that diverges from the selected array prefix is unchanged. -/
theorem fixedFloorAtPath_diverges {T E U : Ty} {n : Nat} (p : Path T (.ref (.fixed E n)))
    (B : List Int) (x : SVal T) {x' : SVal T} (h : fixedFloorAtPath p B x = some x')
    (q : Path T U) (hd : Path.Diverges p q) : x'.findM q = x.findM q := by
  obtain ⟨v, hv, hs⟩ := fixedFloorAtPath_saved p B x h
  exact SVal.findM_saveM_diverges hd x (fixedFloorValue B v) hs

/-- Presence plus the length breakpoint constructs the rebuilt enclosing value
with both its full indexed lookup equation and its diverging-path frame. -/
theorem fixedFloorAtPath_reconstruction {T E : Ty} {n : Nat}
    (p : Path T (.ref (.fixed E n))) (B : List Int) (x : SVal T)
    {v : SVal (.ref (.fixed E n))} (hx : x.findM p = some v) (hn : (n : Int) ∈ B) :
    ∃ x' : SVal T, fixedFloorAtPath p B x = some x' ∧
      (∀ {U : Ty} (i : PrimTy.uint.Denote) (q : Path E U),
        x'.findM (p.append (.atF i q)) =
          x.findM (p.append (.atF (fixedFloorIndex B i) q))) ∧
      (∀ {U : Ty} (q : Path T U), Path.Diverges p q → x'.findM q = x.findM q) := by
  obtain ⟨x', hs⟩ := fixedFloorAtPath_exists p B x hx
  exact ⟨x', hs, fun i q => fixedFloorAtPath_find p B x hs hn i q,
    fun q hd => fixedFloorAtPath_diverges p B x hs q hd⟩

end Solidity.Decide
