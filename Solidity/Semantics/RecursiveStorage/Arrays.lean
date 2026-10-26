import Solidity.Semantics.RecursiveStorage.Clear
import Solidity.Semantics.RecursiveStorage.Paths

/-! Empty push preserves retained reference slots and resets the new primitive
slot, as the existing interpreter does. Pop clears its former last live slot
and leaves every older shadow slot untouched. Logical paths can still reach
retained slots; source indexing uses the additional live-length check. -/

namespace Solidity.TypeGraph

def Value.push {n : Nat} {G : Schema n} {E : Ty n} :
    Value G (.array E) → Option (Value G (.array E))
  | .array extent length _ slots =>
    if h : length.val + 1 < 2 ^ 256 then
      let extent' : Extent := ⟨max extent.val (length.val + 1), by
        have he := extent.isLt
        omega⟩
      some (.array extent' ⟨length.val + 1, h⟩ (Nat.le_max_right _ _)
        (fun i => if E.isPrimitive = true ∧ i.val = length.val then .absent
          else if hi : i.val < extent.val then slots ⟨i.val, hi⟩ else .absent))
    else none

def Value.pop {n : Nat} {G : Schema n} {E : Ty n} :
    Value G (.array E) → Option (Value G (.array E))
  | .array extent length le slots =>
    if h : 0 < length.val then
      some (.array extent ⟨length.val - 1, by have hl := length.isLt; omega⟩
        (by change length.val - 1 ≤ extent.val; omega)
        (fun i => if i.val = length.val - 1 then (slots i).clear else slots i))
    else none

def Step.getLive {n : Nat} {G : Schema n}
    (defaults : (T : Ty n) → Value G T) :
    {A B : Ty n} → Step G A B → Value G A → Option (Value G B)
  | _, _, s@(.index i), v@(.array _ length _ _) =>
    if i.val < length.val then s.get defaults v else none
  | _, _, s, v => s.get defaults v

def Path.readLive {n : Nat} {G : Schema n}
    (defaults : (T : Ty n) → Value G T) :
    {A B : Ty n} → Path G A B → Value G A → Option (Value G B)
  | _, _, .nil, v => some v
  | _, _, .cons s p, v => (s.getLive defaults v).bind (p.readLive defaults)

def Value.find {n : Nat} {G : Schema n} {A B : Ty n}
    (v : Value G A) (p : Path G A B) : Option (Value G B) := p.read Value.dflt v

def Value.save {n : Nat} {G : Schema n} {A B : Ty n}
    (v : Value G A) (p : Path G A B) (value : Value G B) : Option (Value G A) :=
  p.save Value.dflt v value

def Value.delAt {n : Nat} {G : Schema n} {A B : Ty n}
    (v : Value G A) (p : Path G A B) : Option (Value G A) := do
  let old ← v.find p
  v.save p old.clear

def Ty.Head {n : Nat} : Ty n → Type
  | .prim p => p.Denote
  | .array _ => Index × Extent
  | _ => Unit

def Value.head {n : Nat} {G : Schema n} : {T : Ty n} → Value G T → T.Head
  | _, .prim v => v
  | _, .node _ => ()
  | _, .array extent length _ _ => (length, extent)
  | _, .fixed _ => ()
  | _, .mapping _ => ()

def Value.observe {n : Nat} {G : Schema n} {A B : Ty n}
    (v : Value G A) (p : Path G A B) : Option B.Head := (v.find p).map Value.head

/-- Includes failed reads, words, live lengths and retained extents. Raw
constructor equality additionally distinguishes absent and explicit defaults. -/
def Value.ObsEq {n : Nat} {G : Schema n} {T : Ty n} (v w : Value G T) : Prop :=
  ∀ {U : Ty n} (p : Path G T U), v.observe p = w.observe p

theorem Value.find_save {n : Nat} {G : Schema n} {A B : Ty n}
    (root result : Value G A) (p : Path G A B) (v : Value G B)
    (h : root.save p v = some result) : result.find p = some v :=
  p.read_save Value.dflt root result v h

theorem Value.push_length {n : Nat} {G : Schema n} {E : Ty n}
    (v result : Value G (.array E)) (h : v.push = some result) :
    result.length.val = v.length.val + 1 := by
  cases v with
  | array extent length le slots =>
    simp only [Value.push] at h
    split at h
    next cap => cases h; rfl
    next cap => cases h

theorem Value.push_extent {n : Nat} {G : Schema n} {E : Ty n}
    (v result : Value G (.array E)) (h : v.push = some result) :
    v.extent.val ≤ result.extent.val := by
  cases v with
  | array extent length le slots =>
    simp only [Value.push] at h
    split at h
    next cap => cases h; exact Nat.le_max_left _ _
    next cap => cases h

theorem Value.push_keeps_slot {n : Nat} {G : Schema n} {E : Ty n}
    (defaults : (T : Ty n) → Value G T)
    (v result : Value G (.array E)) (i : Index)
    (preserve : E.isPrimitive = false ∨ i.val ≠ v.length.val)
    (allocated : i.val < v.extent.val) (h : v.push = some result) :
    Step.get defaults (.index i) result = Step.get defaults (.index i) v := by
  cases v with
  | array extent length le slots =>
    simp only [Value.push] at h
    split at h
    next cap =>
      cases h
      change i.val < extent.val at allocated
      have hn : ¬ (E.isPrimitive = true ∧ i.val = length.val) := by
        intro ⟨hp, hi⟩
        rcases preserve with notPrim | other
        · rw [notPrim] at hp
          cases hp
        · exact other hi
      have hi : i.val < max extent.val (length.val + 1) :=
        Nat.lt_of_lt_of_le allocated (Nat.le_max_left _ _)
      simp only [Step.get, dif_pos hi, if_neg hn, dif_pos allocated]
    next cap => cases h

theorem Value.pop_length {n : Nat} {G : Schema n} {E : Ty n}
    (v result : Value G (.array E)) (h : v.pop = some result) :
    result.length.val + 1 = v.length.val ∧ result.extent = v.extent := by
  cases v with
  | array extent length le slots =>
    simp only [Value.pop] at h
    split at h
    next live => cases h; constructor; change length.val - 1 + 1 = length.val; omega; rfl
    next live => cases h

end Solidity.TypeGraph
