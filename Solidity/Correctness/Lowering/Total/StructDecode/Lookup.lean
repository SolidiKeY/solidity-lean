import Solidity.Correctness.Lowering.Total.ReferenceDecode

/-!
# Helpers of the struct-declaration decoder

Facts that do not mention the decoder: an ordered list correspondence; a contract's own declarations of a name
are what `Source.Env.lookup` returns from that contract; the first table row of
a key among the rows of that key; and the reference spelling of a type without
a mapping outside its structs, which does not depend on the location.
-/
namespace Solidity.Correctness.Lowering.Total.StructDecode

open Solidity.Semantics (lookupBy)
open Source (DataLoc)
open ReferenceDecode (spellType spellRef)

/-- Ordered correspondence of two lists: neither has an extra element. -/
inductive Pairs {α β : Type} (R : α → β → Prop) : List α → List β → Prop where
  | nil : Pairs R [] []
  | cons {a b as bs} : R a b → Pairs R as bs → Pairs R (a :: as) (b :: bs)

theorem Pairs.length {α β : Type} {R : α → β → Prop} {as : List α} {bs : List β}
    (h : Pairs R as bs) : as.length = bs.length := by
  induction h with
  | nil => rfl
  | cons _ _ ih => simp [ih]

/-- A declaration of the scope `c` named `w`, as `Source.Env.declared` asks. -/
def named (c : String) (w : Name) (d : Source.Decl) : Bool :=
  d.scope == some c && d.name == w && w != ""

/-- A linearization starts at its own contract. -/
theorem chain_head (E : Source.Env) (c : String) :
    ∃ rest, (E.linearize c).getD [c] = c :: rest := by
  unfold Source.Env.linearize Source.Env.linearizeF
  dsimp only
  generalize List.mapM (E.linearizeF E.decls.length) (E.bases c).reverse = r
  cases r with
  | none => exact ⟨[], rfl⟩
  | some ls =>
    dsimp only
    generalize Source.Env.merge _ _ = m
    cases m with
    | none => exact ⟨[], rfl⟩
    | some l => exact ⟨l, rfl⟩

/-- A name a contract declares itself denotes exactly its own declarations of
it, from that contract: they shadow every base and the file level. -/
theorem lookup_declared {E : Source.Env} {c x : String} (h : E.declared (some c) x ≠ []) :
    E.lookup (some c) x = E.declared (some c) x := by
  have vis : E.visible (some c) (some c) x = E.declared (some c) x := by
    simp [Source.Env.visible]
  obtain ⟨rest, chain⟩ := chain_head E c
  have ne : (E.declared (some c) x).isEmpty = false := by
    cases hd : E.declared (some c) x with
    | nil => exact absurd hd h
    | cons _ _ => rfl
  simp [Source.Env.lookup, chain, vis, ne]

/-- The first row of a key is the head of the rows of that key. -/
theorem lookupBy_filter {α : Type} (w : Name) : ∀ l : List (Name × α),
    lookupBy w l = ((l.filter (·.1 == w)).head?).map (·.2)
  | [] => rfl
  | (k, v) :: l => by
      by_cases hk : k = w
      · subst hk; simp [lookupBy]
      · have hk' : ¬ w = k := fun h => hk h.symm
        simp [lookupBy, hk, hk', lookupBy_filter w l]

mutual
/-- No mapping outside the structs the type mentions. -/
def maplessTy : Ty → Bool
  | .prim _ => true
  | .ref R => maplessRef R
def maplessRef : RefTy → Bool
  | .struct _ => true
  | .array T | .fixed T _ => maplessTy T
  | .mapping _ _ => false
end

variable {C : Contract} {widths : List (Name × Nat)}

mutual
/-- Only a mapping's spelling asks for the location. -/
theorem spellType_loc : (T : Ty) → (key : Name) → (loc : DataLoc) → maplessTy T = true →
    spellType C widths key loc T = spellType C widths key .storage T
  | .prim _, _, _, _ => by simp only [spellType]
  | .ref R, key, loc, h => by
      simpa only [spellType] using spellRef_loc R key loc (by simpa only [maplessTy] using h)
theorem spellRef_loc : (R : RefTy) → (key : Name) → (loc : DataLoc) → maplessRef R = true →
    spellRef C widths key loc R = spellRef C widths key .storage R
  | .struct _, _, _, _ => by simp only [spellRef]
  | .array T, key, loc, h => by
      simp only [spellRef, spellType_loc T _ loc (by simpa only [maplessRef] using h)]
  | .fixed T _, key, loc, h => by
      simp only [spellRef, spellType_loc T _ loc (by simpa only [maplessRef] using h)]
  | .mapping _ _, _, _, h => by simp [maplessRef] at h
end

end Solidity.Correctness.Lowering.Total.StructDecode
