import Solidity.Semantics.RecursiveStorage.Copy

/-!
Copy admission over the actual graph, including guarded recursive edges.
A finite node marking is accepted only if it contains the root's node edges,
is closed under every marked declaration's fields, and encounters no mapping.
Checking the certificate follows all edges, unlike the inline layout rank.

This is a typed admission interface for graph clients. The ordinary solc JSON
reader still uses the old type representation and does not call it yet.
-/

namespace Solidity.TypeGraph

/-- Mappings forbid source assignment; arrays and fixed arrays propagate it.
Nodes consult a finite marking, checked against declarations below. -/
def Ty.copyAllowed {n : Nat} (marked : Fin n → Bool) : Ty n → Bool
  | .prim _ => true
  | .node i => marked i
  | .array E => E.copyAllowed marked
  | .fixed E _ => E.copyAllowed marked
  | .mapping _ _ => false

/-- A closed mapping-free subgraph containing the assigned type. -/
def CopyPermit.Valid {n : Nat} (G : Schema n) (T : Ty n) (marked : Fin n → Bool) : Prop :=
  T.copyAllowed marked = true ∧
    ∀ i, marked i = true → ∀ f ∈ G.fields i, f.2.copyAllowed marked = true

instance {n : Nat} (G : Schema n) (T : Ty n) (marked : Fin n → Bool) :
    Decidable (CopyPermit.Valid G T marked) := by
  unfold CopyPermit.Valid
  infer_instance

structure CopyPermit {n : Nat} (G : Schema n) (T : Ty n) where
  marked : Fin n → Bool
  valid : CopyPermit.Valid G T marked

/-- Check finite compiler-supplied node marks; no admission assertion is trusted. -/
def CopyPermit.check {n : Nat} (G : Schema n) (T : Ty n) (marked : Fin n → Bool) :
    Option (CopyPermit G T) :=
  if h : CopyPermit.Valid G T marked then some ⟨marked, h⟩ else none

/-- Reification when an importer emits the checked Boolean certificate. -/
def CopyPermit.checked {n : Nat} {G : Schema n} {T : Ty n} (marked : Fin n → Bool)
    (h : decide (CopyPermit.Valid G T marked) = true) : CopyPermit G T :=
  ⟨marked, of_decide_eq_true h⟩

theorem CopyPermit.no_mapping {n : Nat} {G : Schema n} {K : PrimTy} {V : Ty n}
    (permit : CopyPermit G (.mapping K V)) : False := by
  have h : false = true := permit.valid.1
  cases h

/-- A permit is inherited by every well-typed selector. In particular, the
node case uses the checked declaration closure rather than the layout rank. -/
def CopyPermit.step {n : Nat} {G : Schema n} {A B : Ty n}
    (permit : CopyPermit G A) (selector : Step G A B) : CopyPermit G B := by
  refine ⟨permit.marked, ⟨?_, permit.valid.2⟩⟩
  cases selector with
  | field position =>
    obtain ⟨f, hf⟩ := position.mem
    exact permit.valid.2 _ permit.valid.1 (f, _) hf
  | index _ => exact permit.valid.1
  | fixed _ => exact permit.valid.1
  | key _ => exact False.elim (CopyPermit.no_mapping permit)

/-- Every finite path remains in the checked mapping-free subgraph. -/
def CopyPermit.along {n : Nat} {G : Schema n} :
    {A B : Ty n} → CopyPermit G A → Path G A B → CopyPermit G B
  | _, _, permit, .nil => permit
  | _, _, permit, .cons selector rest => (permit.step selector).along rest

theorem CopyPermit.no_mapping_path {n : Nat} {G : Schema n} {T V : Ty n} {K : PrimTy}
    (permit : CopyPermit G T) (path : Path G T (.mapping K V)) : False :=
  (permit.along path).no_mapping

/-- Source-facing assignment requires mapping freedom. Internal `write` remains
available for the storage algebra, whose mapping case preserves the old value. -/
def Value.assign {n : Nat} {G : Schema n} {A T : Ty n}
    (root : Value G A) (dst : Path G A T) (_permit : CopyPermit G T)
    (src : Value G T) : Option (Value G A) := root.write dst src

/-- Source-facing path copy checks the same recursive type certificate. -/
def Value.assignAt {n : Nat} {G : Schema n} {A T : Ty n}
    (root : Value G A) (dst src : Path G A T) (_permit : CopyPermit G T) :
    Option (Value G A) := root.copyAt dst src

end Solidity.TypeGraph
