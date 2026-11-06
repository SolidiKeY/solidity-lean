import Solidity.Yul.Views.InventoryUnchanged

/-! Constructor preparation from ACTUAL typed heap contents and Placement.
No supplied image inventory, decoder inverse, or alternative source state.
Failure is unsupported preparation, not a source/Yul execution result. -/
namespace Solidity.Yul.Views

/-- Finite dependent traversal; its only bound is the actual declared length. -/
def prepareFin : (n : Nat) → (A : Fin n → Type) → ((i : Fin n) → Option (A i)) → Option ((i : Fin n) → A i)
  | 0, _, _ => some (fun i => Fin.elim0 i)
  | n+1, A, f => do
    let x ← f 0
    let xs ← prepareFin n (fun i => A i.succ) (fun i => f i.succ)
    pure (Fin.cases x xs)

/-- Actual owned reference fallback, using constructor elimination. -/
def prepareOwnedReference {D : Source.Layout} {h : Source.Heap D} (p : Placement h)
    {τ : Source.STy} (v : Source.Val D τ) : Option {w // MemoryElement p v w} := by
  cases v with
  | memRef loc a =>
    exact (h.ty a).pbind (fun σ owned =>
      if shape : σ.memShape = τ.memShape then
        some ⟨ownedPointerWord p a σ owned,.pointer loc a σ owned shape⟩ else none)
  | _ => exact none

/-- Canonical word or an actual typed owned memory reference. -/
def prepareElement {D : Source.Layout} {h : Source.Heap D} (p : Placement h)
    {τ : Source.STy} (v : Source.Val D τ) : Option {w // MemoryElement p v w} :=
  match word : v.word with
  | some w => some ⟨w,.scalar v w word⟩
  | none => prepareOwnedReference p v

/-- One actual member must be a value/pointer cell, never inline child data. -/
structure PreparedMember {D : Source.Layout} {h : Source.Heap D} (p : Placement h)
    {τ : Source.STy} (d : Source.Data D τ) where
  value : Source.Val D τ
  word : Roadmap.Word
  same : d = .val value
  encoded : MemoryElement p value word

def prepareMember {D : Source.Layout} {h : Source.Heap D} (p : Placement h)
    {τ : Source.STy} (d : Source.Data D τ) : Option (PreparedMember p d) := by
  cases d with
  | val v => exact (prepareElement p v).map (fun e => ⟨v,e.1,rfl,e.2⟩)
  | _ => exact none

/-- Recursion is on the declared member list, using actual constructor elimination. -/
def prepareFields {D : Source.Layout} {h : Source.Heap D} (p : Placement h) :
    (τs : List Source.STy) → (fs : Source.DataList D τs) → Option ({ws // MemoryFields p fs ws})
  | [], fs => by cases fs; exact some ⟨[],.nil⟩
  | _ :: τs, fs => by
    cases fs with
    | cons d ds =>
      exact (prepareMember p d).bind (fun x => (prepareFields p τs ds).map (fun tail =>
        ⟨x.word :: tail.1, Eq.mpr (congrArg (fun d => MemoryFields p (.cons d ds) (x.word :: tail.1)) x.same) (MemoryFields.cons x.value x.word x.encoded ds tail.1 tail.2)⟩))

def prepareHeapImage {D : Source.Layout} {h : Source.Heap D} (p : Placement h)
    (a : Nat) (τ : Source.STy) (d : Source.Data D τ) (found : h.get a = some ⟨τ,d⟩) : Option (MemoryImage p d) := by
  cases d with
  | val v => exact False.elim (no_value_memory_shape v _ (p.typed a _ _ found))
  | @bytes l bs =>
    cases l with
    | memory => exact some (.bytes bs (heapByte_length_bound h p a false bs found))
    | _ => exact none
  | @string l bs =>
    cases l with
    | memory => exact some (.string bs (heapByte_length_bound h p a true bs found))
    | _ => exact none
  | @array l σ k n hl xs =>
    exact (prepareFin n (fun i => PreparedMember p (xs i)) (fun i => prepareMember p (xs i))).map (fun members => by
      let values := fun i : Fin n => (members i).value
      let words := fun i : Fin n => (members i).word
      have same : xs = fun i => Source.Data.val (values i) := funext (fun i => (members i).same)
      have image := memoryArrayImage p a n hl values words (fun i => (members i).encoded) (same ▸ found)
      rw [same]
      exact image)
  | @struct l name fs => exact (prepareFields p _ fs).map (fun fields => .words _ _ (.strct fs fields.1 fields.2))
  | mapping m => exact False.elim (by have impossible := p.typed a _ _ found; cases impossible)

end Solidity.Yul.Views
