import Solidity.Frontend.SolcJson.YulOccurrenceSchema

/-! Complete collection of schema-selected actual AST JSON positions/roles.
Every emitted position carries OccurrenceD, and every such position is covered
by a successful collection. The existing raw-input decoder bound is an input;
no bound sufficiency, Source namespace or reference-accounting theorem follows. -/
namespace Solidity.Frontend.YulJson.Occurrences
open Lean (Json)

structure Collected (root : Json) (start : Bool) where
  occurrences : List (Occurrence root start)
  complete : ∀ {path write node}, OccurrenceD root start path write node →
    ∃ occurrence ∈ occurrences,
      occurrence.path = path ∧ occurrence.write = write ∧ occurrence.node = node

inductive CheckedChildren (root : Json) (start : Bool) : List (Child root start) → Type where
  | nil : CheckedChildren root start []
  | cons {child rest} : Collected child.node child.role → CheckedChildren root start rest →
      CheckedChildren root start (child::rest)

def CheckedChildren.flatten {root start entries}
    (checked : CheckedChildren root start entries) : List (Occurrence root start) := by
  apply CheckedChildren.casesOn (motive := fun _ _ => List (Occurrence root start)) checked
  case nil => exact []
  case cons =>
    intro child rest first remaining
    exact first.occurrences.map child.liftOccurrence ++ remaining.flatten
termination_by structural checked

theorem CheckedChildren.flatten_cons {root start child rest}
    (first : Collected child.node child.role) (remaining : CheckedChildren root start rest) :
    (CheckedChildren.cons (child := child) first remaining).flatten =
      first.occurrences.map child.liftOccurrence ++ remaining.flatten := rfl

def checkChildren {root start}
    (run : ∀ child : Child root start, Except YulJson.Error (Collected child.node child.role)) :
    (entries : List (Child root start)) → Except YulJson.Error (CheckedChildren root start entries)
  | [] => .ok .nil
  | child::rest => do
      let first ← run child
      let remaining ← checkChildren run rest
      pure (.cons first remaining)

theorem CheckedChildren.covers {root start entries}
    (checked : CheckedChildren root start entries) (child : Child root start)
    (member : child ∈ entries) {path write node}
    (inside : OccurrenceD child.node child.role path write node) :
    ∃ occurrence ∈ checked.flatten, occurrence.path = child.edge::path ∧
      occurrence.write = write ∧ occurrence.node = node := by
  induction checked with
  | nil => cases member
  | @cons selected rest first remaining ih =>
      rcases List.mem_cons.mp member with same | member
      · subst child
        obtain ⟨found,found_mem,samePath,sameWrite,sameNode⟩ := first.complete inside
        refine ⟨selected.liftOccurrence found,?_,?_,sameWrite,sameNode⟩
        · rw [flatten_cons]
          exact List.mem_append_left _ (List.mem_map.mpr ⟨found,found_mem,rfl⟩)
        · exact congrArg (List.cons selected.edge) samePath
      · obtain ⟨found,found_mem,samePath,sameWrite,sameNode⟩ := ih member
        refine ⟨found,?_,samePath,sameWrite,sameNode⟩
        rw [flatten_cons]
        exact List.mem_append_right _ found_mem

def Collected.fromChildren {root start} (children : Children root start)
    (checked : CheckedChildren root start children.entries) : Collected root start :=
  ⟨checked.flatten,by
    intro path write node occurrence
    obtain ⟨child,member,rest,same,inside⟩ := children.cover occurrence
    obtain ⟨found,found_mem,samePath,sameWrite,sameNode⟩ := checked.covers child member inside
    exact ⟨found,found_mem,samePath.trans same.symm,sameWrite,sameNode⟩⟩

def Collected.identifier (root : Json) (start : Bool) (identifier : isIdentifier root = true) :
    Collected root start :=
  ⟨[⟨[],start,root,.identifier identifier⟩],by
    intro path write node occurrence
    cases occurrence with
    | identifier _ => exact ⟨_,List.mem_cons_self,rfl,rfl,rfl⟩
    | array index _ => cases (show false = true from identifier)
    | object index notIdentifier _ _ => cases (notIdentifier.symm.trans identifier)⟩

def Collected.empty (root : Json) (start : Bool)
    (impossible : ∀ {path write node}, OccurrenceD root start path write node → False) :
    Collected root start :=
  ⟨[],by intro path write node occurrence; exact False.elim (impossible occurrence)⟩

def collect (fuel : Nat) (root : Json) (start : Bool := false) :
    Except YulJson.Error (Collected root start) :=
  match fuel with
  | 0 => .error .depth
  | fuel+1 =>
      match root with
      | .null => pure (Collected.empty .null start (by
          intro path write node occurrence
          cases occurrence with
          | identifier yes => cases (show false = true from yes)))
      | .bool value => pure (Collected.empty (.bool value) start (by
          intro path write node occurrence
          cases occurrence with
          | identifier yes => cases (show false = true from yes)))
      | .num value => pure (Collected.empty (.num value) start (by
          intro path write node occurrence
          cases occurrence with
          | identifier yes => cases (show false = true from yes)))
      | .str value => pure (Collected.empty (.str value) start (by
          intro path write node occurrence
          cases occurrence with
          | identifier yes => cases (show false = true from yes)))
      | .arr values => do
          let children := arrayChildren values start
          let checked ← checkChildren (fun child => collect fuel child.node child.role) children.entries
          pure (Collected.fromChildren children checked)
      | .obj fields =>
          match identifier : isIdentifier (.obj fields) with
          | true => pure (Collected.identifier (.obj fields) start identifier)
          | false => do
              let children := objectChildren fields start identifier
              let checked ← checkChildren (fun child => collect fuel child.node child.role) children.entries
              pure (Collected.fromChildren children checked)
termination_by structural fuel

end Solidity.Frontend.YulJson.Occurrences
