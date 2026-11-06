import Solidity.Source.Eval
import Solidity.Evm.Machine

/-! G37.03/P4: signature-indexed internal candidates and canonical nonzero
machine tags. This does not change source admission or the source evaluator.
The independent source currently has direct calls, not dynamic-call RExprs.
Zero/out-of-table tags are a dispatch refusal, not a newly chosen halt policy. -/
namespace Solidity.Backend.InternalDispatch
open Source

structure Candidate (E : Source.Env) (ps rs : List STy) (qualifier : Option Source.Mutability) where
  declaration : Decl
  member : declaration ∈ E.decls
  signature : declaration.fnSig E = some (ps, rs)
  mutability : declaration.fnMut = qualifier
  internal : declaration.fnVis ≠ some .external

def Candidate.identity {E ps rs qualifier} (c : Candidate E ps rs qualifier) : DeclName :=
  ⟨c.declaration.scope, c.declaration.name⟩

/-- The table is indexed by the *whole* dependent source signature. Its finite
capacity reserves zero; identity uniqueness rules out ambiguous declarations.
Completeness of an extracted table is a separate obligation, never assumed
from a points-to approximation. -/
structure Table (E : Source.Env) (ps rs : List STy) (qualifier : Option Source.Mutability) where
  size : Nat
  candidate : Fin size → Candidate E ps rs qualifier
  distinct : Function.Injective (fun i => (candidate i).identity)
  capacity : size < Evm.W

variable {E : Source.Env} {ps rs : List STy} {qualifier : Option Source.Mutability}

def Table.tag (t : Table E ps rs qualifier) (i : Fin t.size) : (Fin Evm.W) :=
  ⟨i.val + 1, by have hi := i.isLt; have ht := t.capacity; omega⟩

def Table.decode (t : Table E ps rs qualifier) (word : (Fin Evm.W)) : Option (Fin t.size) :=
  if h : 0 < word.val ∧ word.val ≤ t.size then
    some ⟨word.val - 1, by omega⟩
  else none

theorem Table.tag_injective (t : Table E ps rs qualifier) : Function.Injective t.tag := by
  intro i j h
  apply Fin.ext
  have eq := congrArg Fin.val h
  change i.val + 1 = j.val + 1 at eq
  omega

theorem Table.decode_tag (t : Table E ps rs qualifier) (i : Fin t.size) :
    t.decode (t.tag i) = some i := by
  have hi := i.isLt
  simp only [Table.decode, Table.tag]
  split
  · congr 1
  · rename_i h
    exact False.elim (h (by omega))

theorem Table.decode_zero (t : Table E ps rs qualifier) :
    t.decode (Evm.wmod 0) = none := by
  simp only [Table.decode, Evm.wmod, Nat.zero_mod, Nat.lt_irrefl, false_and, dite_false]

theorem Table.decode_outside (t : Table E ps rs qualifier) (w : (Fin Evm.W))
    (outside : t.size < w.val) : t.decode w = none := by
  simp only [Table.decode]
  split
  · rename_i h
    omega
  · rfl

/-- The source function value keeps its source declaration identity, not a
stringified/erased signature or an arbitrary machine word. -/
def functionName {D : Source.Layout} {τ : STy} (v : Source.Val D τ) : Option DeclName :=
  Source.Val.casesOn (motive := fun _ _ => Option DeclName) v
    (fun {_} _ _ => none)
    (fun _ => none)
    (fun {_} _ => none)
    (fun {_ _} _ _ => none)
    (fun {_} _ _ => none)
    (fun {_} _ => none)
    (fun {_} _ => none)
    (fun {_} _ => none)
    (fun {_ _ _} name => some name)
    (fun {_ _ _} _ _ _ => none)
    (fun {_} _ _ => none)
    (fun {_} _ _ => none)
    (fun {_} _ _ _ => none)

def Table.Rep (t : Table E ps rs qualifier)
    (value : Source.Val E.layout (.fn false ps rs qualifier)) (word : (Fin Evm.W)) : Prop :=
  ∃ i : Fin t.size, functionName value = some (t.candidate i).identity ∧ word = t.tag i

/-- Actual equality of encoded words agrees with source declaration equality;
the guard premise of a dispatch-chain theorem need not be assumed. -/
theorem Table.guard_agrees (t : Table E ps rs qualifier)
    (value : Source.Val E.layout (.fn false ps rs qualifier)) (word : (Fin Evm.W))
    (represented : t.Rep value word) (j : Fin t.size) :
    decide (word = t.tag j) = decide (functionName value = some (t.candidate j).identity) := by
  obtain ⟨i, name, rfl⟩ := represented
  rw [name]
  have tags : t.tag i = t.tag j ↔ i = j := ⟨fun (h : t.tag i = t.tag j) => t.tag_injective h, congrArg t.tag⟩
  have names : (t.candidate i).identity = (t.candidate j).identity ↔ i = j :=
    ⟨fun (h : (t.candidate i).identity = (t.candidate j).identity) => t.distinct h, congrArg (fun k => (t.candidate k).identity)⟩
  simp only [Option.some.injEq, tags, names]

theorem Table.candidate_agrees (t : Table E ps rs qualifier)
    (value : Source.Val E.layout (.fn false ps rs qualifier)) (word : (Fin Evm.W))
    (represented : t.Rep value word) :
    ∃ i : Fin t.size, t.decode word = some i ∧
      functionName value = some (t.candidate i).identity ∧
      (t.candidate i).declaration.fnSig E = some (ps, rs) ∧
      (t.candidate i).declaration.fnMut = qualifier := by
  obtain ⟨i, name, rfl⟩ := represented
  exact ⟨i, t.decode_tag i, name, (t.candidate i).signature, (t.candidate i).mutability⟩

#print axioms Table.guard_agrees
#print axioms Table.candidate_agrees
end Solidity.Backend.InternalDispatch
