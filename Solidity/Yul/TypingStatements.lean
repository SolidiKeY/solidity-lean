import Solidity.Yul.TypingSites

/-! Direct-statement metadata from actual intrinsic block/walk derivations.
Every item retains both environments and the original StatementD. This is
an observer, not another statement representation or execution semantics. -/
namespace Solidity.Yul.TypingStatements
open Solidity.Source (Syn)
open Solidity.Yul.BlockTyping (Env)
open Solidity.Yul.BlockScope (Scope)
open Solidity.Yul.ScopedBlockTyping

structure Item where
  X : List ExternalType
  scope : Scope X
  F : List Sig
  n : Nat
  m : Nat
  environment : Env F n
  control : Control
  tree : Syn .yulStmt
  final : Env F m
  typed : StatementD scope environment control tree final

def Item.ofD {X scope F n E c tree m final}
    (typed : @StatementD X scope F n E c tree m final) : Item :=
  ⟨X,scope,F,n,m,E,c,tree,final,typed⟩

abbrev Trace := List (Nat × Item)
def All (predicate : Nat → Item → Prop) (trace : Trace) : Prop :=
  ∀ entry ∈ trace, predicate entry.1 entry.2

def walk {X scope F n E c body m final}
    (d : @WalkD X scope F n E c body m final) : Nat → Trace := by
  apply WalkD.casesOn
    (motive_2 := fun {X} scope {F} {n} E c body {m} final _ => Nat → Trace) d
  case nil =>
    intro X scope F n E c offset
    exact []
  case cons =>
    intro X scope F n E c first rest m next k final head tail offset
    exact (offset,Item.ofD head)::walk tail (offset+1)
termination_by structural d

def block {X scope F n E c body} (d : @BlockD X scope F n E c body) : Trace := by
  apply BlockD.casesOn
    (motive_1 := fun {X} scope {F} {n} E c body _ => Trace) d
  intro X scope F n E c body headers m final headersD typedWalk
  exact walk typedWalk 0

def everyWalk {X scope F n E c body m final}
    (d : @WalkD X scope F n E c body m final) :
    Nat → (Nat → Item → Prop) → Prop := by
  apply WalkD.casesOn
    (motive_2 := fun {X} scope {F} {n} E c body {m} final _ =>
      Nat → (Nat → Item → Prop) → Prop) d
  case nil =>
    intro X scope F n E c offset predicate
    exact True
  case cons =>
    intro X scope F n E c first rest m next k final head tail offset predicate
    exact predicate offset (Item.ofD head) ∧ everyWalk tail (offset+1) predicate
termination_by structural d

private theorem all_cons (predicate : Nat → Item → Prop) (first : Nat × Item) (rest : Trace) :
    All predicate (first::rest) ↔ predicate first.1 first.2 ∧ All predicate rest := by
  constructor
  · intro all
    exact ⟨all first List.mem_cons_self,fun entry present =>
      all entry (List.mem_cons_of_mem _ present)⟩
  · rintro ⟨head,tail⟩ entry present
    rcases List.mem_cons.mp present with same | later
    · cases same; exact head
    · exact tail entry later

theorem all_walk {X scope F n E c body m final}
    (d : @WalkD X scope F n E c body m final) (offset : Nat)
    (predicate : Nat → Item → Prop) :
    All predicate (walk d offset) ↔ everyWalk d offset predicate := by
  revert offset
  apply WalkD.casesOn
    (motive_2 := fun {X} scope {F} {n} E c body {m} final d =>
      ∀ offset, All predicate (walk d offset) ↔ everyWalk d offset predicate) d
  case nil =>
    intro X scope F n E c offset
    constructor
    · intro _; trivial
    · intro _ entry impossible; cases impossible
  case cons =>
    intro X scope F n E c first rest m next k final head tail offset
    change All predicate ((offset,Item.ofD head)::walk tail (offset+1)) ↔
      predicate offset (Item.ofD head) ∧ everyWalk tail (offset+1) predicate
    simp only [all_cons,all_walk tail (offset+1) predicate]
termination_by structural d

theorem walk_lower_bound {X scope F n E c body m final}
    (d : @WalkD X scope F n E c body m final) (offset : Nat) :
    All (fun ordinal _ => offset ≤ ordinal) (walk d offset) := by
  revert offset
  apply WalkD.casesOn
    (motive_2 := fun {X} scope {F} {n} E c body {m} final d =>
      ∀ offset, All (fun ordinal _ => offset ≤ ordinal) (walk d offset)) d
  case nil =>
    intro X scope F n E c offset entry impossible
    cases impossible
  case cons =>
    intro X scope F n E c first rest m next k final head tail offset entry present
    change entry ∈ (offset,Item.ofD head)::walk tail (offset+1) at present
    rcases List.mem_cons.mp present with same | later
    · cases same; exact Nat.le_refl _
    · have bound := walk_lower_bound tail (offset+1) entry later
      exact Nat.le_trans (Nat.le_add_right _ _) bound
termination_by structural d

theorem walk_position_unique {X scope F n E c body m final}
    (d : @WalkD X scope F n E c body m final) (offset : Nat)
    {one two : Nat × Item} (first : one ∈ walk d offset)
    (second : two ∈ walk d offset) (same : one.1 = two.1) : one = two := by
  revert offset one two
  apply WalkD.casesOn
    (motive_2 := fun {X} scope {F} {n} E c body {m} final d =>
      ∀ offset {one two}, one ∈ walk d offset → two ∈ walk d offset →
        one.1 = two.1 → one = two) d
  case nil =>
    intro X scope F n E c offset one two impossible
    cases impossible
  case cons =>
    intro X scope F n E c first rest m next k final head tail offset one two fromOne fromTwo same
    change one ∈ (offset,Item.ofD head)::walk tail (offset+1) at fromOne
    change two ∈ (offset,Item.ofD head)::walk tail (offset+1) at fromTwo
    rcases List.mem_cons.mp fromOne with oneHead | oneTail
    · rcases List.mem_cons.mp fromTwo with twoHead | twoTail
      · exact oneHead.trans twoHead.symm
      · cases oneHead
        have bound := walk_lower_bound tail (offset+1) two twoTail
        change offset = two.1 at same
        omega
    · rcases List.mem_cons.mp fromTwo with twoHead | twoTail
      · cases twoHead
        have bound := walk_lower_bound tail (offset+1) one oneTail
        change one.1 = offset at same
        omega
      · exact walk_position_unique tail (offset+1) oneTail twoTail same
termination_by structural d

theorem block_position_unique {X scope F n E c body}
    (d : @BlockD X scope F n E c body) {one two : Nat × Item}
    (first : one ∈ block d) (second : two ∈ block d)
    (same : one.1 = two.1) : one = two := by
  cases d with
  | intro headers typedWalk =>
      exact walk_position_unique typedWalk 0 first second same

theorem Item.checker_agrees (item : Item) :
    ScopedBlockTyping.checkStatement item.scope item.environment item.control item.tree =
      some ⟨item.m,item.final,item.typed⟩ := item.typed.complete

end Solidity.Yul.TypingStatements
