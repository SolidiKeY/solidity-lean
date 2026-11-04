import Solidity.Frontend.QualifiedUnits.Specification

/-! Checked declaration resolution. Errors distinguish missing names,
ambiguous identities and a lexically shadowing local. Every proper prefix
must have one identity; the terminal may be a coherent overload set. -/
namespace Solidity.Frontend.QualifiedUnits
open Solidity.Source Solidity.Frontend.Static

inductive Failure where
  | missing
  | ambiguous
  | invalidScope
  | localShadow (index : Nat)
  deriving DecidableEq, Repr

/-- Candidates at a namespace, including identity-based inherited members. -/
def namespaceCandidates (P : UnitSet) (R : List Remapping) (a : Sym) (x : String) : List Sym :=
  match a with
  | .unit u => P.globals R u x
  | .decl i => (inheritedMembers P R i x).map Sym.decl

theorem mem_namespaceCandidates {P : UnitSet} {R : List Remapping} {a b : Sym} {x : String} :
    b ∈ namespaceCandidates P R a x ↔ NamespaceStep P R a x b := by
  cases a with
  | unit u =>
    constructor
    · intro h; exact .unit (globals_sound h)
    · intro h; cases h with
      | unit hs => exact globals_complete hs
  | decl i =>
    constructor
    · intro h
      obtain ⟨j, hj, hb⟩ := List.mem_map.mp h
      subst hb
      exact .decl (mem_inheritedMembers.mp hj)
    · intro h; cases h with
      | decl hm => exact List.mem_map.mpr ⟨_, mem_inheritedMembers.mpr hm, rfl⟩

/-- Members shadow file-level/imported declarations. -/
def headCandidates (P : UnitSet) (R : List Remapping) (u : String) (scope : Option DeclId)
    (x : String) : List Sym :=
  match scope with
  | none => P.globals R u x
  | some i =>
    if inheritedMembers P R i x = [] then P.globals R u x
    else (inheritedMembers P R i x).map Sym.decl

theorem inherited_empty_iff {P : UnitSet} {R : List Remapping} {i : DeclId} {x : String} :
    inheritedMembers P R i x = [] ↔ ¬ ∃ j, InheritedMember P R i x j := by
  constructor
  · intro he ⟨j, hj⟩
    have hm := mem_inheritedMembers.mpr hj
    rw [he] at hm
    cases hm
  · intro hn
    apply List.eq_nil_iff_forall_not_mem.mpr
    intro j hj
    exact hn ⟨j, mem_inheritedMembers.mp hj⟩

theorem mem_headCandidates {P : UnitSet} {R : List Remapping} {u x : String}
    {scope : Option DeclId} {s : Sym} :
    s ∈ headCandidates P R u scope x ↔ Head P R u scope x s := by
  cases scope with
  | none =>
    constructor
    · intro h; exact .global (fun _ hi => by cases hi) (globals_sound h)
    · intro h; cases h with
      | member he _ => cases he
      | global _ hs => exact globals_complete hs
  | some i =>
    unfold headCandidates
    simp only
    split
    · rename_i he
      have hn := inherited_empty_iff.mp he
      constructor
      · intro h
        apply Head.global
        · intro j hj
          cases Option.some.inj hj
          exact hn
        · exact globals_sound h
      · intro h; cases h with
        | member hi hm =>
          cases Option.some.inj hi
          exact False.elim (hn ⟨_, hm⟩)
        | global _ hs => exact globals_complete hs
    · rename_i he
      constructor
      · intro h
        obtain ⟨j, hj, hs⟩ := List.mem_map.mp h
        subst hs
        exact .member rfl (mem_inheritedMembers.mp hj)
      · intro h; cases h with
        | member hi hm =>
          cases Option.some.inj hi
          exact List.mem_map.mpr ⟨_, mem_inheritedMembers.mpr hm, rfl⟩
        | global hn _ => exact False.elim (he (inherited_empty_iff.mpr (hn i rfl)))

theorem compatible_iff {P : UnitSet} {a b : Sym} :
    P.compatible a b = true ↔ Overloadable P a b := by
  cases a with
  | unit u => cases b <;> simp only [UnitSet.compatible, Overloadable, Bool.false_eq_true]
  | decl i =>
    cases b with
    | unit u => simp only [UnitSet.compatible, Overloadable, Bool.false_eq_true]
    | decl j =>
      cases hi : P.decl? i <;> cases hj : P.decl? j <;>
        simp only [UnitSet.compatible, Overloadable, hi, hj, Bool.false_eq_true,
          Bool.and_eq_true, beq_iff_eq]

theorem noClash_iff {P : UnitSet} {L : List Sym} :
    P.noClash L = true ↔ Coherent P (fun a => a ∈ L) := by
  simp only [UnitSet.noClash, List.all_eq_true, Bool.or_eq_true, beq_iff_eq,
    compatible_iff]
  constructor
  · intro h a b ha hb
    exact h a ha b hb
  · intro h a ha b hb
    exact h a b ha hb

/-- Suffix resolution consumes one component per recursive call. Identity
duplicates do not make a prefix ambiguous; differing identities do. -/
def checkSuffix (P : UnitSet) (R : List Remapping) (L : List Sym) :
    List String → Except Failure (List Sym)
  | [] => if L = [] then .error .missing
      else if P.noClash L then .ok L else .error .ambiguous
  | x :: xs =>
    match L with
    | [] => .error .missing
    | a :: rest =>
      if rest.all (· == a) then checkSuffix P R (namespaceCandidates P R a x) xs
      else .error .ambiguous

theorem checkSuffix_iff {P : UnitSet} {R : List Remapping} {L : List Sym}
    {xs : List String} {s : Sym} :
    (∃ out, checkSuffix P R L xs = .ok out ∧ s ∈ out) ↔
      Admits P R (fun a => a ∈ L) xs s := by
  induction xs generalizing L with
  | nil =>
    by_cases he : L = []
    · subst he
      simp only [checkSuffix, if_true]
      constructor
      · intro ⟨out, ho, _⟩; cases ho
      · intro h; cases h with
        | terminal hs _ => cases hs
    · by_cases hc : P.noClash L = true
      · simp only [checkSuffix, he, if_false, hc, if_true]
        constructor
        · intro ⟨out, ho, hs⟩
          cases ho
          exact .terminal hs (noClash_iff.mp hc)
        · intro h; cases h with
          | terminal hs _ => exact ⟨L, rfl, hs⟩
      · simp only [checkSuffix, he, if_false, hc]
        constructor
        · intro ⟨out, ho, _⟩; cases ho
        · intro h; cases h with
          | terminal _ hco => exact False.elim (hc (noClash_iff.mpr hco))
  | cons x xs ih =>
    cases L with
    | nil =>
      simp only [checkSuffix]
      constructor
      · intro ⟨out, ho, _⟩; cases ho
      · intro h; cases h with
        | next ha _ _ => cases ha
    | cons a rest =>
      by_cases he : rest.all (· == a) = true
      · have hu : ∀ b, b ∈ a :: rest → b = a := by
          intro b hb
          rcases List.mem_cons.mp hb with hb | hb
          · exact hb
          · exact beq_iff_eq.mp ((List.all_eq_true.mp he) b hb)
        simp only [checkSuffix, he, if_true]
        constructor
        · intro h
          have ht : Admits P R (NamespaceStep P R a x) xs s := by
            simpa only [mem_namespaceCandidates] using ih.mp h
          exact .next List.mem_cons_self hu ht
        · intro h; cases h with
          | next hb _ ht =>
            have e : _ = a := hu _ hb
            subst e
            apply ih.mpr
            simpa only [mem_namespaceCandidates] using ht
      · simp only [checkSuffix, he]
        constructor
        · intro ⟨out, ho, _⟩; cases ho
        · intro h; cases h with
          | next hb hu _ =>
            have ea := hu a List.mem_cons_self
            have he' : rest.all (· == a) = true := by
              apply List.all_eq_true.mpr
              intro b hb'
              exact beq_iff_eq.mpr ((hu b (List.mem_cons_of_mem _ hb')).trans ea.symm)
            exact False.elim (he he')

/-- Resolve a declaration path in a lexical context, preserving local priority. -/
def resolve (P : UnitSet) (R : List Remapping) (u : String) (scope : Option DeclId)
    (locals : List String) (p : IdPath) : Except Failure (List Sym) :=
  if ValidScope P u scope then
    match locals.idxOf? p.head with
    | some i => .error (.localShadow i)
    | none => checkSuffix P R (headCandidates P R u scope p.head) p.tail
  else .error .invalidScope

/-- Complete and sound acceptance over the independent lexical/path relation. -/
theorem resolve_iff {P : UnitSet} {R : List Remapping} {u : String} {scope : Option DeclId}
    {locals : List String} {p : IdPath} {s : Sym} :
    (∃ out, resolve P R u scope locals p = .ok out ∧ s ∈ out) ↔
      Resolved P R u scope locals p s := by
  by_cases hv : ValidScope P u scope
  · unfold resolve Resolved
    simp only [hv, if_true, true_and]
    cases hl : locals.idxOf? p.head with
    | some i =>
      constructor
      · intro ⟨out, ho, _⟩; cases ho
      · intro ⟨hn, _⟩; cases hn
    | none =>
      simp only [true_and]
      rw [checkSuffix_iff]
      simp only [mem_headCandidates]
  · unfold resolve Resolved
    simp only [hv, if_false, false_and]
    constructor
    · intro ⟨out, ho, _⟩; cases ho
    · intro h; cases h

/-- No-clash preservation for every successful answer, with no admission premise. -/
theorem resolve_noClash {P : UnitSet} {R : List Remapping} {u : String} {scope : Option DeclId}
    {locals : List String} {p : IdPath} {out : List Sym}
    (h : resolve P R u scope locals p = .ok out) : P.noClash out = true := by
  apply noClash_iff.mpr
  intro a b ha hb
  have ra := resolve_iff.mp ⟨out, h, ha⟩
  have rb := resolve_iff.mp ⟨out, h, hb⟩
  exact ra.2.2.coherent rb.2.2

/-- Inherited lookup returns original, existing declarations. -/
theorem InheritedFrom.decl_exists {P : UnitSet} {R : List Remapping} {root i j : DeclId}
    {x : String} (h : InheritedFrom P R root i x j) : ∃ d, P.decl? j = some d := by
  induction h with
  | here hm => cases hm.1 with
    | intro _ _ hd _ _ _ _ _ _ => exact ⟨_, hd⟩
  | base _ _ _ ih => exact ih

theorem NamespaceStep.decl_exists {P : UnitSet} {R : List Remapping} {a : Sym} {x : String}
    {i : DeclId} (h : NamespaceStep P R a x (.decl i)) : ∃ d, P.decl? i = some d := by
  cases h with
  | unit hs => obtain ⟨d, hd, _⟩ := hs.decl_exists; exact ⟨d, hd⟩
  | decl hm => exact InheritedFrom.decl_exists hm

theorem Head.decl_exists {P : UnitSet} {R : List Remapping} {u x : String} {scope : Option DeclId}
    {i : DeclId} (h : Head P R u scope x (.decl i)) : ∃ d, P.decl? i = some d := by
  cases h with
  | member _ hm => exact InheritedFrom.decl_exists hm
  | global _ hs => obtain ⟨d, hd, _⟩ := hs.decl_exists; exact ⟨d, hd⟩

theorem Admits.decl_exists {P : UnitSet} {R : List Remapping} {S : Sym → Prop} {xs : List String}
    {i : DeclId} (h : Admits P R S xs (.decl i))
    (hs : ∀ j, S (.decl j) → ∃ d, P.decl? j = some d) : ∃ d, P.decl? i = some d := by
  induction xs generalizing S with
  | nil => cases h with
    | terminal hi _ => exact hs i hi
  | cons x xs ih => cases h with
    | next _ _ ht => exact ih ht (fun _ hj => hj.decl_exists)

/-- Every successful declaration identity still names its original source
node; no identity is minted or renamed by namespace or inheritance traversal. -/
theorem resolve_identity {P : UnitSet} {R : List Remapping} {u : String} {scope : Option DeclId}
    {locals : List String} {p : IdPath} {out : List Sym} {i : DeclId}
    (h : resolve P R u scope locals p = .ok out) (hi : Sym.decl i ∈ out) :
    ∃ d, P.decl? i = some d := by
  have hr := resolve_iff.mp ⟨out, h, hi⟩
  exact hr.2.2.decl_exists (fun _ hj => hj.decl_exists)

end Solidity.Frontend.QualifiedUnits
