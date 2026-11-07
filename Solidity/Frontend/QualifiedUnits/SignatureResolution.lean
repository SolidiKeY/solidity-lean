import Solidity.Frontend.QualifiedUnits.Checked
import Solidity.Frontend.QualifiedUnits.SignatureMembers

/-! Signature-aware declaration resolution over original Source identities.
The existing nearest-name resolver/observations remain unchanged. Terminal
coherence, valid scopes, local priority and proper-prefix uniqueness reuse
its public contracts. Collection failure refuses the admissible route; it
cannot fall through to globals or count as a distinct signature. -/
namespace Solidity.Frontend.QualifiedUnits.SignatureResolution
open Solidity.Source Solidity.Frontend.Static

/-- The nearest visible set is a nonempty overload family. -/
def Eligible (P : UnitSet) (R : List Remapping) (i : DeclId) (x : String) : Prop :=
  (∃ j, InheritedMember P R i x j) ∧
    ∀ j, InheritedMember P R i x j → SignatureMembers.overload P j = true

def eligible (P : UnitSet) (R : List Remapping) (i : DeclId) (x : String) : Bool :=
  if inheritedMembers P R i x = [] then false
  else (inheritedMembers P R i x).all (SignatureMembers.overload P)

theorem eligible_iff {P : UnitSet} {R : List Remapping} {i : DeclId} {x : String} :
    eligible P R i x = true ↔ Eligible P R i x := by
  by_cases he : inheritedMembers P R i x = []
  · simp only [eligible,he,if_true,Bool.false_eq_true,false_iff]
    intro ⟨hm,_⟩
    exact inherited_empty_iff.mp he hm
  · simp only [eligible,he,if_false,List.all_eq_true]
    constructor
    · intro h
      have existsMember : ∃ j, InheritedMember P R i x j := by
        cases hm : inheritedMembers P R i x with
        | nil => exact False.elim (he hm)
        | cons j rest => exact ⟨j,mem_inheritedMembers.mp (by rw [hm]; exact List.mem_cons_self)⟩
      exact ⟨existsMember,fun j hj => h j (mem_inheritedMembers.mpr hj)⟩
    · intro ⟨_,h⟩ j hj
      exact h j (mem_inheritedMembers.mp hj)

/-- A visible non-overloadable declaration anywhere in the owner order is a
barrier, not a declaration to silently discard while recovering older functions. -/
def SafeOwners (P : UnitSet) (R : List Remapping) (i : DeclId) (x : String) : Prop :=
  ∃ owners, SignatureMembers.order P R i = some owners ∧
    ∀ owner, owner ∈ owners → ∀ j, VisibleMember P i owner x j → SignatureMembers.overload P j = true

def safeOwners (P : UnitSet) (R : List Remapping) (i : DeclId) (x : String) : Bool :=
  match SignatureMembers.order P R i with
  | none => false
  | some owners => owners.all fun owner => (visibleMembers P i owner x).all (SignatureMembers.overload P)

theorem safeOwners_iff {P : UnitSet} {R : List Remapping} {i : DeclId} {x : String} :
    safeOwners P R i x = true ↔ SafeOwners P R i x := by
  unfold safeOwners SafeOwners
  cases ho : SignatureMembers.order P R i with
  | none => simp only [Bool.false_eq_true,reduceCtorEq,false_and,exists_false]
  | some owners =>
    simp only [List.all_eq_true,mem_visibleMembers,Option.some.injEq]
    constructor
    · intro h; exact ⟨owners,rfl,h⟩
    · rintro ⟨_,rfl,h⟩; exact h

/-- Original nearest declarations retain non-overloadable shadowing. An
eligible overload family instead uses the independent collected judgment. -/
inductive Member (P : UnitSet) (R : List Remapping) (i : DeclId) (x : String) : DeclId → Prop where
  | plain {j : DeclId} : (¬ Eligible P R i x) → InheritedMember P R i x j → Member P R i x j
  | signature {j : DeclId} : Eligible P R i x → SafeOwners P R i x → SignatureMembers.Collected P R i x j → Member P R i x j

def candidates (P : UnitSet) (R : List Remapping) (i : DeclId) (x : String) : List DeclId :=
  if eligible P R i x then
    if safeOwners P R i x then (SignatureMembers.collect P R i x).getD [] else []
  else inheritedMembers P R i x

theorem mem_candidates {P : UnitSet} {R : List Remapping} {i j : DeclId} {x : String} :
    j ∈ candidates P R i x ↔ Member P R i x j := by
  by_cases he : eligible P R i x = true
  · have hr := eligible_iff.mp he
    by_cases hs : safeOwners P R i x = true
    · have hsafe := safeOwners_iff.mp hs
      simp only [candidates,he,hs,if_true]
      have hc : j ∈ (SignatureMembers.collect P R i x).getD [] ↔ SignatureMembers.Collected P R i x j := by
        rw [← SignatureMembers.collected_iff]
        cases h : SignatureMembers.collect P R i x with
        | none => simp only [Option.getD_none,List.not_mem_nil,reduceCtorEq,false_and,exists_false]
        | some out =>
          simp only [Option.getD_some,Option.some.injEq]
          constructor
          · intro hj; exact ⟨out,rfl,hj⟩
          · rintro ⟨_,rfl,hj⟩; exact hj
      rw [hc]
      constructor
      · exact Member.signature hr hsafe
      · intro h; cases h with
        | plain hn _ => exact False.elim (hn hr)
        | signature _ _ hm => exact hm
    · simp only [candidates,he,hs,if_true,Bool.false_eq_true,if_false,List.not_mem_nil,false_iff]
      intro h
      cases h with
      | plain hn _ => exact hn hr
      | signature _ hp _ => exact hs (safeOwners_iff.mpr hp)
  · have hn : ¬ Eligible P R i x := fun h => he (eligible_iff.mpr h)
    simp only [candidates,he]
    constructor
    · intro h; exact .plain hn (mem_inheritedMembers.mp h)
    · intro h; cases h with
      | plain _ hm => exact mem_inheritedMembers.mpr hm
      | signature hr _ _ => exact False.elim (hn hr)

theorem Member.nearest_exists {P : UnitSet} {R : List Remapping} {i j : DeclId} {x : String}
    (h : Member P R i x j) : ∃ k, InheritedMember P R i x k := by
  cases h with
  | plain _ hm => exact ⟨_,hm⟩
  | signature he _ _ => exact he.1

theorem Member.decl_exists {P : UnitSet} {R : List Remapping} {i j : DeclId} {x : String}
    (h : Member P R i x j) : ∃ d, P.decl? j = some d := by
  cases h with
  | plain _ hm => exact InheritedFrom.decl_exists hm
  | signature _ _ hm =>
    obtain ⟨out,hc,hj⟩ := SignatureMembers.collected_iff.mpr hm
    exact SignatureMembers.collect_identity hc hj

inductive NamespaceStep (P : UnitSet) (R : List Remapping) : Sym → String → Sym → Prop where
  | unit {u x : String} {s : Sym} : Sees P R u x s → NamespaceStep P R (.unit u) x s
  | decl {i j : DeclId} {x : String} : Member P R i x j → NamespaceStep P R (.decl i) x (.decl j)

/-- Lexical declaration head: contract members precede the importing unit's
globals. Locals are tested by `Resolved` before this relation is used. -/
inductive Head (P : UnitSet) (R : List Remapping) (u : String) (scope : Option DeclId)
    (x : String) : Sym → Prop where
  | member {i j : DeclId} : scope = some i → Member P R i x j → Head P R u scope x (.decl j)
  | global {s : Sym} : (∀ i, scope = some i → ¬ ∃ j, InheritedMember P R i x j) →
      Sees P R u x s → Head P R u scope x s

inductive Admits (P : UnitSet) (R : List Remapping) : (Sym → Prop) → List String → Sym → Prop where
  | terminal {S : Sym → Prop} {s : Sym} : S s → Coherent P S → Admits P R S [] s
  | next {S : Sym → Prop} {a s : Sym} {x : String} {xs : List String} :
      S a → (∀ b, S b → b = a) → Admits P R (NamespaceStep P R a x) xs s →
      Admits P R S (x :: xs) s

def Resolved (P : UnitSet) (R : List Remapping) (u : String) (scope : Option DeclId)
    (locals : List String) (p : IdPath) (s : Sym) : Prop :=
  ValidScope P u scope ∧ locals.idxOf? p.head = none ∧ Admits P R (Head P R u scope p.head) p.tail s

/-- An accepted namespace prefix cannot contain a second identity. -/
theorem Admits.prefix_unique {P : UnitSet} {R : List Remapping} {S : Sym → Prop}
    {x : String} {xs : List String} {s : Sym} (h : Admits P R S (x :: xs) s) :
    ∃ a, S a ∧ ∀ b, S b → b = a := by
  cases h with
  | next ha hu _ => exact ⟨_, ha, hu⟩

/-- Accepted terminal answers preserve no-clash, including duplicate and
converging identity routes. -/
theorem Admits.coherent {P : UnitSet} {R : List Remapping} {S : Sym → Prop}
    {xs : List String} {s t : Sym} (h : Admits P R S xs s) (k : Admits P R S xs t) :
    Compatible P s t := by
  induction xs generalizing S with
  | nil =>
    cases h with
    | terminal hs hc => cases k with
      | terminal ht _ => exact hc s t hs ht
  | cons x xs ih =>
    cases h with
    | next ha hu hs => cases k with
      | next hb _ ht =>
        have e := hu _ hb
        subst e
        exact ih hs ht

/-- Local shadowing blocks every declaration-namespace interpretation. -/
theorem local_shadows {P : UnitSet} {R : List Remapping} {u : String} {scope : Option DeclId}
    {locals : List String} {p : IdPath} {i : Nat} {s : Sym}
    (h : locals.idxOf? p.head = some i) : ¬ Resolved P R u scope locals p s := by
  intro ⟨_, hn, _⟩
  rw [h] at hn
  cases hn

def namespaceCandidates (P : UnitSet) (R : List Remapping) (a : Sym) (x : String) : List Sym :=
  match a with
  | .unit u => P.globals R u x
  | .decl i => (candidates P R i x).map Sym.decl

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
      exact .decl (mem_candidates.mp hj)
    · intro h; cases h with
      | decl hm => exact List.mem_map.mpr ⟨_, mem_candidates.mpr hm, rfl⟩

/-- Members shadow file-level/imported declarations. -/
def headCandidates (P : UnitSet) (R : List Remapping) (u : String) (scope : Option DeclId)
    (x : String) : List Sym :=
  match scope with
  | none => P.globals R u x
  | some i =>
    if inheritedMembers P R i x = [] then P.globals R u x
    else (candidates P R i x).map Sym.decl

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
          exact False.elim (hn hm.nearest_exists)
        | global _ hs => exact globals_complete hs
    · rename_i he
      constructor
      · intro h
        obtain ⟨j, hj, hs⟩ := List.mem_map.mp h
        subst hs
        exact .member rfl (mem_candidates.mp hj)
      · intro h; cases h with
        | member hi hm =>
          cases Option.some.inj hi
          exact List.mem_map.mpr ⟨_, mem_candidates.mpr hm, rfl⟩
        | global hn _ => exact False.elim (he (inherited_empty_iff.mpr (hn i rfl)))

def checkSuffix (P : UnitSet) (R : List Remapping) (L : List Sym) :
    List String → Except Failure (List Sym)
  | [] => Solidity.Frontend.QualifiedUnits.checkSuffix P R L []
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
      simp only [checkSuffix,Solidity.Frontend.QualifiedUnits.checkSuffix, if_true]
      constructor
      · intro ⟨out, ho, _⟩; cases ho
      · intro h; cases h with
        | terminal hs _ => cases hs
    · by_cases hc : P.noClash L = true
      · simp only [checkSuffix,Solidity.Frontend.QualifiedUnits.checkSuffix, he, if_false, hc, if_true]
        constructor
        · intro ⟨out, ho, hs⟩
          cases ho
          exact .terminal hs (noClash_iff.mp hc)
        · intro h; cases h with
          | terminal hs _ => exact ⟨L, rfl, hs⟩
      · simp only [checkSuffix,Solidity.Frontend.QualifiedUnits.checkSuffix, he, if_false, hc]
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

theorem NamespaceStep.decl_exists {P : UnitSet} {R : List Remapping} {a : Sym} {x : String}
    {i : DeclId} (h : NamespaceStep P R a x (.decl i)) : ∃ d, P.decl? i = some d := by
  cases h with
  | unit hs => obtain ⟨d, hd, _⟩ := hs.decl_exists; exact ⟨d, hd⟩
  | decl hm => exact hm.decl_exists

theorem Head.decl_exists {P : UnitSet} {R : List Remapping} {u x : String} {scope : Option DeclId}
    {i : DeclId} (h : Head P R u scope x (.decl i)) : ∃ d, P.decl? i = some d := by
  cases h with
  | member _ hm => exact hm.decl_exists
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

end Solidity.Frontend.QualifiedUnits.SignatureResolution
