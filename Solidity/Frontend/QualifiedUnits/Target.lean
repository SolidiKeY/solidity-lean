import Solidity.Frontend.QualifiedUnits.Linearization
import Solidity.Frontend.QualifiedUnits.SignatureResolution

/-! The final SOL-QN target relation, including inherited overloads.

The hierarchy used for overload collection is the independent C3
`Linearization.Linear` judgment (no `order`, fuel or `idUniverse` bound);
inherited overload families are `SignatureMembers.WalkMember` derivations
over that hierarchy; nearest non-overloadable declarations keep their
lexical priority; qualified paths use unique proper prefixes and coherent
terminal symbols.

Trusted executable leaves remain, stated as propositions: `group` (the
Bool `overload` filter over `visibleMembers`), `Unhidden` (`hides … = some
false`, which compares `normalize` keys), `Normalized` (`normalize … = some
_`) and `overload` in `SafeOwners`/`Eligible`. The plain branch and the
global barrier use `InheritedMember`, reachability along the syntactic base
graph, which does not require a valid linearization; only the overload
branch requires `Linear`.

`target_iff` proves the public consumer `SignatureResolution.resolve` sound
and complete for `Target` with no premise. This is completeness against an
implementation-shaped relation whose hierarchy part is independent; it is
not independent Solidity semantics, external Solidity correctness, parser
correspondence or cross-unit expression typing (G13), and does not validate
inheritance or override legality (G14). -/
namespace Solidity.Frontend.QualifiedUnits.Target
open Solidity.Source Solidity.Frontend.Static SignatureMembers

/-- Inherited overload collection over the independent C3 hierarchy. -/
def Collected (P : UnitSet) (R : List Remapping) (root : DeclId) (x : String) (j : DeclId) : Prop :=
  ∃ owners, Linearization.Linear P R root owners ∧
    (∀ owner, owner ∈ owners → Normalized P R (group P root owner x)) ∧
    WalkMember P R root x owners [] j

/-- No visible non-overloadable declaration anywhere in the C3 hierarchy. -/
def SafeOwners (P : UnitSet) (R : List Remapping) (i : DeclId) (x : String) : Prop :=
  ∃ owners, Linearization.Linear P R i owners ∧
    ∀ owner, owner ∈ owners → ∀ j, VisibleMember P i owner x j → overload P j = true

inductive Member (P : UnitSet) (R : List Remapping) (i : DeclId) (x : String) : DeclId → Prop where
  | plain {j : DeclId} : (¬ SignatureResolution.Eligible P R i x) → InheritedMember P R i x j → Member P R i x j
  | signature {j : DeclId} : SignatureResolution.Eligible P R i x → SafeOwners P R i x →
      Collected P R i x j → Member P R i x j

inductive Step (P : UnitSet) (R : List Remapping) : Sym → String → Sym → Prop where
  | unit {u x : String} {s : Sym} : Sees P R u x s → Step P R (.unit u) x s
  | decl {i j : DeclId} {x : String} : Member P R i x j → Step P R (.decl i) x (.decl j)

inductive Head (P : UnitSet) (R : List Remapping) (u : String) (scope : Option DeclId)
    (x : String) : Sym → Prop where
  | member {i j : DeclId} : scope = some i → Member P R i x j → Head P R u scope x (.decl j)
  | global {s : Sym} : (∀ i, scope = some i → ¬ ∃ j, InheritedMember P R i x j) →
      Sees P R u x s → Head P R u scope x s

inductive Admits (P : UnitSet) (R : List Remapping) : (Sym → Prop) → List String → Sym → Prop where
  | terminal {S : Sym → Prop} {s : Sym} : S s → Coherent P S → Admits P R S [] s
  | next {S : Sym → Prop} {a s : Sym} {x : String} {xs : List String} :
      S a → (∀ b, S b → b = a) → Admits P R (Step P R a x) xs s → Admits P R S (x :: xs) s

/-- Final target: valid lexical scope, no local shadowing of the head, then
an admissible qualified route from the lexical head. -/
def Target (P : UnitSet) (R : List Remapping) (u : String) (scope : Option DeclId)
    (locals : List String) (p : IdPath) (s : Sym) : Prop :=
  ValidScope P u scope ∧ locals.idxOf? p.head = none ∧ Admits P R (Head P R u scope p.head) p.tail s

theorem collected_iff {P : UnitSet} {R : List Remapping} {root j : DeclId} {x : String} :
    SignatureMembers.Collected P R root x j ↔ Collected P R root x j := by
  unfold SignatureMembers.Collected Collected
  simp only [Linearization.order_iff, ready_iff]

theorem safeOwners_iff {P : UnitSet} {R : List Remapping} {i : DeclId} {x : String} :
    SignatureResolution.SafeOwners P R i x ↔ SafeOwners P R i x := by
  unfold SignatureResolution.SafeOwners SafeOwners
  simp only [Linearization.order_iff]

theorem member_iff {P : UnitSet} {R : List Remapping} {i j : DeclId} {x : String} :
    SignatureResolution.Member P R i x j ↔ Member P R i x j := by
  constructor
  · intro h
    cases h with
    | plain hn hm => exact .plain hn hm
    | signature he hs hc => exact .signature he (safeOwners_iff.mp hs) (collected_iff.mp hc)
  · intro h
    cases h with
    | plain hn hm => exact .plain hn hm
    | signature he hs hc => exact .signature he (safeOwners_iff.mpr hs) (collected_iff.mpr hc)

theorem step_eq {P : UnitSet} {R : List Remapping} :
    SignatureResolution.NamespaceStep P R = Step P R := by
  funext a x b
  apply propext
  constructor
  · intro h
    cases h with
    | unit hs => exact .unit hs
    | decl hm => exact .decl (member_iff.mp hm)
  · intro h
    cases h with
    | unit hs => exact .unit hs
    | decl hm => exact .decl (member_iff.mpr hm)

theorem head_eq {P : UnitSet} {R : List Remapping} {u : String} {scope : Option DeclId} {x : String} :
    SignatureResolution.Head P R u scope x = Head P R u scope x := by
  funext s
  apply propext
  constructor
  · intro h
    cases h with
    | member he hm => exact .member he (member_iff.mp hm)
    | global hn hs => exact .global hn hs
  · intro h
    cases h with
    | member he hm => exact .member he (member_iff.mpr hm)
    | global hn hs => exact .global hn hs

theorem admits_iff {P : UnitSet} {R : List Remapping} {S : Sym → Prop} {xs : List String} {s : Sym} :
    SignatureResolution.Admits P R S xs s ↔ Admits P R S xs s := by
  induction xs generalizing S with
  | nil =>
    constructor
    · intro h; cases h with | terminal hs hc => exact .terminal hs hc
    · intro h; cases h with | terminal hs hc => exact .terminal hs hc
  | cons x xs ih =>
    constructor
    · intro h
      cases h with
      | next ha hu ht =>
        rw [step_eq] at ht
        exact .next ha hu (ih.mp ht)
    · intro h
      cases h with
      | next ha hu ht =>
        have ht' := ih.mpr ht
        rw [← step_eq] at ht'
        exact .next ha hu ht'

theorem resolved_iff {P : UnitSet} {R : List Remapping} {u : String} {scope : Option DeclId}
    {locals : List String} {p : IdPath} {s : Sym} :
    SignatureResolution.Resolved P R u scope locals p s ↔ Target P R u scope locals p s := by
  unfold SignatureResolution.Resolved Target
  rw [head_eq, admits_iff]

/-- Sound and complete public resolution for the final declarative target. -/
theorem target_iff {P : UnitSet} {R : List Remapping} {u : String} {scope : Option DeclId}
    {locals : List String} {p : IdPath} {s : Sym} :
    (∃ out, SignatureResolution.resolve P R u scope locals p = .ok out ∧ s ∈ out) ↔
      Target P R u scope locals p s := by
  rw [SignatureResolution.resolve_iff, resolved_iff]

/-- Every answer of a successful `resolve` is a target answer, and the
answer list (not the relation) passes the existing no-clash check. -/
theorem Target.noClash {P : UnitSet} {R : List Remapping} {u : String} {scope : Option DeclId}
    {locals : List String} {p : IdPath} {out : List Sym}
    (h : SignatureResolution.resolve P R u scope locals p = .ok out) :
    P.noClash out = true ∧ ∀ s, s ∈ out → Target P R u scope locals p s :=
  ⟨SignatureResolution.resolve_noClash h, fun _ hs => target_iff.mp ⟨out, h, hs⟩⟩

theorem Target.identity {P : UnitSet} {R : List Remapping} {u : String} {scope : Option DeclId}
    {locals : List String} {p : IdPath} {i : DeclId}
    (h : Target P R u scope locals p (.decl i)) : ∃ d, P.decl? i = some d := by
  obtain ⟨out, ho, hi⟩ := target_iff.mpr h
  exact SignatureResolution.resolve_identity ho hi

/-- A refused query has no target answer at all (missing, ambiguous, local
shadow, invalid scope or failed collection are not partial answers). -/
theorem refused_no_target {P : UnitSet} {R : List Remapping} {u : String} {scope : Option DeclId}
    {locals : List String} {p : IdPath} {e : Failure}
    (h : SignatureResolution.resolve P R u scope locals p = .error e) :
    ∀ s, ¬ Target P R u scope locals p s := by
  intro s ht
  obtain ⟨out, ho, _⟩ := target_iff.mpr ht
  rw [h] at ho
  cases ho

end Solidity.Frontend.QualifiedUnits.Target
