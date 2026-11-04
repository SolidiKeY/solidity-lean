import Solidity.Frontend.QualifiedUnits.Lookup

/-! Unique unit-namespace paths to base contracts/interfaces. No inheritance
or expression typing is needed: contracts cannot be nested in the existing
intrinsic syntax. Ambiguous prefixes cannot be rescued by a later suffix. -/
namespace Solidity.Frontend.QualifiedUnits
open Solidity.Source Solidity.Frontend.Static

def BaseKind (k : DeclKind) : Prop := k = .contract ∨ k = .interface
instance instDecidableBaseKind (k : DeclKind) : Decidable (BaseKind k) := by
  unfold BaseKind
  infer_instance

/-- One identity, regardless of repeated occurrences of that identity. -/
def uniqueSymbol : List Sym → Option Sym
  | [] => none
  | a :: rest => if rest.all (· == a) then some a else none

theorem uniqueSymbol_iff {L : List Sym} {a : Sym} : uniqueSymbol L = some a ↔
    a ∈ L ∧ ∀ b, b ∈ L → b = a := by
  cases L with
  | nil =>
    constructor
    · intro h; cases h
    · intro ⟨h, _⟩; cases h
  | cons b rest =>
    unfold uniqueSymbol
    simp only
    split
    · rename_i he
      constructor
      · intro h
        cases h
        refine ⟨List.mem_cons_self, ?_⟩
        intro c hc
        rcases List.mem_cons.mp hc with hc | hc
        · exact hc
        · exact beq_iff_eq.mp ((List.all_eq_true.mp he) c hc)
      · intro ⟨_, hu⟩
        have hb := hu b List.mem_cons_self
        cases hb
        rfl
    · rename_i he
      constructor
      · intro h; cases h
      · intro ⟨_, hu⟩
        have hb := hu b List.mem_cons_self
        apply False.elim
        apply he
        apply List.all_eq_true.mpr
        intro c hc
        exact beq_iff_eq.mpr ((hu c (List.mem_cons_of_mem _ hc)).trans hb.symm)

inductive UnitRoute (P : UnitSet) (R : List Remapping) : (Sym → Prop) → List String → DeclId → Prop where
  | terminal {S : Sym → Prop} {i : DeclId} {d : Decl} :
      S (.decl i) → (∀ b, S b → b = .decl i) → P.decl? i = some d → BaseKind d.kind →
      UnitRoute P R S [] i
  | next {S : Sym → Prop} {u x : String} {xs : List String} {i : DeclId} :
      S (.unit u) → (∀ b, S b → b = .unit u) → UnitRoute P R (Sees P R u x) xs i →
      UnitRoute P R S (x :: xs) i

def unitTail (P : UnitSet) (R : List Remapping) (L : List Sym) : List String → Option DeclId
  | [] =>
    match uniqueSymbol L with
    | some (.decl i) =>
      match P.decl? i with
      | some d => if BaseKind d.kind then some i else none
      | none => none
    | _ => none
  | x :: xs =>
    match uniqueSymbol L with
    | some (.unit u) => unitTail P R (P.globals R u x) xs
    | _ => none

theorem unitTail_iff {P : UnitSet} {R : List Remapping} {L : List Sym} {xs : List String}
    {i : DeclId} : unitTail P R L xs = some i ↔ UnitRoute P R (fun a => a ∈ L) xs i := by
  induction xs generalizing L with
  | nil =>
    constructor
    · intro h
      unfold unitTail at h
      cases hu : uniqueSymbol L with
      | none => rw [hu] at h; cases h
      | some a =>
        rw [hu] at h
        cases a with
        | unit => cases h
        | decl j =>
          simp only at h
          cases hd : P.decl? j with
          | none => rw [hd] at h; cases h
          | some d =>
            rw [hd] at h
            simp only at h
            split at h
            · rename_i hk
              cases h
              obtain ⟨ha, hh⟩ := uniqueSymbol_iff.mp hu
              exact .terminal ha hh hd hk
            · cases h
    · intro h; cases h with
      | terminal ha hu hd hk =>
        simp only [unitTail, uniqueSymbol_iff.mpr ⟨ha, hu⟩, hd, hk, if_true]
  | cons x xs ih =>
    constructor
    · intro h
      unfold unitTail at h
      cases hu : uniqueSymbol L with
      | none => rw [hu] at h; cases h
      | some a =>
        rw [hu] at h
        cases a with
        | decl => cases h
        | unit u =>
          obtain ⟨ha, hh⟩ := uniqueSymbol_iff.mp hu
          have ht : UnitRoute P R (Sees P R u x) xs i := by
            simpa only [mem_globals] using ih.mp h
          exact .next ha hh ht
    · intro h; cases h with
      | next ha hu ht =>
        simp only [unitTail, uniqueSymbol_iff.mpr ⟨ha, hu⟩]
        apply ih.mpr
        simpa only [mem_globals] using ht

/-- Unique base-target lookup retains every qualifier and verifies base kind. -/
def unitBase (P : UnitSet) (R : List Remapping) (u : String) (p : IdPath) : Option DeclId :=
  unitTail P R (P.globals R u p.head) p.tail

theorem unitBase_iff {P : UnitSet} {R : List Remapping} {u : String} {p : IdPath} {i : DeclId} :
    unitBase P R u p = some i ↔ UnitRoute P R (Sees P R u p.head) p.tail i := by
  unfold unitBase
  rw [unitTail_iff]
  simp only [mem_globals]

theorem UnitRoute.decl_exists {P : UnitSet} {R : List Remapping} {S : Sym → Prop}
    {xs : List String} {i : DeclId} (h : UnitRoute P R S xs i) :
    ∃ d, P.decl? i = some d ∧ BaseKind d.kind := by
  induction h with
  | terminal _ _ hd hk => exact ⟨_, hd, hk⟩
  | next _ _ _ ih => exact ih

end Solidity.Frontend.QualifiedUnits
