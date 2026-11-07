import Solidity.Lowering.P9.BodyRecognizerCompleteness

/-! Existential fuel completeness of catalogueB relative to the original
BoundMemoryCatalogue, not universal Source coverage. -/
namespace Solidity.Source.Calls.Recognize
open Solidity.Source.Progress
variable {E : Env}

theorem entryB_mono (G : Glob E) (c : String) (values : List Decl)
    (d : Decl) {n m : Nat} (order : n ≤ m) (accepted : entryB G c values n d = true) :
    entryB G c values m d = true := by
  unfold entryB at accepted ⊢
  rcases Bool.and_eq_true_iff.mp accepted with ⟨declared,rest⟩
  refine Bool.and_eq_true_iff.mpr ⟨declared,?_⟩
  split at rest
  · rename_i ps rs targetPs rs' b sourceSig targetSig body
    simp only [Bool.and_eq_true] at rest ⊢
    exact ⟨⟨rest.1.1,List.all_eq_true.mpr (fun τ member =>
      finiteDefaultB_mono order (List.all_eq_true.mp rest.1.2 τ member))⟩,rest.2⟩
  · cases rest

theorem catalogueB_mono (G : Glob E) (c : String) (values ds : List Decl)
    {n m : Nat} (order : n ≤ m) (accepted : catalogueB G c values n ds = true) :
    catalogueB G c values m ds = true :=
  List.all_eq_true.mpr (fun d member =>
    entryB_mono G c values d order (List.all_eq_true.mp accepted d member))

theorem entryB_complete (G : Glob E) (c : String) (values : List Decl) (d : Decl)
    (entry : BoundMemoryCatalogue (· ∈ values) G c [d]) :
    ∃ fuel, entryB G c values fuel d = true := by
  obtain ⟨declared,ps,rs,targetPs,b,sourceSig,targetSig,body,mods,defaults,ready⟩ :=
    entry d (by simp only [List.mem_singleton])
  obtain ⟨fuel,accepted⟩ := finiteDefaultsB_exists rs (fun τ member =>
    finiteDefaultB_complete (defaults τ member))
  refine ⟨fuel,?_⟩
  simp only [entryB,decide_eq_true declared,sourceSig,targetSig,body,mods,decide_true,
    List.isEmpty_nil,Bool.true_and,accepted,boundB_complete ready]

theorem entries_common_fuel (G : Glob E) (c : String) (values ds : List Decl)
    (entries : ∀ d ∈ ds, ∃ fuel, entryB G c values fuel d = true) :
    ∃ fuel, catalogueB G c values fuel ds = true := by
  induction ds with
  | nil => exact ⟨0,rfl⟩
  | cons d ds ih =>
    obtain ⟨a,head⟩ := entries d (by simp only [List.mem_cons,true_or])
    obtain ⟨b,tail⟩ := ih (fun x member =>
      entries x (by simp only [List.mem_cons];exact Or.inr member))
    refine ⟨max a b,List.all_eq_true.mpr ?_⟩
    intro x member
    rcases List.mem_cons.mp member with same | rest
    · subst x; exact entryB_mono G c values d (Nat.le_max_left _ _) head
    · exact entryB_mono G c values x (Nat.le_max_right _ _)
        (List.all_eq_true.mp tail x rest)

theorem catalogueB_complete (G : Glob E) (c : String) (values ds : List Decl)
    (catalogue : BoundMemoryCatalogue (· ∈ values) G c ds) :
    ∃ fuel, catalogueB G c values fuel ds = true := by
  apply entries_common_fuel
  intro d member
  apply entryB_complete
  intro x only
  have same := List.mem_singleton.mp only
  subst x
  exact catalogue d member

theorem catalogueB_iff_from_elaborate (res : Resolution)
    (elaborated : (Source.elaborate res).isSome = true)
    (G : Glob res.env) (program : G.prog = Source.progOf res.env) (c : String)
    (values ds : List Decl) (checked : Solidity.Lowering.P9.WholeProgram.check res G c values = true) :
    BoundMemoryCatalogue (· ∈ values) G c ds ↔
      ∃ fuel, catalogueB G c values fuel ds = true :=
  ⟨catalogueB_complete G c values ds,fun ⟨fuel,accepted⟩ =>
    catalogueB_from_elaborate res elaborated G program c values ds fuel checked accepted⟩

/-- info: 'Solidity.Source.Calls.Recognize.entryB_mono' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms entryB_mono
/-- info: 'Solidity.Source.Calls.Recognize.catalogueB_mono' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms catalogueB_mono
/-- info: 'Solidity.Source.Calls.Recognize.entryB_complete' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms entryB_complete
/-- info: 'Solidity.Source.Calls.Recognize.entries_common_fuel' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms entries_common_fuel
/-- info: 'Solidity.Source.Calls.Recognize.catalogueB_complete' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms catalogueB_complete
/-- info: 'Solidity.Source.Calls.Recognize.catalogueB_iff_from_elaborate' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms catalogueB_iff_from_elaborate
end Solidity.Source.Calls.Recognize
