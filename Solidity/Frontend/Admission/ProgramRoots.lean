import Solidity.Frontend.Admission.ProgramObservations

/-! Typed roots of the actual carried Program fields. This inventories finite rosters, not dynamic dispatch or semantic reachability outside those rosters. No source program, frame, evaluator or profile is replaced. -/
namespace Solidity.Frontend.Admission
open Solidity.Source

inductive ProgramRoot {E : Env} (P : Program E) where
  | body (declaration : Decl) (value : RBody E)
  | constant (declaration : Decl) (value : RInit E)
  | constructor (contract : String) (value : RBody E)
  | initializer (contract : String) (value : RInit E)
  | baseArguments (contract : String) (value : RBaseArg E (P.ctorLocals contract))

def declarationRoots {E : Env} (P : Program E) (d : Decl) : List (ProgramRoot P) :=
  (P.body d).toList.map (ProgramRoot.body d) ++
    (P.consts d).toList.map (ProgramRoot.constant d)

def contractRoots {E : Env} (P : Program E) (c : String) : List (ProgramRoot P) :=
  (P.ctor c).toList.map (ProgramRoot.constructor c) ++
    (P.inits c).map (ProgramRoot.initializer c) ++
    (P.baseArgs c).map (ProgramRoot.baseArguments c)

def programRoots {E : Env} (P : Program E) : List (ProgramRoot P) :=
  E.decls.flatMap (declarationRoots P) ++ P.contracts.flatMap (contractRoots P)

/-- Independent field lookup/roster relation, without referring to programRoots. -/
def ProgramRoot.Occurs {E : Env} {P : Program E} : ProgramRoot P → Prop
  | .body d b => d ∈ E.decls ∧ P.body d = some b
  | .constant d i => d ∈ E.decls ∧ P.consts d = some i
  | .constructor c b => c ∈ P.contracts ∧ P.ctor c = some b
  | .initializer c i => c ∈ P.contracts ∧ i ∈ P.inits c
  | .baseArguments c a => c ∈ P.contracts ∧ a ∈ P.baseArgs c

def ProgramRoot.observations {E : Env} {P : Program E} : ProgramRoot P → List ObservationSite
  | .body _ b => bodyObservations b
  | .constant _ i => Solidity.Frontend.Admission.observations i.e
  | .constructor _ b => bodyObservations b
  | .initializer _ i => Solidity.Frontend.Admission.observations i.e
  | .baseArguments _ a => convObservations a.args

theorem programRoots_exact {E : Env} (P : Program E) (r : ProgramRoot P) :
    r ∈ programRoots P ↔ r.Occurs := by
  cases r <;> simp only [programRoots, declarationRoots, contractRoots,
    ProgramRoot.Occurs, List.mem_append, List.mem_flatMap, List.mem_map,
    Option.mem_toList, ProgramRoot.body.injEq, ProgramRoot.constant.injEq,
    ProgramRoot.constructor.injEq, ProgramRoot.initializer.injEq,
    ProgramRoot.baseArguments.injEq, reduceCtorEq, exists_false,
    exists_eq_left, exists_and_left,
    exists_and_right, heq_eq_eq, false_and, and_false, false_or, or_false,
    and_assoc, and_left_comm, and_comm]

theorem programRoots_observations {E : Env} (P : Program E) :
    (programRoots P).flatMap ProgramRoot.observations = programObservations P := by
  have hd (d : Decl) : (declarationRoots P d).flatMap ProgramRoot.observations =
      declarationObservations P d := by
    simp only [declarationRoots, declarationObservations, List.flatMap_append,
      List.flatMap_map, ProgramRoot.observations]
  have hc (c : String) : (contractRoots P c).flatMap ProgramRoot.observations =
      contractObservations P c := by
    simp only [contractRoots, contractObservations, List.flatMap_append,
      List.flatMap_map, ProgramRoot.observations]
  simp only [programRoots, programObservations, List.flatMap_append,
    List.flatMap_assoc, hd, hc]

/-- Exact observation-admission proposition, proved below. This equivalence classifies observations, not all source features. -/
abbrev RootAdmissionEquivalence {E : Env} (P : Program E) : Prop :=
  (programObservations P).all ObservationSite.allowed = true ↔
    ∀ r : ProgramRoot P, r.Occurs → ∀ site ∈ r.observations, site.allowed = true

/-- info: 'Solidity.Frontend.Admission.programRoots_exact' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms programRoots_exact
/-- info: 'Solidity.Frontend.Admission.programRoots_observations' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms programRoots_observations
theorem root_admission_equivalence : ∀ {E : Solidity.Source.Env} (P : Solidity.Source.Program E), Solidity.Frontend.Admission.RootAdmissionEquivalence P := by
  intro E P
  unfold Solidity.Frontend.Admission.RootAdmissionEquivalence
  rw [← Solidity.Frontend.Admission.programRoots_observations P]
  constructor
  · intro h r hr site hs
    exact List.all_eq_true.mp h site (List.mem_flatMap.mpr ⟨r, (Solidity.Frontend.Admission.programRoots_exact P r).mpr hr, hs⟩)
  · intro h
    apply List.all_eq_true.mpr
    intro site hs
    obtain ⟨r, hr, hs⟩ := List.mem_flatMap.mp hs
    exact h r ((Solidity.Frontend.Admission.programRoots_exact P r).mp hr) site hs

/-- info: 'Solidity.Frontend.Admission.root_admission_equivalence' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms root_admission_equivalence
end Solidity.Frontend.Admission
