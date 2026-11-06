import Solidity.Frontend.Admission.RootObservations
import Solidity.Source.Elaborated

/-! Finite observation scanning of the actual carried Program. This closes
container enumeration, not semantic reachability or all-feature extraction.
No program, source relation, profile or evaluator representation is changed. -/
namespace Solidity.Frontend.Admission
open Solidity.Source

def bodyObservations {E : Env} (b : RBody E) : List ObservationSite :=
  itemsObservations b.items ++ b.mods.flatMap (fun m => convObservations m.args)

def declarationObservations {E : Env} (P : Program E) (d : Decl) : List ObservationSite :=
  (P.body d).toList.flatMap bodyObservations ++
    (P.consts d).toList.flatMap (fun i => observations i.e)

def contractObservations {E : Env} (P : Program E) (c : String) : List ObservationSite :=
  (P.ctor c).toList.flatMap bodyObservations ++
    (P.inits c).flatMap (fun i => observations i.e) ++
    (P.baseArgs c).flatMap (fun a => convObservations a.args)

/-- Every environment declaration and every carried contract is scanned,
including unused bodies. Calls are not recursively unfolded: scanning all
carried declarations handles cycles without a fuel bound. This does not prove
that an arbitrary target queried by the evaluator belongs to the roster. -/
def programObservations {E : Env} (P : Program E) : List ObservationSite :=
  E.decls.flatMap (declarationObservations P) ++ P.contracts.flatMap (contractObservations P)

/-- Independent container-level occurrence relation on the actual Program
fields. Inner expression occurrence remains the existing typed visitor. -/
def ProgramSite {E : Env} (P : Program E) (site : ObservationSite) : Prop :=
  (∃ d ∈ E.decls, (∃ b, P.body d = some b ∧ site ∈ bodyObservations b) ∨
    (∃ i, P.consts d = some i ∧ site ∈ observations i.e)) ∨
  (∃ c ∈ P.contracts, (∃ b, P.ctor c = some b ∧ site ∈ bodyObservations b) ∨
    (∃ i ∈ P.inits c, site ∈ observations i.e) ∨
    (∃ a ∈ P.baseArgs c, site ∈ convObservations a.args))

theorem program_observation_iff {E : Env} (P : Program E) (site : ObservationSite) :
    site ∈ programObservations P ↔ ProgramSite P site := by
  simp only [programObservations, declarationObservations, contractObservations,
    ProgramSite, List.mem_append, List.mem_flatMap, Option.mem_toList, or_assoc]

theorem body_site_in_program {E : Env} (P : Program E) {d : Decl} {b : RBody E}
    (hd : d ∈ E.decls) (hb : P.body d = some b) {site : ObservationSite}
    (hs : site ∈ bodyObservations b) : site ∈ programObservations P :=
  (program_observation_iff P site).mpr (.inl ⟨d, hd, .inl ⟨b, hb, hs⟩⟩)

theorem modifier_argument_in_program {E : Env} (P : Program E) {d : Decl} {b : RBody E}
    (hd : d ∈ E.decls) (hb : P.body d = some b) {m : RModInv E b.locals}
    (hm : m ∈ b.mods) {site : ObservationSite} (hs : site ∈ convObservations m.args) :
    site ∈ programObservations P := by
  apply body_site_in_program P hd hb
  exact List.mem_append_right _ (List.mem_flatMap.mpr ⟨m, hm, hs⟩)

theorem constant_site_in_program {E : Env} (P : Program E) {d : Decl} {i : RInit E}
    (hd : d ∈ E.decls) (hi : P.consts d = some i) {site : ObservationSite}
    (hs : site ∈ observations i.e) : site ∈ programObservations P :=
  (program_observation_iff P site).mpr (.inl ⟨d, hd, .inr ⟨i, hi, hs⟩⟩)

theorem constructor_site_in_program {E : Env} (P : Program E) {c : String} {b : RBody E}
    (hc : c ∈ P.contracts) (hb : P.ctor c = some b) {site : ObservationSite}
    (hs : site ∈ bodyObservations b) : site ∈ programObservations P :=
  (program_observation_iff P site).mpr (.inr ⟨c, hc, .inl ⟨b, hb, hs⟩⟩)

theorem initializer_site_in_program {E : Env} (P : Program E) {c : String} {i : RInit E}
    (hc : c ∈ P.contracts) (hi : i ∈ P.inits c) {site : ObservationSite}
    (hs : site ∈ observations i.e) : site ∈ programObservations P :=
  (program_observation_iff P site).mpr (.inr ⟨c, hc, .inr (.inl ⟨i, hi, hs⟩)⟩)

theorem base_argument_in_program {E : Env} (P : Program E) {c : String}
    {a : RBaseArg E (P.ctorLocals c)} (hc : c ∈ P.contracts) (ha : a ∈ P.baseArgs c)
    {site : ObservationSite} (hs : site ∈ convObservations a.args) :
    site ∈ programObservations P :=
  (program_observation_iff P site).mpr (.inr ⟨c, hc, .inr (.inr ⟨a, ha, hs⟩)⟩)

/-- No executed-call assumption is smuggled into the scan. Once its actual
lookup target is in the roster, every observation in that target body is
covered, including mutually/self recursive targets, without unfolding calls. -/
theorem target_body_covered {E : Env} (P : Program E)
    (accepted : (programObservations P).all ObservationSite.allowed = true)
    {d : Decl} {b : RBody E} (hd : d ∈ E.decls) (hb : P.body d = some b) :
    ∀ site ∈ bodyObservations b, site.allowed = true := by
  intro site hs
  exact List.all_eq_true.mp accepted site (body_site_in_program P hd hb hs)

theorem accepted_program_iff {E : Env} (P : Program E) :
    (programObservations P).all ObservationSite.allowed = true ↔
      ∀ site, ProgramSite P site → site.allowed = true := by
  constructor
  · intro h site hs
    exact List.all_eq_true.mp h site ((program_observation_iff P site).mpr hs)
  · intro h
    exact List.all_eq_true.mpr (fun site hs => h site ((program_observation_iff P site).mp hs))

/-- The source elaboration already ties constructor bodies to real environment
members. Their observations therefore also occur in the declaration scan. -/
theorem elaborated_constructor_in_declarations (a : Elaborated) {c : String} {b : RBody a.res.env}
    (hb : a.prog.ctor c = some b) {site : ObservationSite} (hs : site ∈ bodyObservations b) :
    site ∈ a.res.env.decls.flatMap (declarationObservations a.prog) := by
  obtain ⟨d, hd, _, _, hbody⟩ := a.ctor_typed c b hb
  apply List.mem_flatMap.mpr
  refine ⟨d, hd, ?_⟩
  apply List.mem_append_left
  apply List.mem_flatMap.mpr
  exact ⟨b, by simpa only [Option.mem_toList] using hbody, hs⟩
/-- Modifier target identity is retained separately from observation arguments;
its profile feature and executed-target roster obligations remain separate. -/
def programModifierTargets {E : Env} (P : Program E) : List Decl :=
  E.decls.flatMap (fun d => (P.body d).toList.flatMap (fun b => b.mods.map (·.modifier))) ++
    P.contracts.flatMap (fun c => (P.ctor c).toList.flatMap (fun b => b.mods.map (·.modifier)))

theorem modifier_target_iff {E : Env} (P : Program E) (target : Decl) :
    target ∈ programModifierTargets P ↔
    (∃ d ∈ E.decls, ∃ b, P.body d = some b ∧ ∃ m ∈ b.mods, m.modifier = target) ∨
    (∃ c ∈ P.contracts, ∃ b, P.ctor c = some b ∧ ∃ m ∈ b.mods, m.modifier = target) := by
  simp only [programModifierTargets, List.mem_append, List.mem_flatMap,
    List.mem_map, Option.mem_toList]

/-- Written base identities are kept without assuming they resolve. -/
def programBaseTargets {E : Env} (P : Program E) : List String :=
  P.contracts.flatMap (fun c => (P.baseArgs c).map (·.base))

theorem base_target_iff {E : Env} (P : Program E) (target : String) :
    target ∈ programBaseTargets P ↔
    ∃ c ∈ P.contracts, ∃ a ∈ P.baseArgs c, a.base = target := by
  simp only [programBaseTargets, List.mem_flatMap, List.mem_map]
end Solidity.Frontend.Admission
