import Solidity.Frontend.Admission.ProgramObservations
import Solidity.Lowering.P9.ProgramAdmission

/-! Checked finite dispatch-target coverage for the actual source Program.
This consumes P9's function-dispatch membership proof. It does not prove
that arbitrary executed receivers/contracts/targets occur in these rosters,
that frames agree, or that full G15/SourceSpec admission is implemented. -/
namespace Solidity.Lowering.P8.DispatchCoverage
open Source Frontend.Admission

/-- Modifier dispatch selects an actual environment entry or its input.
No equality of names is substituted for intrinsic declaration identity. -/
theorem dispatchMod_mem {E : Env} (G : Glob E) (c : String) (d : Decl)
    (hd : d ∈ E.decls) : G.dispatchMod c d ∈ E.decls := by
  unfold Glob.dispatchMod
  dsimp only
  split
  · cases hf : ((E.linearize c).getD [c]).findSome? (fun s =>
        (E.declared (some s) d.name).find? fun d' =>
          d'.kind == .modifier && (G.prog.body d').isSome) with
    | none => exact hd
    | some d' =>
      obtain ⟨s, _, hfind⟩ := List.exists_of_findSome?_eq_some hf
      have hm := (List.mem_filter.mp (List.mem_of_find?_eq_some hfind)).1
      exact hm
  · exact hd

def checkFunctionTarget {E : Env} (G : Glob E) (c : String) (d : Decl) : Bool :=
  decide (d ∈ E.decls) && (G.prog.body (G.dispatchFn c d)).isSome

def checkModifierTarget {E : Env} (G : Glob E) (c : String) (d : Decl) : Bool :=
  decide (d ∈ E.decls) && (G.prog.body (G.dispatchMod c d)).isSome

theorem function_target_sound {E : Env} (G : Glob E) (c : String) (d : Decl)
    (h : checkFunctionTarget G c d = true) :
    G.dispatchFn c d ∈ E.decls ∧ ∃ b, G.prog.body (G.dispatchFn c d) = some b := by
  simp only [checkFunctionTarget, Bool.and_eq_true, decide_eq_true_eq] at h
  refine ⟨P9.WholeProgram.dispatch_mem G c d E.decls rfl h.1, ?_⟩
  cases hb : G.prog.body (G.dispatchFn c d) with
  | none => rw [hb] at h; cases h.2
  | some b => exact ⟨b, rfl⟩

theorem modifier_target_sound {E : Env} (G : Glob E) (c : String) (d : Decl)
    (h : checkModifierTarget G c d = true) :
    G.dispatchMod c d ∈ E.decls ∧ ∃ b, G.prog.body (G.dispatchMod c d) = some b := by
  simp only [checkModifierTarget, Bool.and_eq_true, decide_eq_true_eq] at h
  refine ⟨dispatchMod_mem G c d h.1, ?_⟩
  cases hb : G.prog.body (G.dispatchMod c d) with
  | none => rw [hb] at h; cases h.2
  | some b => exact ⟨b, rfl⟩

def checkCallSite {E : Env} (G : Glob E) (c : String) : ObservationSite → Bool
  | .internalCall d | .externalCall d => checkFunctionTarget G c d
  | _ => true

/-- Check actual intrinsic declaration identity and selected body existence
at every finite contract/call/modifier target. No manual allowlist, fuel bound
or desired result is provided. Base-name resolution is a separate obligation. -/
def check {E : Env} (G : Glob E) : Bool :=
  G.prog.contracts.all fun c =>
    (programObservations G.prog).all (checkCallSite G c) &&
      (programModifierTargets G.prog).all (checkModifierTarget G c)

theorem call_site_checked {E : Env} (G : Glob E) (h : check G = true)
    {c : String} (hc : c ∈ G.prog.contracts) {site : ObservationSite}
    (hs : site ∈ programObservations G.prog) : checkCallSite G c site = true := by
  have hall := List.all_eq_true.mp h c hc
  simp only [Bool.and_eq_true] at hall
  exact List.all_eq_true.mp hall.1 site hs

theorem modifier_checked {E : Env} (G : Glob E) (h : check G = true)
    {c : String} (hc : c ∈ G.prog.contracts) {d : Decl}
    (hd : d ∈ programModifierTargets G.prog) : checkModifierTarget G c d = true := by
  have hall := List.all_eq_true.mp h c hc
  simp only [Bool.and_eq_true] at hall
  exact List.all_eq_true.mp hall.2 d hd

theorem internal_body_covered {E : Env} (G : Glob E) (h : check G = true)
    {c : String} (hc : c ∈ G.prog.contracts) {d : Decl}
    (hd : ObservationSite.internalCall d ∈ programObservations G.prog) :
    ∃ b, G.prog.body (G.dispatchFn c d) = some b ∧
      ∀ site ∈ bodyObservations b, site ∈ programObservations G.prog := by
  obtain ⟨hm, b, hb⟩ := function_target_sound G c d (call_site_checked G h hc hd)
  exact ⟨b, hb, fun site hs => body_site_in_program G.prog hm hb hs⟩

theorem external_body_covered {E : Env} (G : Glob E) (h : check G = true)
    {c : String} (hc : c ∈ G.prog.contracts) {d : Decl}
    (hd : ObservationSite.externalCall d ∈ programObservations G.prog) :
    ∃ b, G.prog.body (G.dispatchFn c d) = some b ∧
      ∀ site ∈ bodyObservations b, site ∈ programObservations G.prog := by
  obtain ⟨hm, b, hb⟩ := function_target_sound G c d (call_site_checked G h hc hd)
  exact ⟨b, hb, fun site hs => body_site_in_program G.prog hm hb hs⟩

theorem modifier_body_covered {E : Env} (G : Glob E) (h : check G = true)
    {c : String} (hc : c ∈ G.prog.contracts) {d : Decl}
    (hd : d ∈ programModifierTargets G.prog) :
    ∃ b, G.prog.body (G.dispatchMod c d) = some b ∧
      ∀ site ∈ bodyObservations b, site ∈ programObservations G.prog := by
  obtain ⟨hm, b, hb⟩ := modifier_target_sound G c d (modifier_checked G h hc hd)
  exact ⟨b, hb, fun site hs => body_site_in_program G.prog hm hb hs⟩

#print axioms dispatchMod_mem
#print axioms internal_body_covered
#print axioms external_body_covered
#print axioms modifier_body_covered
end Solidity.Lowering.P8.DispatchCoverage
