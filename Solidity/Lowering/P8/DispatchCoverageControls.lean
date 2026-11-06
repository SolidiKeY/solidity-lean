import Solidity.Lowering.P8.DispatchCoverage
import Solidity.Lowering.P9.CallControls
import Solidity.Lowering.P9.AdmissionControls

/-! Reuse the published actually elaborated P9 function and source execution.
Additional carrier mutations are explicitly synthetic checker controls, not
new elaboration, SourceSpec or EVM execution witnesses. -/
namespace Solidity.Lowering.P8.DispatchControls
open Source Frontend.Admission DispatchCoverage P9

theorem actual_target_checked (fixed : Roadmap.Fixed) :
    checkFunctionTarget (P9.glob fixed) "P9" declaration = true := by
  simp only [checkFunctionTarget, dispatch_eq,
    show (P9.glob fixed).prog.body declaration = some body from prog_body,
    Option.isSome_some, Bool.and_true, decide_eq_true_eq]
  exact declaration_present

theorem actual_target_in_scan (fixed : Roadmap.Fixed) :
    ∀ site ∈ bodyObservations body, site ∈ programObservations (P9.glob fixed).prog :=
  fun _ hs => body_site_in_program _ declaration_present prog_body hs

/-- Actual source-machine observation, reused verbatim; not an EVM claim. -/
theorem inherited_source_execution (fixed : Roadmap.Fixed) (s : St resolution.env) :
    (callInternal (P9.glob fixed) caller 10 declaration (ps := []) .nil [.bool]).run (.nil, s) =
      (.ok (.val (.bool true)), (.nil, s)) := internal_success fixed s

/-- A genuine typed recursive call site; no termination claim. -/
def recursiveBody : RBody resolution.env := {
  ps := [], rs := [.bool], inModifier := false
  locals := [.bool], out := [.bool]
  items := .stmt (.expr protectedCall) .nil }

def recursiveProgram : Program resolution.env := {
  body := fun _ => some recursiveBody, consts := fun _ => none
  inits := fun _ => [], ctor := fun _ => none, ctorLocals := fun _ => []
  baseArgs := fun _ => [], contracts := ["P9"] }

def recursiveGlob : Glob resolution.env := {
  P9.glob AdmissionControls.observationFixed with prog := recursiveProgram }

theorem recursive_site_populated :
    ObservationSite.internalCall declaration ∈ programObservations recursiveProgram := by
  apply body_site_in_program recursiveProgram declaration_present rfl
  exact List.mem_append_left _ List.mem_cons_self

theorem recursive_dispatch : recursiveGlob.dispatchFn "P9" declaration = declaration := by
  have hscope : (declaration.scope.isSome && ["P9"].any (fun x => some x == declaration.scope)) = true := by decide +kernel
  unfold Glob.dispatchFn
  rw [signature, linearize_eq]
  simp only [Option.getD_some]
  rw [hscope]
  simp only [↓reduceIte, List.findSome?_cons, fn_in_eq, List.find?_cons,
    show recursiveGlob.prog.body declaration = some recursiveBody from rfl,
    Option.isSome_some, Option.getD_some]

theorem recursive_targets_checked : check recursiveGlob = true := by
  have hfn : checkFunctionTarget recursiveGlob "P9" declaration = true := by
    simp only [checkFunctionTarget, recursive_dispatch,
      show recursiveGlob.prog.body declaration = some recursiveBody from rfl,
      Option.isSome_some, Bool.and_true, decide_eq_true_eq]
    exact declaration_present
  change (((checkFunctionTarget recursiveGlob "P9" declaration &&
    (checkFunctionTarget recursiveGlob "P9" declaration && true)) && true) && true) = true
  rw [hfn]
  rfl

/-- Successful target/body coverage derives from the computed check. -/
theorem recursive_body_covered :
    ∃ b, recursiveGlob.prog.body (recursiveGlob.dispatchFn "P9" declaration) = some b ∧
      ∀ site ∈ bodyObservations b, site ∈ programObservations recursiveGlob.prog :=
  internal_body_covered recursiveGlob recursive_targets_checked
    (by decide +kernel) recursive_site_populated

/-- A missing body makes the local target query fail. A retained constructor
call site below prevents the global negative control becoming vacuous. -/
def noBodies : Glob resolution.env :=
  {recursiveGlob with prog := {recursiveProgram with body := fun _ => none, ctor := fun _ => some recursiveBody}}

theorem missing_body_refused : checkFunctionTarget noBodies "P9" declaration = false := by
  simp only [checkFunctionTarget]
  exact Bool.and_false _

theorem missing_body_global_refused : check noBodies = false := by decide +kernel

theorem missing_body_call_retained :
    ObservationSite.internalCall declaration ∈ programObservations noBodies.prog := by
  apply (program_observation_iff noBodies.prog _).mpr
  exact .inr ⟨"P9", List.mem_cons_self, .inl ⟨recursiveBody, rfl, List.mem_append_left _ List.mem_cons_self⟩⟩

/-- Intrinsic declaration identity, not spelling alone, controls the roster. -/
def foreignDecl : Decl := {declaration with scope := some "Foreign"}
theorem foreign_target_refused : checkFunctionTarget recursiveGlob "P9" foreignDecl = false := by decide +kernel

/-- The actual interface fixture is elaborated, yet its abstract declaration
has no body. No invented implementation is admitted. -/
def abstractGlob : Glob AdmissionControls.interfaceResolution.env := {
  prog := progOf AdmissionControls.interfaceResolution.env
  pipeline := .legacy, fixed := AdmissionControls.observationFixed
  balance0 := fun _ => ⟨0, by decide⟩, hasCode := fun _ _ => true
  callee := fun _ => .answer (.success []), timestamp := ⟨0, by decide⟩ }

theorem abstract_target_refused :
    checkFunctionTarget abstractGlob "NoContract" AdmissionControls.abstractDecl = false := by decide +kernel

/-- Synthetic modifier carrier: actual .modifier identity and a populated
invocation; fallback dispatch at a free scope is checked, not assumed. -/
def modifierDecl : Decl := ⟨.modifier, "guard", none, false,
  .modifier "guard" .none false none (.some (.block .nil))⟩
def modifierEnv : Env := ⟨[modifierDecl]⟩
def modifierBody : RBody modifierEnv := {
  ps := [], rs := [], inModifier := true, locals := [], out := [], items := .stmt (.expr (.magic .block "timestamp" rfl)) .nil
  mods := [⟨modifierDecl, [], .nil⟩] }
def modifierProgram : Program modifierEnv := {
  body := fun _ => some modifierBody, consts := fun _ => none
  inits := fun _ => [], ctor := fun _ => none, ctorLocals := fun _ => []
  baseArgs := fun _ => [], contracts := ["Carrier"] }
def modifierGlob : Glob modifierEnv := {
  prog := modifierProgram, pipeline := .legacy, fixed := AdmissionControls.observationFixed
  balance0 := fun _ => ⟨0, by decide⟩, hasCode := fun _ _ => true
  callee := fun _ => .answer (.success []), timestamp := ⟨0, by decide⟩ }

theorem modifier_populated : programModifierTargets modifierProgram = [modifierDecl] := rfl

theorem modifier_target_checked : checkModifierTarget modifierGlob "Carrier" modifierDecl = true := by decide +kernel

theorem modifier_program_checked : check modifierGlob = true := by decide +kernel

theorem modifier_selected_covered :
    ∃ b, modifierGlob.prog.body (modifierGlob.dispatchMod "Carrier" modifierDecl) = some b ∧
      ∀ site ∈ bodyObservations b, site ∈ programObservations modifierGlob.prog :=
  modifier_body_covered modifierGlob modifier_program_checked List.mem_cons_self
    (by rw [show modifierGlob.prog = modifierProgram from rfl, modifier_populated]; exact List.mem_cons_self)

theorem modifier_observation_populated : bodyObservations modifierBody = [.magic .block "timestamp"] := rfl

/-- The selected modifier body has a real observation, not empty coverage. -/
theorem selected_modifier_observation :
    ObservationSite.magic .block "timestamp" ∈ programObservations modifierGlob.prog :=
  body_site_in_program _ List.mem_cons_self rfl (by rw [modifier_observation_populated]; exact List.mem_cons_self)

def absentModifier : Glob modifierEnv := {
  modifierGlob with prog := {modifierProgram with body := (fun _ => none), ctor := (fun _ => some modifierBody)} }

theorem missing_modifier_refused : checkModifierTarget absentModifier "Carrier" modifierDecl = false := by decide +kernel

theorem missing_modifier_global_refused : check absentModifier = false := by decide +kernel

#print axioms modifier_program_checked
#print axioms modifier_selected_covered
#print axioms missing_modifier_global_refused
#print axioms missing_body_global_refused
#print axioms actual_target_checked
#print axioms recursive_targets_checked
#print axioms recursive_body_covered
#print axioms missing_body_refused
#print axioms foreign_target_refused
#print axioms abstract_target_refused
#print axioms inherited_source_execution
end Solidity.Lowering.P8.DispatchControls
