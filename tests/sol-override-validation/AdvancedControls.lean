import Solidity.Frontend.OverrideValidation.Memoized

/-! Inhabited full-judgment and original-body controls. All theorem witnesses
are checked by the kernel; executable pins are explicitly separate. -/
namespace Solidity.Frontend.OverrideValidation.AdvancedControls
open Solidity.Source

def emptyBody : Syn (.opt (.block .body)) := .some (.block .nil)
def returnBody : Syn (.opt (.block .body)) :=
  .some (.block (.cons (.stmtItem (.returnStmt .none)) .nil))
def fn (b : Syn (.opt (.block .body))) : Syn (.part false) :=
  .function (.ident "f") .nil (some .pub) none .nil false none .nil b

def root : Syn .top := .contract false "C" .none .nil (.cons (fn emptyBody) .nil)
def good : Env := (Syn.unit (.cons root .nil)).env

def rootRef : Node good := ⟨0, by decide⟩
def fnRef : Node good := ⟨1, by decide⟩

/-- A nonempty concrete contract inhabits the complete independent judgment. -/
theorem good_accepted : OverrideGraphOK good := by
  apply validateB_iff.mp
  unfold validateB
  have he : extractionB good = true := extractionB_iff.mpr rfl
  rw [he]
  decide

theorem good_certificate : (certify good).isSome = true := certify_isSome_iff.mpr good_accepted

theorem good_dispatch : dispatch good rootRef fnRef = some ⟨fnRef, fnRef⟩ := by
  apply dispatch_iff.mpr
  exact ⟨rfl, choose_iff.mp (by decide)⟩

theorem good_original_body :
    good.decls[fnRef.val]? = some fnRef.decl ∧ fnRef.decl.hasBody = true :=
  ⟨node_lookup fnRef, rfl⟩

/-- The root syntax still contains f, but the flattened member is missing. -/
def missing : Env := ⟨[⟨.contract, "C", none, true, root⟩]⟩

theorem missing_rejected : ¬ OverrideGraphOK missing := by
  intro h
  have hl : missing.decls.length = (reconstructed missing).length := congrArg List.length h.extraction
  change 1 = 2 at hl
  cases hl

theorem missing_certificate : certify missing = none := certify_none_iff.mpr missing_rejected

/-- The flattened member has the same name/signature but a substituted body. -/
def substituted : Env := ⟨[⟨.contract, "C", none, true, root⟩,
  ⟨.function, "f", some "C", false, fn returnBody⟩]⟩

def isEmpty (d : Decl) : Bool :=
  match d.kind, d.top, d.node with
  | .function, _, .function _ _ _ _ _ _ _ _ (.some (.block .nil)) => true
  | _, _, _ => false

theorem substituted_rejected : ¬ OverrideGraphOK substituted := by
  intro h
  have hb := congrArg (fun ds : List Decl => (ds[1]?).map isEmpty) h.extraction
  change some false = some true at hb
  cases hb

def u256 : Syn .typeName := .elem (.int false 256 (by decide))
def badVar : Syn (.part false) := .stateVar u256 (some .priv) none (some []) false "x" .none

def privateOverride : Env :=
  (Syn.unit (.cons (.contract false "D" .none .nil (.cons badVar .nil)) .nil)).env

def privateVarRef : Node privateOverride := ⟨1, by decide⟩

theorem private_override_rejected : ¬ OverrideGraphOK privateOverride := by
  intro h
  have hb := (h.valid.attributes privateVarRef).stateVariableOverride rfl rfl
  change none = some Family.getter at hb
  cases hb

theorem private_override_certificate : certify privateOverride = none :=
  certify_none_iff.mpr private_override_rejected

/-- Every special callable family has a nonempty accepted Source witness. -/
def single (part : Syn (.part false)) : Env :=
  (Syn.unit (.cons (.contract false "Special" .none .nil (.cons part .nil)) .nil)).env

def getterEnv : Env := single (.stateVar u256 (some .pub) none none false "x" .none)
def fallbackEnv : Env := single (.fallback .fbNoParams true none .nil false none emptyBody)
def receiveEnv : Env := single (.receive true true .nil false none emptyBody)
def placeholderBody : Syn (.opt (.block .body)) :=
  .some (.block (.cons (.stmtItem (.simpleStmt (.exprStmt (.ident "_")))) .nil))
def modifierEnv : Env := single (.modifier "m" .none false none placeholderBody)

theorem getter_accepted : OverrideGraphOK getterEnv := by
  apply validateB_iff.mp
  unfold validateB
  have he : extractionB getterEnv = true := extractionB_iff.mpr rfl
  rw [he]
  decide

theorem fallback_accepted : OverrideGraphOK fallbackEnv := by
  apply validateB_iff.mp
  unfold validateB
  have he : extractionB fallbackEnv = true := extractionB_iff.mpr rfl
  rw [he]
  decide

theorem receive_accepted : OverrideGraphOK receiveEnv := by
  apply validateB_iff.mp
  unfold validateB
  have he : extractionB receiveEnv = true := extractionB_iff.mpr rfl
  rw [he]
  decide

theorem modifier_accepted : OverrideGraphOK modifierEnv := by
  apply validateB_iff.mp
  unfold validateB
  have he : extractionB modifierEnv = true := extractionB_iff.mpr rfl
  rw [he]
  decide

/-- info: true -/
#guard_msgs in
#eval fastValidateB good

/-- info: false -/
#guard_msgs in
#eval fastValidateB substituted

/-- info: false -/
#guard_msgs in
#eval fastValidateB privateOverride

end Solidity.Frontend.OverrideValidation.AdvancedControls

-- Complete theorem axiom audit; only standard kernel axioms are permitted.
/-- info: 'Solidity.Frontend.OverrideValidation.AdvancedControls.good_accepted' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms Solidity.Frontend.OverrideValidation.AdvancedControls.good_accepted
/-- info: 'Solidity.Frontend.OverrideValidation.AdvancedControls.good_certificate' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms Solidity.Frontend.OverrideValidation.AdvancedControls.good_certificate
/-- info: 'Solidity.Frontend.OverrideValidation.AdvancedControls.good_dispatch' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms Solidity.Frontend.OverrideValidation.AdvancedControls.good_dispatch
/-- info: 'Solidity.Frontend.OverrideValidation.AdvancedControls.good_original_body' depends on axioms: [propext] -/
#guard_msgs in
#print axioms Solidity.Frontend.OverrideValidation.AdvancedControls.good_original_body
/-- info: 'Solidity.Frontend.OverrideValidation.AdvancedControls.missing_rejected' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms Solidity.Frontend.OverrideValidation.AdvancedControls.missing_rejected
/-- info: 'Solidity.Frontend.OverrideValidation.AdvancedControls.missing_certificate' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms Solidity.Frontend.OverrideValidation.AdvancedControls.missing_certificate
/-- info: 'Solidity.Frontend.OverrideValidation.AdvancedControls.substituted_rejected' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms Solidity.Frontend.OverrideValidation.AdvancedControls.substituted_rejected
/-- info: 'Solidity.Frontend.OverrideValidation.AdvancedControls.private_override_rejected' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms Solidity.Frontend.OverrideValidation.AdvancedControls.private_override_rejected
/-- info: 'Solidity.Frontend.OverrideValidation.AdvancedControls.private_override_certificate' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms Solidity.Frontend.OverrideValidation.AdvancedControls.private_override_certificate
/-- info: 'Solidity.Frontend.OverrideValidation.AdvancedControls.getter_accepted' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms Solidity.Frontend.OverrideValidation.AdvancedControls.getter_accepted
/-- info: 'Solidity.Frontend.OverrideValidation.AdvancedControls.fallback_accepted' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms Solidity.Frontend.OverrideValidation.AdvancedControls.fallback_accepted
/-- info: 'Solidity.Frontend.OverrideValidation.AdvancedControls.receive_accepted' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms Solidity.Frontend.OverrideValidation.AdvancedControls.receive_accepted
/-- info: 'Solidity.Frontend.OverrideValidation.AdvancedControls.modifier_accepted' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms Solidity.Frontend.OverrideValidation.AdvancedControls.modifier_accepted
