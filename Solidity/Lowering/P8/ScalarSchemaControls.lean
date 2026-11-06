import Solidity.Lowering.P8.ScalarSchema

/-! Actual resolved, WellFormed and in-profile core Source witnesses. These are
not parser-completeness or whole checked-frontend admission certificates. -/
namespace Solidity.Lowering.P8.ScalarControls

def decl (name : String) (m : Source.Syn .structMember)
    (ms : Source.Syn (.list .structMember)) : Source.Decl :=
  ⟨.struct, name, none, true, .struct name m ms⟩
def unit (name : String) (m : Source.Syn .structMember)
    (ms : Source.Syn (.list .structMember)) : Source.Syn .unit :=
  .unit (.cons (.topPart (.struct name m ms)) .nil)
def resolution (name : String) (m : Source.Syn .structMember)
    (ms : Source.Syn (.list .structMember)) : Source.Resolution :=
  Source.resolveUnit {pipeline := .legacy} (unit name m ms)

theorem core_wellFormed (name : String) (m : Source.Syn .structMember)
    (ms : Source.Syn (.list .structMember))
    (ht : (decl name m ms).typesOK (resolution name m ms).env = true) :
    Source.WellFormed (resolution name m ms) := by
  have only : ∀ d ∈ (resolution name m ms).unit.decls, d = decl name m ms := by
    intro d hd
    change d ∈ [decl name m ms] at hd
    simpa only [List.mem_cons, List.not_mem_nil, or_false] using hd
  refine ⟨rfl, ?_, ?_, ?_, by change 0 ≤ 1; decide, ?_, ?_, ?_, ?_, ?_⟩
  · intro d hd hk
    have he := only d hd
    subst d
    rcases hk with hk | hk <;> cases hk
  · change List.Pairwise _ [decl name m ms]
    exact .cons (by intro a ha; cases ha) .nil
  · intro ws hw
    change ws ∈ ([] : List (List String)) at hw
    cases hw
  · intro d hd
    have he := only d hd
    subst d
    exact ht
  · intro d hd
    have he := only d hd
    subst d
    rfl
  · intro d hd hc
    have he := only d hd
    subst d
    cases hc
  · intro d hd e hi
    have he := only d hd
    subst d
    cases hi
  · intro d hd hb
    have he := only d hd
    subst d
    cases hb

def first : Source.Syn .structMember := .structMember (.elem (.int false 8 (by decide))) "value"
def rest : Source.Syn (.list .structMember) := .cons (.structMember (.elem .bool) "live") .nil

def good := decl "P8Record" first rest
def goodResolution := resolution "P8Record" first rest

theorem good_resolves : Source.Resolves' {pipeline := .legacy} (unit "P8Record" first rest) goodResolution :=
  ⟨rfl, rfl⟩
theorem good_wellFormed : Source.WellFormed goodResolution := core_wellFormed _ _ _ rfl
theorem good_profile : Source.InProfileSyntax goodResolution := rfl

def compiled := (scalarStruct good rfl .storage).get (by decide +kernel)

theorem schema_from_core_source :
    Source.WellFormed goodResolution ∧ Source.InProfileSyntax goodResolution ∧
    Nonempty (V07.DeclarationGraph goodResolution.env .storage compiled.1) :=
  ⟨good_wellFormed, good_profile, ⟨compiled.2⟩⟩

theorem exact_fields : compiled.1.fields ⟨0, by decide⟩ =
    [("value", .prim .uint), ("live", .prim .bool)] := by decide +kernel

theorem wrong_field_order : compiled.1.fields ⟨0, by decide⟩ ≠
    [("live", .prim .bool), ("value", .prim .uint)] := by decide +kernel

def duplicateRest : Source.Syn (.list .structMember) := .cons (.structMember (.elem .bool) "value") .nil

theorem duplicate_core_wellFormed : Source.WellFormed (resolution "P8Record" first duplicateRest) :=
  core_wellFormed _ _ _ rfl

theorem duplicate_profile : Source.InProfileSyntax (resolution "P8Record" first duplicateRest) := rfl

/-- Current core WellFormed/profile ALONE do not establish the graph's distinct
field invariant. This actual producer rejects the duplicate; no premise is
weakened and this is not labelled an approved-profile exclusion. -/
theorem duplicate_rejected : scalarStruct (decl "P8Record" first duplicateRest) rfl .storage = none := rfl

def arrayField : Source.Syn .structMember := .structMember (.array (.elem .bool) .none) "children"

theorem array_core_wellFormed : Source.WellFormed (resolution "P8Array" arrayField .nil) :=
  core_wellFormed _ _ _ rfl

theorem array_profile : Source.InProfileSyntax (resolution "P8Array" arrayField .nil) := rfl

/-- A legal-shaped reference field is an OPEN producer case, NOT a source
profile refusal or evidence of complete admission. -/
theorem array_still_open : scalarStruct (decl "P8Array" arrayField .nil) rfl .storage = none := rfl

#print axioms schema_from_core_source
#print axioms duplicate_core_wellFormed
#print axioms duplicate_rejected
#print axioms array_still_open
end Solidity.Lowering.P8.ScalarControls
