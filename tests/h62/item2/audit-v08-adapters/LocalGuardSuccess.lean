import Solidity.Backend.FailurePaths.LocalGuardSelectionControls

/-! Supported dynamic local-require success, exact failure, joint premises and
trivial compiler refutations. Guards the regression where selected execution
ignores the runtime Boolean input. This instruction interpreter has no charged gas
or fork parameter; no gas/fork adequacy is asserted by this module. -/
namespace H62.AuditV08Adapters.LocalGuardSuccess
open Solidity Solidity.Backend Solidity.Backend.FailurePaths
open Evm Evm.Memory

abbrev Input := Source.RStmt PrimitivePackets.Comparisons.Controls.E [] false .body [.bool] [.bool]
abbrev Candidate := Input → Option (List Evm.Instr)

def actual : Candidate := LocalGuardSelection.compile
  (C:=PrimitivePackets.Comparisons.Controls.C) LocalGuardSelection.Controls.map
  0 RuntimeGuard.Controls.fragment

/-- Both outcomes are mandatory, and the successful outcome retains the
whole populated machine. The supported Source statement reads its input local. -/
def Contract (compiler : Candidate) : Prop :=
  ∀ value : Bool, ∃ code : List Evm.Instr,
    compiler LocalGuardSelection.Controls.input = some code ∧
    run code (RuntimeGuard.Controls.machine value) =
      (if value then .ok (RuntimeGuard.Controls.machine value) 0 else .revert)

theorem actual_contract : Contract actual := by
  intro value
  exact ⟨LocalGuardSelection.Controls.code,LocalGuardSelection.Controls.selected,
    (LocalGuardSelection.Controls.observations .legacy value).2.2.2⟩

/-- Deterministic selection makes independently quantified runtime cases
share one selected witness. An explicit index rules out the empty-domain case. -/
theorem option_selection_joint {α β : Type} (selected : Option α)
    (relation : β → α → Prop) (index : β) :
    (∀ value, ∃ code, selected = some code ∧ relation value code) ↔
      ∃ code, selected = some code ∧ ∀ value, relation value code :=
  ⟨fun cases => (cases index).elim fun code chosen =>
      ⟨code, chosen.1, fun value => (cases value).elim fun _other related =>
        (Option.some.inj (chosen.1.symm.trans related.1)).symm ▸ related.2⟩,
    fun joint value => joint.elim fun code chosen => ⟨code, chosen.1, chosen.2 value⟩⟩

/-- One selected program satisfies ALL original runtime cases together;
this is equivalent to Contract, with unchanged full-machine outcomes. -/
theorem contract_joint_iff (compiler : Candidate) :
    Contract compiler ↔ ∃ code,
      compiler LocalGuardSelection.Controls.input = some code ∧
      ∀ value : Bool, run code (RuntimeGuard.Controls.machine value) =
        (if value then .ok (RuntimeGuard.Controls.machine value) 0 else .revert) :=
  option_selection_joint _ _ true

theorem actual_joint : ∃ code,
    actual LocalGuardSelection.Controls.input = some code ∧
    ∀ value : Bool, run code (RuntimeGuard.Controls.machine value) =
      (if value then .ok (RuntimeGuard.Controls.machine value) 0 else .revert) :=
  (contract_joint_iff actual).mp actual_contract

def rejectAll : Candidate := fun _ => none
def alwaysRevert : Candidate := fun _ => some [.revert]

theorem rejectAll_not_contract : ¬ Contract rejectAll := by
  intro claimed
  obtain ⟨code,selected,_⟩ := claimed true
  change none = some code at selected
  cases selected

theorem alwaysRevert_not_contract : ¬ Contract alwaysRevert := by
  intro claimed
  obtain ⟨code,selected,ran⟩ := claimed true
  change some [.revert] = some code at selected
  have same : [.revert] = code := Option.some.inj selected
  rw [←same] at ran
  change Evm.Out.revert = Evm.Out.ok (RuntimeGuard.Controls.machine true) 0 at ran
  cases ran

/-- Regression guarded: a contract cannot be met by code whose observed
outcome ignores the runtime Boolean input, even when selection succeeds. -/
def InputBlind (compiler : Candidate) : Prop :=
  ∀ code, compiler LocalGuardSelection.Controls.input = some code →
    (run code (RuntimeGuard.Controls.machine true)).isRevert =
      (run code (RuntimeGuard.Controls.machine false)).isRevert

/-- Any supported compiler must select one code image with distinct runtime
outcomes. No Source-success or desired-execution hypothesis is added. -/
theorem contract_distinguishes_runtime_input (compiler : Candidate)
    (supported : Contract compiler) :
    ∃ code, compiler LocalGuardSelection.Controls.input = some code ∧
      (run code (RuntimeGuard.Controls.machine true)).isRevert ≠
        (run code (RuntimeGuard.Controls.machine false)).isRevert := by
  obtain ⟨code, selected, success⟩ := supported true
  obtain ⟨other, selectedOther, failure⟩ := supported false
  have same : code = other := Option.some.inj (selected.symm.trans selectedOther)
  subst other
  refine ⟨code, selected, ?_⟩
  intro indistinguishable
  rw [success, failure] at indistinguishable
  change false = true at indistinguishable
  cases indistinguishable

theorem inputBlind_not_contract (compiler : Candidate) (blind : InputBlind compiler) :
    ¬ Contract compiler := by
  intro supported
  obtain ⟨code, selected, distinct⟩ := contract_distinguishes_runtime_input compiler supported
  exact distinct (blind code selected)

theorem actual_not_inputBlind : ¬ InputBlind actual := by
  intro blind
  exact inputBlind_not_contract actual blind actual_contract

/-- Exact simultaneous nontrivial premises of frozen selected_correct, on
one shared value/machine/local frame. No result-execution premise is assumed. -/
theorem selected_correct_joint (value : Bool) :
    actual LocalGuardSelection.Controls.input = some LocalGuardSelection.Controls.code ∧
    (∀ (i : Source.Idx [.bool] .bool) (v : Bool),
      (RuntimeGuard.Controls.locals value).get i = .bool v →
      TEnv.get (LocalGuardSelection.Controls.map i) (RuntimeGuard.Controls.state value).env = v) ∧
    StateRepr 1 0 4 RuntimeGuard.Controls.fragment (RuntimeGuard.Controls.state value)
      PrimitivePackets.Comparisons.Controls.addresses (RuntimeGuard.Controls.machine value) :=
  ⟨LocalGuardSelection.Controls.selected,LocalGuardSelection.Controls.local_relation value,
    RuntimeGuard.Controls.represented value⟩

/-- Success and failure for both existing Source pipelines at the same populated
input fixture; this is the exact whole-machine observation already published. -/
theorem both_pipeline_runs (pipeline : Roadmap.Pipeline) (value : Bool) :
    (Source.execS (PrimitivePackets.Comparisons.Controls.global pipeline)
      PrimitivePackets.Comparisons.Controls.frame 7 0 none LocalGuardSelection.Controls.input
      (RuntimeGuard.Controls.locals value)).run
      (Source.L0 _,PrimitivePackets.Comparisons.Controls.sourceState) =
      (if value then (.ok (.normal (RuntimeGuard.Controls.locals value)),
        (Source.L0 _,PrimitivePackets.Comparisons.Controls.sourceState))
       else (.error (.revert []),(Source.L0 _,PrimitivePackets.Comparisons.Controls.sourceState))) ∧
    run LocalGuardSelection.Controls.code (RuntimeGuard.Controls.machine value) =
      (if value then .ok (RuntimeGuard.Controls.machine value) 0 else .revert) :=
  (LocalGuardSelection.Controls.observations pipeline value).2.2

/-- Whole carriers witness dependent proof fields together, including the
index. Separate field equalities would not establish these global premises. -/
theorem views_joint :
    Nonempty (LocalGuardSelection.View LocalGuardSelection.Controls.input) ∧
    Nonempty (LocalGuardSelection.BoolLocalView
      (.local .here : Source.RExpr PrimitivePackets.Comparisons.Controls.E [.bool] .bool)) := by
  constructor
  · exact ⟨⟨.here, rfl, HEq.rfl⟩⟩
  · exact ⟨⟨rfl, .here, rfl⟩⟩

/-- info: 'H62.AuditV08Adapters.LocalGuardSuccess.actual_contract' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms actual_contract
/-- info: 'H62.AuditV08Adapters.LocalGuardSuccess.rejectAll_not_contract' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms rejectAll_not_contract
/-- info: 'H62.AuditV08Adapters.LocalGuardSuccess.alwaysRevert_not_contract' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms alwaysRevert_not_contract
/-- info: 'H62.AuditV08Adapters.LocalGuardSuccess.selected_correct_joint' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms selected_correct_joint
/-- info: 'H62.AuditV08Adapters.LocalGuardSuccess.both_pipeline_runs' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms both_pipeline_runs
/-- info: 'H62.AuditV08Adapters.LocalGuardSuccess.views_joint' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms views_joint
#print axioms actual_joint
#print axioms actual_not_inputBlind
end H62.AuditV08Adapters.LocalGuardSuccess
