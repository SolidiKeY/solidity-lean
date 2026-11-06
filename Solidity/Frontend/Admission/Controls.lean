import Solidity.Frontend.Admission.Profile
import Solidity.Frontend.Admission.RootObservations
import Solidity.Source.FailureResources

/-! # Inhabited admission-extraction and failure-resource controls
These kernel controls exercise actual resolved syntax and the published policy.
They do not run the solc importer or claim a failure-aware source semantics.
-/
namespace Solidity.Frontend.Admission.Controls
open Solidity.Source
open Solidity.Language
open Solidity.Frontend.Source
open Solidity.Source.FailureResources

private def env : Env := ⟨[]⟩
private def timestamp : RExpr env [] (.int IntTy.u256) := .magic .block "timestamp" rfl
private def self : RExpr env [] (.contract ⟨none, "C"⟩) := .this "C"

/-- Two inhabited roots retain both different observations in order. -/
theorem two_roots : rootObservations [⟨[], _, timestamp⟩, ⟨[], _, self⟩] =
    [.magic .block "timestamp", .builtin .this] := rfl

theorem two_roots_admitted :
    (rootObservations [⟨[], _, timestamp⟩, ⟨[], _, self⟩]).all ObservationSite.allowed = true := by
  decide

/-- A resolved local is positional; its former spelling cannot create a builtin. -/
theorem shadowed_local : observations (RExpr.local (E := env) (Γ := [.int IntTy.u256]) .here) = [] := rfl

/-- Untaken branches are still inspected structurally. -/
theorem branch_observation : stmtObservations
    (RStmt.ifElse (E := env) (R := []) (M := false) (k := .body)
      (.bool false) .skip (.expr timestamp)) = [.magic .block "timestamp"] := rfl

/-- Post expressions, not only loop bodies and tests, are roots. -/
theorem loop_post_observation : stmtObservations
    (RStmt.forLoop (E := env) (R := []) (M := false) (l := false) (u := false)
      .skip .none (.some timestamp) .skip) = [.magic .block "timestamp"] := rfl

/-- S01 refuses an excluded magic member before resolved expressions exist. -/
theorem block_number_has_no_resolved_type : Builtin.block.memberTy "number" = none := rfl

/-- Raw metadata for an excluded observation cannot pass local classification. -/
theorem block_number_refused : (ObservationSite.magic .block "number").allowed = false := by decide

theorem unknown_member_refused : (ObservationSite.magic .msg "notAMember").allowed = false := rfl

theorem excluded_after_allowed : (ScopeScan.certify [⟨.msgSender, 1⟩, ⟨.delegatecall, 2⟩,
    ⟨.blockTimestamp, 3⟩]).features = [.msgSender, .delegatecall, .blockTimestamp] :=
  ScopeScan.certify_features _

theorem mixed_group_refused : (ScopeScan.certify [⟨.msgSender, 1⟩, ⟨.delegatecall, 2⟩]).diagnostic? ≠ none := by
  apply (ScopeScan.certify_rejected_iff _).mpr
  refine ⟨⟨.delegatecall, 2⟩, List.mem_cons_of_mem _ (List.mem_cons_self ..), ?_⟩
  change ¬ (Feature.delegatecall.scope = .model ∨ Feature.delegatecall.scope = .abstract)
  decide

private def dropped : Roadmap.Evm.FailurePoints := {
  tx := fun _ => .dropped, frame := fun _ => none }
private def frameZero : Roadmap.Evm.FailurePoints := {
  tx := fun _ => .runs 7 none, frame := fun _ => some 0 }

theorem failure_free_inhabited : NoFail (noFailures (fun i => i + 7)) := noFailures_noFail _
theorem dropped_refused : ¬ NoFail dropped := dropped_not_noFail (i := 123) rfl
theorem frame_zero_refused : ¬ NoFail frameZero := frame_not_noFail (k := 73) rfl

/-- Replacing choices changes the schedule and preserves the actual horizon. -/
theorem replacement : (Bound.withFailures ⟨19, dropped⟩ frameZero).points = frameZero ∧
    (Bound.withFailures ⟨19, dropped⟩ frameZero).horizon = 19 := ⟨rfl, rfl⟩

/-- The wrong-observation expectation is refuted in the kernel. -/
theorem wrong_roots_refuted : rootObservations [⟨[], _, timestamp⟩, ⟨[], _, self⟩] ≠
    [.magic .block "timestamp"] := by
  intro h
  change [_ , _] = [_] at h
  cases h

end Solidity.Frontend.Admission.Controls

/-- info: 'Solidity.Frontend.Source.ScopeScan.certify_iff' depends on axioms: [propext] -/
#guard_msgs in #print axioms Solidity.Frontend.Source.ScopeScan.certify_iff
/-- info: 'Solidity.Frontend.Source.ScopeScan.certify_rejected_iff' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Solidity.Frontend.Source.ScopeScan.certify_rejected_iff
/-- info: 'Solidity.Frontend.Admission.accepted_roots' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Solidity.Frontend.Admission.accepted_roots
/-- info: 'Solidity.Frontend.Admission.ObservationSite.allowed_iff' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms Solidity.Frontend.Admission.ObservationSite.allowed_iff
/-- info: 'Solidity.Source.FailureResources.noFail_iff' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Solidity.Source.FailureResources.noFail_iff
/-- info: 'Solidity.Frontend.Admission.Controls.two_roots_admitted' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Solidity.Frontend.Admission.Controls.two_roots_admitted
/-- info: 'Solidity.Frontend.Admission.Controls.wrong_roots_refuted' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Solidity.Frontend.Admission.Controls.wrong_roots_refuted

/-- info: 'Solidity.Source.FailureResources.no_horizon_retraction' does not depend on any axioms -/
#guard_msgs in #print axioms Solidity.Source.FailureResources.no_horizon_retraction
