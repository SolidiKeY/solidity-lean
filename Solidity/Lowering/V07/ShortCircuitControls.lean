import Solidity.Lowering.V07.ShortCircuit
import Solidity.Lowering.V07.P12Controls

namespace Solidity.Lowering.V07.ShortCircuitControls
open Source.SemanticsExamples
open P12Controls (C E SrcCtx TgtCtx source target mapping BindingRel)

def sourceBoth (v : Bool) : Source.EMState E SrcCtx :=
  ((source.1.set .here (.bool v)).set (.there .here) (.bool v),source.2)
def targetBoth (v : Bool) : State C TgtCtx :=
  (target.setLocal .here v).setLocal (.there .here) v

theorem and_take (p : Roadmap.Pipeline) (fuel : Nat) (checked : Bool) :
    (Source.evalE (MixedAssignmentControls.globals p) {F0 with checked := checked} (fuel+3)
      (.binary .and (.assign (.local .here) (.local (.there .here)))
        (.assign (.local (.there .here)) (.local .here)))).run source =
      (.ok (.val (.bool true)),sourceBoth true) ∧
    (shortAssignOperand true .here (.there .here) (.there .here) .here).run target =
      .ok (⟨targetBoth true,List.prefix_refl _⟩,.prim true) ∧
    mapping.Related BindingRel (sourceBoth true).1 (targetBoth true).env := by
  have h := short_assignment_transport (MixedAssignmentControls.globals p)
    {F0 with checked := checked} fuel source target mapping BindingRel P12Controls.initial
    P12Controls.bool_reflect true .here (.there .here) (.there .here) .here
    .here (.there .here) (.there .here) .here rfl rfl rfl rfl
  exact ⟨h.1,h.2.1,h.2.2.1⟩

theorem or_take (p : Roadmap.Pipeline) (fuel : Nat) (checked : Bool) :
    (Source.evalE (MixedAssignmentControls.globals p) {F0 with checked := checked} (fuel+3)
      (.binary .or (.assign (.local (.there .here)) (.local .here))
        (.assign (.local .here) (.local (.there .here))))).run source =
      (.ok (.val (.bool false)),sourceBoth false) ∧
    (shortAssignOperand false (.there .here) .here .here (.there .here)).run target =
      .ok (⟨targetBoth false,List.prefix_refl _⟩,.prim false) ∧
    mapping.Related BindingRel (sourceBoth false).1 (targetBoth false).env := by
  have h := short_assignment_transport (MixedAssignmentControls.globals p)
    {F0 with checked := checked} fuel source target mapping BindingRel P12Controls.initial
    P12Controls.bool_reflect false (.there .here) .here .here (.there .here)
    (.there .here) .here .here (.there .here) rfl rfl rfl rfl
  exact ⟨h.1,h.2.1,h.2.2.1⟩

theorem and_skip (p : Roadmap.Pipeline) (fuel : Nat) (checked : Bool) :
    (Source.evalE (MixedAssignmentControls.globals p) {F0 with checked := checked} (fuel+3)
      (.binary .and (.assign (.local .here) (.local .here))
        (.assign (.local (.there .here)) (.local .here)))).run source =
      (.ok (.val (.bool false)),source) ∧
    (shortAssignOperand true .here .here (.there .here) .here).run target =
      .ok (⟨target,List.prefix_refl _⟩,.prim false) := by
  have h := short_assignment_transport (MixedAssignmentControls.globals p)
    {F0 with checked := checked} fuel source target mapping BindingRel P12Controls.initial
    P12Controls.bool_reflect true .here .here (.there .here) .here
    .here .here (.there .here) .here rfl rfl rfl rfl
  exact ⟨h.1,h.2.1⟩

theorem or_skip (p : Roadmap.Pipeline) (fuel : Nat) (checked : Bool) :
    (Source.evalE (MixedAssignmentControls.globals p) {F0 with checked := checked} (fuel+3)
      (.binary .or (.assign (.local (.there .here)) (.local (.there .here)))
        (.assign (.local .here) (.local (.there .here))))).run source =
      (.ok (.val (.bool true)),source) ∧
    (shortAssignOperand false (.there .here) (.there .here) .here (.there .here)).run target =
      .ok (⟨target,List.prefix_refl _⟩,.prim true) := by
  have h := short_assignment_transport (MixedAssignmentControls.globals p)
    {F0 with checked := checked} fuel source target mapping BindingRel P12Controls.initial
    P12Controls.bool_reflect false (.there .here) (.there .here) .here (.there .here)
    (.there .here) (.there .here) .here (.there .here) rfl rfl rfl rfl
  exact ⟨h.1,h.2.1⟩

theorem reached_right_is_not_initial :
    TEnv.get .here target.env = false ∧ TEnv.get (.there .here) target.env = true ∧
    TEnv.get .here (targetBoth true).env = true ∧
    TEnv.get (.there .here) (targetBoth false).env = false := ⟨rfl,rfl,rfl,rfl⟩

def eagerTarget : State C TgtCtx := target.setLocal (.there .here) false

theorem eager_right_run :
    (Prog.cons (.assignLocal (.there .here) (.simple (.local .here))) .nil).run target =
      .ok (⟨eagerTarget,List.prefix_refl _⟩) := rfl

theorem eager_right_wrong :
    TEnv.get (.there .here) eagerTarget.env ≠ TEnv.get (.there .here) target.env := by decide

theorem mixed_frames (v : Bool) :
    (sourceBoth v).2 = source.2 ∧
    (sourceBoth v).1.get (.there (.there (.there (.there .here)))) = .memRef rfl 0 ∧
    (sourceBoth v).1.get (.there (.there (.there (.there (.there .here))))) =
      .storRef rfl MixedAssignmentControls.path ∧
    TEnv.get (.there (.there (.there (.there .here)))) (targetBoth v).env = some P12Controls.memoryRef ∧
    (targetBoth v).heap.len P12Controls.memoryRef .dyn = 2 ∧
    TEnv.get (.there (.there (.there (.there (.there .here))))) (targetBoth v).env =
      some MixedAssignmentControls.storageRef ∧ (targetBoth v).glob = target.glob :=
  ⟨rfl,rfl,rfl,rfl,P12Controls.live_memory_and_storage.2.1,rfl,rfl⟩

def failure : Source.RExpr E SrcCtx .bool :=
  .compare .eq
    (.binary .div (.local (.there (.there .here)))
      (.conv (.const (Source.Q.ofInt 0)) (.inl (by decide))))
    (.local (.there (.there .here)))

theorem rhs_actually_fails (p : Roadmap.Pipeline) (checked : Bool) :
    revertOf ((Source.evalE (MixedAssignmentControls.globals p) {F0 with checked := checked} 10 failure).run source) =
      some (Source.panicData .divZero) := by
  cases p <;> cases checked <;> decide

theorem failing_rhs_skipped (p : Roadmap.Pipeline) (fuel : Nat) (checked : Bool) :
    (Source.evalE (MixedAssignmentControls.globals p) {F0 with checked := checked} (fuel+3)
      (.binary .and (.assign (.local .here) (.local .here)) failure)).run source =
      (.ok (.val (.bool false)),source) :=
  source_short_skip (MixedAssignmentControls.globals p) {F0 with checked := checked}
    fuel source true .here .here false failure rfl rfl

theorem failing_rhs_forced (p : Roadmap.Pipeline) (checked : Bool) :
    revertOf ((Source.evalE (MixedAssignmentControls.globals p) {F0 with checked := checked} 12
      (.binary .or (.assign (.local .here) (.local .here)) failure)).run source) =
      some (Source.panicData .divZero) := by
  cases p <;> cases checked <;> decide

theorem fresh_capture_position :
    (Idx.here : Idx (.val .bool :: TgtCtx) (.val .bool)).toNat ≠
      (Idx.there (.here : Idx TgtCtx (.val .bool)) : Idx (.val .bool :: TgtCtx) (.val .bool)).toNat := by decide

theorem fresh_boolean_context :
    ((shortAssignOperand true (.here : Idx TgtCtx (.val .bool)) (.there .here) (.there .here) .here).wk
      (Thin.drop (t := .val .bool) .refl)).run
        (target.lift (Thin.drop (t := .val .bool) .refl) (false,target.env)) =
      liftedT₂ (Thin.drop (t := .val .bool) .refl) (false,target.env)
        (.ok ((⟨targetBoth true,List.prefix_refl _⟩ : Out C target.H TgtCtx),(SVal.prim (p := .bool) true : SVal (.prim .bool)))) :=
  short_assign_extension target true .here (.there .here) (.there .here) .here
    (Thin.drop (t := .val .bool) .refl) (false,target.env)

def sameSource (v : Bool) : Source.Idx SrcCtx .bool := if v then .there .here else .here
def sameTarget (v : Bool) : Idx TgtCtx (.val .bool) := if v then .there .here else .here

theorem same_mapped (v : Bool) : mapping.slot (sameSource v) = ⟨.val .bool,sameTarget v⟩ := by
  cases v <;> rfl

theorem all_roles_equal (p : Roadmap.Pipeline) (fuel : Nat) (checked conj v : Bool) :
    (Source.evalE (MixedAssignmentControls.globals p) {F0 with checked := checked} (fuel+3)
      (.binary (if conj then .and else .or)
        (.assign (.local (sameSource v)) (.local (sameSource v)))
        (.assign (.local (sameSource v)) (.local (sameSource v))))).run source =
      (.ok (.val (.bool v)),source) ∧
    (shortAssignOperand conj (sameTarget v) (sameTarget v) (sameTarget v) (sameTarget v)).run target =
      .ok (⟨target,List.prefix_refl _⟩,.prim v) := by
  have h := short_assignment_transport (MixedAssignmentControls.globals p)
    {F0 with checked := checked} fuel source target mapping BindingRel P12Controls.initial
    P12Controls.bool_reflect conj (sameSource v) (sameSource v) (sameSource v) (sameSource v)
    (sameTarget v) (sameTarget v) (sameTarget v) (sameTarget v)
    (same_mapped v) (same_mapped v) (same_mapped v) (same_mapped v)
  cases conj <;> cases v <;> exact ⟨h.1,h.2.1⟩

/-- Target-only failure-kind control; no Source panic payload equivalence. -/
def failingBranch : Prog C (.val .bool :: TgtCtx) (.val .bool :: TgtCtx) := .cons .revert .nil

theorem target_failure_skipped :
    (Stmt.ite (.simple (.local .here)) failingBranch
      (Prog.nil : Prog C (.val .bool :: TgtCtx) (.val .bool :: TgtCtx))).run
      (target.push (t := .val .bool) false) =
      .ok (⟨target.push (t := .val .bool) false,List.prefix_refl _⟩) := rfl

theorem target_failure_forced :
    (Stmt.ite (.simple (.local .here)) failingBranch
      (Prog.nil : Prog C (.val .bool :: TgtCtx) (.val .bool :: TgtCtx))).run
      (target.push (t := .val .bool) true) = .error .revert := rfl

end Solidity.Lowering.V07.ShortCircuitControls
