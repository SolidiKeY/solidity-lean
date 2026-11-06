import Solidity.Lowering.V07.IntegerAssignmentPrefixes
import Solidity.Lowering.V07.ReadControls

namespace Solidity.Lowering.V07.AssignmentControls
open Source.SemanticsExamples

def expression : Source.RExpr E0 [.int .u8,.int .u8] (.int .u8) :=
  .binary .sub (.assign (.local (.there .here)) (.local .here)) (.local (.there .here))
def postSource : Source.EMState E0 [.int .u8,.int .u8] :=
  (ReadControls.source.1.set (.there .here) (.int 7 (by decide)),ReadControls.source.2)
def postTarget : State (default : Contract) [.val .uint,.val .uint] :=
  ReadControls.target.setLocal (.there .here) (integerValue .u8 7 (by decide))

theorem legacy_pair (fuel : Nat) (checked : Bool) :
    (Source.evalPair (G0 .legacy) {F0 with checked := checked} (fuel+3)
      (.assign (.local (.there .here)) (.local .here)) (.local (.there .here))).run ReadControls.source =
      (.ok (.val (.int 7 (by decide)),.val (.int 3 (by decide))),postSource) :=
  source_assign_read_pair _ _ fuel _ _ _ _ _ rfl rfl

theorem viaIR_pair (fuel : Nat) (checked : Bool) :
    (Source.evalPair (G0 .viaIR) {F0 with checked := checked} (fuel+3)
      (.assign (.local (.there .here)) (.local .here)) (.local (.there .here))).run ReadControls.source =
      (.ok (.val (.int 7 (by decide)),.val (.int 7 (by decide))),postSource) :=
  source_assign_read_pair _ _ fuel _ _ _ _ _ rfl rfl

theorem legacy_source (fuel : Nat) (checked : Bool) :
    (Source.evalE (G0 .legacy) {F0 with checked := checked} (fuel+4) expression).run ReadControls.source =
      (.ok (.val (.int 4 (by decide))),postSource) :=
  source_assign_sub_run _ _ fuel _ .u8 (.there .here) .here 7 3 (by decide) (by decide) rfl rfl (by decide)

theorem viaIR_source (fuel : Nat) (checked : Bool) :
    (Source.evalE (G0 .viaIR) {F0 with checked := checked} (fuel+4) expression).run ReadControls.source =
      (.ok (.val (.int 0 (by decide))),postSource) :=
  source_assign_sub_run _ _ fuel _ .u8 (.there .here) .here 7 3 (by decide) (by decide) rfl rfl (by decide)

theorem legacy_prefix :
    (assignReadPrefix .legacy (.there .here) .here).run ReadControls.target =
      .ok (⟨(postTarget.push (integerValue .u8 3 (by decide))).push (integerValue .u8 7 (by decide)),
        List.prefix_refl _⟩) := assign_read_prefix_run _ _ _ _ _ _ rfl rfl

theorem viaIR_prefix :
    (assignReadPrefix .viaIR (.there .here) .here).run ReadControls.target =
      .ok (⟨(postTarget.push (integerValue .u8 7 (by decide))).push (integerValue .u8 7 (by decide)),
        List.prefix_refl _⟩) := assign_read_prefix_run _ _ _ _ _ _ rfl rfl

theorem legacy_target :
    (assignReadSubOperand .legacy .u8 (.there .here) .here).run ReadControls.target =
      .ok (⟨postTarget,List.prefix_refl _⟩,.prim (integerValue .u8 4 (by decide))) :=
  assign_read_sub_operand_run _ _ _ _ _ 7 3 (by decide) (by decide) rfl rfl (by decide)

theorem viaIR_target :
    (assignReadSubOperand .viaIR .u8 (.there .here) .here).run ReadControls.target =
      .ok (⟨postTarget,List.prefix_refl _⟩,.prim (integerValue .u8 0 (by decide))) :=
  assign_read_sub_operand_run _ _ _ _ _ 7 3 (by decide) (by decide) rfl rfl (by decide)

theorem assigned_local_both :
    postSource.1.get (.there .here) = .int 7 (by decide) ∧
    TEnv.get (.there .here) postTarget.env = integerValue .u8 7 (by decide) := ⟨rfl,rfl⟩

theorem stale_initial_state_rejected (fuel : Nat) (checked : Bool) :
    intOf ((Source.evalE (G0 .viaIR) {F0 with checked := checked} (fuel+4) expression).run
      ReadControls.source) ≠ some 4 := by
  rw [viaIR_source]
  decide

theorem wrong_operand_order :
    BinOp.evalT .sub (p := .uint) rfl
      (integerValue .u8 3 (by decide)) (integerValue .u8 7 (by decide)) = none := by decide

def uncaptured : DeferredSource.Operand (default : Contract) [.val .uint,.val .uint] (.prim .uint) :=
  ⟨[.val .uint,.val .uint],.cons (.assignLocal (.there .here) (.simple (.local .here))) .nil,
    .val (.binop .sub rfl rfl (.simple (.local .here)) (.simple (.local (.there .here))))⟩

theorem uncaptured_run : uncaptured.run ReadControls.target =
    .ok (⟨postTarget,List.prefix_refl _⟩,.prim (integerValue .u8 0 (by decide))) := by
  have before : uncaptured.code.run ReadControls.target =
      .ok (⟨postTarget,List.prefix_refl _⟩) := rfl
  have value := intrinsic_sub_run postTarget .u8 (.simple (.local .here))
    (.simple (.local (.there .here))) 7 7 (by decide) (by decide) (by decide) rfl rfl
  unfold DeferredSource.Operand.run
  rw [before]
  change (do
    let v ← (Src.val (.binop .sub rfl rfl (.simple (.local .here))
      (.simple (.local (.there .here)))) : Src (default : Contract) [.val .uint,.val .uint] (.prim .uint)).valueT postTarget
    pure ((⟨postTarget,List.prefix_refl _⟩ : Out (default : Contract) ReadControls.target.H [.val .uint,.val .uint]),v)) = _
  simp only [Src.valueT,value]
  rfl

/-- Only a test observation of the actual run; the main theorems above retain
full states. This is not a replacement Source/target evaluator or value type. -/
def observed {C : Contract} {H : HTy} {Γ : Ctx} {p : PrimTy}
    (result : TRes (Out C H Γ × SVal (.prim p))) : Option Int :=
  match result with
  | .ok (_, .prim v) => PrimTy.num? v
  | .error _ => none

theorem uncaptured_read_rejected :
    observed (uncaptured.run ReadControls.target) ≠
      observed ((assignReadSubOperand .legacy .u8 (.there .here) .here).run ReadControls.target) := by
  rw [uncaptured_run,legacy_target]
  decide

theorem dropped_temporaries_read_wrong_value :
    (Val.binop .sub (p := .uint) rfl rfl (.simple (.local .here))
      (.simple (.local (.there .here)))).evalT
      (((postTarget.push (t := .val .uint) (integerValue .u8 3 (by decide))).push (t := .val .uint)
        (integerValue .u8 7 (by decide))).drop (.push (.push .refl))) =
      .ok (integerValue .u8 0 (by decide)) :=
  intrinsic_sub_run postTarget .u8 _ _ 7 7 (by decide) (by decide) (by decide) rfl rfl

theorem same_index_source (p : Roadmap.Pipeline) (fuel : Nat) (checked : Bool) :
    (Source.evalE (G0 p) {F0 with checked := checked} (fuel+4)
      (.binary .sub (.assign (.local .here) (.local .here)) (.local .here))).run ReadControls.source =
      (.ok (.val (.int 0 (by decide))),ReadControls.source) := by
  have h := source_assign_sub_run (G0 p) {F0 with checked := checked} fuel ReadControls.source
    .u8 .here .here 7 7 (by decide) (by decide) rfl rfl
    (by simp only [ite_self,Int.sub_self]; decide)
  simpa only [ite_self,Int.sub_self] using h

theorem same_index_target (p : Roadmap.Pipeline) :
    (assignReadSubOperand p .u8 .here .here).run ReadControls.target =
      .ok (⟨ReadControls.target,List.prefix_refl _⟩,.prim (integerValue .u8 0 (by decide))) := by
  have h := assign_read_sub_operand_run p ReadControls.target .u8 .here .here 7 7
    (by decide) (by decide) rfl rfl (by simp only [ite_self,Int.sub_self]; decide)
  simpa only [ite_self,Int.sub_self] using h

/-- Concrete gap in the old pure-pair adapter: this actual operand changes
its caller locals, so its whole-state purity premise cannot be supplied. -/
theorem assignment_changes_state (p : Roadmap.Pipeline) (fuel : Nat) :
    ((Source.evalE (G0 p) F0 (fuel+2)
      (.assign (.local (.there .here)) (.local .here))).run ReadControls.source).2 ≠ ReadControls.source := by
  rw [source_assign_local_run (G0 p) F0 fuel ReadControls.source (.there .here) .here
    (.int 7 (by decide)) rfl]
  intro same
  have observed := congrArg (fun state : Source.EMState E0 [.int .u8,.int .u8] =>
    (state.1.get (.there .here)).key) same
  change some (7 : Int) = some 3 at observed
  cases observed

end Solidity.Lowering.V07.AssignmentControls
