import Solidity.Lowering.V07.DoubleControls
import Solidity.Lowering.V07.AssignmentBoundaries

namespace Solidity.Lowering.V07.DoubleNegativeControls
open Source.SemanticsExamples
abbrev SrcCtx : Source.RCtx := [.int .u8,.int .u8]
abbrev TgtCtx : Ctx := [.val .uint,.val .uint]
def si : Bool → Source.Idx SrcCtx (.int .u8) | true => .here | false => .there .here
def ti : Bool → Idx TgtCtx (.val .uint) | true => .here | false => .there .here

theorem initial : IntegerLocalFamily .u8 si ti ReadControls.source.1 ReadControls.target.env := by
  constructor
  · intro k; cases k <;> rfl
  · intro k l; cases k <;> cases l <;> decide

def aliasExpression : Source.RExpr E0 SrcCtx (.int .u8) :=
  .binary .sub (.assign (.local .here) (.local .here))
    (.assign (.local .here) (.local (.there .here)))
def aliasSourcePost : Source.EMState E0 SrcCtx :=
  (ReadControls.source.1.set .here (.int 3 (by decide)),ReadControls.source.2)
def aliasTargetPost : State (default : Contract) TgtCtx :=
  ReadControls.target.setLocal .here (integerValue .u8 3 (by decide))

theorem aliased_destinations (p : Roadmap.Pipeline) (fuel : Nat) (checked : Bool) :
    (Source.evalE (G0 p) {F0 with checked := checked} (fuel+4) aliasExpression).run ReadControls.source =
      (.ok (.val (.int (doubleDelta p 7 3) (DoubleControls.delta_range p))),aliasSourcePost) ∧
    (assignAssignSubOperand p .u8 .here .here (.there .here)).run ReadControls.target =
      .ok (⟨aliasTargetPost,List.prefix_refl _⟩,
        .prim (integerValue .u8 (doubleDelta p 7 3) (DoubleControls.delta_range p))) := by
  have h := double_assignment_transport .u8 si ti (G0 p) {F0 with checked := checked}
    fuel ReadControls.source ReadControls.target initial true true false 7 3 (by decide) (by decide)
    rfl rfl (by decide) (DoubleControls.delta_range p)
  cases p <;> exact ⟨h.1,h.2.1⟩

/-- Deliberately wrong: read the caller's overwritten cells after both
assignments instead of reading the left/right values captured earlier. -/
def uncaptured : DeferredSource.Operand (default : Contract) TgtCtx (.prim .uint) :=
  ⟨.val .uint :: .val .uint :: TgtCtx,assignAssignPrefix .viaIR .here .here (.there .here),
    .val (.binop .sub rfl rfl (.simple (.local (.there (.there .here))))
      (.simple (.local (.there (.there (.there .here))))))⟩

theorem uncaptured_run : uncaptured.run ReadControls.target =
    .ok (⟨aliasTargetPost,List.prefix_refl _⟩,.prim (integerValue .u8 0 (by decide))) := by
  let reached : State (default : Contract) (.val .uint :: .val .uint :: TgtCtx) :=
    (aliasTargetPost.push (integerValue .u8 7 (by decide))).push (integerValue .u8 3 (by decide))
  have value := intrinsic_sub_run reached .u8 (.simple (.local (.there (.there .here))))
    (.simple (.local (.there (.there (.there .here))))) 3 3 (by decide) (by decide) (by decide) rfl rfl
  unfold uncaptured DeferredSource.Operand.run
  rw [assign_assign_prefix_run .viaIR ReadControls.target .here .here (.there .here)
    (integerValue .u8 7 (by decide)) (integerValue .u8 3 (by decide)) rfl rfl (by decide)]
  change (do
    let v ← (Src.val (.binop .sub rfl rfl (.simple (.local (.there (.there .here))))
      (.simple (.local (.there (.there (.there .here)))))) :
      Src (default : Contract) (.val .uint :: .val .uint :: TgtCtx) (.prim .uint)).valueT reached
    pure ((⟨aliasTargetPost,List.prefix_refl _⟩ : Out (default : Contract) ReadControls.target.H TgtCtx),v)) = _
  simp only [Src.valueT,value]
  rfl

theorem uncaptured_read_rejected :
    AssignmentControls.observed (uncaptured.run ReadControls.target) ≠
      AssignmentControls.observed ((assignAssignSubOperand .viaIR .u8 .here .here (.there .here)).run ReadControls.target) := by
  rw [uncaptured_run,(aliased_destinations .viaIR 0 true).2]
  decide

theorem reversed_semantic_operands_rejected :
    BinOp.evalT .sub (p := .uint) rfl (integerValue .u8 3 (by decide)) (integerValue .u8 7 (by decide)) = none ∧
    AssignmentControls.observed ((assignAssignSubOperand .viaIR .u8 .here .here (.there .here)).run ReadControls.target) = some 4 := by
  refine ⟨AssignmentControls.wrong_operand_order,?_⟩
  rw [(aliased_destinations .viaIR 0 true).2]
  rfl

/-- The first destination aliases the second RHS: viaIR must read REACHED7,
not INITIAL3. Thus dropping the double-transport's explicit separation
premise while keeping its initial-right formula would be false. -/
def rhsAliasExpression : Source.RExpr E0 SrcCtx (.int .u8) :=
  .binary .sub (.assign (.local (.there .here)) (.local .here))
    (.assign (.local .here) (.local (.there .here)))
def rhsAliasSourcePost : Source.EMState E0 SrcCtx :=
  ((ReadControls.source.1.set (.there .here) (.int 7 (by decide))).set .here (.int 7 (by decide)),ReadControls.source.2)

theorem rhs_alias_pair (fuel : Nat) (checked : Bool) :
    (Source.evalPair (G0 .viaIR) {F0 with checked := checked} (fuel+3)
      (.assign (.local (.there .here)) (.local .here))
      (.assign (.local .here) (.local (.there .here)))).run ReadControls.source =
        (.ok (.val (.int 7 (by decide)),.val (.int 7 (by decide))),rhsAliasSourcePost) := by
  rw [Source.evalPair]
  change ((Source.evalE (G0 .viaIR) {F0 with checked := checked} (fuel+2)
    (.assign (.local (.there .here)) (.local .here))) >>= fun x => do
      let y ← Source.evalE (G0 .viaIR) {F0 with checked := checked} (fuel+2)
        (.assign (.local .here) (.local (.there .here)))
      pure (x,y)).run ReadControls.source = _
  rw [Source.Hoare.run_bind,
    source_assign_local_run (G0 .viaIR) {F0 with checked := checked} fuel ReadControls.source
      (.there .here) .here (.int 7 (by decide)) rfl]
  dsimp only
  rw [Source.Hoare.run_bind,source_assign_local_run (G0 .viaIR) {F0 with checked := checked} fuel
    (ReadControls.source.1.set (.there .here) (.int 7 (by decide)),ReadControls.source.2)
    .here (.there .here) (.int 7 (by decide)) (source_locals_get_set _ _ _)]
  rfl

theorem rhs_alias_actual_source (fuel : Nat) (checked : Bool) :
    (Source.evalE (G0 .viaIR) {F0 with checked := checked} (fuel+4) rhsAliasExpression).run ReadControls.source =
      (.ok (.val (.int 0 (by decide))),rhsAliasSourcePost) :=
  source_sub_of_pair (G0 .viaIR) {F0 with checked := checked} (fuel+3) ReadControls.source
    rhsAliasSourcePost .u8 _ _ 7 7 (by decide) (by decide) (by decide) (rhs_alias_pair fuel checked)

theorem rhs_alias_initial_formula_false (fuel : Nat) (checked : Bool) :
    (Source.evalE (G0 .viaIR) {F0 with checked := checked} (fuel+4) rhsAliasExpression).run ReadControls.source ≠
      (.ok (.val (.int (doubleDelta .viaIR 7 3) (DoubleControls.delta_range .viaIR))),rhsAliasSourcePost) := by
  rw [rhs_alias_actual_source]
  intro same
  have eq := congrArg Prod.fst same
  cases eq

abbrev SignedSrcCtx : Source.RCtx := [.int Controls.i8,.int Controls.i8]
abbrev SignedTgtCtx : Ctx := [.val .int,.val .int]
def signedSi : Bool → Source.Idx SignedSrcCtx (.int Controls.i8) | true => .here | false => .there .here
def signedTi : Bool → Idx SignedTgtCtx (.val .int) | true => .here | false => .there .here

theorem signed_initial : IntegerLocalFamily Controls.i8 signedSi signedTi
    AssignmentBoundaries.signedSource.1 AssignmentBoundaries.signedTarget.env := by
  constructor
  · intro k; cases k <;> rfl
  · intro k l; cases k <;> cases l <;> decide

theorem signed_range (p : Roadmap.Pipeline) :
    Controls.i8.lo ≤ doubleDelta p (-2) 3 ∧ doubleDelta p (-2) 3 ≤ Controls.i8.hi := by
  cases p <;> decide

theorem signed_actual (p : Roadmap.Pipeline) (fuel : Nat) (checked : Bool) :
    (Source.evalE (G0 p) {F0 with checked := checked} (fuel+4)
      (.binary .sub (.assign (.local .here) (.local .here))
        (.assign (.local .here) (.local (.there .here))))).run AssignmentBoundaries.signedSource =
      (.ok (.val (.int (doubleDelta p (-2) 3) (signed_range p))),
        (AssignmentBoundaries.signedSource.1.set .here (.int 3 (by decide)),AssignmentBoundaries.signedSource.2)) ∧
    (assignAssignSubOperand p Controls.i8 .here .here (.there .here)).run AssignmentBoundaries.signedTarget =
      .ok (⟨AssignmentBoundaries.signedTarget.setLocal .here (integerValue Controls.i8 3 (by decide)),List.prefix_refl _⟩,
        .prim (integerValue Controls.i8 (doubleDelta p (-2) 3) (signed_range p))) := by
  have h := double_assignment_transport Controls.i8 signedSi signedTi (G0 p) {F0 with checked := checked}
    fuel AssignmentBoundaries.signedSource AssignmentBoundaries.signedTarget signed_initial true true false
    (-2) 3 (by decide) (by decide) rfl rfl (by decide) (signed_range p)
  cases p <;> exact ⟨h.1,h.2.1⟩

end Solidity.Lowering.V07.DoubleNegativeControls
