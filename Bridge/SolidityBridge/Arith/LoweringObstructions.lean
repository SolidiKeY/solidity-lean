import SolidityBridge.Arith.NarrowChecked
import Solidity.Syntax.Splice

/-! Current retained-failure-data guard behavior and an inhabited obstruction
to the old unrestricted Lowering.narrowCheck_guard contract. -/
namespace Solidity.Bridge.Arith.LoweringObstructions

theorem actual_guard (C : Contract) (scope : ElabScope) (st : ECtx × Nat)
    (p : PrimTy) (n : Nat) (hn : n < 256) (e : RawExpr)
    (v : Val C st.1.toNCtx.ctx .bool)
    (hc : Solidity.check C st.1.toNCtx .bool (inTyCond p n e) = .ok v) :
    narrowCheck C p n e scope st = pure
      ([.of st.1.toNCtx (match scope.overflow with
        | some o => o.guardStmt v (scope.selfFrame || scope.retainFailureData)
        | none => if scope.selfFrame || scope.retainFailureData then
            panicStmt 17 v else .require v)], st) := by
  funext memo
  have hnctx : nctx scope st = pure (st.1.toNCtx, st) := rfl
  delta narrowCheck
  rw [if_neg (not_le.mpr hn)]
  simp only [bind, ReaderT.bind, StateT.bind, hnctx, Except.bind,
    pure, ReaderT.pure, StateT.pure, Except.pure]
  simp only [checkIn, ElabM.lift, StateT.lift, hc]
  rfl

def exampleContract : Contract := contract!{}
def exampleScope : ElabScope := { funs := [], retainFailureData := true }
def exampleState : ECtx × Nat := ([("x", .val .uint 8)], 0)
def exampleGuard : Val exampleContract exampleState.1.toNCtx.ctx .bool :=
  uintGuard 8 (by decide) (.simple (.local .here))

theorem setup :
    Solidity.check exampleContract exampleState.1.toNCtx .bool
      (inTyCond .uint 8 (.name "x")) = .ok exampleGuard := by
  apply check_uint_guard _ _ 8 (by decide) rfl rfl
  · exact WidthsSyntax.synth_head .uint "x" []
  · exact Widths.check_head .uint "x" []

def isRequire {C : Contract} {Γ Γ' : Ctx} : Stmt C Γ Γ' → Bool
  | .require _ => true
  | _ => false

def observe (r : Except String ((SProg exampleContract × (ECtx × Nat)) × CallMemo)) :
    Option (List Bool) :=
  r.toOption.map fun result => result.1.1.map fun stmt => isRequire stmt.s

/-- The old RHS emits require; current retained-data setup emits a panic guard. -/
theorem retained_data_counterexample :
    narrowCheck exampleContract .uint 8 (.name "x") exampleScope exampleState {} ≠
      .ok (([.of exampleState.1.toNCtx (.require exampleGuard)], exampleState), {}) := by
  rw [actual_guard exampleContract exampleScope exampleState .uint 8 (by decide)
    (.name "x") exampleGuard setup]
  intro h
  have ho := congrArg observe h
  change some [false] = some [true] at ho
  cases ho

def OldNarrowGuard : Prop :=
  ∀ (C : Contract) (scope : ElabScope) (st : ECtx × Nat)
    (p : PrimTy) (n : Nat) (_hn : n < 256) (e : RawExpr)
    (v : Val C st.1.toNCtx.ctx .bool),
    Solidity.check C st.1.toNCtx .bool (inTyCond p n e) = .ok v →
    narrowCheck C p n e scope st = pure
      ([.of st.1.toNCtx (match scope.overflow with
        | some o => o.guardStmt v scope.selfFrame
        | none => if scope.selfFrame then panicStmt 17 v else .require v)], st)

theorem not_old_narrow_guard : ¬ OldNarrowGuard := by
  intro claim
  exact retained_data_counterexample (congrArg (fun f => f {})
    (claim exampleContract exampleScope exampleState .uint 8 (by decide)
      (.name "x") exampleGuard setup))

/-- info: 'Solidity.Bridge.Arith.LoweringObstructions.actual_guard' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms actual_guard
/-- info: 'Solidity.Bridge.Arith.LoweringObstructions.setup' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms setup
/-- info: 'Solidity.Bridge.Arith.LoweringObstructions.retained_data_counterexample' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms retained_data_counterexample
/-- info: 'Solidity.Bridge.Arith.LoweringObstructions.not_old_narrow_guard' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms not_old_narrow_guard
end Solidity.Bridge.Arith.LoweringObstructions
