import Solidity.Yul.RawSourceAdapterLoop
/-! Actual Source for iterations with a present condition and no post.
Unconditional evaluator equality reuses the existing raw while producer;
no duplicate runtime, initializer or optional-post semantics is introduced. -/
namespace Solidity.Yul.RawSourceForIter
theorem source_while : ∀ {env : Solidity.Source.Env} {returns : List Solidity.Source.STy} {modifier u : Bool}
  {ctx after : Solidity.Source.RCtx}
  (condition : Solidity.Source.RExpr env ctx .bool)
  (body : Solidity.Source.RStmt env returns modifier ⟨true,u⟩ ctx after)
  (glob : Solidity.Source.Glob env) (frame : Solidity.Source.Fr) (fuel nps : Nat)
  (ph : Option (Solidity.Source.Ph env)) (locals : Solidity.Source.Locals env.layout ctx),
  Solidity.Source.forIter glob frame fuel nps ph (.some condition) .none body locals =
    Solidity.Source.execS glob frame fuel nps ph
      (Solidity.Source.RStmt.whileLoop (l := true) condition body) locals := by
  intro env returns modifier u ctx after condition body glob frame fuel nps ph locals
  induction fuel generalizing locals with
  | zero => rfl
  | succ fuel ih =>
    conv => lhs; rw [Solidity.Source.forIter]
    conv => rhs; rw [Solidity.Source.execS]
    simp only [pure_bind,ih]
    apply congrArg (fun continuation :
        (Solidity.Source.RVal env.layout .bool × Solidity.Source.Locals env.layout ctx) →
          Solidity.Source.EM env [] (Solidity.Source.Out env.layout ctx ctx) =>
      Solidity.Source.EM.sub locals (Solidity.Source.evalE glob frame fuel condition) >>= continuation)
    funext pair
    rcases pair with ⟨value,next⟩
    apply congrArg (fun continuation :
        Solidity.Source.Val env.layout .bool →
          Solidity.Source.EM env [] (Solidity.Source.Out env.layout ctx ctx) =>
      Solidity.Source.getV value >>= continuation)
    funext clean
    cases clean with
    | bool choice => cases choice <;> rfl
    | memRef impossible _ | storRef impossible _ | cdRef impossible _ => cases impossible
/-- Concrete no-post for-iteration adequacy from the actual proved raw loop. -/
theorem correct : ∀ {ctx : Solidity.Source.Ctx} {returns : List Solidity.Source.STy} {modifier u : Bool}
  {condition : Solidity.Source.RExpr ctx.env ctx.tys .bool}
  {body : Solidity.Source.RStmt ctx.env returns modifier ⟨true,u⟩ ctx.tys ctx.tys}
  (test : Solidity.Yul.LocalBoolControl.Supported ctx.env ctx.tys condition)
  (inside : Solidity.Yul.RawSourceAdapter.Adapter ctx returns modifier u body)
  (glob : Solidity.Source.Glob ctx.env) (frame : Solidity.Source.Fr)
  (fuel nps : Nat) (ph : Option (Solidity.Source.Ph ctx.env))
  (state : Solidity.Yul.RawFrame.State ctx)
  (_same : Solidity.Yul.RawCoherent.coherent state = true),
  Solidity.Yul.RawCoherent.coherent (Solidity.Yul.RawSourceAdapterLoop.run test inside fuel state).2 = true ∧
    (Solidity.Source.forIter glob frame fuel nps ph (.some condition) .none body state.clean).run
      (Solidity.Source.L0 ctx.env,state.world) =
        Solidity.Yul.RawSequence.represented (Solidity.Yul.RawSourceAdapterLoop.run test inside fuel state) := by
  intro ctx returns modifier u condition body test inside glob frame fuel nps ph state same
  simpa only [Solidity.Yul.RawSourceForIter.source_while] using
    (Solidity.Yul.RawSourceAdapterLoop.correct (l := true) test inside glob frame fuel nps ph state same)

end Solidity.Yul.RawSourceForIter
