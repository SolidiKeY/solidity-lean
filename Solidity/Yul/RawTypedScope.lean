import Solidity.Yul.RawGrowingBlock

/-! One typed LOCAL binder can close without changing the raw frame type.
Restoration and closure use actual Source operations. This supplies no
initializer execution, physical layout or general admission theorem. -/
namespace Solidity.Yul.RawTypedScope
def drop {ctx : Solidity.Source.Ctx} {name : String} {ty : Solidity.Source.STy}
    (state : RawFrame.State (ctx.push name ty)) : RawFrame.State ctx :=
  RawDeclarationFrame.ofSnapshot
    ⟨state.clean.drop 1,(RawCoherent.prepare state).1.2,state.world⟩
def close {ctx : Solidity.Source.Ctx} {name : String} {ty : Solidity.Source.STy}
    (result : Solidity.Source.R RawLoopBody.Flow × RawFrame.State (ctx.push name ty)) :
    Solidity.Source.R RawLoopBody.Flow × RawFrame.State ctx :=
  (result.1,drop result.2)
def project {ctx : Solidity.Source.Ctx} {name : String} {ty : Solidity.Source.STy}
    (result : Solidity.Source.R RawLoopBody.Flow × RawFrame.State (ctx.push name ty)) :
    Solidity.Source.R (Solidity.Source.Out ctx.env.layout ctx.tys ctx.tys) ×
      (Solidity.Source.Locals ctx.env.layout [] × Solidity.Source.St ctx.env) :=
  let actual := RawLoopBody.represented result
  ((actual.1.bind (fun out => out.up ctx.tys)).bind Solidity.Source.Out.close,actual.2)
end Solidity.Yul.RawTypedScope

namespace Solidity.Yul.RawTypedScope
theorem restore_drop : ∀ (ctx : Solidity.Source.Ctx) (name : String) (ty : Solidity.Source.STy)
 (locals : Solidity.Source.Locals ctx.env.layout (ctx.push name ty).tys),
 locals.restore ctx.tys = .ok (locals.drop 1) := by
  intro ctx name ty locals
  unfold Solidity.Source.Locals.restore
  have count : (ctx.push name ty).tys.length - ctx.tys.length = 1 := by
    change (ty :: ctx.tys).length - ctx.tys.length = 1
    simp only [List.length_cons]
    omega
  have suffix : (ctx.push name ty).tys.drop
      ((ctx.push name ty).tys.length - ctx.tys.length) = ctx.tys := by
    rw [count]
    rfl
  rw [dif_pos suffix]
  have dropped : ∀ (k : Nat) (one : k = 1)
      (back : (ctx.push name ty).tys.drop k = ctx.tys),
      ((back ▸ Solidity.Source.Locals.drop k locals) : Solidity.Source.Locals ctx.env.layout ctx.tys) = locals.drop 1 := by
    intro k one back
    subst k
    rfl
  rw [dropped _ count suffix]
  rfl

theorem drop_coherent : ∀ (ctx : Solidity.Source.Ctx) (name : String) (ty : Solidity.Source.STy)
 (state : Solidity.Yul.RawFrame.State (ctx.push name ty)),
 Solidity.Yul.RawCoherent.coherent state = true →
 Solidity.Yul.RawCoherent.coherent (Solidity.Yul.RawTypedScope.drop state) = true := by
  intro ctx name ty state same
  unfold drop
  rw [RawCoherent.prepare_coherent state same]
  apply (RawCoherent.coherent_iff _).mpr
  change localWordCells ctx (LocalValues.ofClean state.clean).2 =
    localWordCells ctx (LocalValues.ofClean (state.clean.drop 1))
  exact congrArg (localWordCells ctx)
    (LocalBoolItemScope.drop_clean ctx.env 1 (ctx.push name ty).tys state.clean)

theorem close_correct : ∀ (ctx : Solidity.Source.Ctx) (name : String) (ty : Solidity.Source.STy)
 (result : Solidity.Source.R Solidity.Yul.RawLoopBody.Flow × Solidity.Yul.RawFrame.State (ctx.push name ty)),
 Solidity.Yul.RawCoherent.coherent result.2 = true →
 Solidity.Yul.RawCoherent.coherent (Solidity.Yul.RawTypedScope.close result).2 = true ∧
 Solidity.Yul.RawTypedScope.project result = Solidity.Yul.RawLoopBody.represented (Solidity.Yul.RawTypedScope.close result) := by
  intro ctx name ty result same
  constructor
  · exact drop_coherent ctx name ty result.2 same
  · cases tag : result.1 with
    | error halt =>
      simp only [close,project,RawLoopBody.represented,tag,Except.map]
      rfl
    | ok flow =>
      cases flow with
      | normal =>
        simp only [close,project,RawLoopBody.represented,tag,Except.map,
          RawLoopBody.out,Solidity.Source.Out.up,Solidity.Source.Out.close,restore_drop ctx name ty,Except.bind]
        rfl
      | break_ h =>
        simp only [close,project,RawLoopBody.represented,tag,Except.map,
          RawLoopBody.out,Solidity.Source.Out.up,Solidity.Source.Out.close,restore_drop ctx name ty,Except.bind]
        rfl
      | continue_ h =>
        simp only [close,project,RawLoopBody.represented,tag,Except.map,
          RawLoopBody.out,Solidity.Source.Out.up,Solidity.Source.Out.close,restore_drop ctx name ty,Except.bind]
        rfl
      | leave_ h => cases h

theorem bool_drop_eq : ∀ (ctx : Solidity.Source.Ctx) (name : String)
 (state : Solidity.Yul.RawFrame.State (ctx.push name .bool)),
 Solidity.Yul.RawTypedScope.drop state = Solidity.Yul.RawGrowingBlock.drop state := by
  intro ctx name state
  rfl

theorem bool_close_eq : ∀ (ctx : Solidity.Source.Ctx) (name : String)
 (result : Solidity.Source.R Solidity.Yul.RawLoopBody.Flow × Solidity.Yul.RawFrame.State (ctx.push name .bool)),
 Solidity.Yul.RawTypedScope.close result = Solidity.Yul.RawGrowingBlock.close (.inr result) := by
  intro ctx name result
  rfl

end Solidity.Yul.RawTypedScope
