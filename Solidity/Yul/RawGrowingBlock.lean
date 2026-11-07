import Solidity.Yul.RawGrowingSequence
import Solidity.Yul.LocalBoolItemScope

/-! Concrete closure of one typed Boolean binder around a checked item tail.
The existing exact-word preparation and snapshot frame preserve older values;
only the bound prefix is dropped. Actual Source scope restoration remains the
projection contract. No frontend/general declaration admission is inferred. -/
namespace Solidity.Yul.RawGrowingBlock

def drop {ctx : Solidity.Source.Ctx} {name : String}
    (state : RawFrame.State (ctx.push name .bool)) : RawFrame.State ctx :=
  RawDeclarationFrame.ofSnapshot
    ⟨state.clean.drop 1,(RawCoherent.prepare state).1.2,state.world⟩

def close {ctx name} (result : RawGrowingSequence.Result ctx name) :
    Solidity.Source.R RawLoopBody.Flow × RawFrame.State ctx :=
  match result with
  | .inl failure => (.error failure.1,failure.2)
  | .inr next => (next.1,drop next.2)

def run {ctx returns modifier u name items} (value : Bool)
    (tail : RawCheckedAdapterSequence.Items (ctx.push name .bool) returns modifier u items)
    (pipeline : Solidity.Roadmap.Pipeline) (fuel : Nat) (state : RawFrame.State ctx) :
    Solidity.Source.R RawLoopBody.Flow × RawFrame.State ctx :=
  match fuel with
  | 0 => (.error .timeout,state)
  | n+1 => close (RawGrowingSequence.run value tail pipeline n state)

end Solidity.Yul.RawGrowingBlock

namespace Solidity.Yul.RawGrowingBlock
theorem restore_drop : ∀ (ctx : Solidity.Source.Ctx) (name : String)
 (locals : Solidity.Source.Locals ctx.env.layout (ctx.push name .bool).tys),
 locals.restore ctx.tys = .ok (locals.drop 1) := by
  intro ctx name locals
  unfold Solidity.Source.Locals.restore
  have count : (ctx.push name .bool).tys.length - ctx.tys.length = 1 := by
    change (.bool :: ctx.tys).length - ctx.tys.length = 1
    simp only [List.length_cons]
    omega
  have suffix : (ctx.push name .bool).tys.drop
      ((ctx.push name .bool).tys.length - ctx.tys.length) = ctx.tys := by
    rw [count]
    rfl
  rw [dif_pos suffix]
  have dropped : ∀ (k : Nat) (one : k = 1)
      (back : (ctx.push name .bool).tys.drop k = ctx.tys),
      ((back ▸ Solidity.Source.Locals.drop k locals) : Solidity.Source.Locals ctx.env.layout ctx.tys) = locals.drop 1 := by
    intro k one back
    subst k
    rfl
  rw [dropped _ count suffix]
  rfl

theorem drop_coherent : ∀ (ctx : Solidity.Source.Ctx) (name : String)
 (state : Solidity.Yul.RawFrame.State (ctx.push name .bool)),
 Solidity.Yul.RawCoherent.coherent state = true →
 Solidity.Yul.RawCoherent.coherent (Solidity.Yul.RawGrowingBlock.drop state) = true := by
  intro ctx name state same
  unfold drop
  rw [RawCoherent.prepare_coherent state same]
  apply (RawCoherent.coherent_iff _).mpr
  change localWordCells ctx (LocalValues.ofClean state.clean).2 =
    localWordCells ctx (LocalValues.ofClean (state.clean.drop 1))
  exact congrArg (localWordCells ctx)
    (LocalBoolItemScope.drop_clean ctx.env 1 (ctx.push name .bool).tys state.clean)

theorem close_correct : ∀ (ctx : Solidity.Source.Ctx) (name : String)
 (result : Solidity.Yul.RawGrowingSequence.Result ctx name),
 Solidity.Yul.RawGrowingSequence.Coherent result →
 Solidity.Yul.RawCoherent.coherent (Solidity.Yul.RawGrowingBlock.close result).2 = true ∧
 (let actual := Solidity.Yul.RawGrowingSequence.project result
  (actual.1.bind Solidity.Source.Out.close,actual.2)) =
 Solidity.Yul.RawLoopBody.represented (Solidity.Yul.RawGrowingBlock.close result) := by
  intro ctx name result same
  cases result with
  | inl failure => exact ⟨same,rfl⟩
  | inr next =>
    constructor
    · exact drop_coherent ctx name next.2 same
    · cases tag : next.1 with
      | error halt =>
        simp only [close,RawGrowingSequence.project,RawLoopBody.represented,tag,Except.map]
        rfl
      | ok flow =>
        cases flow with
        | normal =>
          simp only [close,RawGrowingSequence.project,RawLoopBody.represented,tag,Except.map,
            RawLoopBody.out,Solidity.Source.Out.up,Solidity.Source.Out.close,restore_drop ctx name,Except.bind]
          rfl
        | break_ h =>
          simp only [close,RawGrowingSequence.project,RawLoopBody.represented,tag,Except.map,
            RawLoopBody.out,Solidity.Source.Out.up,Solidity.Source.Out.close,restore_drop ctx name,Except.bind]
          rfl
        | continue_ h =>
          simp only [close,RawGrowingSequence.project,RawLoopBody.represented,tag,Except.map,
            RawLoopBody.out,Solidity.Source.Out.up,Solidity.Source.Out.close,restore_drop ctx name,Except.bind]
          rfl
        | leave_ h => cases h

theorem correct : ∀ (ctx : Solidity.Source.Ctx) (name : String) (value : Bool)
 (returns : List Solidity.Source.STy) (modifier u : Bool)
 (items : Solidity.Source.RItems ctx.env returns modifier ⟨true,u⟩
   (ctx.push name .bool).tys (ctx.push name .bool).tys)
 (tail : Solidity.Yul.RawCheckedAdapterSequence.Items (ctx.push name .bool) returns modifier u items)
 (glob : Solidity.Source.Glob ctx.env) (frame : Solidity.Source.Fr), frame.checked = true →
 ∀ (fuel nps : Nat) (ph : Option (Solidity.Source.Ph ctx.env))
 (state : Solidity.Yul.RawFrame.State ctx), Solidity.Yul.RawCoherent.coherent state = true →
 Solidity.Yul.RawCoherent.coherent (Solidity.Yul.RawGrowingBlock.run value tail glob.pipeline fuel state).2 = true ∧
 (Solidity.Source.execS glob frame fuel nps ph
   (Solidity.Source.RStmt.block
    (Solidity.Source.RItems.stmt
     (Solidity.Source.RStmt.declInit (E := ctx.env) (R := returns) (M := modifier)
       (k := ⟨true,u⟩) (Γ := ctx.tys) (τ := .bool) (.bool value) (by rfl)) items))
   state.clean).run (Solidity.Source.L0 ctx.env,state.world) =
 Solidity.Yul.RawLoopBody.represented (Solidity.Yul.RawGrowingBlock.run value tail glob.pipeline fuel state) := by
  intro ctx name value returns modifier u items tail glob frame checked fuel nps ph state same
  cases fuel with
  | zero => exact ⟨same,rfl⟩
  | succ fuel =>
    have part := RawGrowingSequence.correct ctx name value returns modifier u items tail
      glob frame checked fuel nps ph state same
    have closed := close_correct ctx name (RawGrowingSequence.run value tail glob.pipeline fuel state) part.1
    constructor
    · exact closed.1
    · rw [Solidity.Source.execS,Solidity.Source.Hoare.run_bind,part.2]
      cases pairEq : RawGrowingSequence.project (RawGrowingSequence.run value tail glob.pipeline fuel state) with
      | mk tag post =>
        cases tag with
        | error halt =>
          simpa only [pairEq,Except.bind] using closed.2
        | ok out =>
          change (Solidity.Source.EM.lift out.close).run post = _
          rw [RawGrowingSequence.lift_run]
          simpa only [pairEq,Except.bind] using closed.2

end Solidity.Yul.RawGrowingBlock

namespace Solidity.Yul.RawGrowingBlock
def adapter : ∀ (ctx : Solidity.Source.Ctx) (name : String) (value : Bool)
 (returns : List Solidity.Source.STy) (modifier u : Bool)
 (items : Solidity.Source.RItems ctx.env returns modifier ⟨true,u⟩
   (ctx.push name .bool).tys (ctx.push name .bool).tys)
 (tail : Solidity.Yul.RawCheckedAdapterSequence.Items (ctx.push name .bool) returns modifier u items),
 Solidity.Yul.RawCheckedAdapter.Adapter ctx returns modifier u
 (Solidity.Source.RStmt.block
    (Solidity.Source.RItems.stmt
     (Solidity.Source.RStmt.declInit (E := ctx.env) (R := returns) (M := modifier)
       (k := ⟨true,u⟩) (Γ := ctx.tys) (τ := .bool) (.bool value) (by rfl)) items)) := by
  intro ctx name value returns modifier u items tail
  exact {
    run := run value tail
    correct := correct ctx name value returns modifier u items tail
  }
end Solidity.Yul.RawGrowingBlock
