import Solidity.Yul.RawLoopBody

/-! Actual Source items with same-context control propagation. -/
namespace Solidity.Yul.RawControlSequence

inductive Supported (ctx : Solidity.Source.Ctx) (returns : List Solidity.Source.STy)
    (modifier u : Bool) :
    Solidity.Source.RItems ctx.env returns modifier ⟨true,u⟩ ctx.tys ctx.tys → Type where
  | nil : Supported ctx returns modifier u .nil
  | cons {stmt rest} : RawLoopBody.Supported ctx returns modifier u stmt →
      Supported ctx returns modifier u rest →
      Supported ctx returns modifier u (.stmt stmt rest)

def run {ctx returns modifier u items} (proof : Supported ctx returns modifier u items) :
    Nat → RawFrame.State ctx → Solidity.Source.R RawLoopBody.Flow × RawFrame.State ctx := by
  apply Supported.casesOn (motive := fun _ _ =>
    Nat → RawFrame.State ctx → Solidity.Source.R RawLoopBody.Flow × RawFrame.State ctx) proof
  case nil =>
    exact fun fuel state => match fuel with
      | 0 => (.error .timeout,state)
      | _+1 => (.ok .normal,state)
  case cons =>
    intro stmt rest head tail
    exact fun fuel state => match fuel with
      | 0 => (.error .timeout,state)
      | n+1 =>
        let first := RawLoopBody.run head n state
        match first.1 with
        | .error halt => (.error halt,first.2)
        | .ok flow => match flow with
          | .normal => run tail n first.2
          | .break_ _ | .continue_ _ => first
          | .leave_ impossible => nomatch impossible
termination_by structural proof

theorem run_cons {ctx returns modifier u stmt rest}
    (head : RawLoopBody.Supported ctx returns modifier u stmt)
    (tail : Supported ctx returns modifier u rest) (fuel : Nat) (state : RawFrame.State ctx) :
    run (.cons head tail) (fuel+1) state =
      (let first := RawLoopBody.run head fuel state
       match first.1 with
       | .error halt => (.error halt,first.2)
       | .ok flow => match flow with
         | .normal => run tail fuel first.2
         | .break_ _ | .continue_ _ => first
         | .leave_ impossible => nomatch impossible) := rfl

theorem up_self {D : Solidity.Source.Layout} {ctx : Solidity.Source.RCtx}
    (out : Solidity.Source.Out D ctx ctx) : out.up ctx = .ok out := by
  cases out <;> simp only [Solidity.Source.Out.up,RawSequence.restore_self] <;> rfl

theorem close_self {D : Solidity.Source.Layout} {ctx : Solidity.Source.RCtx}
    (out : Solidity.Source.Out D ctx ctx) : out.close = .ok out := by
  cases out <;> simp only [Solidity.Source.Out.close,RawSequence.restore_self] <;> rfl

theorem source_cons {ctx : Solidity.Source.Ctx} {returns : List Solidity.Source.STy}
    {modifier u : Bool}
    {stmt : Solidity.Source.RStmt ctx.env returns modifier ⟨true,u⟩ ctx.tys ctx.tys}
    {rest : Solidity.Source.RItems ctx.env returns modifier ⟨true,u⟩ ctx.tys ctx.tys}
    (glob : Solidity.Source.Glob ctx.env) (frame : Solidity.Source.Fr)
    (fuel nps : Nat) (ph : Option (Solidity.Source.Ph ctx.env)) (state : RawFrame.State ctx)
    (first second : Solidity.Source.R RawLoopBody.Flow × RawFrame.State ctx)
    (headRun : (Solidity.Source.execS glob frame fuel nps ph stmt state.clean).run
      (Solidity.Source.L0 ctx.env,state.world) = RawLoopBody.represented first)
    (tailRun : (Solidity.Source.execItems glob frame fuel nps ph rest first.2.clean).run
      (Solidity.Source.L0 ctx.env,first.2.world) = RawLoopBody.represented second) :
    (Solidity.Source.execItems glob frame (fuel+1) nps ph
      (Solidity.Source.RItems.stmt stmt rest) state.clean).run
      (Solidity.Source.L0 ctx.env,state.world) =
        match first.1 with
        | .error halt => RawLoopBody.represented (.error halt,first.2)
        | .ok flow => match flow with
          | .normal => RawLoopBody.represented second
          | .break_ _ | .continue_ _ => RawLoopBody.represented first
          | .leave_ impossible => nomatch impossible := by
  rw [Solidity.Source.execItems,Solidity.Source.Hoare.run_bind,headRun]
  cases headTag : first.1 with
  | error halt => simp only [RawLoopBody.represented,headTag,Except.map]
  | ok flow =>
    cases flow with
    | normal =>
      simp only [RawLoopBody.represented,headTag,Except.map,RawLoopBody.out]
      rw [Solidity.Source.Hoare.run_bind,tailRun]
      cases tailTag : second.1 with
      | error halt => simp only [RawLoopBody.represented,tailTag,Except.map]
      | ok value =>
        simp only [RawLoopBody.represented,tailTag,Except.map,up_self]
        rfl
    | break_ h =>
      simp only [RawLoopBody.represented,headTag,Except.map,RawLoopBody.out]
      rfl
    | continue_ h =>
      simp only [RawLoopBody.represented,headTag,Except.map,RawLoopBody.out]
      rfl
    | leave_ h => cases h

theorem correct {ctx returns modifier u items} (proof : Supported ctx returns modifier u items)
    (glob : Solidity.Source.Glob ctx.env) (frame : Solidity.Source.Fr)
    (fuel nps : Nat) (ph : Option (Solidity.Source.Ph ctx.env))
    (state : RawFrame.State ctx) (same : RawCoherent.coherent state = true) :
    RawCoherent.coherent (run proof fuel state).2 = true ∧
      (Solidity.Source.execItems glob frame fuel nps ph items state.clean).run
        (Solidity.Source.L0 ctx.env,state.world) = RawLoopBody.represented (run proof fuel state) := by
  induction proof generalizing fuel state with
  | nil => cases fuel <;> exact ⟨same,rfl⟩
  | @cons stmt rest head tail ih =>
    cases fuel with
    | zero => exact ⟨same,rfl⟩
    | succ fuel =>
      have first := RawLoopBody.correct head glob frame fuel nps ph state same
      have second := ih fuel (RawLoopBody.run head fuel state).2 first.1
      have actual := source_cons glob frame fuel nps ph state
        (RawLoopBody.run head fuel state) (run tail fuel (RawLoopBody.run head fuel state).2)
        first.2 second.2
      cases headTag : (RawLoopBody.run head fuel state).1 with
      | error halt =>
        simp only [run_cons,headTag]
        simp only [headTag] at actual
        exact ⟨first.1,actual⟩
      | ok flow =>
        cases flow with
        | normal =>
          simp only [run_cons,headTag]
          simp only [headTag] at actual
          exact ⟨second.1,actual⟩
        | break_ h =>
          simp only [run_cons,headTag]
          simp only [headTag] at actual
          exact ⟨first.1,actual⟩
        | continue_ h =>
          simp only [run_cons,headTag]
          simp only [headTag] at actual
          exact ⟨first.1,actual⟩
        | leave_ h => cases h

def block {ctx returns modifier u items} (proof : Supported ctx returns modifier u items)
    (fuel : Nat) (state : RawFrame.State ctx) :
    Solidity.Source.R RawLoopBody.Flow × RawFrame.State ctx :=
  match fuel with
  | 0 => (.error .timeout,state)
  | n+1 => run proof n state

theorem block_correct {ctx returns modifier u items} (proof : Supported ctx returns modifier u items)
    (glob : Solidity.Source.Glob ctx.env) (frame : Solidity.Source.Fr)
    (fuel nps : Nat) (ph : Option (Solidity.Source.Ph ctx.env))
    (state : RawFrame.State ctx) (same : RawCoherent.coherent state = true) :
    RawCoherent.coherent (block proof fuel state).2 = true ∧
      (Solidity.Source.execS glob frame fuel nps ph (Solidity.Source.RStmt.block items)
        state.clean).run (Solidity.Source.L0 ctx.env,state.world) =
          RawLoopBody.represented (block proof fuel state) := by
  cases fuel with
  | zero => exact ⟨same,rfl⟩
  | succ fuel =>
    dsimp only [block]
    have actual := correct proof glob frame fuel nps ph state same
    constructor
    · exact actual.1
    · rw [Solidity.Source.execS,Solidity.Source.Hoare.run_bind,actual.2]
      cases tag : (run proof fuel state).1 with
      | error halt => simp only [RawLoopBody.represented,tag,Except.map]
      | ok flow =>
        simp only [RawLoopBody.represented,tag,Except.map,close_self]
        rfl

end Solidity.Yul.RawControlSequence
