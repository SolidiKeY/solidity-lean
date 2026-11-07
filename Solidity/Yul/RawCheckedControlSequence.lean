import Solidity.Yul.RawControlSequence
import Solidity.Yul.RawU8Statement

/-! Actual Source items with checked uint8 steps and existing break/continue flow.
Certificates stay intrinsic; checked/coherent Source premises remain explicit. -/
namespace Solidity.Yul.RawCheckedControlSequence

inductive Supported (ctx : Solidity.Source.Ctx) (returns : List Solidity.Source.STy)
    (modifier u : Bool) :
    Solidity.Source.RItems ctx.env returns modifier ⟨true,u⟩ ctx.tys ctx.tys → Type where
  | nil : Supported ctx returns modifier u .nil
  | cons {stmt rest} : RawLoopBody.Supported ctx returns modifier u stmt →
      Supported ctx returns modifier u rest →
      Supported ctx returns modifier u (.stmt stmt rest)

  | uint8 {expr rest} : LocalU8Expr.Supported ctx.env ctx.tys expr →
      Supported ctx returns modifier u rest →
      Supported ctx returns modifier u (.stmt (.expr expr) rest)

def run {ctx returns modifier u items} (proof : Supported ctx returns modifier u items) :
    Solidity.Roadmap.Pipeline → Nat → RawFrame.State ctx → Solidity.Source.R RawLoopBody.Flow × RawFrame.State ctx := by
  apply Supported.casesOn (motive := fun _ _ =>
    Solidity.Roadmap.Pipeline → Nat → RawFrame.State ctx → Solidity.Source.R RawLoopBody.Flow × RawFrame.State ctx) proof
  case nil =>
    exact fun _pipeline fuel state => match fuel with
      | 0 => (.error .timeout,state)
      | _+1 => (.ok .normal,state)
  case cons =>
    intro stmt rest head tail
    exact fun pipeline fuel state => match fuel with
      | 0 => (.error .timeout,state)
      | n+1 =>
        let first := RawLoopBody.run head n state
        match first.1 with
        | .error halt => (.error halt,first.2)
        | .ok flow => match flow with
          | .normal => run tail pipeline n first.2
          | .break_ _ | .continue_ _ => first
          | .leave_ impossible => nomatch impossible
  case uint8 =>
    intro expr rest head tail
    exact fun pipeline fuel state => match fuel with
      | 0 => (.error .timeout,state)
      | n+1 =>
        let first := RawU8Statement.run head pipeline n state
        match first.1 with
        | .error halt => (.error halt,first.2)
        | .ok _ => run tail pipeline n first.2
termination_by structural proof

theorem run_cons {ctx returns modifier u stmt rest}
    (head : RawLoopBody.Supported ctx returns modifier u stmt)
    (tail : Supported ctx returns modifier u rest) (pipeline : Solidity.Roadmap.Pipeline) (fuel : Nat) (state : RawFrame.State ctx) :
    run (.cons head tail) pipeline (fuel+1) state =
      (let first := RawLoopBody.run head fuel state
       match first.1 with
       | .error halt => (.error halt,first.2)
       | .ok flow => match flow with
         | .normal => run tail pipeline fuel first.2
         | .break_ _ | .continue_ _ => first
         | .leave_ impossible => nomatch impossible) := rfl

theorem run_uint8 {ctx returns modifier u expr rest}
 (head : LocalU8Expr.Supported ctx.env ctx.tys expr) (tail : Supported ctx returns modifier u rest)
 (pipeline : Solidity.Roadmap.Pipeline) (fuel : Nat) (state : RawFrame.State ctx) :
 run (.uint8 head tail) pipeline (fuel+1) state =
 (let first := RawU8Statement.run head pipeline fuel state
  match first.1 with
  | .error halt => (.error halt,first.2)
  | .ok _ => run tail pipeline fuel first.2) := rfl

theorem correct : ∀ (ctx : Solidity.Source.Ctx) (returns : List Solidity.Source.STy) (modifier u : Bool)
 (items : Solidity.Source.RItems ctx.env returns modifier ⟨true,u⟩ ctx.tys ctx.tys)
 (proof : Solidity.Yul.RawCheckedControlSequence.Supported ctx returns modifier u items)
 (glob : Solidity.Source.Glob ctx.env) (frame : Solidity.Source.Fr), frame.checked = true →
 ∀ (fuel nps : Nat) (ph : Option (Solidity.Source.Ph ctx.env))
 (state : Solidity.Yul.RawFrame.State ctx), Solidity.Yul.RawCoherent.coherent state = true →
 Solidity.Yul.RawCoherent.coherent (Solidity.Yul.RawCheckedControlSequence.run proof glob.pipeline fuel state).2 = true ∧
 (Solidity.Source.execItems glob frame fuel nps ph items state.clean).run
   (Solidity.Source.L0 ctx.env,state.world) =
 Solidity.Yul.RawLoopBody.represented (Solidity.Yul.RawCheckedControlSequence.run proof glob.pipeline fuel state) := by
  intro ctx returns modifier u items proof glob frame checked fuel nps ph state same
  induction proof generalizing fuel state with
  | nil => cases fuel <;> exact ⟨same,rfl⟩
  | @cons stmt rest head tail ih =>
    cases fuel with
    | zero => exact ⟨same,rfl⟩
    | succ fuel =>
      have first := RawLoopBody.correct head glob frame fuel nps ph state same
      have second := ih fuel (RawLoopBody.run head fuel state).2 first.1
      have actual := RawControlSequence.source_cons glob frame fuel nps ph state
        (RawLoopBody.run head fuel state) (run tail glob.pipeline fuel (RawLoopBody.run head fuel state).2)
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
  | @uint8 expr rest head tail ih =>
    cases fuel with
    | zero => exact ⟨same,rfl⟩
    | succ fuel =>
      have first := RawU8Statement.correct ctx expr head glob frame checked fuel nps ph returns modifier ⟨true,u⟩ state same
      have headRun : (Solidity.Source.execS glob frame fuel nps ph
          (Solidity.Source.RStmt.expr (R:=returns) (M:=modifier) (k:=⟨true,u⟩) expr) state.clean).run
          (Solidity.Source.L0 ctx.env,state.world) =
          RawSequence.represented (RawU8Statement.run head glob.pipeline fuel state) := by
        have observed := first.2
        unfold RawCoherent.observe at observed
        rw [if_pos first.1] at observed
        exact (Option.some.inj observed).symm
      have asFlow := headRun.trans (RawLoopBody.plain_represented (RawU8Statement.run head glob.pipeline fuel state)).symm
      have second := ih fuel (RawU8Statement.run head glob.pipeline fuel state).2 first.1
      have actual := RawControlSequence.source_cons glob frame fuel nps ph state
        ((RawU8Statement.run head glob.pipeline fuel state).1.map (fun _ => (Closed.Flow.normal : RawLoopBody.Flow)),
          (RawU8Statement.run head glob.pipeline fuel state).2)
        (run tail glob.pipeline fuel (RawU8Statement.run head glob.pipeline fuel state).2) asFlow second.2
      cases headTag : (RawU8Statement.run head glob.pipeline fuel state).1 with
      | error halt =>
        simp only [run_uint8,headTag]
        simp only [headTag,Except.map] at actual
        exact ⟨first.1,actual⟩
      | ok value =>
        simp only [run_uint8,headTag]
        simp only [headTag,Except.map] at actual
        exact ⟨second.1,actual⟩

def block {ctx returns modifier u items} (proof : Supported ctx returns modifier u items)
    (pipeline : Solidity.Roadmap.Pipeline) (fuel : Nat) (state : RawFrame.State ctx) :
    Solidity.Source.R RawLoopBody.Flow × RawFrame.State ctx :=
  match fuel with
  | 0 => (.error .timeout,state)
  | n+1 => run proof pipeline n state

theorem block_correct {ctx returns modifier u items} (proof : Supported ctx returns modifier u items)
    (glob : Solidity.Source.Glob ctx.env) (frame : Solidity.Source.Fr)
    (checked : frame.checked = true)
    (fuel nps : Nat) (ph : Option (Solidity.Source.Ph ctx.env))
    (state : RawFrame.State ctx) (same : RawCoherent.coherent state = true) :
    RawCoherent.coherent (block proof glob.pipeline fuel state).2 = true ∧
      (Solidity.Source.execS glob frame fuel nps ph (Solidity.Source.RStmt.block items)
        state.clean).run (Solidity.Source.L0 ctx.env,state.world) =
          RawLoopBody.represented (block proof glob.pipeline fuel state) := by
  cases fuel with
  | zero => exact ⟨same,rfl⟩
  | succ fuel =>
    dsimp only [block]
    have actual := correct ctx returns modifier u items proof glob frame checked fuel nps ph state same
    constructor
    · exact actual.1
    · rw [Solidity.Source.execS,Solidity.Source.Hoare.run_bind,actual.2]
      cases tag : (run proof glob.pipeline fuel state).1 with
      | error halt => simp only [RawLoopBody.represented,tag,Except.map]
      | ok flow =>
        simp only [RawLoopBody.represented,tag,Except.map,RawControlSequence.close_self]
        rfl

end Solidity.Yul.RawCheckedControlSequence
