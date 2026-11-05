import Solidity.Yul.RawCheckedAdapter

/-! Concrete checked Source item/block composition. Contracts index existing
same-context Source syntax. Normal flow executes the tail; control/error keeps
the exact head frame. All proof fields retain checked/coherent premises. -/
namespace Solidity.Yul.RawCheckedAdapterSequence

structure Items (ctx : Solidity.Source.Ctx) (returns : List Solidity.Source.STy)
    (modifier u : Bool)
    (items : Solidity.Source.RItems ctx.env returns modifier ⟨true,u⟩ ctx.tys ctx.tys) where
  run : Solidity.Roadmap.Pipeline → Nat → RawFrame.State ctx →
    Solidity.Source.R RawLoopBody.Flow × RawFrame.State ctx
  correct : ∀ (glob : Solidity.Source.Glob ctx.env) (frame : Solidity.Source.Fr),
    frame.checked = true →
    ∀ (fuel nps : Nat) (ph : Option (Solidity.Source.Ph ctx.env))
    (state : RawFrame.State ctx), RawCoherent.coherent state = true →
      RawCoherent.coherent (run glob.pipeline fuel state).2 = true ∧
        (Solidity.Source.execItems glob frame fuel nps ph items state.clean).run
          (Solidity.Source.L0 ctx.env,state.world) =
            RawLoopBody.represented (run glob.pipeline fuel state)

def ofSequence {ctx returns modifier u items}
    (proof : RawCheckedControlSequence.Supported ctx returns modifier u items) :
    Items ctx returns modifier u items where
  run := RawCheckedControlSequence.run proof
  correct := RawCheckedControlSequence.correct ctx returns modifier u items proof

def fromItems {ctx returns modifier u items}
    (source : RawSourceAdapter.ItemAdapter ctx returns modifier u items) :
    Items ctx returns modifier u items where
  run _pipeline := source.run
  correct glob frame _checked := source.correct glob frame

def nil {ctx returns modifier u} : Items ctx returns modifier u .nil :=
  ofSequence .nil

def runCons {ctx returns modifier u stmt rest}
    (head : RawCheckedAdapter.Adapter ctx returns modifier u stmt)
    (tail : Items ctx returns modifier u rest)
    (pipeline : Solidity.Roadmap.Pipeline) (fuel : Nat) (state : RawFrame.State ctx) :
    Solidity.Source.R RawLoopBody.Flow × RawFrame.State ctx :=
  match fuel with
  | 0 => (.error .timeout,state)
  | n+1 =>
    let first := head.run pipeline n state
    match first.1 with
    | .error halt => (.error halt,first.2)
    | .ok flow => match flow with
      | .normal => tail.run pipeline n first.2
      | .break_ _ | .continue_ _ => first
      | .leave_ impossible => nomatch impossible

def runBlock {ctx returns modifier u items}
    (inside : Items ctx returns modifier u items)
    (pipeline : Solidity.Roadmap.Pipeline) (fuel : Nat) (state : RawFrame.State ctx) :
    Solidity.Source.R RawLoopBody.Flow × RawFrame.State ctx :=
  match fuel with
  | 0 => (.error .timeout,state)
  | n+1 => inside.run pipeline n state

end Solidity.Yul.RawCheckedAdapterSequence

namespace Solidity.Yul.RawCheckedAdapterSequence
theorem cons_correct : ∀ (ctx : Solidity.Source.Ctx) (returns : List Solidity.Source.STy) (modifier u : Bool)
 (stmt : Solidity.Source.RStmt ctx.env returns modifier ⟨true,u⟩ ctx.tys ctx.tys)
 (rest : Solidity.Source.RItems ctx.env returns modifier ⟨true,u⟩ ctx.tys ctx.tys)
 (head : Solidity.Yul.RawCheckedAdapter.Adapter ctx returns modifier u stmt)
 (tail : Solidity.Yul.RawCheckedAdapterSequence.Items ctx returns modifier u rest)
 (glob : Solidity.Source.Glob ctx.env) (frame : Solidity.Source.Fr), frame.checked = true →
 ∀ (fuel nps : Nat) (ph : Option (Solidity.Source.Ph ctx.env))
 (state : Solidity.Yul.RawFrame.State ctx), Solidity.Yul.RawCoherent.coherent state = true →
 Solidity.Yul.RawCoherent.coherent
   (Solidity.Yul.RawCheckedAdapterSequence.runCons head tail glob.pipeline fuel state).2 = true ∧
 (Solidity.Source.execItems glob frame fuel nps ph (.stmt stmt rest) state.clean).run
   (Solidity.Source.L0 ctx.env,state.world) =
 Solidity.Yul.RawLoopBody.represented (Solidity.Yul.RawCheckedAdapterSequence.runCons head tail glob.pipeline fuel state) := by
  intro ctx returns modifier u stmt rest head tail glob frame checked fuel nps ph state same
  unfold runCons
  cases fuel with
  | zero => exact ⟨same,rfl⟩
  | succ fuel =>
    have first := head.correct glob frame checked fuel nps ph state same
    have second := tail.correct glob frame checked fuel nps ph (head.run glob.pipeline fuel state).2 first.1
    have actual := RawControlSequence.source_cons glob frame fuel nps ph state
      (head.run glob.pipeline fuel state) (tail.run glob.pipeline fuel (head.run glob.pipeline fuel state).2) first.2 second.2
    cases headTag : (head.run glob.pipeline fuel state).1 with
    | error halt =>
      simp only [headTag] at actual ⊢
      exact ⟨first.1,actual⟩
    | ok flow =>
      cases flow with
      | normal =>
        simp only [headTag] at actual ⊢
        exact ⟨second.1,actual⟩
      | break_ h =>
        simp only [headTag] at actual ⊢
        exact ⟨first.1,actual⟩
      | continue_ h =>
        simp only [headTag] at actual ⊢
        exact ⟨first.1,actual⟩
      | leave_ h => cases h

theorem block_correct : ∀ (ctx : Solidity.Source.Ctx) (returns : List Solidity.Source.STy) (modifier u : Bool)
 (items : Solidity.Source.RItems ctx.env returns modifier ⟨true,u⟩ ctx.tys ctx.tys)
 (inside : Solidity.Yul.RawCheckedAdapterSequence.Items ctx returns modifier u items)
 (glob : Solidity.Source.Glob ctx.env) (frame : Solidity.Source.Fr), frame.checked = true →
 ∀ (fuel nps : Nat) (ph : Option (Solidity.Source.Ph ctx.env))
 (state : Solidity.Yul.RawFrame.State ctx), Solidity.Yul.RawCoherent.coherent state = true →
 Solidity.Yul.RawCoherent.coherent
   (Solidity.Yul.RawCheckedAdapterSequence.runBlock inside glob.pipeline fuel state).2 = true ∧
 (Solidity.Source.execS glob frame fuel nps ph (.block items) state.clean).run
   (Solidity.Source.L0 ctx.env,state.world) =
 Solidity.Yul.RawLoopBody.represented (Solidity.Yul.RawCheckedAdapterSequence.runBlock inside glob.pipeline fuel state) := by
  intro ctx returns modifier u items inside glob frame checked fuel nps ph state same
  unfold runBlock
  cases fuel with
  | zero => exact ⟨same,rfl⟩
  | succ fuel =>
    have actual := inside.correct glob frame checked fuel nps ph state same
    constructor
    · exact actual.1
    · rw [Solidity.Source.execS,Solidity.Source.Hoare.run_bind,actual.2]
      cases tag : (inside.run glob.pipeline fuel state).1 with
      | error halt => simp only [RawLoopBody.represented,tag,Except.map]
      | ok flow =>
        simp only [RawLoopBody.represented,tag,Except.map,RawControlSequence.close_self]
        rfl


def cons {ctx returns modifier u stmt rest}
    (head : RawCheckedAdapter.Adapter ctx returns modifier u stmt)
    (tail : Items ctx returns modifier u rest) :
    Items ctx returns modifier u (.stmt stmt rest) where
  run := runCons head tail
  correct := cons_correct ctx returns modifier u stmt rest head tail

def block {ctx returns modifier u items}
    (inside : Items ctx returns modifier u items) :
    RawCheckedAdapter.Adapter ctx returns modifier u (.block items) where
  run := runBlock inside
  correct := block_correct ctx returns modifier u items inside

end Solidity.Yul.RawCheckedAdapterSequence
