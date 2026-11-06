import Solidity.Yul.RawSequenceWhile

/-! Typed executable adapters indexed by actual Source syntax.
The law is a real producer obligation, not an axiom or admission certificate.
Concrete constructors below discharge it using existing implementations. -/
namespace Solidity.Yul.RawSourceAdapter

structure Adapter (ctx : Solidity.Source.Ctx) (returns : List Solidity.Source.STy)
    (modifier u : Bool)
    (stmt : Solidity.Source.RStmt ctx.env returns modifier ⟨true,u⟩ ctx.tys ctx.tys) where
  run : Nat → RawFrame.State ctx → Solidity.Source.R RawLoopBody.Flow × RawFrame.State ctx
  correct : ∀ (glob : Solidity.Source.Glob ctx.env) (frame : Solidity.Source.Fr)
    (fuel nps : Nat) (ph : Option (Solidity.Source.Ph ctx.env))
    (state : RawFrame.State ctx), RawCoherent.coherent state = true →
      RawCoherent.coherent (run fuel state).2 = true ∧
        (Solidity.Source.execS glob frame fuel nps ph stmt state.clean).run
          (Solidity.Source.L0 ctx.env,state.world) = RawLoopBody.represented (run fuel state)

structure ItemAdapter (ctx : Solidity.Source.Ctx) (returns : List Solidity.Source.STy)
    (modifier u : Bool)
    (items : Solidity.Source.RItems ctx.env returns modifier ⟨true,u⟩ ctx.tys ctx.tys) where
  run : Nat → RawFrame.State ctx → Solidity.Source.R RawLoopBody.Flow × RawFrame.State ctx
  correct : ∀ (glob : Solidity.Source.Glob ctx.env) (frame : Solidity.Source.Fr)
    (fuel nps : Nat) (ph : Option (Solidity.Source.Ph ctx.env))
    (state : RawFrame.State ctx), RawCoherent.coherent state = true →
      RawCoherent.coherent (run fuel state).2 = true ∧
        (Solidity.Source.execItems glob frame fuel nps ph items state.clean).run
          (Solidity.Source.L0 ctx.env,state.world) = RawLoopBody.represented (run fuel state)

def body {ctx returns modifier u stmt}
    (proof : RawLoopBody.Supported ctx returns modifier u stmt) :
    Adapter ctx returns modifier u stmt :=
  ⟨RawLoopBody.run proof,RawLoopBody.correct proof⟩

def sequence {ctx returns modifier u items}
    (proof : RawControlSequence.Supported ctx returns modifier u items) :
    ItemAdapter ctx returns modifier u items :=
  ⟨RawControlSequence.run proof,RawControlSequence.correct proof⟩

def atom {ctx returns modifier u stmt}
    (proof : RawSource.Supported ctx returns modifier ⟨true,u⟩ stmt) :
    Adapter ctx returns modifier u stmt where
  run fuel state :=
    let actual := RawCoherent.execS proof fuel state
    (actual.1.map (fun _ => .normal),actual.2)
  correct glob frame fuel nps ph state same := by
    change RawCoherent.coherent (RawCoherent.execS proof fuel state).2 = true ∧
      (Solidity.Source.execS glob frame fuel nps ph stmt state.clean).run
        (Solidity.Source.L0 ctx.env,state.world) =
        RawLoopBody.represented ((RawCoherent.execS proof fuel state).1.map
          (fun _ => (Closed.Flow.normal : RawLoopBody.Flow)),(RawCoherent.execS proof fuel state).2)
    rw [RawLoopBody.plain_represented]
    exact ⟨RawCoherent.invariant proof glob frame fuel state same,
      RawCoherent.source_run proof glob frame fuel nps ph state same⟩

def nil {ctx returns modifier u} : ItemAdapter ctx returns modifier u .nil :=
  sequence .nil

def cons {ctx returns modifier u stmt rest}
    (head : Adapter ctx returns modifier u stmt)
    (tail : ItemAdapter ctx returns modifier u rest) :
    ItemAdapter ctx returns modifier u (.stmt stmt rest) where
  run fuel state := match fuel with
    | 0 => (.error .timeout,state)
    | n+1 =>
      let first := head.run n state
      match first.1 with
      | .error halt => (.error halt,first.2)
      | .ok flow => match flow with
        | .normal => tail.run n first.2
        | .break_ _ | .continue_ _ => first
        | .leave_ impossible => nomatch impossible
  correct glob frame fuel nps ph state same := by
    cases fuel with
    | zero => exact ⟨same,rfl⟩
    | succ fuel =>
      have first := head.correct glob frame fuel nps ph state same
      have second := tail.correct glob frame fuel nps ph (head.run fuel state).2 first.1
      have actual := RawControlSequence.source_cons glob frame fuel nps ph state
        (head.run fuel state) (tail.run fuel (head.run fuel state).2) first.2 second.2
      cases headTag : (head.run fuel state).1 with
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

def block {ctx returns modifier u items} (inside : ItemAdapter ctx returns modifier u items) :
    Adapter ctx returns modifier u (.block items) where
  run fuel state := match fuel with
    | 0 => (.error .timeout,state)
    | n+1 => inside.run n state
  correct glob frame fuel nps ph state same := by
    cases fuel with
    | zero => exact ⟨same,rfl⟩
    | succ fuel =>
      have actual := inside.correct glob frame fuel nps ph state same
      constructor
      · exact actual.1
      · rw [Solidity.Source.execS,Solidity.Source.Hoare.run_bind,actual.2]
        cases tag : (inside.run fuel state).1 with
        | error halt => simp only [RawLoopBody.represented,tag,Except.map]
        | ok flow =>
          simp only [RawLoopBody.represented,tag,Except.map,RawControlSequence.close_self]
          rfl

def ifThen {ctx returns modifier u condition stmt}
    (test : LocalBoolControl.Supported ctx.env ctx.tys condition)
    (inside : Adapter ctx returns modifier u stmt) :
    Adapter ctx returns modifier u (.ifThen condition stmt) where
  run fuel state := match fuel with
    | 0 => (.error .timeout,state)
    | n+1 =>
      let first := RawCondition.eval test n state
      match first.1 with
      | .error halt => (.error halt,first.2)
      | .ok choice => if choice then inside.run n first.2 else (.ok .normal,first.2)
  correct glob frame fuel nps ph state same := by
    cases fuel with
    | zero => exact ⟨same,rfl⟩
    | succ fuel =>
      have conditionRun := RawCondition.source_eval test glob frame fuel state same
      cases actual : (Solidity.Source.evalE glob frame fuel condition).run (state.clean,state.world) with
      | mk tag nextState =>
        rcases nextState with ⟨locals,world⟩
        rw [actual] at conditionRun
        let nextFrame : RawFrame.State ctx :=
          RawCoherent.capture state (LocalState.ofClean (locals,world))
        have nextSame : RawCoherent.coherent nextFrame = true :=
          RawCoherent.capture_coherent state locals world
        have nextClean : nextFrame.clean = locals := by
          simp only [nextFrame,RawCoherent.capture,LocalState.ofClean,
            LocalValues.clean_ofClean,Option.getD_some]
        cases tag with
        | error halt =>
          change RawCondition.eval test fuel state = (.error halt,nextFrame) at conditionRun
          simp only [conditionRun]
          exact ⟨nextSame,RawLoopBody.source_error condition stmt glob frame fuel nps ph
            state locals world halt actual⟩
        | ok value =>
          cases value with
          | val value =>
            cases value with
            | bool choice =>
              cases choice with
              | false =>
                change RawCondition.eval test fuel state = (.ok false,nextFrame) at conditionRun
                have conditionActual :
                    (Solidity.Source.evalE glob frame fuel condition).run (state.clean,state.world) =
                      (.ok (.val (.bool false)),(nextFrame.clean,nextFrame.world)) := by
                  rw [nextClean]
                  exact actual
                simp only [conditionRun,Bool.false_eq_true,if_false]
                exact ⟨nextSame,RawLoopBody.source_false condition stmt glob frame fuel nps ph
                  state nextFrame conditionActual⟩
              | true =>
                change RawCondition.eval test fuel state = (.ok true,nextFrame) at conditionRun
                have conditionActual :
                    (Solidity.Source.evalE glob frame fuel condition).run (state.clean,state.world) =
                      (.ok (.val (.bool true)),(nextFrame.clean,nextFrame.world)) := by
                  rw [nextClean]
                  exact actual
                have next := inside.correct glob frame fuel nps ph nextFrame nextSame
                simp only [conditionRun,if_true]
                exact ⟨next.1,RawLoopBody.source_true condition stmt glob frame fuel nps ph
                  state nextFrame (inside.run fuel nextFrame) conditionActual next.2⟩
            | memRef impossible _ | storRef impossible _ | cdRef impossible _ => cases impossible

/-- Concrete producer composition, not a theorem requiring a caller's run law. -/
theorem if_sequence_correct {ctx returns modifier u condition items}
    (test : LocalBoolControl.Supported ctx.env ctx.tys condition)
    (proof : RawControlSequence.Supported ctx returns modifier u items)
    (glob : Solidity.Source.Glob ctx.env) (frame : Solidity.Source.Fr)
    (fuel nps : Nat) (ph : Option (Solidity.Source.Ph ctx.env))
    (state : RawFrame.State ctx) (same : RawCoherent.coherent state = true) :
    RawCoherent.coherent ((ifThen test (block (sequence proof))).run fuel state).2 = true ∧
      (Solidity.Source.execS glob frame fuel nps ph
        (Solidity.Source.RStmt.ifThen condition (.block items)) state.clean).run
        (Solidity.Source.L0 ctx.env,state.world) =
          RawLoopBody.represented ((ifThen test (block (sequence proof))).run fuel state) :=
  (ifThen test (block (sequence proof))).correct glob frame fuel nps ph state same

end Solidity.Yul.RawSourceAdapter
