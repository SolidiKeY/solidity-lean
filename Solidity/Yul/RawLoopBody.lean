import Solidity.Yul.RawWhile

/-! Certified actual Source loop bodies with intrinsic existing Yul control.
This extends the raw local adapter, not Source.Val or Source's AST. -/
namespace Solidity.Yul.RawLoopBody

abbrev Flow := Closed.Flow { function := false, loop := true }

inductive Supported (ctx : Solidity.Source.Ctx) (returns : List Solidity.Source.STy)
    (modifier u : Bool) :
    Solidity.Source.RStmt ctx.env returns modifier ⟨true,u⟩ ctx.tys ctx.tys → Type where
  | plain {items} : RawSequence.Supported ctx returns modifier ⟨true,u⟩ items →
      Supported ctx returns modifier u (.block items)
  | skip : Supported ctx returns modifier u .skip
  | break_ : Supported ctx returns modifier u .brk
  | continue_ : Supported ctx returns modifier u .cont
  | ifThen {condition body} : LocalBoolControl.Supported ctx.env ctx.tys condition →
      Supported ctx returns modifier u body →
      Supported ctx returns modifier u (.ifThen condition body)

def run {ctx returns modifier u stmt} (proof : Supported ctx returns modifier u stmt) :
    Nat → RawFrame.State ctx → Solidity.Source.R Flow × RawFrame.State ctx := by
  apply Supported.casesOn (motive := fun _ _ =>
    Nat → RawFrame.State ctx → Solidity.Source.R Flow × RawFrame.State ctx) proof
  case plain =>
    intro items body
    exact fun fuel state =>
      let result := RawSequence.block body fuel state
      (result.1.map (fun _ => .normal),result.2)
  case skip =>
    exact fun fuel state => match fuel with
      | 0 => (.error .timeout,state)
      | _+1 => (.ok .normal,state)
  case break_ =>
    exact fun fuel state => match fuel with
      | 0 => (.error .timeout,state)
      | _+1 => (.ok (.break_ rfl),state)
  case continue_ =>
    exact fun fuel state => match fuel with
      | 0 => (.error .timeout,state)
      | _+1 => (.ok (.continue_ rfl),state)
  case ifThen =>
    intro condition body test next
    exact fun fuel state => match fuel with
      | 0 => (.error .timeout,state)
      | n+1 =>
        let first := RawCondition.eval test n state
        match first.1 with
        | .error halt => (.error halt,first.2)
        | .ok choice => if choice then run next n first.2 else (.ok .normal,first.2)
termination_by structural proof

theorem run_ifThen {ctx returns modifier u condition body}
    (test : LocalBoolControl.Supported ctx.env ctx.tys condition)
    (next : Supported ctx returns modifier u body) (fuel : Nat) (state : RawFrame.State ctx) :
    run (.ifThen test next) (fuel+1) state =
      (let first := RawCondition.eval test fuel state
       match first.1 with
       | .error halt => (.error halt,first.2)
       | .ok choice => if choice then run next fuel first.2 else (.ok .normal,first.2)) := rfl

def out {ctx} (state : RawFrame.State ctx) :
    Flow → Solidity.Source.Out ctx.env.layout ctx.tys ctx.tys
  | .normal => .normal state.clean
  | .break_ _ => .brk state.clean
  | .continue_ _ => .cont state.clean
  | .leave_ impossible => nomatch impossible

def represented {ctx} (result : Solidity.Source.R Flow × RawFrame.State ctx) :
    Solidity.Source.R (Solidity.Source.Out ctx.env.layout ctx.tys ctx.tys) ×
      (Solidity.Source.Locals ctx.env.layout [] × Solidity.Source.St ctx.env) :=
  (result.1.map (out result.2),(Solidity.Source.L0 ctx.env,result.2.world))

theorem plain_represented {ctx} (result : Solidity.Source.R Unit × RawFrame.State ctx) :
    represented (result.1.map (fun _ => (Closed.Flow.normal : Flow)),result.2) =
      RawSequence.represented result := by
  cases tag : result.1 <;> simp only [represented,RawSequence.represented,tag,Except.map,out]

theorem source_error {ctx : Solidity.Source.Ctx} {returns : List Solidity.Source.STy}
    {modifier u : Bool} (condition : Solidity.Source.RExpr ctx.env ctx.tys .bool)
    (body : Solidity.Source.RStmt ctx.env returns modifier ⟨true,u⟩ ctx.tys ctx.tys)
    (glob : Solidity.Source.Glob ctx.env) (frame : Solidity.Source.Fr)
    (fuel nps : Nat) (ph : Option (Solidity.Source.Ph ctx.env))
    (state : RawFrame.State ctx) (next : Solidity.Source.Locals ctx.env.layout ctx.tys)
    (world : Solidity.Source.St ctx.env) (halt : Solidity.Source.Halt)
    (actual : (Solidity.Source.evalE glob frame fuel condition).run (state.clean,state.world) =
      (.error halt,(next,world))) :
    (Solidity.Source.execS glob frame (fuel+1) nps ph
      (Solidity.Source.RStmt.ifThen condition body) state.clean).run
      (Solidity.Source.L0 ctx.env,state.world) =
        (.error halt,(Solidity.Source.L0 ctx.env,world)) := by
  rw [Solidity.Source.execS, Solidity.Source.Hoare.run_bind,
    RawCondition.sub_error condition glob frame fuel state.clean next state.world world halt actual]

theorem source_false {ctx : Solidity.Source.Ctx} {returns : List Solidity.Source.STy}
    {modifier u : Bool} (condition : Solidity.Source.RExpr ctx.env ctx.tys .bool)
    (body : Solidity.Source.RStmt ctx.env returns modifier ⟨true,u⟩ ctx.tys ctx.tys)
    (glob : Solidity.Source.Glob ctx.env) (frame : Solidity.Source.Fr)
    (fuel nps : Nat) (ph : Option (Solidity.Source.Ph ctx.env))
    (state next : RawFrame.State ctx)
    (actual : (Solidity.Source.evalE glob frame fuel condition).run (state.clean,state.world) =
      (.ok (.val (.bool false)),(next.clean,next.world))) :
    (Solidity.Source.execS glob frame (fuel+1) nps ph
      (Solidity.Source.RStmt.ifThen condition body) state.clean).run
      (Solidity.Source.L0 ctx.env,state.world) =
        represented (.ok .normal,next) := by
  rw [Solidity.Source.execS, Solidity.Source.Hoare.run_bind,
    RawCondition.sub_bool condition glob frame fuel state.clean next.clean
      state.world next.world false actual]
  rfl

theorem source_true {ctx : Solidity.Source.Ctx} {returns : List Solidity.Source.STy}
    {modifier u : Bool} (condition : Solidity.Source.RExpr ctx.env ctx.tys .bool)
    (body : Solidity.Source.RStmt ctx.env returns modifier ⟨true,u⟩ ctx.tys ctx.tys)
    (glob : Solidity.Source.Glob ctx.env) (frame : Solidity.Source.Fr)
    (fuel nps : Nat) (ph : Option (Solidity.Source.Ph ctx.env))
    (state next : RawFrame.State ctx) (result : Solidity.Source.R Flow × RawFrame.State ctx)
    (actual : (Solidity.Source.evalE glob frame fuel condition).run (state.clean,state.world) =
      (.ok (.val (.bool true)),(next.clean,next.world)))
    (branch : (Solidity.Source.execS glob frame fuel nps ph body next.clean).run
      (Solidity.Source.L0 ctx.env,next.world) = represented result) :
    (Solidity.Source.execS glob frame (fuel+1) nps ph
      (Solidity.Source.RStmt.ifThen condition body) state.clean).run
      (Solidity.Source.L0 ctx.env,state.world) = represented result := by
  rw [Solidity.Source.execS, Solidity.Source.Hoare.run_bind,
    RawCondition.sub_bool condition glob frame fuel state.clean next.clean
      state.world next.world true actual]
  change (do
    let value ← Solidity.Source.execS glob frame fuel nps ph body next.clean
    Solidity.Source.EM.lift value.close).run (Solidity.Source.L0 ctx.env,next.world) = _
  rw [Solidity.Source.Hoare.run_bind,branch]
  cases tag : result.1 with
  | error halt => simp only [represented,tag,Except.map]
  | ok flow =>
    cases flow with
    | normal =>
      simp only [represented,tag,Except.map,out,Solidity.Source.Out.close,RawSequence.restore_self]
      rfl
    | break_ h => simp only [represented,tag,Except.map,out,Solidity.Source.Out.close]; rfl
    | continue_ h => simp only [represented,tag,Except.map,out,Solidity.Source.Out.close]; rfl
    | leave_ h => cases h

theorem correct {ctx returns modifier u stmt} (proof : Supported ctx returns modifier u stmt)
    (glob : Solidity.Source.Glob ctx.env) (frame : Solidity.Source.Fr)
    (fuel nps : Nat) (ph : Option (Solidity.Source.Ph ctx.env))
    (state : RawFrame.State ctx) (same : RawCoherent.coherent state = true) :
    RawCoherent.coherent (run proof fuel state).2 = true ∧
      (Solidity.Source.execS glob frame fuel nps ph stmt state.clean).run
        (Solidity.Source.L0 ctx.env,state.world) = represented (run proof fuel state) := by
  induction proof generalizing fuel state with
  | plain body =>
    have actual := RawSequence.block_correct body glob frame fuel nps ph state same
    change RawCoherent.coherent (RawSequence.block body fuel state).2 = true ∧
      (Solidity.Source.execS glob frame fuel nps ph (.block _) state.clean).run
        (Solidity.Source.L0 ctx.env,state.world) =
        represented ((RawSequence.block body fuel state).1.map (fun _ => (Closed.Flow.normal : Flow)),
          (RawSequence.block body fuel state).2)
    rw [plain_represented]
    exact actual
  | skip => cases fuel <;> exact ⟨same,rfl⟩
  | break_ => cases fuel <;> exact ⟨same,rfl⟩
  | continue_ => cases fuel <;> exact ⟨same,rfl⟩
  | @ifThen condition body test next ih =>
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
          simp only [run_ifThen,conditionRun]
          exact ⟨nextSame,source_error condition body glob frame fuel nps ph state locals world halt actual⟩
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
                simp only [run_ifThen,conditionRun,Bool.false_eq_true,if_false]
                exact ⟨nextSame,source_false condition body glob frame fuel nps ph state nextFrame conditionActual⟩
              | true =>
                change RawCondition.eval test fuel state = (.ok true,nextFrame) at conditionRun
                have conditionActual :
                    (Solidity.Source.evalE glob frame fuel condition).run (state.clean,state.world) =
                      (.ok (.val (.bool true)),(nextFrame.clean,nextFrame.world)) := by
                  rw [nextClean]
                  exact actual
                have bodyRun := ih fuel nextFrame nextSame
                simp only [run_ifThen,conditionRun,if_true]
                exact ⟨bodyRun.1,source_true condition body glob frame fuel nps ph
                  state nextFrame (run next fuel nextFrame) conditionActual bodyRun.2⟩
            | memRef impossible _ | storRef impossible _ | cdRef impossible _ => cases impossible

end Solidity.Yul.RawLoopBody
