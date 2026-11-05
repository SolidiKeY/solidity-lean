import Solidity.Yul.RawSourceAdapterDoWhile
/-! Actual Source unchecked-item transport beside the H11 local raw frame.
The inner proof uses checked=false; the tail uses the original frame.
This same-context control slice does not prove checked arithmetic coverage. -/
namespace Solidity.Yul.RawSourceAdapterUnchecked
theorem source_unchecked {ctx : Solidity.Source.Ctx} {returns : List Solidity.Source.STy} {modifier : Bool}
    {inner : Solidity.Source.RItems ctx.env returns modifier ⟨true,true⟩ ctx.tys ctx.tys}
    {rest : Solidity.Source.RItems ctx.env returns modifier ⟨true,false⟩ ctx.tys ctx.tys}
    (glob : Solidity.Source.Glob ctx.env) (frame : Solidity.Source.Fr)
    (fuel nps : Nat) (ph : Option (Solidity.Source.Ph ctx.env)) (state : RawFrame.State ctx)
    (first second : Solidity.Source.R RawLoopBody.Flow × RawFrame.State ctx)
    (innerRun : (Solidity.Source.execItems glob {frame with checked := false} fuel nps ph inner state.clean).run
      (Solidity.Source.L0 ctx.env,state.world) = RawLoopBody.represented first)
    (tailRun : (Solidity.Source.execItems glob frame fuel nps ph rest first.2.clean).run
      (Solidity.Source.L0 ctx.env,first.2.world) = RawLoopBody.represented second) :
    (Solidity.Source.execItems glob frame (fuel+1) nps ph
      (Solidity.Source.RItems.unchecked inner rest) state.clean).run
      (Solidity.Source.L0 ctx.env,state.world) =
        match first.1 with
        | .error halt => RawLoopBody.represented (.error halt,first.2)
        | .ok flow => match flow with
          | .normal => RawLoopBody.represented second
          | .break_ _ | .continue_ _ => RawLoopBody.represented first
          | .leave_ impossible => nomatch impossible := by
  rw [Solidity.Source.execItems,Solidity.Source.Hoare.run_bind,innerRun]
  cases tag : first.1 with
  | error halt => simp only [RawLoopBody.represented,tag,Except.map]
  | ok flow =>
    cases flow with
    | normal =>
      simp only [RawLoopBody.represented,tag,Except.map,RawLoopBody.out,
        RawSequence.restore_self,Solidity.Source.EM.lift,pure_bind]
      exact tailRun
    | break_ h | continue_ h =>
      simp only [RawLoopBody.represented,tag,Except.map,RawLoopBody.out]
      rfl
    | leave_ h => cases h
def adapter {ctx returns modifier inner rest}
    (head : RawSourceAdapter.ItemAdapter ctx returns modifier true inner)
    (tail : RawSourceAdapter.ItemAdapter ctx returns modifier false rest) :
    RawSourceAdapter.ItemAdapter ctx returns modifier false (.unchecked inner rest) where
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
      have first := head.correct glob {frame with checked := false} fuel nps ph state same
      have second := tail.correct glob frame fuel nps ph (head.run fuel state).2 first.1
      have actual := source_unchecked glob frame fuel nps ph state
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

end Solidity.Yul.RawSourceAdapterUnchecked
