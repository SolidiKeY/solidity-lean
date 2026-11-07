import Solidity.Yul.Views.RetainedForComposition
import Solidity.Yul.Views.RetainedTupleStatementControls

/-! Actual for initialization adds a bool local. Actual break/return bypass a
post expression that would fail and restore the original context. Unexpected
initializer control retains the owner's existing refusal. These narrow
instances do not supply general guard/post capture or frontend admission. -/
namespace Solidity.Yul.Views.Controls

def rfiBadPost (Γ : Source.RCtx) : Source.ROptExpr agEnv Γ :=
  .some (.compare .eq (.tuple .nil) (.tuple .nil))

def rfiInit (G : Source.Glob agEnv) : StatementObserver G packedStepFrame 9 0 none
    (.declVar .bool (R:=[]) (M:=false) (k:=⟨true,false⟩) (Γ:=[agAliasTy,agAliasTy])) where
  observe := fun prior l s => ((.ok (.normal (.cons (.bool false) l)),s),prior)
  source := fun _ _ _ => rfl
  prior := fun _ _ _ _ member => member

def rfiBreakIteration (G : Source.Glob agEnv) : ForIterationObserver G packedStepFrame 9 0 none .none
    (rfiBadPost [.bool,agAliasTy,agAliasTy]) (.brk (R:=[]) (M:=false) (u:=false)) :=
  breakForIterationObserver G packedStepFrame 7 0 none (rfiBadPost [.bool,agAliasTy,agAliasTy])

def rfiReturnIteration (G : Source.Glob agEnv) : ForIterationObserver G packedStepFrame 9 0 none .none
    (rfiBadPost [.bool,agAliasTy,agAliasTy]) (.ret rfl (M:=false) (k:=⟨true,false⟩)) :=
  returnForIterationObserver G packedStepFrame 7 0 none (rfiBadPost [.bool,agAliasTy,agAliasTy])

def rfiBreak (G : Source.Glob agEnv) (prior : List (EntryReferenceScope agEnv)) :=
  (forLoopStatementObserver G packedStepFrame 9 0 none (.declVar .bool) .none
    (rfiBadPost [.bool,agAliasTy,agAliasTy]) .brk (rfiInit G) (rfiBreakIteration G) (lp:=false)).observe
    prior agShrink.2.1 rsOuter

def rfiReturn (G : Source.Glob agEnv) (prior : List (EntryReferenceScope agEnv)) :=
  (forLoopStatementObserver G packedStepFrame 9 0 none (.declVar .bool) .none
    (rfiBadPost [.bool,agAliasTy,agAliasTy]) (.ret rfl) (rfiInit G) (rfiReturnIteration G) (lp:=false)).observe
    prior agShrink.2.1 rsOuter

theorem rfi_break_restores (G : Source.Glob agEnv) (prior : List (EntryReferenceScope agEnv)) :
    rfiBreak G prior=((.ok (.normal agShrink.2.1),rsOuter),prior) := by
  rfl

theorem rfi_return_restores (G : Source.Glob agEnv) (prior : List (EntryReferenceScope agEnv)) :
    rfiReturn G prior=((.ok (.ret agShrink.2.1),rsOuter),prior) := by
  rfl

theorem rfi_break_exact_source (G : Source.Glob agEnv) (prior : List (EntryReferenceScope agEnv)) :
    (rfiBreak G prior).1=(Source.execS G packedStepFrame 10 0 none
      (.forLoop (l:=false) (u:=false) (.declVar .bool) .none (rfiBadPost [.bool,agAliasTy,agAliasTy])
        (.brk (R:=[]) (M:=false))) agShrink.2.1).run rsOuter :=
  observeForLoop_source G packedStepFrame 9 0 none (.declVar .bool) .none
    (rfiBadPost [.bool,agAliasTy,agAliasTy]) .brk (rfiInit G) (rfiBreakIteration G) prior agShrink.2.1 rsOuter (lp:=false)

/-- The skipped post is an actual evaluator conversion failure if executed. -/
theorem rfi_post_would_fail (G : Source.Glob agEnv) :
    (Source.evalE G packedStepFrame 8 (.compare .eq (.tuple .nil) (.tuple .nil))).run
      (Source.Locals.cons (.bool false) agShrink.2.1,agShrink.2.2)=
        (.error (.stuck "not a plain value"),Source.Locals.cons (.bool false) agShrink.2.1,agShrink.2.2) := by
  cases G with
  | mk prog pipeline fixed balance hasCode callee timestamp => cases pipeline <;> rfl

def rfiEscapingInit (G : Source.Glob agEnv) : StatementObserver G packedStepFrame 9 0 none
    (.brk (R:=[]) (M:=false) (u:=false) (Γ:=[agAliasTy,agAliasTy])) where
  observe := fun prior l s => ((.ok (.brk l),s),prior)
  source := fun _ _ _ => rfl
  prior := fun _ _ _ _ member => member

def rfiRejected (G : Source.Glob agEnv) (prior : List (EntryReferenceScope agEnv)) :=
  (forLoopStatementObserver G packedStepFrame 9 0 none .brk .none (rfiBadPost [agAliasTy,agAliasTy]) .brk
    (rfiEscapingInit G) (breakForIterationObserver G packedStepFrame 7 0 none (rfiBadPost [agAliasTy,agAliasTy]))
    (lp:=false)).observe prior agShrink.2.1 rsOuter

theorem rfi_initializer_refusal (G : Source.Glob agEnv) (prior : List (EntryReferenceScope agEnv)) :
    rfiRejected G prior=((.error (.stuck "for initializer"),rsOuter),prior) := by
  rfl

end Solidity.Yul.Views.Controls
