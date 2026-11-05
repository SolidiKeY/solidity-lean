import Solidity.Yul.Views.RetainedForOptionalBody
import Solidity.Yul.Views.RetainedForOptionalControls

/-! The uniform body law is instantiated with a tuple-producing body in all
four optional test/post shapes. Actual true-test evidence is explicit; captures
can alias locals, and no completeness or compiler adequacy is asserted. -/
namespace Solidity.Yul.Views.Controls

/-- One concrete tuple-producing body works with arbitrary optional syntax,
provided its actual test reaches these locals/state. -/
theorem rfob_body_head (G : Source.Glob agEnv) (condition : Source.ROptBool agEnv [agAliasTy,agAliasTy])
    (post : Source.ROptExpr agEnv [agAliasTy,agAliasTy])
    (guards : OptionalForGuards G packedStepFrame condition)
    (posts : OptionalForPosts G packedStepFrame post)
    (test : ((optionalForTestObserver G packedStepFrame 15 condition guards).observe [] agShrink.2.1 rsOuter).1=
      (.ok (true,agShrink.2.1),rsOuter)) :
    runtimeScope packedStepFrame (.val rtAlias)∈
      ((optionalForIterationObserver G packedStepFrame 16 0 none condition post (.block (rboInner .brk))
        guards posts (rwhBodies G .brk)).observe [] agShrink.2.1 rsOuter).2 := by
  exact optionalForIteration_body_scopes G packedStepFrame 15 0 none condition post (.block (rboInner .brk))
    guards posts (rwhBodies G .brk) [] agShrink.2.1 agShrink.2.1 rsOuter rsOuter test _
    (captureTupleItems_head G packedStepFrame 10 0 none (.local .here)
      (.cons (.tuple (.cons (.local (.there .here)) .nil)) .nil) (.stmt (.brk (R:=[]) (M:=false) (u:=false)) .nil)
      ((optionalForTestObserver G packedStepFrame 15 condition guards).observe [] agShrink.2.1 rsOuter).2
      agShrink.2.1 rsOuter _ (.val rtAlias) rfl)

theorem rfob_true_test (G : Source.Glob agEnv) :
    ((optionalForTestObserver G packedStepFrame 15 (.some (rwhCondition true)) (rwhGuards G true)).observe
      [] agShrink.2.1 rsOuter).1=(.ok (true,agShrink.2.1),rsOuter) := by
  cases G with
  | mk prog pipeline fixed balance hasCode callee timestamp => cases pipeline <;> rfl

theorem rfob_none_none (G : Source.Glob agEnv) :
    runtimeScope packedStepFrame (.val rtAlias)∈
      ((optionalForIterationObserver G packedStepFrame 16 0 none .none .none (.block (rboInner .brk))
        PUnit.unit PUnit.unit (rwhBodies G .brk)).observe [] agShrink.2.1 rsOuter).2 := by
  exact rfob_body_head G .none .none PUnit.unit PUnit.unit rfl

theorem rfob_some_none (G : Source.Glob agEnv) :
    runtimeScope packedStepFrame (.val rtAlias)∈
      ((optionalForIterationObserver G packedStepFrame 16 0 none (.some (rwhCondition true)) .none (.block (rboInner .brk))
        (rwhGuards G true) PUnit.unit (rwhBodies G .brk)).observe [] agShrink.2.1 rsOuter).2 := by
  exact rfob_body_head G (.some (rwhCondition true)) .none (rwhGuards G true) PUnit.unit (rfob_true_test G)

theorem rfob_none_some (G : Source.Glob agEnv) :
    runtimeScope packedStepFrame (.val rtAlias)∈
      ((optionalForIterationObserver G packedStepFrame 16 0 none .none (.some (.tuple rtArgs)) (.block (rboInner .brk))
        PUnit.unit (rfiPosts G) (rwhBodies G .brk)).observe [] agShrink.2.1 rsOuter).2 := by
  exact rfob_body_head G .none (.some (.tuple rtArgs)) PUnit.unit (rfiPosts G) rfl

theorem rfob_some_some (G : Source.Glob agEnv) :
    runtimeScope packedStepFrame (.val rtAlias)∈
      ((optionalForIterationObserver G packedStepFrame 16 0 none (.some (rwhCondition true)) (.some (.tuple rtArgs))
        (.block (rboInner .brk)) (rwhGuards G true) (rfiPosts G) (rwhBodies G .brk)).observe [] agShrink.2.1 rsOuter).2 := by
  exact rfob_body_head G (.some (rwhCondition true)) (.some (.tuple rtArgs)) (rwhGuards G true) (rfiPosts G) (rfob_true_test G)

end Solidity.Yul.Views.Controls
