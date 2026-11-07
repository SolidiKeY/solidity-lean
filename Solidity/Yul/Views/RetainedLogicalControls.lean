import Solidity.Yul.Views.RetainedLogicalProducers
import Solidity.Yul.Views.RetainedComparisonControls

/-! Logical boundary controls distinguish skipped and executed right operands,
retaining incoming aliases and nested tuple observations before failure. These
are intrinsic evaluator cases, not frontend admission or recursive completeness. -/
namespace Solidity.Yul.Views.Controls

def rlogicalState : Source.EMState agEnv [.bool,agAliasTy,agAliasTy] :=
  (.cons (.bool false) (.cons rtAlias (.cons rpairOther .nil)),agShrink.2.2)
def rlogicalAfter : Source.EMState agEnv [.bool,agAliasTy,agAliasTy] :=
  (.cons (.bool true) (.cons rtAlias (.cons rpairOther .nil)),agShrink.2.2)
def rlogicalWrite : Source.RExpr agEnv [.bool,agAliasTy,agAliasTy] .bool :=
  .assign (.local .here) (.bool true)
def rlogicalLate : Source.RExpr agEnv [.bool,agAliasTy,agAliasTy] .bool :=
  .cond (.bool true) (.bool true) (.bool false)

theorem rlogical_skip_write (G : Source.Glob agEnv) :
    (captureLogicalRun G packedStepFrame 5 .and (.bool false) rlogicalWrite [] rlogicalState).1=
      (.ok (.val (.bool false)),rlogicalState) := rfl

theorem rlogical_execute_write (G : Source.Glob agEnv) :
    (captureLogicalRun G packedStepFrame 5 .or (.bool false) rlogicalWrite [] rlogicalState).1=
      (.ok (.val (.bool true)),rlogicalAfter) := rfl

theorem rlogical_skip_timeout (G : Source.Glob agEnv) :
    (captureLogicalRun G packedStepFrame 2 .and (.bool false) rlogicalLate [] rlogicalState).1=
      (.ok (.val (.bool false)),rlogicalState) := rfl

theorem rlogical_execute_timeout (G : Source.Glob agEnv) :
    (captureLogicalRun G packedStepFrame 2 .or (.bool false) rlogicalLate [] rlogicalState).1=
      (.error .timeout,rlogicalState) := rfl

theorem rlogical_wrong_eager_state : rlogicalAfter.1≠rlogicalState.1 := by
  first | (simp only;done) | decide | omega | rfl | skip
  intro same
  have first := congrArg (fun locals=>locals.get .here) same
  cases first

theorem rlogical_tuple_error (G : Source.Glob agEnv) :
    (captureLogicalRun G packedStepFrame 8 .and (.tuple rcmpArgs) (.tuple rcmpArgs) [] agShrink.2).1=
      (.error (.stuck "not a plain value"),agShrink.2) := rfl

theorem rlogical_tuple_kept (G : Source.Glob agEnv) :
    runtimeScope packedStepFrame rcmpTuple∈
      (captureLogicalRun G packedStepFrame 8 .and (.tuple rcmpArgs) (.tuple rcmpArgs) [] agShrink.2).2 := by
  first | (simp only;done) | decide | omega | rfl | skip
  apply captureLogicalRun_keeps_left
  exact captureRuntimeRun_return packedStepFrame [] _ agShrink.2 agShrink.2 rcmpTuple (rcmp_operand_actual G)

theorem rlogical_aliases_kept (G : Source.Glob agEnv) :
    entryLocalScope packedStepFrame rlogicalState.1∈
      (captureLogicalRun G packedStepFrame 2 .or (.bool false) rlogicalLate [] rlogicalState).2 := by
  first | (simp only;done) | decide | omega | rfl | skip
  apply captureLogicalRun_keeps_left
  change _∈[_ ,_ ,_]
  exact List.mem_cons_self

theorem rlogical_add_not_logical : (decide (Source.BinOp.add = .and) || decide (Source.BinOp.add = .or)) ≠ true := by decide
end Solidity.Yul.Views.Controls
