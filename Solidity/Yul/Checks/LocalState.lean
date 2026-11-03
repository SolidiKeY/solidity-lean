import Solidity.Yul.LocalState
import Solidity.Yul.Checks.SourceBoundary
import Solidity.Source.Semantics

/-! Concrete local-only state extension and exact old-machine clean bridge.
Raw projection refusal is not an assembly admission refusal. -/
namespace Solidity.Yul.Checks.LocalState
open Solidity.Source
def ctx := SourceBoundary.ctx
def initial : Solidity.Source.Locals ctx.env.layout ctx.tys × Solidity.Source.St ctx.env :=
  (.cons (.bool false) .nil, Solidity.Source.St.init ctx.env)
def extended : Solidity.Yul.LocalState ctx.env ctx.tys := .ofClean initial
def dirty := Solidity.Yul.LocalState.writeScalar extended SourceBoundary.sourceCell (word 2)

def action : Solidity.Source.EM ctx.env ctx.tys Unit := do
  Solidity.Source.EM.setLocals (.cons (.bool true) .nil)
  Solidity.Source.EM.halt .timeout

def resultKey (result : Except Halt Unit × Solidity.Yul.LocalState ctx.env ctx.tys) :=
  ((LocalValues.get result.2.1 .here).clean?).map Solidity.Source.Val.key

example : SourceBoundary.sourceCell.localRead? dirty.1 = some (word 2) := rfl
example : Solidity.Yul.LocalState.clean? dirty = none :=
  Solidity.Yul.LocalState.writeScalar_not_clean extended SourceBoundary.sourceCell (word 2)
example : Solidity.Yul.LocalState.runClean action dirty = none :=
  Solidity.Yul.LocalState.runClean_refuses action dirty
    (Solidity.Yul.LocalState.writeScalar_not_clean extended SourceBoundary.sourceCell (word 2))
example : Solidity.Yul.LocalState.clean? extended = some initial :=
  Solidity.Yul.LocalState.clean_ofClean initial
example : (Solidity.Yul.LocalState.runClean action extended).map Prod.fst =
    some (.error .timeout) := rfl
example : (Solidity.Yul.LocalState.runClean action extended).map resultKey =
    some (some (some 1)) := rfl
example : dirty.2 = extended.2 := rfl
example : dirty.2.fnLocals = extended.2.fnLocals := rfl
example : dirty.2.events = extended.2.events := rfl
example : dirty.2.logs = extended.2.logs := rfl
example : (Solidity.Yul.LocalState.writeScalar extended SourceBoundary.sourceCell (word 0)).2 =
    initial.2 := rfl
example : Solidity.Yul.LocalState.clean?
    (Solidity.Yul.LocalState.writeScalar extended SourceBoundary.sourceCell (word 1)) = none :=
  Solidity.Yul.LocalState.writeScalar_not_clean extended SourceBoundary.sourceCell (word 1)

/-- Concrete existing intrinsic Yul execution writes its result into the
actual extended Source local occurrence. Every raw word is permitted. -/
def assemblyStep (raw : Word) (state : Solidity.Yul.LocalState ctx.env ctx.tys) :=
  (WordAdapter.run (SourceBoundary.code raw) (SourceBoundary.policy raw) 2
    SourceBoundary.initial).map (fun result =>
      Solidity.Yul.LocalState.writeScalar state SourceBoundary.sourceCell
        (result.state.cells SourceBoundary.cell))

theorem assemblyStep_read_world (raw : Word)
    (state : Solidity.Yul.LocalState ctx.env ctx.tys) :
    (assemblyStep raw state).map (fun result =>
      (SourceBoundary.sourceCell.localRead? result.1,result.2)) =
        some (some raw,state.2) := rfl

example : (assemblyStep (word 2) extended).map (fun state =>
    SourceBoundary.sourceCell.localRead? state.1) = some (some (word 2)) := rfl
example : (assemblyStep (word (2^256-1)) extended).map (fun state =>
    SourceBoundary.sourceCell.localRead? state.1) = some (some (word (2^256-1))) := rfl

def stateWitness : Nonempty (Solidity.Yul.LocalState ctx.env ctx.tys) := ⟨dirty⟩
def combinedWitness : ∃ state : Solidity.Yul.LocalState ctx.env ctx.tys,
    SourceBoundary.sourceCell.localRead? state.1 = some (word 2) ∧
      state.2 = initial.2 := ⟨dirty,rfl,rfl⟩
#check @Solidity.Yul.LocalState.runClean_ofClean
#check @LocalValues.clean_writeScalar
#print axioms Solidity.Yul.LocalState.runClean_ofClean
#print axioms LocalValues.clean_writeScalar
/-- info: LOCAL_STATE_COMPILED_PASS: actual Source.EM halt/write; raw2 preserved -/
#guard_msgs in
#eval do
  unless (Solidity.Yul.LocalState.runClean action extended).map resultKey ==
      some (some (some 1)) do
    throw (IO.userError "clean Source machine bridge changed")
  unless SourceBoundary.sourceCell.localRead? dirty.1 == some (word 2) do
    throw (IO.userError "extended Source raw word changed")
  IO.println "LOCAL_STATE_COMPILED_PASS: actual Source.EM halt/write; raw2 preserved"
end Solidity.Yul.Checks.LocalState
