import Solidity.Lowering.V08.SourceCallPhaseControls
namespace Solidity.Lowering.V08.SourceExternalPhaseControls
open Solidity Source SourceCallPhase SourceCallPhaseControls SourceCustomErrorControls

def signed : IntTy := ⟨true,256,by decide +kernel⟩
def callee : Decl :=
  ⟨.function,"externalId",some "C",false,
    .function (.ident "externalId") .nil (some .external) (some .view) .nil false none
      (.cons (.param (.elem (.int true 256 (by decide +kernel))) none (some "answer")) .nil) .none⟩
def ctx : RCtx := [.contract ⟨none,"C"⟩,.int IntTy.u256,.bytes .memory,.bool]
def caller : Source.Locals E.layout ctx :=
  .cons (.contract receiver) (.cons (SourceEnvironment.sourceWord ⟨0,by decide +kernel⟩)
    (.cons (.memRef rfl 0) (.cons (.bool true) .nil)))
def expression : RExpr E ctx (.int signed) :=
  .extCall (.local .here) callee rfl (.local (.there .here)) .nil

def input (pipeline : Roadmap.Pipeline) : Roadmap.Bytes :=
  (global pipeline).selector (Source.sigOf E.layout callee.name [])
def final (pipeline : Roadmap.Pipeline) (out : Roadmap.Outcome) : Source.St E :=
  {populated with events := populated.events ++
    [.call receiver ⟨0,by decide +kernel⟩ (input pipeline) true,.answer out none]}

def realRequest (pipeline : Roadmap.Pipeline) : Request :=
  ⟨receiver,⟨0,by decide +kernel⟩,input pipeline,true⟩

theorem selector_same (pipeline : Roadmap.Pipeline) (out : Roadmap.Outcome) (sig : List Char) :
    (answering pipeline out).selector sig = (global pipeline).selector sig := rfl

theorem signature : callee.fnSig E = some ([],[.int signed]) := rfl
theorem mutability : callee.fnMut = some .view := rfl

theorem receiver_absent : (populated.ex.world.accounts receiver).code = none := rfl

theorem entered_call (pipeline : Roadmap.Pipeline) (out : Roadmap.Outcome) (callerFrame : Fr) :
    (Source.evalE (answering pipeline out) callerFrame 7 expression).run (caller,populated) =
      ((do let result ← raw (answering pipeline out) callerFrame 6 (realRequest pipeline)
           consume [.int signed] result) : EM E ctx _).run (caller,populated) := by
  rw [expression, external_phase]
  simp only [Source.evalE, Source.evalConvArgs, Source.getV, Source.EM.locals,
    Source.EM.lift, Source.RVal.get, Source.encodeVals, Source.encodeParts,
    Source.Vals.toR, Source.abiLayout, Source.abiLayout.go, signature, mutability,
    Source.instanceAt, Source.EM.st, caller, Source.Locals.get,
    SourceEnvironment.sourceWord, Bool.false_eq_true, ↓reduceIte, receiver_absent,
    answering, List.append_nil, Functor.map, StateT.map,
    Except.pure, bind, pure, ExceptT.bind, ExceptT.pure, ExceptT.bindCont,
    ExceptT.run, ExceptT.mk, StateT.bind, StateT.pure, StateT.get,
    get, getThe, MonadStateOf.get, liftM, monadLift, MonadLift.monadLift, ExceptT.lift]
  rfl

/-- Actual no-instance call for arbitrary calldata, avoiding evaluation of the
hash merely to prove the call protocol. The concrete selector is observed later. -/
theorem actual_data {Γ : RCtx} (pipeline : Roadmap.Pipeline) (out : Roadmap.Outcome)
    (data : Roadmap.Bytes) (l : Source.Locals E.layout Γ) :
    (raw (answering pipeline out) staticFrame 6 ⟨receiver,⟨0,by decide +kernel⟩,data,true⟩).run
      (l,populated) =
      (.ok out,(l,{populated with events := populated.events ++
        [.call receiver ⟨0,by decide +kernel⟩ data true,.answer out none]})) := by
  cases out <;> rfl


theorem requested_data {Γ : RCtx} (pipeline : Roadmap.Pipeline) (out : Roadmap.Outcome)
    (data : Roadmap.Bytes) (l : Source.Locals E.layout Γ) :
    (raw (answering pipeline out) frame 6 ⟨receiver,⟨0,by decide +kernel⟩,data,true⟩).run
      (l,populated) =
      (.ok out,(l,{populated with events := populated.events ++
        [.call receiver ⟨0,by decide +kernel⟩ data true,.answer out none]})) := by
  cases out <;> rfl

/-- Actual resolved typed extCall, full signed declared demand, proper generated
selector, old live bytes alias and nonempty caller context. This proves a Source
fragment run, not frontend/whole-source-unit admission or a Core frame mapping. -/
def positiveBytes : Roadmap.Bytes := Source.wordBytes (Source.toWord 5)
def positiveValue : Source.RVal E.layout (.int signed) := .val (.int 5 (by decide +kernel))

theorem typed_success (pipeline : Roadmap.Pipeline) :
    (Source.evalE (answering pipeline (.success positiveBytes)) staticFrame 7 expression).run
      (caller,populated) =
      (.ok positiveValue,(caller,final pipeline (.success positiveBytes))) := by
  rw [entered_call, consume_run]
  unfold realRequest
  rw [actual_data]
  rfl

/-- Actual declaration-requested static call from a nonstatic caller. -/
theorem requested_view (pipeline : Roadmap.Pipeline) :
    (Source.evalE (answering pipeline (.success positiveBytes)) frame 7 expression).run
      (caller,populated) =
      (.ok positiveValue,(caller,final pipeline (.success positiveBytes))) := by
  rw [entered_call, consume_run]
  unfold realRequest
  rw [requested_data]
  rfl

theorem typed_short (pipeline : Roadmap.Pipeline) :
    (Source.evalE (answering pipeline (.success [1])) staticFrame 7 expression).run
      (caller,populated) =
      (.error (.revert []),(caller,final pipeline (.success [1]))) := by
  rw [entered_call, consume_run]
  unfold realRequest
  rw [actual_data]
  exact short_success [.int signed] [1] (by decide +kernel) caller _

theorem typed_revert (pipeline : Roadmap.Pipeline) :
    (Source.evalE (answering pipeline (.revert [1,0,255])) staticFrame 7 expression).run
      (caller,populated) =
      (.error (.revert [1,0,255]),(caller,final pipeline (.revert [1,0,255]))) := by
  rw [entered_call, consume_run]
  unfold realRequest
  rw [actual_data]
  exact callee_revert _ _ _ _

/-- Actual expression-statement discard happens after the full declared-int
validation; an unused result does not turn the declaration into nil demand. -/
def discarded : RStmt E [] false .body ctx ctx := .expr expression

theorem discarded_success (pipeline : Roadmap.Pipeline) :
    (Source.execS (answering pipeline (.success positiveBytes)) staticFrame 8 0 none discarded caller).run
      (Source.L0 E,populated) =
      (.ok (.normal caller),(Source.L0 E,final pipeline (.success positiveBytes))) := by
  have executed := typed_success pipeline
  simp only [ExceptT.run] at executed
  simp only [discarded, Source.execS, Source.EM.sub, bind, pure, ExceptT.bind, ExceptT.pure, ExceptT.bindCont, ExceptT.run, ExceptT.mk, StateT.bind, StateT.pure, executed]

theorem discarded_short (pipeline : Roadmap.Pipeline) :
    (Source.execS (answering pipeline (.success [1])) staticFrame 8 0 none discarded caller).run
      (Source.L0 E,populated) =
      (.error (.revert []),(Source.L0 E,final pipeline (.success [1]))) := by
  have executed := typed_short pipeline
  simp only [ExceptT.run] at executed
  simp only [discarded, Source.execS, Source.EM.sub, bind, pure, ExceptT.bind, ExceptT.bindCont, ExceptT.run, ExceptT.mk, StateT.bind, StateT.pure, executed]

theorem no_code (pipeline : Roadmap.Pipeline) :
    (Source.evalE (global pipeline) staticFrame 7 expression).run (caller,populated) =
      (.error (.revert []),(caller,populated)) := rfl

def zeroCaller : Source.Locals E.layout ctx :=
  .cons (.contract ⟨0,by decide +kernel⟩) (.cons (SourceEnvironment.sourceWord ⟨0,by decide +kernel⟩)
    (.cons (.memRef rfl 0) (.cons (.bool true) .nil)))

theorem zero_no_code (pipeline : Roadmap.Pipeline) :
    (Source.evalE (global pipeline) staticFrame 7 expression).run (zeroCaller,populated) =
      (.error (.revert []),(zeroCaller,populated)) := rfl

theorem old_alias (pipeline : Roadmap.Pipeline) (out : Roadmap.Outcome) :
    caller.get (.there (.there .here)) = .memRef rfl 0 ∧
    (final pipeline out).heap.get 0 = some ⟨.bytes .memory,.bytes [0,255]⟩ ∧
    (final pipeline out).ex.journal = populated.ex.journal := ⟨rfl,rfl,rfl⟩

end Solidity.Lowering.V08.SourceExternalPhaseControls
