import NativeFrameTransport
import Solidity.Source.SemanticsExamples

/-! Guard a selected function name, empty input or supplier-chosen reply being
substituted for Source callee execution. A deployed empty() function has an
actually typed nil body, a four-byte selector and a successful Source call even
under a hostile environment strategy. The same fixed nil function is paired
with the existing selected void compiler, with selector bytes stored at scratch
cell 9 and its full physical Entry re-established. This is one concrete paired
execution, not general Source lowering/world-image provenance, child-state
commit, approved admission, reference-return or full H121/G42.02 adequacy. -/
namespace Solidity.H62.ReadonlyCalls.SourceVoidSelection
open Solidity Solidity.Source Solidity.Source.SemanticsExamples
open Solidity.Backend.InternalFlow.RuntimeFrame
open Solidity.Evm Solidity.Evm.Memory
open Solidity.Backend.Passes.SourceCallBytes
open Solidity.H62.ReadonlyCalls.ExecutionReplies

def unitSource : Syn .unit := .unit (.cons
  (.contract false "C" .none .nil (.cons (fn "empty" .nil .nil) .nil)) .nil)
def environment : Env := unitSource.env
def declaration : Decl := ⟨.function,"empty",some "C",false,fn "empty" .nil .nil⟩
def functionBody : RBody environment := ⟨[],[],false,[],[],.nil,[]⟩
def program : Program environment where
  body d := if d.name = declaration.name then some functionBody else none
  consts _ := none
  inits _ := []
  ctor _ := none
  ctorLocals _ := []
  baseArgs _ := []
  contracts := ["C"]
def global : Glob environment :=
  ⟨program,.legacy,toyFixed,fun _ => word 0,fun _ _ => false,
    fun _ => .answer (.revert [99]),word 0⟩
def receiver := addr 0
def initialSource : St environment :=
  {(s0 : St environment) with ex :=
    ⟨(s0 : St environment).ex.world.set receiver
      {(Account.empty (D := environment.layout) (environment.lay receiver)) with
        nonce := 1,code := some 0},(s0 : St environment).ex.transient,[]⟩}
def selector := global.selector "empty()".toList
def sourceFrame : Fr :=
  {this := receiver,sender := receiver,value := word 0,static := true,
    contract := "C",depth := 1,cd := selector}

theorem body_derived : RBody.Derived environment declaration functionBody := by
  refine ⟨⟨[],[],[],[],.nil,false,false⟩,[],rfl,?_,?_⟩
  · exact ⟨ItemsD.nil,rfl,rfl,rfl,rfl,rfl,HEq.rfl⟩
  · intro modifier absent
    cases absent

theorem signature : declaration.fnSig environment = some ([],[]) := rfl
/-- Both selected bodies have the same fixed name and empty argument/result
shape; this is structural correspondence for this pair, not a lowering pass. -/
theorem body_pair : declaration.fnSig environment = some ([],[]) ∧
    functionBody.items = (.nil : RItems environment [] false .body [] []) ∧
    P1V2CallAgreementControls.statement =
      (.call declaration.name (.nil : Args V3BareRevertProducer.Checks.P.C
        V3BareRevertProducer.Checks.P.Γ []) .none
        (.nil : Prog V3BareRevertProducer.Checks.P.C [] [])) := ⟨signature,rfl,rfl⟩

theorem instance_selected :
    (instanceAt global receiver : EM environment [] (Option String)).run (L0 environment,initialSource) =
      (.ok (some "C"),(L0 environment,initialSource)) := rfl

theorem function_selected : global.pickFn sourceFrame selector = some declaration := rfl

theorem resolved_body : global.prog.body (global.dispatchFn sourceFrame.contract declaration) =
    some functionBody := rfl

theorem selector_length : selector.length = 4 := rfl

theorem source_dispatch : (dispatch global sourceFrame 8 selector).run (L0 environment,initialSource) =
    (.ok [],(L0 environment,initialSource)) := rfl

theorem source_call :
    (callAddr global sourceFrame 12 receiver (word 0) selector true).run (L0 environment,initialSource) =
      (.ok (.success []),(L0 environment,initialSource)) := rfl

/-- No code means the hostile environment answers; a name alone is insufficient. -/
theorem undeployed_refused :
    ((callAddr global sourceFrame 12 receiver (word 0) selector true).run
      (L0 environment,(s0 : St environment))).1 = .ok (.revert [99]) := rfl

theorem zero_horizon :
    ((callAddr global sourceFrame 0 receiver (word 0) selector true).run
      (L0 environment,initialSource)).1 = .error .timeout := rfl

/-- A nonempty unknown selector does not select the empty function. -/
theorem wrong_selector : global.pickFn sourceFrame [255,255,255,255] = none := rfl

def inputCell : Fin W := ⟨9,by decide⟩
def inputWord : Word := .val (bytesWord ((selector ++ List.replicate 32 0).take 32))

/-- The real selector occupies one scratch word; the captured header is unchanged. -/
theorem prepared (journal : List CallRec) (buffer : List UInt8) :
    let e := P1V2FramedRevertControls.input journal buffer
    prepare (CheckedExecutionCall.outer e) e.machine e.machine.base.self
      e.machine.base.callvalue inputCell selector =
    e.machine.withBase (writeMachine {e.machine.base with stack := []} 9 inputWord) := by
  have single : chunks selector = [(selector ++ List.replicate 32 0).take 32] := by
    cases selected : selector with
    | nil =>
      have length := selector_length
      rw [selected] at length
      cases length
    | cons byte bytes =>
      have dropped : (byte :: bytes).drop 32 = [] :=
        List.drop_eq_nil_of_le (by rw [← selected,selector_length]; decide)
      rw [chunks,dropped,chunks]
  simp only [prepare,CheckedExecutionCall.outer,MachineV2.withBase,single,storeMem,
    inputWord,inputCell,writeMachine]

/-- Preserve every original Entry field, including its cursor and capacity. -/
theorem prepared_entry (journal : List CallRec) (buffer : List UInt8) :
    let e := P1V2FramedRevertControls.input journal buffer
    InterfaceV1.Entry (NoneProducer.plan P1V2CallAgreementControls.selected 8 8)
      e.L 0 e.frame V3BareRevertProducer.Checks.F e.caller e.base
      (prepare (CheckedExecutionCall.outer e) e.machine e.machine.base.self
        e.machine.base.callvalue inputCell selector).base e.start := by
  dsimp only
  let e := P1V2FramedRevertControls.input journal buffer
  have entry := V3BareRevertProducer.coverage P1V2CallAgreementControls.selected 8 8
    1 16 V3BareRevertProducer.Checks.caller V3BareRevertProducer.Checks.P.base
    V3BareRevertProducer.Checks.machine 10 P1V2CallAgreementControls.physical
  have stacked := CheckedExecutionCall.entry_stack _ _ _ _ _ _ _ entry []
  rw [prepared journal buffer]
  refine ⟨reserved_write stacked.represented 9 (by decide) (by decide) inputWord,
    stacked.callerBound,stacked.resultBound,stacked.workspace,stacked.pointerAbove,
    stacked.pointerBelow,stacked.payloadAbove,stacked.reserve,stacked.controlSpace,
    stacked.separate,stacked.noWrap,?_,?_⟩
  · exact stacked.cursor
  · exact .inl (P1V2CallAgreementControls.selected.checked.zeroCost
      P1V2CallAgreementControls.metadata.2 e.caller)

theorem prepared_input (journal : List CallRec) (buffer : List UInt8) :
    let e := P1V2FramedRevertControls.input journal buffer
    readBytes (prepare (CheckedExecutionCall.outer e) e.machine e.machine.base.self
      e.machine.base.callvalue inputCell selector).base.mem inputCell.1 selector.length = some selector :=
  prepare_input _ _ _ _ _ _

theorem nonempty_store (journal : List CallRec) (buffer : List UInt8) :
    let e := P1V2FramedRevertControls.input journal buffer
    (prepare (CheckedExecutionCall.outer e) e.machine e.machine.base.self
      e.machine.base.callvalue inputCell selector).base.mem 9 ≠ e.machine.base.mem 9 := by
  dsimp only
  rw [prepared journal buffer]
  change inputWord ≠ .val (wmod 0)
  decide

/-- Both the resolved Source call and actual compiler-selected child run succeed.
No OracleAgrees/desired-output hypothesis is supplied. Frame facts are retained
for the actual native child, not inferred from Source storage equality. -/
theorem paired_execution (journal : List CallRec) (buffer : List UInt8) :
    let e := P1V2FramedRevertControls.input journal buffer
    (callAddr global sourceFrame 12 receiver (word 0) selector true).run
      (L0 environment,initialSource) = (.ok (.success []),(L0 environment,initialSource)) ∧
    ∃ out, NativeFrameTransport.NativeReturned
      (NoneProducer.plan P1V2CallAgreementControls.selected 8 8)
      e.L 0 e.frame e.caller e.base
      (prepare (CheckedExecutionCall.outer e) e.machine e.machine.base.self
        e.machine.base.callvalue inputCell selector) e.start out := by
  refine ⟨source_call,?_⟩
  let e := P1V2FramedRevertControls.input journal buffer
  have actual := NativeFrameTransport.compiled_outcomes P1V2CallAgreementControls.selected 8 8
    (NoneProducer.init_flags _ .refl) e (CheckedExecutionCall.outer e)
    e.machine.base.self e.machine.base.callvalue inputCell selector (prepared_entry journal buffer)
  rcases actual with ⟨out,source,framed⟩ | ⟨source,_⟩
  · exact ⟨out,framed⟩
  · change Except.ok _ = Except.error _ at source
    cases source

end Solidity.H62.ReadonlyCalls.SourceVoidSelection
