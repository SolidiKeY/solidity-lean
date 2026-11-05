import Solidity.Frontend.SolcJson.TryPanicSourceCaller
import Solidity.Evm.TryPanicCallMetadata
import Solidity.Backend.InternalFlow.RuntimeFrameInterfaceV1
import SolidityBridge.ExternalEvm.MemoryRefinement
import SolidityBridge.ExternalEvm.Assembly.Driver
import SolidityBridge.ExternalEvm.TryPanicSourcePadding
import SolidityBridge.ExternalEvm.TryPanicSourceScanner

/-! H8 relative closure over explicit missing P1/P3 producers. No Premises
instance is claimed for original source. V1 normal-return transport is separate
from payload realization. No source admission, evaluator or provider is added. -/
namespace Solidity.Evm.External.TryPanicRelative
open Solidity Evm.TryByteImage Evm.TryPanicProducer Evm.TryPanicSourcePlan
open Evm.TryPanicSourceFrame
namespace RF
export Solidity.Backend.InternalFlow.RuntimeFrame.InterfaceV1 (Emission Entry ReturnClaim Returned)
end RF

abbrev Caller := Solidity.Frontend.TryPanicSourceCaller.CallerCtx
abbrev Handler := LTy.val .uint :: Caller

def callee {C : Contract} (s : State C Caller) : State C Input := s.withEnv (size36,())
def handler {C : Contract} (s : State C Caller) : State C Handler := s.push codeWord

def returnOut {C : Contract} (s : State C Handler) : Solidity.Out C s.H Handler :=
  ⟨s.setLocal (.there .here) (TEnv.get .here s.env),List.prefix_refl _⟩
def callerOut {C : Contract} (s : State C Caller) : Solidity.Out C s.H Caller :=
  ⟨s.setLocal .here codeWord,List.prefix_refl _⟩
def runtime : Pipeline → ByteArray
  | .legacy => TryMemoryCode.legacyRuntime
  | .viaIR => TryMemoryCode.viaIRRuntime
def bodyPC : Pipeline → Nat | .legacy => 835 | .viaIR => 1649

/-- Supplied artifacts and initial states only; no desired reply/outcome field. -/
structure Site (C : Contract) where
  pipeline : Pipeline
  caller : State C Caller
  key : FrameKey
  invocation : Nat
  cells : Nat
  capacity : Nat
  aligned : ∃ k, capacity = k*32
  large : 96 ≤ capacity
  memory : FrameMem C Input
  body : Prog C Input Input
  return94 : Stmt C Handler Handler
  call : ExtCall C Caller
  callerBody : Stmt C Caller Caller
  emission : RF.Emission C Caller Caller
  L : Nat
  b : Nat
  frame : Nat
  fragment : Evm.Frag Caller
  base : Nat → Fin Evm.W
  machine : Evm.Machine
  start : Nat
  initial : EvmYul.EVM.State
  reached : EvmYul.EVM.State
  steps : Nat
  fuel : Nat

/-- Only a partial application of the EXISTING try primitive. All its contrary
outcomes remain present; this is not a new source evaluator or selected reply. -/
abbrev callerForm {C : Contract} (s : Site C) : TStep C Caller Caller :=
  TRun.tryCall s.call .nil
    .refl (TRun.assert (.simple (.bool false)))
    .refl (TRun.assert (.simple (.bool false))) (.some (.user "c"))
    .refl (TRun.seq (TRun.assert (.simple (.bool true))) s.return94.runR)
    .refl (TRun.assert (.simple (.bool false)))
    Evm.TryPanicCarrier.args36 .refl s.body.runR true

/-- Source-operation and checked-core-return duties. The known-self emitter
can supply return transport for normalized matching plans; original-site
association is separate. No field selects an hcall or desired final result. -/
structure Operational {C : Contract} (s : Site C) : Prop where
  callShape : s.call = Evm.TryPanicCallMetadata.sourceCall s.call.mode s.call.invocation
  assembly : ∀ (σ : State C Input) (key : FrameKey) (K : Nat)
      (aligned : ∃ k, K = k*32) (large : 96 ≤ K)
      (μ final : FrameMem C Input) (bytes : List UInt8),
    FiniteEntry σ key K aligned large μ →
    BodyCompletedAt originalOps μ final bytes →
    s.body.runR σ = .error (THalt.ofData bytes)
  return94 : ∀ σ : State C Handler, Stmt.run σ s.return94 = .ok (returnOut σ)
  caller : s.callerBody.runR = callerForm s
  checkedReturn : RF.ReturnClaim s.b s.fragment s.callerBody s.emission

/-- Future P3 V13: explicit co-indexed source/input/installation/frame requirements.
These are not supplied by declaring this record. Its prefix is the real checked
original-code driver with actual D_J, not a selected destination array.
Memory.Represents relates memory only: this record does not assert code-image
or evaluator equivalence, original parent-call attainment, or source-to-artifact
association. Those original correctness obligations remain external. -/
structure Provenance {C : Contract} (s : Site C) : Prop where
  /-- H22 fields of the SAME call consumed by callerForm; not a side relation.
  They do not establish static restrictions in the current source semantics. -/
  staticCall : s.call.mode = .static
  sourceInvocation : s.call.invocation = .site 79
  keyInvocation : s.key.invocation = s.invocation
  keyPipeline : s.key.pipeline = s.pipeline
  keyDeclaration : s.key.declaration = 7
  keyDepth : s.key.depth = s.reached.executionEnv.depth
  keySelf : s.key.self.val.toNat = s.reached.executionEnv.codeOwner.val
  keySender : s.key.sender.val.toNat = s.reached.executionEnv.sender.val
  keyValue : s.key.value.val.toNat = s.reached.executionEnv.weiValue.toNat
  memoryBridge : Memory.Represents s.cells s.machine s.reached.toMachineState
  finite : FiniteEntry (callee s.caller) s.key s.capacity s.aligned s.large s.memory
  nonzero : s.caller.tx.selfAddress.val ≠ 0
  rootCode : s.initial.executionEnv.code = runtime s.pipeline
  fresh : s.initial.pc = .ofNat 0 ∧ s.initial.stack = [] ∧
    s.initial.memory = ByteArray.empty ∧ s.initial.activeWords = .ofNat 0
  prefixRun : Assembly.driverSteps s.steps s.fuel
    (EvmYul.EVM.D_J (runtime s.pipeline) (.ofNat 0)) s.initial = .ok s.reached
  bodyPC : s.reached.pc = .ofNat (bodyPC s.pipeline)
  context : s.reached.executionEnv = s.initial.executionEnv
  world : s.reached.toState = s.initial.toState
  owner : s.reached.executionEnv.codeOwner.val = s.caller.tx.selfAddress.val.toNat
  sender : s.reached.executionEnv.sender = s.reached.executionEnv.codeOwner
  source : s.reached.executionEnv.source = s.reached.executionEnv.codeOwner
  value : s.reached.executionEnv.weiValue = .ofNat 0
  permission : s.reached.executionEnv.perm = false
  installed : ∃ account : EvmYul.Account .EVM,
    s.reached.accountMap.find? s.reached.executionEnv.codeOwner = some account ∧
    account.code = runtime s.pipeline
  nonprecompile : ¬ s.reached.executionEnv.codeOwner ∈ EvmYul.π
  input : EvmYul.uInt256OfByteArray (s.reached.executionEnv.calldata.readBytes 4 32) =
    EvmYul.UInt256.ofNat (TEnv.get sizeSlot s.memory.st.env).val.toNat
  argumentStack : s.reached.stack.head? = some
    (EvmYul.UInt256.ofNat (TEnv.get sizeSlot s.memory.st.env).val.toNat)
  physical : s.reached.memory.size = s.capacity ∧
    ∀ i : Fin s.memory.capacity, s.reached.memory.data[i.val]! = s.memory.data i
  resident : (s.reached.activeWords * (⟨32⟩ : EvmYul.UInt256)).toNat = s.capacity
  returnEntry : RF.Entry s.emission s.L s.b s.frame s.fragment
    s.caller s.base s.machine s.start

/-- Explicit typed premises, not an asserted original producer instance. -/
structure Premises {C : Contract} (s : Site C) : Prop where
  p1 : Operational s
  p3 : Provenance s

variable {C : Contract}

theorem call_receiver (s : Site C) (h : Operational s) :
    s.call.addr = Evm.TryPanicCarrier.selfCall.addr := by
  have projected : s.call.addr =
      (Evm.TryPanicCallMetadata.sourceCall (C := C) s.call.mode s.call.invocation).addr :=
    congrArg (fun call : ExtCall C Caller => call.addr) h.callShape
  exact projected

/-- Direct H22 hypotheses about the call actually consumed by callerForm. -/
theorem call_metadata (s : Site C) (h : Provenance s) :
    s.call.mode = .static ∧ s.call.invocation = .site 79 :=
  ⟨h.staticCall,h.sourceInvocation⟩

theorem completed (s : Site C) (h : Premises s) :
    ∃ final : FrameMem C Input, BodyCompletedAt originalOps s.memory final computed36 := by
  rcases Solidity.Frontend.TryPanicSourceCaller.source_c36_completed
    (Solidity.Frontend.TryPanicSourcePlan.derive_original s.pipeline)
    (Solidity.Frontend.TryPanicSourceCaller.derive_original_c s.pipeline)
    s.caller s.key s.capacity s.aligned s.large s.memory h.p3.finite with
    ⟨_,_,final,body,_,_,_⟩
  exact ⟨final,body⟩

theorem body_halt (s : Site C) (h : Premises s) :
    s.body.runR (callee s.caller) = .error (THalt.ofData computed36) := by
  obtain ⟨final,body⟩ := completed s h
  exact h.p1.assembly _ s.key s.capacity s.aligned s.large s.memory final computed36 h.p3.finite body

theorem call_halt (s : Site C) (h : Premises s) :
    TRun.call Evm.TryPanicCarrier.args36 (.rets .nil) .refl s.body.runR s.caller =
      .error (THalt.ofData computed36) := by
  unfold TRun.call
  rw [Evm.TryPanicCarrier.args36_eval]
  change (s.body.runR (callee s.caller)).map _ = _
  rw [body_halt s h]
  rfl

theorem caught (s : Site C) (h : Premises s) :
    TRun.catchBytes s.call .nil Evm.TryPanicCarrier.args36
      .refl s.body.runR true s.caller = .ok computed36 := by
  apply TRun.catchBytes_self_data
  · change (s.call.addr.evalT s.caller).val ≠ 0
    rw [call_receiver s h.p1]
    exact h.p3.nonzero
  · rw [call_receiver s h.p1]
    rfl
  · exact call_halt s h

private theorem raw_halt : THalt.ofData computed36 = .revertWith computed36 := by
  rw [computed36_panic]
  rfl
private theorem no_error : Semantics.decodeError computed36 = none := by decide +kernel

theorem caller_return (s : Site C) (h : Premises s) :
    Stmt.run s.caller s.callerBody = .ok (callerOut s.caller) := by
  have call : TRun.call Evm.TryPanicCarrier.args36 (.rets .nil) .refl s.body.runR s.caller =
      .error (.revertWith computed36) := by
    rw [←raw_halt]
    exact call_halt s h
  have own : (s.call.addr.evalT s.caller).val = s.caller.tx.selfAddress.val := by
    rw [call_receiver s h.p1]
    rfl
  change s.callerBody.runR s.caller = _
  rw [h.p1.caller]
  simp only [callerForm,TRun.tryCall,own,if_neg h.p3.nonzero,decide_true,Bool.true_and,
    if_true,Binders.toRet,call,no_error,computed36_decode]
  change (TRun.seq (TRun.assert (.simple (.bool true))) s.return94.runR
    (handler s.caller)).map _ = _
  have asserted : TRun.assert (.simple (.bool true)) (handler s.caller) =
      .ok ⟨handler s.caller,List.prefix_refl _⟩ := rfl
  rw [TRun.seq,asserted]
  simp only [Except.map]
  rw [show s.return94.runR (handler s.caller) = .ok (returnOut (handler s.caller)) from h.p1.return94 _]
  rfl

/-- Conditional consequence of the SAME supplied operational/provenance premises.
This does not prove Nonempty(Premises originalSite) or original execution. -/
theorem return_of_premises (s : Site C) (h : Premises s) :
    ∃ out : Solidity.Out C s.caller.H Caller,
      Stmt.run s.caller s.callerBody = .ok out ∧
      RF.Returned s.emission s.L s.b s.frame s.caller s.base s.machine s.start out := by
  refine ⟨callerOut s.caller,caller_return s h,?_⟩
  exact h.p1.checkedReturn s.L s.frame s.caller s.base s.machine s.start
    h.p3.returnEntry _ (caller_return s h)

theorem slot74 (s : Site C) : TEnv.get .here (callerOut s.caller).st.env = codeWord := rfl

theorem ordinary_selection (s : Site C) (h : Premises s) :
    EvmYul.toExecute .EVM s.reached.accountMap s.reached.executionEnv.codeOwner =
      .Code (runtime s.pipeline) := by
  obtain ⟨account,lookup,code⟩ := h.p3.installed
  simp only [EvmYul.toExecute,if_neg h.p3.nonprecompile,lookup,code]
  rfl

theorem first_destination (p : Pipeline) :
    (EvmYul.EVM.D_J (runtime p) (.ofNat 0)).contains
      (.ofNat (match p with | .legacy => 15 | .viaIR => 18)) = true := by
  cases p with
  | legacy => exact TryPanicSourceScanner.legacy_first_destination
  | viaIR => exact TryPanicSourceScanner.viaIR_first_destination

theorem actual_overlap (s : Site C) (h : Premises s) (x y : EvmYul.UInt256) :
    ((s.reached.toMachineState.mstore (.ofNat 0) x).mstore (.ofNat 4) y).memory.readWithPadding 4 32 =
      Memory.encoding y := by
  apply TryPanicSourcePadding.overlap_read
  rw [h.p3.physical.1]
  have large : 96 ≤ s.capacity := s.large
  omega

/-- Relative bounded result. P1 Returned is core Evm.run, not EvmYul.X;
this theorem does not equate evaluators or assert whole native adequacy. -/
theorem bounded (s : Site C) (h : Premises s) :
    s.body.runR (callee s.caller) = .error (THalt.ofData computed36) ∧
    TRun.catchBytes s.call .nil Evm.TryPanicCarrier.args36
      .refl s.body.runR true s.caller = .ok computed36 ∧
    Semantics.decodePanic computed36 = some codeWord ∧
    Stmt.run s.caller s.callerBody = .ok (callerOut s.caller) ∧
    RF.Returned s.emission s.L s.b s.frame s.caller s.base s.machine s.start (callerOut s.caller) := by
  refine ⟨body_halt s h,caught s h,computed36_decode,caller_return s h,?_⟩
  exact h.p1.checkedReturn s.L s.frame s.caller s.base s.machine s.start
    h.p3.returnEntry _ (caller_return s h)

/-- An inhabited generic value-transfer CONTROL, not original lowering. -/
def returnControl : Stmt C Handler Handler :=
  .assignLocal (.there .here) (.simple (.local .here))
theorem return_control (σ : State C Handler) :
    Stmt.run σ (returnControl (C := C)) = .ok (returnOut σ) := rfl

theorem return_control_not_error (σ : State C Handler) (e : THalt) :
    Stmt.run σ (returnControl (C := C)) ≠ .error e := by
  rw [return_control]
  intro bad
  cases bad

theorem compiled_code (s : Site C) (h : Premises s) :
    s.reached.executionEnv.code = runtime s.pipeline :=
  (congrArg (fun env : EvmYul.ExecutionEnv .EVM => env.code) h.p3.context).trans h.p3.rootCode

theorem input36 (s : Site C) (h : Premises s) :
    EvmYul.uInt256OfByteArray (s.reached.executionEnv.calldata.readBytes 4 32) =
      EvmYul.UInt256.ofNat 36 := by
  have initialized : s.memory = entryK (callee s.caller) s.key s.capacity s.aligned s.large :=
    h.p3.finite
  have value : TEnv.get sizeSlot s.memory.st.env = size36 := by rw [initialized]; rfl
  rw [h.p3.input,value]
  rfl

theorem argument36 (s : Site C) (h : Premises s) :
    s.reached.stack.head? = some (EvmYul.UInt256.ofNat 36) := by
  have initialized : s.memory = entryK (callee s.caller) s.key s.capacity s.aligned s.large :=
    h.p3.finite
  have value : TEnv.get sizeSlot s.memory.st.env = size36 := by rw [initialized]; rfl
  rw [h.p3.argumentStack,value]
  rfl

theorem reached_destination (s : Site C) (h : Premises s) :
    (EvmYul.EVM.D_J s.reached.executionEnv.code (.ofNat 0)).contains
      (.ofNat (match s.pipeline with | .legacy => 15 | .viaIR => 18)) = true := by
  rw [compiled_code s h]
  exact first_destination s.pipeline

/-- Conditional closure consumes H7 on the supplied reached code/memory.
The Returned, input/argument and ordinary-selection conjuncts consume explicit
operational/provenance fields; they are not original invocation derivations.
No EvmYul run or original-site Premises instance is established here. -/
theorem closed (s : Site C) (h : Premises s) :
    (∃ final : FrameMem C Input, BodyCompletedAt originalOps s.memory final computed36) ∧
    TRun.catchBytes s.call .nil Evm.TryPanicCarrier.args36
      .refl s.body.runR true s.caller = .ok computed36 ∧
    Semantics.decodePanic computed36 = some codeWord ∧
    Stmt.run s.caller s.callerBody = .ok (callerOut s.caller) ∧
    RF.Returned s.emission s.L s.b s.frame s.caller s.base s.machine s.start (callerOut s.caller) ∧
    EvmYul.toExecute .EVM s.reached.accountMap s.reached.executionEnv.codeOwner = .Code (runtime s.pipeline) ∧
    EvmYul.uInt256OfByteArray (s.reached.executionEnv.calldata.readBytes 4 32) = .ofNat 36 ∧
    s.reached.stack.head? = some (EvmYul.UInt256.ofNat 36) ∧
    (EvmYul.EVM.D_J s.reached.executionEnv.code (.ofNat 0)).contains
      (.ofNat (match s.pipeline with | .legacy => 15 | .viaIR => 18)) = true ∧
    ∀ x y : EvmYul.UInt256,
      ((s.reached.toMachineState.mstore (.ofNat 0) x).mstore (.ofNat 4) y).memory.readWithPadding 4 32 =
        Memory.encoding y := by
  refine ⟨completed s h,caught s h,computed36_decode,caller_return s h,?_,
    ordinary_selection s h,input36 s h,argument36 s h,reached_destination s h,actual_overlap s h⟩
  exact h.p1.checkedReturn s.L s.frame s.caller s.base s.machine s.start
    h.p3.returnEntry _ (caller_return s h)

/-- An explicit inhabitant of the UNIFORM normalized value-transfer law.
This is not an inhabitant of the original Premises structure. -/
theorem return_law_inhabited :
    Nonempty { statement : Stmt C Handler Handler //
      ∀ σ : State C Handler, Stmt.run σ statement = .ok (returnOut σ) } :=
  ⟨⟨returnControl,return_control⟩⟩

/-- The contrary zero-receiver branch survives the uniform caller equation. -/
theorem zero_receiver (s : Site C) (h : Operational s)
    (zero : s.caller.tx.selfAddress.val = 0) :
    Stmt.run s.caller s.callerBody = .error .revert := by
  change s.callerBody.runR s.caller = _
  rw [h.caller]
  have receiver : (s.call.addr.evalT s.caller).val = 0 := by
    rw [call_receiver s h]
    exact zero
  simp only [callerForm,TRun.tryCall,receiver,if_pos]

/-- Generic realization cannot be filled by the old constant carrier36, even
though it agrees at c's argument36. The source f's actual local0 control has a
completed empty-data branch, so the assembly-law antecedent is not vacuous. -/
theorem constant_carrier_refused (s : Site C) (wrong : s.body = Evm.TryPanicCarrier.carrier36) :
    ¬ Operational s := by
  intro h
  let σ : State C Input := s.caller.withEnv (zero,())
  have aligned : ∃ k, (96 : Nat) = k*32 := ⟨3,rfl⟩
  have large : 96 ≤ (96 : Nat) := Nat.le_refl _
  have fits : (TEnv.get sizeSlot σ.env).val.toNat ≤ 96 := by change 0 ≤ 96; decide
  have empty : dataK σ s.key 96 aligned large fits = [] := by
    apply List.eq_nil_of_length_eq_zero
    rw [data_length]
    rfl
  have model : BodyCompletedAt originalOps (entryK σ s.key 96 aligned large)
      (imageK σ s.key 96 aligned large) [] := by
    have model : BodyCompletedAt originalOps (entryK σ s.key 96 aligned large)
        (imageK σ s.key 96 aligned large) (dataK σ s.key 96 aligned large fits) :=
      completed_generic σ s.key 96 aligned large fits
    rw [empty] at model
    exact model
  have actual : s.body.runR σ = .error .revert :=
    h.assembly σ s.key 96 aligned large _ _ [] rfl model
  have carrier : s.body.runR σ = .error (.revertWith computed36) := by
    rw [wrong,←raw_halt]
    exact Evm.TryPanicCarrier.carrier36_halt σ
  rw [actual] at carrier
  cases carrier

end Solidity.Evm.External.TryPanicRelative
