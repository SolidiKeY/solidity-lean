import Solidity.Yul.World.FailureFuel
import Solidity.Yul.Composition.ReturningPhysical
import Solidity.Yul.Composition.RuntimeBlockPhysical

/-! Actual ordinary-function nonempty CALL/STATICCALL result -> real typed
external decoder -> actual allocation/local-alias canonical rethrow. This is an
owned consumer router, not Source.try selection, allocation placement or G01.
The returned physical completion is pre-catch; paired EMState is real post-catch. -/
namespace Solidity.Yul.Composition.FailurePhysical
open Solidity.Source
open Solidity.Roadmap (Word Bytes Outcome)
open Solidity.Yul.Views
open Solidity.Yul.World
open PhysicalCompletion
open ReturningCall (env uint input errorData)

/-- ACTUAL allocRef/heapBytes readback then an actual typed scoped alias/rethrow.
Old caller locals come from EM.locals, not a reconstructed desired frame. -/
def allocateRethrow {Γ} (G : Glob env) (F : Fr) (fuel : Nat) (bytes : Bytes) : EM env Γ Bytes := do
  let (ref,_) ← HeapCatchPhysical.allocateRead F bytes
  let caller ← EM.locals
  RuntimeBlockPhysical.executeBound G F fuel .here (.cons ref caller)

theorem allocate_rethrow {Γ} (G : Glob env) (F : Fr) (fuel : Nat) (bytes : Bytes) (s : EMState env Γ) :
    (allocateRethrow G F (fuel+4) bytes).run s =
      (.error (.revert bytes),(s.1,RuntimeBlockPhysical.allocatedState s.2 bytes)) := by
  unfold allocateRethrow
  rw [Source.Hoare.run_bind,HeapCatchPhysical.allocateRead_run]
  dsimp only
  have caller : (EM.locals : EM env Γ (Locals env.layout Γ)).run
      (s.1,RuntimeBlockPhysical.allocatedState s.2 bytes) =
      (.ok s.1,(s.1,RuntimeBlockPhysical.allocatedState s.2 bytes)) := rfl
  unfold RuntimeBlockPhysical.allocatedState at caller ⊢
  rw [Source.Hoare.run_bind,caller]
  dsimp only
  apply RuntimeBlockPhysical.execute_bound_run G F fuel s.2.heap.next bytes .here _ s.1 _ rfl
  exact Source.Heap.alloc_get _ _

/-- Actual extReturn halt is captured by actual attempt. This consumer selects
only the existing revert constructor, never swallowing timeout/stuck. -/
def catchDecoded {Γ} (G : Glob env) (F : Fr) (fuel : Nat) (outcome : Outcome) : EM env Γ Bytes := do
  let captured ← EM.attempt (ReturningPhysical.decode outcome)
  match captured with
  | .error (.revert bytes) => allocateRethrow G F fuel bytes
  | .error halt => EM.halt halt
  | .ok _ => pure []

theorem catch_revert {Γ} (G : Glob env) (F : Fr) (fuel : Nat) (bytes : Bytes) (s : EMState env Γ) :
    (catchDecoded G F (fuel+4) (.revert bytes)).run s =
      (.error (.revert bytes),(s.1,RuntimeBlockPhysical.allocatedState s.2 bytes)) := by
  have captured : (EM.attempt (ReturningPhysical.decode (.revert bytes))).run s =
      (.ok (.error (.revert bytes)),s) := by
    rw [AttemptPhysical.attempt_run,ReturningPhysical.decode_revert]
  unfold catchDecoded
  rw [Source.Hoare.run_bind,captured]
  exact allocate_rethrow G F fuel bytes s

theorem catch_success {Γ} (G : Glob env) (F : Fr) (fuel : Nat) (s : EMState env Γ) :
    (catchDecoded G F fuel (.success ReturningCall.output)).run s = (.ok [],s) := by
  have captured : (EM.attempt (ReturningPhysical.decode (.success ReturningCall.output))).run s =
      (.ok (.ok (.val (.int (ReturningCall.value : Int) (by decide)))),s) := by
    rw [AttemptPhysical.attempt_run,ReturningPhysical.decode_output]
  unfold catchDecoded
  rw [Source.Hoare.run_bind,captured]
  rfl

/-- Keep the actual physical completion separately from decoder/allocation
post-state. Catch allocation is NOT silently identified with a physical address. -/
def consume {Γ} (G : Glob env) (F : Fr) (fuel : Nat) (result : Option (Except Halt Outcome × Result env Γ)) :=
  result.map fun (status,completed) =>
    ((match status with
      | .ok outcome => (catchDecoded G F fuel outcome).run completed.1.1.1
      | .error halt => (.error halt,completed.1.1.1)),completed)

def callCatch (G : Glob env) (F : Fr) (fuel : Nat) {Γ} (s : EMState env Γ)
    (r : ResidualJournal complementCarrierOwnership) (b : BoolEncodingJournal)
    (o : ObservedEffects env.layout env.lay env.lay) (shared : o.effects.execution=s.2.ex)
    (m : ByteView) (gas offset size : Word) :=
  consume G F fuel (call (CallerFrame.liftInvoke (ReturningCall.invokeFailure G)) s r b o shared m
    (ReturningCall.parent s) .call CallerFrameChecks.receiver gas 7 offset size)

/-- Concrete producer, actual decoder/capture, allocated fullbytes and actual
resolved rethrow. Code/transfer/load facts are real, not a desired run premise. -/
theorem call_rethrow (G : Glob env) (F : Fr) (fuel : Nat) {Γ} (s : EMState env Γ)
    (next : ExecState env.layout env.lay env.lay)
    (code : (s.2.ex.world.accounts CallerFrameChecks.receiver).code=some 0)
    (transfer : s.2.ex.transfer CallerFrameChecks.owner CallerFrameChecks.receiver 7=some next)
    (r : ResidualJournal complementCarrierOwnership) (b : BoolEncodingJournal)
    (o : ObservedEffects env.layout env.lay env.lay) (shared : o.effects.execution=s.2.ex)
    (m : ByteView) (gas offset size : Word) (loaded : PhysicalHeapPort.port.load m offset size=some (input G)) :
    callCatch G F (fuel+4) s r b o shared m gas offset size =
      some ((.error (.revert (errorData G)),(s.1,RuntimeBlockPhysical.allocatedState s.2 (errorData G))),
        GeneralFailure.result G s r b o) := by
  unfold callCatch
  rw [GeneralFailure.call_actual G s next code transfer r b o shared m gas offset size loaded]
  change some ((catchDecoded G F (fuel+4) (.revert (errorData G))).run s,_) = _
  rw [catch_revert]

def staticCatch (G : Glob env) (F : Fr) (fuel : Nat) {Γ} (s : EMState env Γ)
    (r : ResidualJournal complementCarrierOwnership) (b : BoolEncodingJournal)
    (o : ObservedEffects env.layout env.lay env.lay) (shared : o.effects.execution=s.2.ex)
    (m : ByteView) (gas offset size : Word) :=
  consume G F fuel (call (CallerFrame.liftInvoke (GeneralFailure.staticInvoke G)) s r b o shared m
    (ReturningCall.parent s) .staticcall CallerFrameChecks.receiver gas 0 offset size)

theorem static_rethrow (G : Glob env) (F : Fr) (fuel : Nat) {Γ} (s : EMState env Γ)
    (next : ExecState env.layout env.lay env.lay)
    (code : (s.2.ex.world.accounts CallerFrameChecks.receiver).code=some 0)
    (transfer : s.2.ex.transfer CallerFrameChecks.owner CallerFrameChecks.receiver 0=some next)
    (r : ResidualJournal complementCarrierOwnership) (b : BoolEncodingJournal)
    (o : ObservedEffects env.layout env.lay env.lay) (shared : o.effects.execution=s.2.ex)
    (m : ByteView) (gas offset size : Word) (loaded : PhysicalHeapPort.port.load m offset size=some (input G)) :
    staticCatch G F (fuel+4) s r b o shared m gas offset size =
      some ((.error (.revert (errorData G)),(s.1,RuntimeBlockPhysical.allocatedState s.2 (errorData G))),
        GeneralFailure.result G s r b o) := by
  unfold staticCatch
  rw [GeneralFailure.static_call G s next code transfer r b o shared m gas offset size loaded]
  change some ((catchDecoded G F (fuel+4) (.revert (errorData G))).run s,_) = _
  rw [catch_revert]


theorem catch_zero {Γ} (G : Glob env) (F : Fr) (bytes : Bytes) (s : EMState env Γ) :
    (catchDecoded G F 0 (.revert bytes)).run s =
      (.error .timeout,(s.1,RuntimeBlockPhysical.allocatedState s.2 bytes)) := by
  have captured : (EM.attempt (ReturningPhysical.decode (.revert bytes))).run s =
      (.ok (.error (.revert bytes)),s) := by rw [AttemptPhysical.attempt_run,ReturningPhysical.decode_revert]
  unfold catchDecoded allocateRethrow
  rw [Source.Hoare.run_bind,captured]
  dsimp only
  rw [Source.Hoare.run_bind,HeapCatchPhysical.allocateRead_run]
  rfl

/-- Allocation is a real catch effect BEFORE a zero-fuel rethrow times out. -/
theorem allocated_contents {Γ} (s : EMState env Γ) (bytes : Bytes) :
    (RuntimeBlockPhysical.allocatedState s.2 bytes).heap.get s.2.heap.next =
      some ⟨.bytes .memory,.bytes bytes⟩ := Source.Heap.alloc_get _ _

theorem old_alias {Γ} (s : EMState env Γ) (bytes : Bytes) (a : Nat) (different : a≠s.2.heap.next) :
    (RuntimeBlockPhysical.allocatedState s.2 bytes).heap.get a=s.2.heap.get a :=
  Source.Heap.alloc_other _ _ different

theorem complete_fields {Γ} (s : EMState env Γ) (bytes : Bytes)
    (G : Glob env) (r : ResidualJournal complementCarrierOwnership) (b : BoolEncodingJournal)
    (o : ObservedEffects env.layout env.lay env.lay) :
    (RuntimeBlockPhysical.allocatedState s.2 bytes).ex=s.2.ex ∧
    (RuntimeBlockPhysical.allocatedState s.2 bytes).fnLocals=s.2.fnLocals ∧
    (RuntimeBlockPhysical.allocatedState s.2 bytes).logs=s.2.logs ∧
    (RuntimeBlockPhysical.allocatedState s.2 bytes).events=s.2.events ∧
    (GeneralFailure.result G s r b o).1=(⟨⟨s,r⟩,b⟩ : Carrier env Γ) ∧
    (GeneralFailure.result G s r b o).2.trace=o.trace ∧
    (GeneralFailure.result G s r b o).2.effects.returndata=errorData G :=
  ⟨rfl,rfl,rfl,rfl,rfl,rfl,rfl⟩

theorem payload_exact (G : Glob env) : (errorData G).drop 4=ReturningCall.output := by
  have length : ((ReturningCall.glob G).selector (sigOf env.layout "Denied" [uint])).length=4 := by
    simp only [Glob.selector,List.length_take,wordBytes_length]
    rfl
  unfold ReturningCall.errorData
  rw [←length,List.drop_left]

/-- Actual static-argument decoder AFTER the known error's four-byte selector.
This fact is about the real producer, not a general Source try selector. -/
theorem payload_decoded {Γ} (G : Glob env) (s : EMState env Γ) :
    (Source.decodeArg ((errorData G).drop 4) 0 uint : EM env Γ _).run s =
      (.ok (.int (ReturningCall.value : Int) (by decide)),s) := by
  rw [payload_exact]
  rfl

theorem consume_halt {Γ} (G : Glob env) (F : Fr) (fuel : Nat) (c : Result env Γ) (halt : Halt) :
    consume G F fuel (some (.error halt,c)) = some ((.error halt,c.1.1.1),c) := rfl

theorem consume_missing {Γ} (G : Glob env) (F : Fr) (fuel : Nat) :
    consume G F fuel (none : Option (Except Halt Outcome × Result env Γ))=none := rfl

theorem timeout_actual (G : Glob env) (F : Fr) (fuel : Nat) {Γ} (s : EMState env Γ)
    (next : ExecState env.layout env.lay env.lay)
    (code : (s.2.ex.world.accounts CallerFrameChecks.receiver).code=some 0)
    (transfer : s.2.ex.transfer CallerFrameChecks.owner CallerFrameChecks.receiver 7=some next)
    (r : ResidualJournal complementCarrierOwnership) (b : BoolEncodingJournal)
    (o : ObservedEffects env.layout env.lay env.lay) (shared : o.effects.execution=s.2.ex)
    (m : ByteView) (gas offset size : Word) (loaded : PhysicalHeapPort.port.load m offset size=some (input G)) :
    consume G F fuel (call (CallerFrame.liftInvoke (ReturningCall.invokeTemplateAt 6 true G)) s r b o shared m
      (ReturningCall.parent s) .call CallerFrameChecks.receiver gas 7 offset size) =
      some ((.error .timeout,GeneralReturning.after s next),pending o ⟨⟨GeneralReturning.after s next,r⟩,b⟩ []) := by
  rw [FailureFuel.call_timeout G s next code transfer r b o shared m gas offset size loaded]
  rfl

/-- Actual return-window operation before catch. Requires the real shared
execution and placement/ownership, not an asserted EVM allocation address. -/
def copyCatch {Γ} (G : Glob env) (F : Fr) (fuel : Nat) (c : Result env Γ)
    (shared : c.2.effects.execution=c.1.1.1.2.ex) (p : Placement c.1.1.1.2.heap)
    (a : Nat) (string : Bool) (old : Bytes)
    (found : c.1.1.1.2.heap.get a=some ⟨heapByteType string,heapByteData env.layout string old⟩)
    (memory : ByteView) (offset source size : Word) :=
  let copied := copyAfter c shared p a string old found memory offset source size
  (copied,copied.2.map fun actual =>
    ((catchDecoded G F fuel (.revert c.2.effects.returndata)).run actual.1.2,actual.2))

/-- The SAME actual producer completion supplies the full buffer to a strict
copy window; the actual post-copy Source heap is then allocated/rethrown. -/
theorem copied_catch (G : Glob env) (F : Fr) (fuel : Nat) (ex : ExecState env.layout env.lay env.lay) :
    (copyCatch G F (fuel+4)
      (GeneralFailure.result G (GeneralReturningChecks.caller G ex) CallerFrameChecks.residual CallerFrameChecks.encoding (GeneralReturningChecks.observed ex))
      rfl (ReturningCall.placement G) 1 false ReturningCall.old rfl (ReturningCall.memory G) 1 4 2).2 =
      some ((.error (.revert (errorData G)),
        ((GeneralReturningChecks.caller G ex).1,RuntimeBlockPhysical.allocatedState
          (withSourceHeap (GeneralReturningChecks.caller G ex) (ReturningCall.copiedHeap G)).2 (errorData G))),
        (CallerFrameChecks.residual,CallerFrameChecks.encoding),
        (GeneralFailure.result G (GeneralReturningChecks.caller G ex) CallerFrameChecks.residual CallerFrameChecks.encoding (GeneralReturningChecks.observed ex)).2) := by
  unfold copyCatch
  rw [GeneralFailure.copied_payload G ex]
  change some ((catchDecoded G F (fuel+4) (.revert (errorData G))).run _,_) = _
  rw [catch_revert]
  rfl

abbrev FunctionType : STy := .fn true [.bool] [.int IntTy.u8] (some .view)
abbrev RawContext : RCtx := [.bool,.int IntTy.u8,FunctionType,FunctionType,.bytes .memory]

/-- Environment-correct raw witness; no cast from the unrelated originEnv. -/
def rawValues : LocalValues env RawContext :=
  (.scalar (.basic (.scalar .bool)) (toWord 2),
   (.scalar (.basic (.scalar (.int IntTy.u8 ⟨0,by decide⟩ rfl))) (toWord 257),
    (.externalFunction _ _ _ (toWord (2^256-1)) (toWord 0x89abcdef),
     (.externalFunction _ _ _ (toWord 22136) (toWord (2^256-1)),(.clean (.memRef rfl 0),())))))

theorem raw_not_clean (state : Source.St env) : LocalState.clean? (rawValues,state)=none := rfl

def withRaw {Γ Λ} (raw : LocalValues env Λ)
    (actual : Option ((Except Halt Bytes × EMState env Γ) × Result env Γ)) :=
  actual.map fun result => (result,(raw,result.1.2.2))

def caller (G : Glob env) := GeneralReturningChecks.caller G SourceBoundaryRules.prefixedExecution
def observed := GeneralReturningChecks.observed SourceBoundaryRules.prefixedExecution

def sample (G : Glob env) (fuel : Nat) :=
  withRaw rawValues (callCatch G ReturningCall.parentFrame fuel (caller G)
    CallerFrameChecks.residual CallerFrameChecks.encoding observed rfl (ReturningCall.memory G) 10000 160 4)

theorem sample_run (G : Glob env) (fuel : Nat) :
    sample G (fuel+4) = some
      (((.error (.revert (errorData G)),((caller G).1,RuntimeBlockPhysical.allocatedState (caller G).2 (errorData G))),
        GeneralFailure.result G (caller G) CallerFrameChecks.residual CallerFrameChecks.encoding observed),
        (rawValues,RuntimeBlockPhysical.allocatedState (caller G).2 (errorData G))) := by
  unfold sample
  rw [call_rethrow G ReturningCall.parentFrame fuel (caller G) SourceBoundaryRules.prefixedMoved rfl rfl
    _ _ _ rfl _ 10000 160 4 (ReturningCall.input_load G)]
  rfl

theorem static_sample (G : Glob env) (fuel : Nat) :
    staticCatch G ReturningCall.parentFrame (fuel+4) (caller G)
      CallerFrameChecks.residual CallerFrameChecks.encoding observed rfl (ReturningCall.memory G) 10000 160 4 =
      some ((.error (.revert (errorData G)),((caller G).1,RuntimeBlockPhysical.allocatedState (caller G).2 (errorData G))),
        GeneralFailure.result G (caller G) CallerFrameChecks.residual CallerFrameChecks.encoding observed) :=
  static_rethrow G ReturningCall.parentFrame fuel (caller G) GeneralReturningChecks.staticPrefixed rfl rfl
    _ _ _ rfl _ 10000 160 4 (ReturningCall.input_load G)


/-- The real known failing program also refuses BEFORE entry when transfer is
impossible; no custom-error execution is assumed for this empty result. -/
theorem source_refused (G : Glob env) (s : EMState env [])
    (code : (s.2.ex.world.accounts CallerFrameChecks.receiver).code=some 0)
    (transfer : s.2.ex.transfer CallerFrameChecks.owner CallerFrameChecks.receiver 7=none) :
    (Source.callAddr (ReturningCall.failingGlob G) ReturningCall.parentFrame 10
      CallerFrameChecks.receiver 7 (input G) false).run s = (.ok (.revert []),s) := by
  simp only [Source.callAddr,ReturningCall.parentFrame,show ¬(0≥1024) from by decide,if_false,
    Bool.false_and,Bool.false_eq_true,Source.Hoare.run_bind,ReturningCall.run_pure,GeneralFailure.selected G s code,
    ReturningCall.run_mark,ReturningCall.run_st,show CallerFrameChecks.receiver≠CallerFrameChecks.owner from by decide,
    transfer,Bool.not_false,if_true]

theorem refused_invoke (G : Glob env) {Γ} (s : EMState env Γ)
    (code : (s.2.ex.world.accounts CallerFrameChecks.receiver).code=some 0)
    (transfer : s.2.ex.transfer CallerFrameChecks.owner CallerFrameChecks.receiver 7=none)
    (r : ResidualJournal complementCarrierOwnership) (b : BoolEncodingJournal)
    (o : ObservedEffects env.layout env.lay env.lay) (gas : Word) :
    CallerFrame.liftInvoke (ReturningCall.invokeFailure G) o
      (enter s r (ReturningCall.parent s) .call CallerFrameChecks.receiver 7 (input G))
      .call CallerFrameChecks.receiver gas (input G) ⟨⟨s,r⟩,b⟩ =
      some ((.ok (.revert []),⟨⟨s,r⟩,b⟩),[]) := by
  have ran := FailureFuel.invoke_run G 10 (⟨L0 env,s.2⟩ : EMState env []) ⟨L0 env,s.2⟩ code r b o gas (.ok (.revert []))
    (source_refused G ⟨L0 env,s.2⟩ code transfer)
  simp only [List.drop_length,List.map_nil] at ran
  exact CallerFrame.liftInvoke_exact (ReturningCall.invokeFailure G) o
    (enter s r (ReturningCall.parent s) .call CallerFrameChecks.receiver 7 (input G))
    .call CallerFrameChecks.receiver gas (input G) ⟨⟨s,r⟩,b⟩ (.ok (.revert [])) ⟨⟨⟨L0 env,s.2⟩,r⟩,b⟩ [] ran

theorem refused_call (G : Glob env) {Γ} (s : EMState env Γ)
    (code : (s.2.ex.world.accounts CallerFrameChecks.receiver).code=some 0)
    (transfer : s.2.ex.transfer CallerFrameChecks.owner CallerFrameChecks.receiver 7=none)
    (r : ResidualJournal complementCarrierOwnership) (b : BoolEncodingJournal)
    (o : ObservedEffects env.layout env.lay env.lay) (shared : o.effects.execution=s.2.ex)
    (m : ByteView) (gas offset size : Word) (loaded : PhysicalHeapPort.port.load m offset size=some (input G)) :
    call (CallerFrame.liftInvoke (ReturningCall.invokeFailure G)) s r b o shared m
      (ReturningCall.parent s) .call CallerFrameChecks.receiver gas 7 offset size =
      some (.ok (.revert []),GeneralReturning.refusedResult s r b o) := by
  rw [call_normal_rule _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ rfl loaded
    (refused_invoke G s code transfer r b o gas),GeneralReturning.refused_finish G s r b o]

theorem refused_rethrow (G : Glob env) (F : Fr) (fuel : Nat) {Γ} (s : EMState env Γ)
    (code : (s.2.ex.world.accounts CallerFrameChecks.receiver).code=some 0)
    (transfer : s.2.ex.transfer CallerFrameChecks.owner CallerFrameChecks.receiver 7=none)
    (r : ResidualJournal complementCarrierOwnership) (b : BoolEncodingJournal)
    (o : ObservedEffects env.layout env.lay env.lay) (shared : o.effects.execution=s.2.ex)
    (m : ByteView) (gas offset size : Word) (loaded : PhysicalHeapPort.port.load m offset size=some (input G)) :
    callCatch G F (fuel+4) s r b o shared m gas offset size =
      some ((.error (.revert []),(s.1,RuntimeBlockPhysical.allocatedState s.2 [])),GeneralReturning.refusedResult s r b o) := by
  unfold callCatch
  rw [refused_call G s code transfer r b o shared m gas offset size loaded]
  change some ((catchDecoded G F (fuel+4) (.revert [])).run s,_) = _
  rw [catch_revert]

theorem static_missing (G : Glob env) (s : EMState env []) r b o
    (code : (s.2.ex.world.accounts CallerFrameChecks.receiver).code=none) :
    GeneralFailure.staticInvoke G o (enter s r (ReturningCall.parent s) .staticcall CallerFrameChecks.receiver 0 (input G))
      .staticcall CallerFrameChecks.receiver 10000 (input G) ⟨⟨s,r⟩,b⟩=none :=
  GeneralFailure.static_unregistered G s r b o code

theorem static_wrong_kind (G : Glob env) o frame target gas bytes c :
    GeneralFailure.staticInvoke G o frame .call target gas bytes c=none :=
  GeneralFailure.static_wrong_kind G o frame target gas bytes c

theorem static_nonstatic (G : Glob env) (s : EMState env []) r b o :
    GeneralFailure.staticInvoke G o (enter s r (ReturningCall.parent s) .call CallerFrameChecks.receiver 7 (input G))
      .staticcall CallerFrameChecks.receiver 10000 (input G) ⟨⟨s,r⟩,b⟩=none :=
  GeneralFailure.static_nonstatic_refused G s r b o

/-- Reachability and actual copy/catch use the identical concrete completion.
No arbitrary configured outcome is a premise of either component. -/
theorem sample_copy_reachable (G : Glob env) (F : Fr) (fuel : Nat) :
    call (CallerFrame.liftInvoke (ReturningCall.invokeFailure G)) (caller G)
      CallerFrameChecks.residual CallerFrameChecks.encoding observed rfl (ReturningCall.memory G)
      (ReturningCall.parent (caller G)) .call CallerFrameChecks.receiver 10000 7 160 4 =
      some (.ok (.revert (errorData G)),GeneralFailure.result G (caller G) CallerFrameChecks.residual CallerFrameChecks.encoding observed) ∧
    (copyCatch G F (fuel+4) (GeneralFailure.result G (caller G) CallerFrameChecks.residual CallerFrameChecks.encoding observed)
      rfl (ReturningCall.placement G) 1 false ReturningCall.old rfl (ReturningCall.memory G) 1 4 2).2 =
      some ((.error (.revert (errorData G)),
        ((caller G).1,RuntimeBlockPhysical.allocatedState
          (withSourceHeap (caller G) (ReturningCall.copiedHeap G)).2 (errorData G))),
        (CallerFrameChecks.residual,CallerFrameChecks.encoding),
        (GeneralFailure.result G (caller G) CallerFrameChecks.residual CallerFrameChecks.encoding observed).2) :=
  ⟨GeneralFailure.prefix_control G,copied_catch G F fuel SourceBoundaryRules.prefixedExecution⟩

/-- A full call result's exact retained buffer, not only its length/tag. -/
theorem full_buffer (G : Glob env) {Γ} (s : EMState env Γ) r b o :
    (GeneralFailure.result G s r b o).2.effects.returndata =
      (ReturningCall.glob G).selector (sigOf env.layout "Denied" [uint]) ++ ReturningCall.output := rfl


/-- Exact view RETENTION for every actual registry/bank, not a claim that an
arbitrary caller/carrier is a valid representation or has a chosen layout. -/
theorem represented_retained {Γ} (s : EMState env Γ) (bytes : Bytes)
    (r : ResidualJournal complementCarrierOwnership) (b : BoolEncodingJournal)
    (ps ts : (a : Solidity.Roadmap.Address) → List (ScalarPath env.layout (env.lay a)))
    (a : Solidity.Roadmap.Address) (slot : Word) :
    reencodePersistentSlot (representedBanks ps false b) ⟨(RuntimeBlockPhysical.allocatedState s.2 bytes).ex,r⟩ a slot =
      reencodePersistentSlot (representedBanks ps false b) ⟨s.2.ex,r⟩ a slot ∧
    reencodeTransientSlot (representedBanks ts true b) ⟨(RuntimeBlockPhysical.allocatedState s.2 bytes).ex,r⟩ a slot =
      reencodeTransientSlot (representedBanks ts true b) ⟨s.2.ex,r⟩ a slot := ⟨rfl,rfl⟩

/-- Public adapter registration failure is NOT Source/EVM empty revert. -/
theorem call_missing (G : Glob env) (s : EMState env []) r b o gas
    (missing : (s.2.ex.world.accounts CallerFrameChecks.receiver).code=none) :
    ReturningCall.invokeFailure G o (enter s r (ReturningCall.parent s) .call CallerFrameChecks.receiver 7 (input G))
      .call CallerFrameChecks.receiver gas (input G) ⟨⟨s,r⟩,b⟩=none := by
  unfold ReturningCall.invokeFailure ReturningCall.invokeTemplateAt ReturningCall.template
  change (if decide ((s.2.ex.world.accounts CallerFrameChecks.receiver).code=some 0) then
    some (ReturningCall.pack ⟨⟨s,r⟩,b⟩ ((Source.callAddr (ReturningCall.failingGlob G) ReturningCall.parentFrame 10
      CallerFrameChecks.receiver 7 (input G) false).run s)) else none)=_
  rw [missing]
  rfl

end Solidity.Yul.Composition.FailurePhysical
