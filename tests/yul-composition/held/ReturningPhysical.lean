import Solidity.Yul.World.GeneralReturningOutput

/-! Selected actual CALL/STATICCALL followed by Source's real typed external
return decoder. The physical result is retained as the pre-decode completion;
the paired EMState is the actual decoder post-state, not a second semantics.
Registered code, real transfer, supplied Fixed selector/prefix, concrete horizon
and physical input premises remain explicit. No general callee/try/G01 adequacy. -/
namespace Solidity.Yul.Composition.ReturningPhysical
open Solidity.Source
open Solidity.Roadmap (Word Bytes Outcome)
open Solidity.Yul.Views
open Solidity.Yul.World
open PhysicalCompletion
open ReturningCall (env uint output)

/-- Typed decoder of the exact complete returned buffer; no length-only oracle. -/
def decode {Γ} (outcome : Outcome) : EM env Γ (RVal env.layout (.ret [uint])) :=
  Source.extReturn [uint] outcome

theorem decode_output {Γ} (s : EMState env Γ) :
    (decode (.success output)).run s =
      (.ok (.val (.int (ReturningCall.value : Int) (by decide))),s) := rfl

theorem decode_revert {Γ} (s : EMState env Γ) (bytes : Bytes) :
    (decode (.revert bytes)).run s = (.error (.revert bytes),s) := rfl

theorem decode_short {Γ} (s : EMState env Γ) :
    (decode (.success [0x11,0x22,0x33,0x44])).run s = (.error (.revert []),s) := rfl

/-- Same length, different full payload decodes to a different typed integer. -/
theorem decode_wrong {Γ} (s : EMState env Γ) :
    (decode (.success (Solidity.Source.wordBytes (toWord (ReturningCall.value+1))))).run s =
      (.ok (.val (.int ((ReturningCall.value+1 : Nat) : Int) (by decide))),s) := rfl

/-- Capture the actual decoder run alongside the unmodified physical completion.
Timeout/stuck are Source halts, never converted into EVM failure outcomes. -/
def consume {Γ} (result : Option (Except Halt Outcome × Result env Γ)) :
    Option ((Except Halt (RVal env.layout (.ret [uint])) × EMState env Γ) × Result env Γ) :=
  result.map fun (outcome,completion) =>
    ((match outcome with
      | .ok out => (decode out).run completion.1.1.1
      | .error halt => (.error halt,completion.1.1.1)),completion)

def callThenDecode (G : Glob env) {Γ} (s : EMState env Γ)
    (r : ResidualJournal complementCarrierOwnership) (b : BoolEncodingJournal)
    (o : ObservedEffects env.layout env.lay env.lay) (shared : o.effects.execution=s.2.ex)
    (m : ByteView) (gas offset size : Word) :=
  consume (call (CallerFrame.liftInvoke (ReturningCall.invoke G)) s r b o shared m
    (ReturningCall.parent s) .call CallerFrameChecks.receiver gas 7 offset size)

theorem call_decode (G : Glob env) {Γ} (s : EMState env Γ)
    (next : ExecState env.layout env.lay env.lay)
    (code : (s.2.ex.world.accounts CallerFrameChecks.receiver).code=some 0)
    (transfer : s.2.ex.transfer CallerFrameChecks.owner CallerFrameChecks.receiver 7=some next)
    (r : ResidualJournal complementCarrierOwnership) (b : BoolEncodingJournal)
    (o : ObservedEffects env.layout env.lay env.lay) (shared : o.effects.execution=s.2.ex)
    (m : ByteView) (gas offset size : Word)
    (loaded : PhysicalHeapPort.port.load m offset size=some (ReturningCall.input G)) :
    callThenDecode G s r b o shared m gas offset size =
      some ((.ok (.val (.int (ReturningCall.value : Int) (by decide))),GeneralReturning.after s next),
        GeneralReturning.successResult s next r b o) := by
  unfold callThenDecode
  rw [GeneralReturning.call_actual G s next code transfer r b o shared m gas offset size loaded]
  change some ((decode (.success output)).run (GeneralReturning.after s next),_) = _
  rw [decode_output]

def staticThenDecode (G : Glob env) {Γ} (s : EMState env Γ)
    (r : ResidualJournal complementCarrierOwnership) (b : BoolEncodingJournal)
    (o : ObservedEffects env.layout env.lay env.lay) (shared : o.effects.execution=s.2.ex)
    (m : ByteView) (gas offset size : Word) :=
  consume (call (CallerFrame.liftInvoke (ReturningStatic.invoke G)) s r b o shared m
    (ReturningCall.parent s) .staticcall CallerFrameChecks.receiver gas 0 offset size)

theorem static_decode (G : Glob env) {Γ} (s : EMState env Γ)
    (next : ExecState env.layout env.lay env.lay)
    (code : (s.2.ex.world.accounts CallerFrameChecks.receiver).code=some 0)
    (transfer : s.2.ex.transfer CallerFrameChecks.owner CallerFrameChecks.receiver 0=some next)
    (r : ResidualJournal complementCarrierOwnership) (b : BoolEncodingJournal)
    (o : ObservedEffects env.layout env.lay env.lay) (shared : o.effects.execution=s.2.ex)
    (m : ByteView) (gas offset size : Word)
    (loaded : PhysicalHeapPort.port.load m offset size=some (ReturningCall.input G)) :
    staticThenDecode G s r b o shared m gas offset size =
      some ((.ok (.val (.int (ReturningCall.value : Int) (by decide))),GeneralReturning.after s next),
        GeneralReturning.successResult s next r b o) := by
  unfold staticThenDecode
  rw [GeneralReturning.static_call G s next code transfer r b o shared m gas offset size loaded]
  change some ((decode (.success output)).run (GeneralReturning.after s next),_) = _
  rw [decode_output]

theorem consume_halt {Γ} (c : Result env Γ) (halt : Halt) :
    consume (some (.error halt,c))=some ((.error halt,c.1.1.1),c) := rfl

theorem consume_refused {Γ} (c : Result env Γ) :
    consume (some (.ok (.revert []),c))=some ((.error (.revert []),c.1.1.1),c) := rfl

theorem consume_missing {Γ} : consume (none : Option (Except Halt Outcome × Result env Γ))=none := rfl

/-- Every carrier/journal/observation field, not just the typed decoded value. -/
theorem completion_frame {Γ} (s : EMState env Γ) next r b o :
    (GeneralReturning.successResult s next r b o).1.1.1 = GeneralReturning.after s next ∧
    (GeneralReturning.successResult s next r b o).1.1.2 = r ∧
    (GeneralReturning.successResult s next r b o).1.2 = b ∧
    (GeneralReturning.successResult s next r b o).2.trace = o.trace ∧
    (GeneralReturning.successResult s next r b o).2.effects.returndata = output :=
  ⟨rfl,rfl,rfl,rfl,rfl⟩


/-- Constructive same two-object caller heap, typed aliases, fnLocals and
caller observation/journal prefixes from the actual producer input. -/
def sample (G : Glob env) :=
  callThenDecode G (ReturningCall.caller G) CallerFrameChecks.residual CallerFrameChecks.encoding
    (ReturningCall.observed G) rfl (ReturningCall.memory G) 10000 160 4

theorem sample_run (G : Glob env) :
    sample G = some ((.ok (.val (.int (ReturningCall.value : Int) (by decide))),
      GeneralReturning.after (ReturningCall.caller G) ReturningCall.moved),
      GeneralReturning.successResult (ReturningCall.caller G) ReturningCall.moved
        CallerFrameChecks.residual CallerFrameChecks.encoding (ReturningCall.observed G)) :=
  call_decode G (ReturningCall.caller G) ReturningCall.moved rfl ReturningCall.transfer_actual
    _ _ _ rfl _ 10000 160 4 (ReturningCall.input_load G)

theorem static_sample (G : Glob env) :
    staticThenDecode G (ReturningCall.caller G) CallerFrameChecks.residual CallerFrameChecks.encoding
      (ReturningCall.observed G) rfl (ReturningCall.memory G) 10000 160 4 =
      some ((.ok (.val (.int (ReturningCall.value : Int) (by decide))),
        GeneralReturning.after (ReturningCall.caller G) ReturningStatic.zeroMoved),
        GeneralReturning.successResult (ReturningCall.caller G) ReturningStatic.zeroMoved
          CallerFrameChecks.residual CallerFrameChecks.encoding (ReturningCall.observed G)) :=
  static_decode G (ReturningCall.caller G) ReturningStatic.zeroMoved rfl ReturningStatic.transfer_zero
    _ _ _ rfl _ 10000 160 4 (ReturningCall.input_load G)

/-- Actual failed transfer, not a supplied revert outcome. -/
theorem call_refused_decode (G : Glob env) {Γ} (s : EMState env Γ)
    (code : (s.2.ex.world.accounts CallerFrameChecks.receiver).code=some 0)
    (transfer : s.2.ex.transfer CallerFrameChecks.owner CallerFrameChecks.receiver 7=none)
    (r : ResidualJournal complementCarrierOwnership) (b : BoolEncodingJournal)
    (o : ObservedEffects env.layout env.lay env.lay) (shared : o.effects.execution=s.2.ex)
    (m : ByteView) (gas offset size : Word)
    (loaded : PhysicalHeapPort.port.load m offset size=some (ReturningCall.input G)) :
    callThenDecode G s r b o shared m gas offset size =
      some ((.error (.revert []),s),GeneralReturning.refusedResult s r b o) := by
  unfold callThenDecode
  rw [GeneralReturning.call_refused G s code transfer r b o shared m gas offset size loaded]
  rfl

/-- Actual smaller horizon retains the transferred dirty source execution and
OLD return buffer; it is not rolled back or converted to a normal EVM revert. -/
theorem timeout_decode (G : Glob env) {Γ} (s : EMState env Γ)
    (next : ExecState env.layout env.lay env.lay)
    (code : (s.2.ex.world.accounts CallerFrameChecks.receiver).code=some 0)
    (transfer : s.2.ex.transfer CallerFrameChecks.owner CallerFrameChecks.receiver 7=some next)
    (r : ResidualJournal complementCarrierOwnership) (b : BoolEncodingJournal)
    (o : ObservedEffects env.layout env.lay env.lay) (shared : o.effects.execution=s.2.ex)
    (m : ByteView) (gas offset size : Word)
    (loaded : PhysicalHeapPort.port.load m offset size=some (ReturningCall.input G)) :
    consume (call (CallerFrame.liftInvoke (ReturningCall.invokeAt 6 G)) s r b o shared m
      (ReturningCall.parent s) .call CallerFrameChecks.receiver gas 7 offset size)=
      some ((.error .timeout,GeneralReturning.after s next),
        pending o ⟨⟨GeneralReturning.after s next,r⟩,b⟩ []) := by
  rw [GeneralReturning.call_timeout G s next code transfer r b o shared m gas offset size loaded]
  rfl

theorem input_refused_decode (G : Glob env) {Γ} (s : EMState env Γ)
    (r : ResidualJournal complementCarrierOwnership) (b : BoolEncodingJournal)
    (o : ObservedEffects env.layout env.lay env.lay) (shared : o.effects.execution=s.2.ex)
    (m : ByteView) (gas offset size : Word) (bad : PhysicalHeapPort.port.load m offset size=none) :
    callThenDecode G s r b o shared m gas offset size = none := by
  unfold callThenDecode
  rw [GeneralReturning.input_refused G s r b o shared m gas offset size bad]
  rfl

/-- Missing registered receiver code is an adapter refusal BEFORE invocation,
not an empty-success value or a claimed general no-code EVM behavior. -/
theorem missing_code (G : Glob env) {Γ} (s : EMState env Γ)
    (missing : (s.2.ex.world.accounts CallerFrameChecks.receiver).code=none)
    (r : ResidualJournal complementCarrierOwnership) (b : BoolEncodingJournal)
    (o : ObservedEffects env.layout env.lay env.lay) (gas : Word) :
    ReturningCall.invoke G o (enter s r (ReturningCall.parent s) .call CallerFrameChecks.receiver 7 (ReturningCall.input G))
      .call CallerFrameChecks.receiver gas (ReturningCall.input G) ⟨⟨⟨L0 env,s.2⟩,r⟩,b⟩ = none := by
  unfold ReturningCall.invoke ReturningCall.invokeAt ReturningCall.invokeTemplateAt ReturningCall.template
  simp only [enter,ReturningCall.parent,ExecState.enter,missing,reduceCtorEq,decide_false,Bool.and_false,if_false]

/-- Full source heap/aliases/saved frame/log fields after typed decoding. -/
theorem sample_state (G : Glob env) :
    (GeneralReturning.after (ReturningCall.caller G) ReturningCall.moved).1=ReturningCall.locals ∧
    (GeneralReturning.after (ReturningCall.caller G) ReturningCall.moved).2.heap=ReturningCall.heap G ∧
    (GeneralReturning.after (ReturningCall.caller G) ReturningCall.moved).2.fnLocals=(ReturningCall.caller G).2.fnLocals ∧
    (GeneralReturning.after (ReturningCall.caller G) ReturningCall.moved).2.logs=[(CallerFrameChecks.owner,[0x70])] :=
  ⟨rfl,rfl,rfl,rfl⟩


/-- General physical input load is discharged by the actual finite heap encoder;
no arbitrary byte image is identified with logical heap indices. -/
theorem call_decode_encoded (G : Glob env) {Γ} (s : EMState env Γ)
    (next : ExecState env.layout env.lay env.lay)
    (code : (s.2.ex.world.accounts CallerFrameChecks.receiver).code=some 0)
    (transfer : s.2.ex.transfer CallerFrameChecks.owner CallerFrameChecks.receiver 7=some next)
    (r : ResidualJournal complementCarrierOwnership) (b : BoolEncodingJournal)
    (o : ObservedEffects env.layout env.lay env.lay) (shared : o.effects.execution=s.2.ex)
    (p : Placement s.2.heap) (es : List (HeapByteEntry s.2.heap))
    (distinct : (es.map HeapByteEntry.id).Nodup) (e : HeapByteEntry s.2.heap)
    (member : e ∈ es) (bytes : e.bytes=ReturningCall.input G) (background : ByteView) (gas : Word) :
    callThenDecode G s r b o shared (encodeByteHeap p es background) gas
      (PhysicalHeapPort.payloadOffset s.2.heap p e.id e.string e.bytes e.found)
      ⟨e.bytes.length,heapByte_length_bound s.2.heap p e.id e.string e.bytes e.found⟩ =
      some ((.ok (.val (.int (ReturningCall.value : Int) (by decide))),GeneralReturning.after s next),
        GeneralReturning.successResult s next r b o) := by
  apply call_decode G s next code transfer r b o shared
  exact (PhysicalHeapPort.load_encoded s.2.heap p es distinct e member background).trans (congrArg some bytes)

/-- After the actual bounded output copy, decoding its unchanged full return
buffer preserves the copied source heap exactly. The consumer runs the actual
copy operation, rather than assuming a favorable output heap. -/
def decodeCopied {Γ} (c : Result env Γ)
    (shared : c.2.effects.execution=c.1.1.1.2.ex) (p : Placement c.1.1.1.2.heap)
    (a : Nat) (string : Bool) (old : Bytes)
    (found : c.1.1.1.2.heap.get a=some ⟨heapByteType string,heapByteData env.layout string old⟩)
    (memory : ByteView) (offset capacity : Word) :=
  let copied := copyOutput c shared p a string old found memory offset capacity
  (copied, copied.2.map fun answer => (decode (.success c.2.effects.returndata)).run answer.1.2)

theorem copied_decoder {Γ} (s : EMState env Γ) (next : ExecState env.layout env.lay env.lay)
    (r : ResidualJournal complementCarrierOwnership) (b : BoolEncodingJournal)
    (o : ObservedEffects env.layout env.lay env.lay) (p : Placement s.2.heap)
    (es : List (HeapByteEntry s.2.heap)) (distinct : (es.map HeapByteEntry.id).Nodup)
    (e : HeapByteEntry s.2.heap) (member : e ∈ es) (background : ByteView)
    (offset capacity : Word) (inside : offset.val+min capacity.val output.length≤e.bytes.length) :
    (decodeCopied (GeneralReturning.successResult s next r b o) rfl p e.id e.string e.bytes e.found
      (encodeByteHeap p es background) offset capacity).2 =
      some (.ok (.val (.int (ReturningCall.value : Int) (by decide))),
        withSourceHeap (GeneralReturning.after s next) (s.2.heap.write e.id
          (heapByteData env.layout e.string (HeapWindow.splice e.bytes offset.val (callOutput output capacity.val)))
          (heap_ty_of_get _ e.id _ _ e.found))) := by
  unfold decodeCopied
  rw [GeneralReturning.output_encoded s next r b o p es distinct e member background offset capacity inside]
  change some ((decode (.success output)).run _) = _
  rw [decode_output]

end Solidity.Yul.Composition.ReturningPhysical
