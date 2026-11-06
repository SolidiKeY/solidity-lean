import Solidity.Yul.Composition.FailurePhysical
open Solidity
open Lean Solidity.Source Solidity.Yul Solidity.Yul.Views Solidity.Yul.World Solidity.Yul.World.PhysicalCompletion
open Solidity.Yul.Composition Solidity.Yul.Composition.FailurePhysical
open Solidity.Yul.World.ReturningCall (env)

/-- Selected concrete Fixed hash only for finite Source controls; main laws
quantify G and retain its actual selector as an explicit producer input. -/
def global : Glob env where
  prog := {
    body := fun _=>none
    consts := fun _=>none
    inits := fun _=>[]
    ctor := fun _=>none
    ctorLocals := fun _=>[]
    baseArgs := fun _=>[]
    contracts := [] }
  pipeline := .legacy
  fixed := {
    evm := Solidity.Roadmap.Evm.withKeccak
    ledger := fun balance _ a=>balance a
    regionLen := 1
    rootSlots := 1 }
  balance0 := fun _=>0
  hasCode := fun _ _=>false
  callee := fun _=>.answer (.success [])
  timestamp := 0

def bytesJson (bs : Solidity.Roadmap.Bytes) : Json := toJson (bs.map UInt8.toNat)
def reference {τ} (value : Val env.layout τ) : Json :=
  match value with | .memRef _ id=>Json.mkObj [("logicalIndex",toJson id)] | _=>Json.mkObj [("unexpected",toJson true)]
def localJson {Γ} : Locals env.layout Γ → List Json
  | .nil=>[]
  | .cons value rest=>reference value::localJson rest

def objectJson (state : Source.St env) (id : Nat) : Json :=
  match state.heap.get id with
  | some ⟨_,.bytes bs⟩=>Json.mkObj [("kind",toJson "bytes"),("bytes",bytesJson bs)]
  | none=>Json.null
  | some _=>Json.mkObj [("kind",toJson "unexpected")]

def storageJson {L} (s : Storage env.layout L) : Json := toJson
  ([s.cell Views.Controls.finiteFlag |>.isSome,s.cell Views.Controls.finiteSmall |>.isSome,
    s.cell Views.Controls.packedBytesPath |>.isSome,s.cell Views.Controls.packedAddressPath |>.isSome] : List Bool)

def accountJson {L} (a : Account env.layout L) : Json :=
  Json.mkObj [("balance",toJson (toString a.balance.val)),("nonce",toJson a.nonce),("code",toJson a.code),("storagePresence",storageJson a.storage)]
def addresses : List Solidity.Roadmap.Address := [1,32,48,49,64]
def entryJson : Entry env.layout env.lay env.lay → Json
  | .account a old=>Json.mkObj [("kind",toJson "account"),("address",toJson (toString a.val)),("old",accountJson old)]
  | .transient a old=>Json.mkObj [("kind",toJson "transient"),("address",toJson (toString a.val)),("old",storageJson old)]

def eventJson : Solidity.Roadmap.Event → Json
  | .credit a value=>Json.mkObj [("kind",toJson "credit"),("address",toJson (toString a.val)),("value",toJson (toString value.val))]
  | other=>Json.mkObj [("unexpected",toJson (reprStr other))]
def observationJson : Observation → Json
  | .event e=>Json.mkObj [("kind",toJson "event"),("event",eventJson e)]
  | .log l=>Json.mkObj [("kind",toJson "log"),("emitter",toJson (toString l.emitter.val)),
      ("topics",toJson (l.topics.toList.map fun x=>toString x.val)),("data",bytesJson l.data)]

def stateJson {Γ} (s : EMState env Γ) : Json :=
  Json.mkObj [("locals",toJson (localJson s.1)),("heapNext",toJson s.2.heap.next),
    ("heap",toJson ([0,1,2].map (objectJson s.2))),
    ("fnLocals",match s.2.fnLocals with | ⟨_,ls⟩=>toJson (localJson ls)),
    ("events",toJson (s.2.events.map eventJson)),
    ("legacyLogs",toJson (s.2.logs.map fun(a,bs)=>Json.arr #[toJson (toString a.val),bytesJson bs])),
    ("world",toJson (addresses.map fun a=>Json.mkObj [("address",toJson (toString a.val)),("account",accountJson (s.2.ex.world.accounts a)),("transientPresence",storageJson (s.2.ex.transient.cells a))])),
    ("journal",toJson (s.2.ex.journal.map entryJson))]

def residualJson (r : ResidualJournal complementCarrierOwnership) : Json := toJson
  (r.journal.map fun(k,v)=>Json.arr #[toJson k.transient,toJson (toString k.address.val),toJson (toString k.slot.val),toJson (toString v.val)])
def ownedJson (b : BoolEncodingJournal) : Json := toJson
  (b.journal.map fun(k,v)=>Json.arr #[toJson k.transient,toJson (toString k.account.val),toJson (toString k.slot.val),toJson k.offset.val,toJson v.val.val])
def residualKey : ResidualKey complementCarrierOwnership := ⟨false,1,7,by intro bad; exact bad⟩
def ownedKey : OwnedByteKey := ⟨false,1,7,⟨0,by decide⟩⟩
def journalJson (r : ResidualJournal complementCarrierOwnership) (b : BoolEncodingJournal) : Json :=
  Json.mkObj [("residual",residualJson r),("owned",ownedJson b),
    ("selectedResidual",toJson (toString (r.cells residualKey).val)),("selectedOwnedByte",toJson (b.cells ownedKey).val.val)]

def rawJson (raw : LocalValues env RawContext) : Json :=
  let scalar := fun {τ} (value : LocalValue env τ) => match value.scalar? with | some v=>toJson (toString v.val) | none=>Json.null
  let fn := fun (value : LocalValue env FunctionType) => match value with
    | .externalFunction _ _ _ a s=>Json.mkObj [("address",toJson (toString a.val)),("selector",toJson (toString s.val))]
    | _=>Json.null
  Json.mkObj [("bool",scalar (raw.get .here)),("uint8",scalar (raw.get (.there .here))),
    ("first",fn (raw.get (.there (.there .here)))),("second",fn (raw.get (.there (.there (.there .here))))),
    ("memory",match raw.get (.there (.there (.there (.there .here)))) with | .clean v=>reference v | _=>Json.null),
    ("clean",toJson (LocalValues.clean? RawContext raw).isSome)]

def haltJson : Halt → Json
  | .revert bs=>Json.mkObj [("tag",toJson "revert"),("bytes",bytesJson bs)]
  | .timeout=>Json.mkObj [("tag",toJson "timeout")]
  | .stuck why=>Json.mkObj [("tag",toJson "stuck"),("reason",toJson why)]
def outcomeJson : Except Halt Solidity.Roadmap.Outcome → Json
  | .error h=>Json.mkObj [("tag",toJson "halt"),("halt",haltJson h)]
  | .ok (.success bs)=>Json.mkObj [("tag",toJson "success"),("bytes",bytesJson bs)]
  | .ok (.revert bs)=>Json.mkObj [("tag",toJson "revert"),("bytes",bytesJson bs)]
def consumerJson : Except Halt Solidity.Roadmap.Bytes → Json
  | .error h=>haltJson h
  | .ok bs=>Json.mkObj [("tag",toJson "success"),("bytes",bytesJson bs)]

def physicalJson {Γ} (c : Result env Γ) : Json :=
  Json.mkObj [("state",stateJson c.1.1.1),("journals",journalJson c.1.1.2 c.1.2),
    ("returndata",bytesJson c.2.effects.returndata),("trace",toJson (c.2.trace.map observationJson))]

def row (name layer : String) (g : Glob env) (s : EMState env [.bytes .memory,.bytes .memory])
    (fuel : Nat) (actual : Option (Except Halt Solidity.Roadmap.Outcome × Result env [.bytes .memory,.bytes .memory])) : Json :=
  let consumed := withRaw rawValues (consume g ReturningCall.parentFrame fuel actual)
  let before := stateJson s
  let producer := actual.map fun (status,c)=>Json.mkObj [("status",outcomeJson status),("completion",physicalJson c),
    ("completed",toJson (match status with | .ok _=>true | .error _=>false))]
  let after := consumed.map fun (run,raw)=>Json.mkObj [("status",consumerJson run.1.1),("state",stateJson run.1.2),("raw",rawJson raw.1)]
  Json.mkObj [("name",toJson name),("layer",toJson layer),("before",before),("rawBefore",rawJson rawValues),
    ("producer",producer.getD Json.null),("consumer",after.getD Json.null)]

def poor := SourceBoundaryRules.prefixedExecution.apply (.account CallerFrameChecks.owner (fun a=>a.withBalance 0))
def overflow := SourceBoundaryRules.prefixedExecution.apply (.account CallerFrameChecks.receiver (fun a=>a.withBalance (toWord (2^256-1))))
def unregistered := SourceBoundaryRules.prefixedExecution.apply (.account CallerFrameChecks.receiver (fun a=>{a with code:=none}))

def wrongKind (g : Glob env) : Invoke env [.bytes .memory,.bytes .memory] :=
  fun o f _ target gas bs c=>CallerFrame.liftInvoke (GeneralFailure.staticInvoke g) o f .call target gas bs c
def wrongStatic (g : Glob env) : Invoke env [.bytes .memory,.bytes .memory] :=
  fun o f kind target gas bs c=>CallerFrame.liftInvoke (GeneralFailure.staticInvoke g) o {f with source:={f.source with static:=false}} kind target gas bs c

def model (pipeline : Solidity.Roadmap.Pipeline) : Json := Id.run do
  let g := {global with pipeline:=pipeline}
  let s := caller g
  let actual := fun invoke kind value (state : EMState env [.bytes .memory,.bytes .memory])
      (o : ObservedEffects env.layout env.lay env.lay) (shared : o.effects.execution=state.2.ex) =>
    call invoke state CallerFrameChecks.residual CallerFrameChecks.encoding o shared
    (ReturningCall.memory g) (ReturningCall.parent state) kind CallerFrameChecks.receiver 10000 value 160 4
  let rawCall := actual (CallerFrame.liftInvoke (ReturningCall.invokeFailure g)) .call 7 s observed rfl
  let rawStatic := actual (CallerFrame.liftInvoke (GeneralFailure.staticInvoke g)) .staticcall 0 s observed rfl
  let rows := [row "call" "actual-known-call" g s 4 rawCall,row "static" "actual-known-staticcall" g s 4 rawStatic,
    row "consumer-timeout" "actual-known-call" g s 0 rawCall,
    row "entered-child-timeout" "actual-known-call-horizon6" g s 4
      (actual (CallerFrame.liftInvoke (ReturningCall.invokeTemplateAt 6 true g)) .call 7 s observed rfl)]
  let poorS:=GeneralReturningChecks.caller g poor
  let overflowS:=GeneralReturningChecks.caller g overflow
  let missingS:=GeneralReturningChecks.caller g unregistered
  let rows:=rows++[
    row "insufficient-transfer" "actual-known-refusal" g poorS 4
      (actual (CallerFrame.liftInvoke (ReturningCall.invokeFailure g)) .call 7 poorS (GeneralReturningChecks.observed poor) rfl),
    row "overflow-transfer" "actual-known-refusal" g overflowS 4
      (actual (CallerFrame.liftInvoke (ReturningCall.invokeFailure g)) .call 7 overflowS (GeneralReturningChecks.observed overflow) rfl),
    row "missing-code" "adapter-refusal" g missingS 4
      (actual (CallerFrame.liftInvoke (ReturningCall.invokeFailure g)) .call 7 missingS (GeneralReturningChecks.observed unregistered) rfl),
    row "static-wrong-kind" "adapter-refusal" g s 4 (actual (wrongKind g) .staticcall 0 s observed rfl),
    row "static-nonstatic-frame" "adapter-refusal" g s 4 (actual (wrongStatic g) .staticcall 0 s observed rfl)]
  let boundary := fun outcome=>some (.ok outcome,finish s CallerFrameChecks.encoding observed
    (enter s CallerFrameChecks.residual (ReturningCall.parent s) .call CallerFrameChecks.receiver 7 (ReturningCall.input g))
    ⟨⟨s,CallerFrameChecks.residual⟩,CallerFrameChecks.encoding⟩ [] outcome)
  let data:=ReturningCall.errorData g
  let wrongSelector:=data.set 0 ((data.headD 0) ^^^ 1)
  let wrongPayload:=data.set 35 0x56
  let rows:=rows++[
    row "wrong-selector" "decoder-boundary-control" g s 4 (boundary (.revert wrongSelector)),
    row "wrong-payload" "decoder-boundary-control" g s 4 (boundary (.revert wrongPayload)),
    row "truncated" "decoder-boundary-control" g s 4 (boundary (.revert (data.take 35))),
    row "empty-revert" "decoder-boundary-control" g s 4 (boundary (.revert [])),
    row "short-success" "decoder-boundary-control" g s 4 (boundary (.success [0x11,0x22])),
    row "normal-success" "decoder-boundary-control" g s 4 (boundary (.success ReturningCall.output))]
  let copied := copyCatch g ReturningCall.parentFrame 4
    (GeneralFailure.result g s CallerFrameChecks.residual CallerFrameChecks.encoding observed)
    rfl (ReturningCall.placement g) 1 false ReturningCall.old rfl (ReturningCall.memory g) 1 4 2
  let copiedJson := copied.1.2.map fun out=>Json.mkObj [
    ("physicalBytes",bytesJson (readBytes out.1.1 288 6)),("state",stateJson out.1.2),
    ("journals",journalJson out.2.1.1 out.2.1.2),("returndata",bytesJson out.2.2.effects.returndata),
    ("trace",toJson (out.2.2.trace.map observationJson))]
  let caughtJson := copied.2.map fun out=>Json.mkObj [("status",consumerJson out.1.1),("state",stateJson out.1.2),
    ("journals",journalJson out.2.1.1 out.2.1.2),("returndata",bytesJson out.2.2.effects.returndata),
    ("trace",toJson (out.2.2.trace.map observationJson))]
  let invalid := copyCatch g ReturningCall.parentFrame 4
    (GeneralFailure.result g s CallerFrameChecks.residual CallerFrameChecks.encoding observed)
    rfl (ReturningCall.placement g) 1 false ReturningCall.old rfl (ReturningCall.memory g) 1 37 0
  let decoded := (Source.decodeArg (data.drop 4) 0 ReturningCall.uint : EM env [] _).run (L0 env,s.2)
  let decodedValue := match decoded.1 with | .ok value=>toJson (value.key.map fun n=>toString n) | .error h=>haltJson h
  return Json.mkObj [("pipeline",toJson (match pipeline with | .legacy=>"legacy" | .viaIR=>"viaIR")),("cases",toJson rows),
    ("copied",copiedJson.getD Json.null),("copiedCatch",caughtJson.getD Json.null),
    ("invalidCopy",Json.mkObj [("completion",physicalJson invalid.1.1),("copyIsNone",toJson invalid.1.2.isNone),("consumerIsNone",toJson invalid.2.isNone)]),
    ("decodedKnownArgument",decodedValue),("exactEnd",((returnWindow data 36 0).map bytesJson).getD Json.null)]

def main : IO Unit := IO.println (Json.compress (Json.mkObj [("schema",toJson (1:Nat)),
  ("engine",toJson "actual-GeneralFailure-Source-consumer"),("nativeComparisons",toJson (0:Nat)),
  ("fullProofGate",toJson "pending"),("profiles",toJson [model .legacy,model .viaIR])]))
