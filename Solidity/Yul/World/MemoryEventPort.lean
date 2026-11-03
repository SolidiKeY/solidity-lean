import Solidity.Yul.World.MemoryEventControls

/-! Actual Source/common-observation port for checked pure arguments including
memory bytes/string. All lower executions are real computations, not callee
outcome premises. General side-effecting arguments remain outside this port. -/
namespace Solidity.Yul.World.MemoryEventPort
open Solidity.Source
open Solidity.Roadmap (Bytes)
open Solidity.Yul.Views
open Solidity.Yul.World.PhysicalCompletion
open Solidity.Yul.World.StaticEventEncoding (Split metadata topics resultLog)

def after {E : Env} {Δ : RCtx} {ts : List STy} (G : Glob E) (F : Fr) (event : Decl) (legacy : Bytes)
    (s : EMState E Δ) : EMState E Δ :=
  ⟨s.1,{s.2 with logs:=(F.this,G.selector (sigOf E.layout event.name ts)++legacy)::s.2.logs}⟩

theorem source_normal {E Γ Δ ts} (G : Glob E) (F : Fr) (n : Nat) (event : Decl)
    (typed : event.paramTys E=some ts) (args : RConvArgs E Γ ts) (l : Locals E.layout Γ)
    (s : EMState E Δ) (vs : Vals E.layout ts)
    (evaluated : (Source.evalConvArgs G F n args).run ⟨l,s.2⟩=(.ok vs,⟨l,s.2⟩))
    (legacy : Bytes) (codec : (Source.encodeVals F n false vs.toR).run ⟨Source.L0 E,s.2⟩=(.ok legacy,⟨Source.L0 E,s.2⟩))
    (normal : F.static=false) :
    StaticEventPort.source G F n event typed args l s=(.ok (.normal l,Source.L0 E),after (ts:=ts) G F event legacy s) := by
  unfold StaticEventPort.source
  rw [Source.run_sub,MemoryEventSource.actual G F n event typed args l l s.2 s.2 vs evaluated legacy codec normal]
  rfl

theorem source_static {E Γ Δ ts} (G : Glob E) (F : Fr) (n : Nat) (event : Decl)
    (typed : event.paramTys E=some ts) (args : RConvArgs E Γ ts) (l : Locals E.layout Γ)
    (s : EMState E Δ) (vs : Vals E.layout ts)
    (evaluated : (Source.evalConvArgs G F n args).run ⟨l,s.2⟩=(.ok vs,⟨l,s.2⟩))
    (legacy : Bytes) (codec : (Source.encodeVals F n false vs.toR).run ⟨Source.L0 E,s.2⟩=(.ok legacy,⟨Source.L0 E,s.2⟩))
    (static : F.static=true) :
    StaticEventPort.source G F n event typed args l s=(.error (.revert []),s) := by
  unfold StaticEventPort.source
  rw [Source.run_sub,MemoryEventSource.actual_static G F n event typed args l l s.2 s.2 vs evaluated legacy codec static]

def execute {E Γ Δ ts} (G : Glob E) (F : Fr) (n : Nat) (event : Decl)
    (typed : event.paramTys E=some ts) (args : RConvArgs E Γ ts) (l : Locals E.layout Γ) (_localArgs : LocalEventBoundary.LocalArguments args)
    (s : EMState E Δ) (vs : Vals E.layout ts)
    (_evaluated : (Source.evalConvArgs G F n args).run ⟨l,s.2⟩=(.ok vs,⟨l,s.2⟩))
    (legacy : Bytes) (_fullCodec : (Source.encodeVals F n false vs.toR).run ⟨Source.L0 E,s.2⟩=(.ok legacy,⟨Source.L0 E,s.2⟩))
    (flags : List Bool) (anonymous : Bool) (_shape : metadata event=some (flags,anonymous))
    (part : Split E.layout) (_partition : (MemoryEventEncoding.split G F n flags vs).run s=(.ok (some part),s))
    (data : Bytes) (_codec : (Source.encodeVals F n false part.2.2.toR).run s=(.ok data,s))
    (_fits : (topics (ts:=ts) G event anonymous part).length<5)
    (r : ResidualJournal complementCarrierOwnership) (b : BoolEncodingJournal)
    (o : ObservedEffects E.layout E.lay E.lay) (_shared : o.effects.execution=s.2.ex) :
    ((Except Halt Unit × Carrier E Δ) × ObservedEffects E.layout E.lay E.lay) :=
  let formatted:=(MemoryEventEncoding.encode G F n event typed vs).run s
  let actual:=StaticEventPort.source G F n event typed args l s
  ((actual.1.map (fun _=>()),⟨⟨actual.2,r⟩,b⟩),
    match actual.1,formatted.1 with
    | .ok _,.ok (some log) => emitObserved o log
    | _,_ => o)

theorem execute_normal {E Γ Δ ts} (G : Glob E) (F : Fr) (n : Nat) (event : Decl)
    (typed : event.paramTys E=some ts) (args : RConvArgs E Γ ts) (l : Locals E.layout Γ) (localArgs : LocalEventBoundary.LocalArguments args)
    (s : EMState E Δ) (vs : Vals E.layout ts)
    (evaluated : (Source.evalConvArgs G F n args).run ⟨l,s.2⟩=(.ok vs,⟨l,s.2⟩))
    (legacy : Bytes) (fullCodec : (Source.encodeVals F n false vs.toR).run ⟨Source.L0 E,s.2⟩=(.ok legacy,⟨Source.L0 E,s.2⟩))
    (flags : List Bool) (anonymous : Bool) (shape : metadata event=some (flags,anonymous))
    (part : Split E.layout) (partition : (MemoryEventEncoding.split G F n flags vs).run s=(.ok (some part),s))
    (data : Bytes) (codec : (Source.encodeVals F n false part.2.2.toR).run s=(.ok data,s))
    (fits : (topics (ts:=ts) G event anonymous part).length<5)
    (r : ResidualJournal complementCarrierOwnership) (b : BoolEncodingJournal)
    (o : ObservedEffects E.layout E.lay E.lay) (shared : o.effects.execution=s.2.ex) (normal : F.static=false) :
    execute G F n event typed args l localArgs s vs evaluated legacy fullCodec flags anonymous shape part partition data codec fits r b o shared=
      ((.ok (),⟨⟨after (ts:=ts) G F event legacy s,r⟩,b⟩),emitObserved o (resultLog (ts:=ts) G F event anonymous part fits data)) := by
  unfold execute
  rw [MemoryEventEncoding.encode_exact G F n event typed vs s flags anonymous shape part partition data codec fits,
    source_normal G F n event typed args l s vs evaluated legacy fullCodec normal]
  rfl
end Solidity.Yul.World.MemoryEventPort
