import Solidity.Yul.World.StaticEventControls

/-! Actual Source.emit/common-log port for direct-word arguments with a proved
pure argument evaluation. The pure-expression premise is explicit; arbitrary
argument side effects need separate physical journal transport. -/
namespace Solidity.Yul.World.StaticEventPort
open Solidity.Source
open Solidity.Roadmap (Word Bytes)
open Solidity.Yul.Views
open Solidity.Yul.World.PhysicalCompletion
open Solidity.Yul.World.StaticEventArgs
open Solidity.Yul.World.StaticEventEncoding

def after {E : Env} {Δ : RCtx} {ts : List STy} (G : Glob E) (F : Fr) (event : Decl) (words : List Word)
    (s : EMState E Δ) : EMState E Δ :=
  ⟨s.1,{s.2 with logs:=(F.this,G.selector (sigOf E.layout event.name ts)++
    Source.abiLayout (words.map (fun w=>(false,wordBytes w))))::s.2.logs}⟩

def source {E Γ Δ ts} (G : Glob E) (F : Fr) (n : Nat) (event : Decl)
    (typed : event.paramTys E=some ts) (args : RConvArgs E Γ ts) (l : Locals E.layout Γ)
    (s : EMState E Δ) :=
  (Source.EM.sub (Source.L0 E) (Source.execS G F (n+1) 0 none (StaticEventSource.statement event typed args) l)).run s

theorem source_normal {E Γ Δ ts} (G : Glob E) (F : Fr) (n : Nat) (event : Decl)
    (typed : event.paramTys E=some ts) (args : RConvArgs E Γ ts) (l : Locals E.layout Γ)
    (s : EMState E Δ) (vs : Vals E.layout ts)
    (evaluated : (Source.evalConvArgs G F n args).run ⟨l,s.2⟩=(.ok vs,⟨l,s.2⟩))
    (words : List Word) (computed : words? vs=some words) (normal : F.static=false) :
    source G F n event typed args l s=(.ok (.normal l,Source.L0 E),after (ts:=ts) G F event words s) := by
  unfold source
  rw [Source.run_sub,StaticEventSource.actual G F n event typed args l l s.2 s.2 vs evaluated words computed normal]
  rfl

theorem source_static {E Γ Δ ts} (G : Glob E) (F : Fr) (n : Nat) (event : Decl)
    (typed : event.paramTys E=some ts) (args : RConvArgs E Γ ts) (l : Locals E.layout Γ)
    (s : EMState E Δ) (vs : Vals E.layout ts)
    (evaluated : (Source.evalConvArgs G F n args).run ⟨l,s.2⟩=(.ok vs,⟨l,s.2⟩))
    (words : List Word) (computed : words? vs=some words) (static : F.static=true) :
    source G F n event typed args l s=(.error (.revert []),s) := by
  unfold source
  rw [Source.run_sub,StaticEventSource.actual_static G F n event typed args l l s.2 s.2 vs evaluated words computed static]

/-- Execute the actual Source node, then the existing pure selected ABI codec.
Proofs below require concrete metadata/partition checks, never a desired run. -/
def execute {E Γ Δ ts} (G : Glob E) (F : Fr) (n : Nat) (event : Decl)
    (typed : event.paramTys E=some ts) (args : RConvArgs E Γ ts) (l : Locals E.layout Γ)
    (s : EMState E Δ) (vs : Vals E.layout ts)
    (_evaluated : (Source.evalConvArgs G F n args).run ⟨l,s.2⟩=(.ok vs,⟨l,s.2⟩))
    (flags : List Bool) (anonymous : Bool) (_shape : metadata event=some (flags,anonymous))
    (part : Split E.layout) (_partition : split flags vs=some part)
    (_fits : (topics (ts:=ts) G event anonymous part).length<5)
    (r : ResidualJournal complementCarrierOwnership) (b : BoolEncodingJournal)
    (o : ObservedEffects E.layout E.lay E.lay) (_shared : o.effects.execution=s.2.ex) :
    ((Except Halt Unit × Carrier E Δ) × ObservedEffects E.layout E.lay E.lay) :=
  let actual:=source G F n event typed args l s
  let formatted:=(encode G F n event typed vs).run actual.2
  ((actual.1.map (fun _=>()),⟨⟨actual.2,r⟩,b⟩),
    match actual.1,formatted.1 with
    | .ok _,.ok (some log) => emitObserved o log
    | _,_ => o)

theorem execute_normal {E Γ Δ ts} (G : Glob E) (F : Fr) (n : Nat) (event : Decl)
    (typed : event.paramTys E=some ts) (args : RConvArgs E Γ ts) (l : Locals E.layout Γ)
    (s : EMState E Δ) (vs : Vals E.layout ts)
    (evaluated : (Source.evalConvArgs G F n args).run ⟨l,s.2⟩=(.ok vs,⟨l,s.2⟩))
    (words : List Word) (computed : words? vs=some words) (normal : F.static=false)
    (flags : List Bool) (anonymous : Bool) (shape : metadata event=some (flags,anonymous))
    (part : Split E.layout) (partition : split flags vs=some part)
    (dataWords : List Word) (dataComputed : words? part.2.2=some dataWords)
    (fits : (topics (ts:=ts) G event anonymous part).length<5)
    (r : ResidualJournal complementCarrierOwnership) (b : BoolEncodingJournal)
    (o : ObservedEffects E.layout E.lay E.lay) (shared : o.effects.execution=s.2.ex) :
    execute G F n event typed args l s vs evaluated flags anonymous shape part partition fits r b o shared=
      ((.ok (),⟨⟨after (ts:=ts) G F event words s,r⟩,b⟩),emitObserved o
        (resultLog (ts:=ts) G F event anonymous part fits
          (Source.abiLayout (dataWords.map (fun w=>(false,wordBytes w)))))) := by
  unfold execute
  rw [source_normal G F n event typed args l s vs evaluated words computed normal]
  dsimp only
  rw [encode_exact G F n event typed vs _ flags anonymous shape part partition dataWords dataComputed fits]
  rfl
end Solidity.Yul.World.StaticEventPort
