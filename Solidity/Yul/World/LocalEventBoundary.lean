import Solidity.Yul.World.StaticEventRaw

/-! Source-state equality alone is not a call-freedom certificate: known
selfcalls may leave net state unchanged. This intrinsic consumer domain names
actual self-typed local arguments, not a world-adequacy premise or new AST.
The older StaticEventPort equations remain computed Source-adapter equations;
use the constrained entry below when reasoning about argument call freedom.
Compiler-generated-call noninterference remains a separate open obligation. -/
namespace Solidity.Yul.World.LocalEventBoundary
open Solidity.Source
open Solidity.Yul.Views
open Solidity.Yul.World.PhysicalCompletion
open Solidity.Yul.World.StaticEventEncoding (Split metadata topics split)

inductive LocalArguments {E : Env} {Γ : RCtx} : {ts : List STy} → RConvArgs E Γ ts → Prop where
  | nil : LocalArguments .nil
  | cons {τ : STy} {ts : List STy} (i : Source.Idx Γ τ)
      (self : τ.implicit E.isBase τ=true) (rest : RConvArgs E Γ ts) :
      LocalArguments rest → LocalArguments (.cons (.local i) self rest)
def staticExecute {E Γ Δ ts} (G : Glob E) (F : Fr) (n : Nat) (event : Decl)
    (typed : event.paramTys E=some ts) (args : RConvArgs E Γ ts) (l : Locals E.layout Γ) (_local : LocalArguments args)
    (s : EMState E Δ) (vs : Vals E.layout ts)
    (_evaluated : (Source.evalConvArgs G F n args).run ⟨l,s.2⟩=(.ok vs,⟨l,s.2⟩))
    (flags : List Bool) (anonymous : Bool) (_shape : metadata event=some (flags,anonymous))
    (part : Split E.layout) (_partition : split flags vs=some part)
    (_fits : (topics (ts:=ts) G event anonymous part).length<5)
    (r : ResidualJournal complementCarrierOwnership) (b : BoolEncodingJournal)
    (o : ObservedEffects E.layout E.lay E.lay) (_shared : o.effects.execution=s.2.ex) :
    ((Except Halt Unit × Carrier E Δ) × ObservedEffects E.layout E.lay E.lay) :=
  StaticEventPort.execute G F n event typed args l s vs _evaluated flags anonymous _shape part _partition _fits r b o _shared

theorem static_arguments_local (anonymous : Bool) : LocalArguments (StaticEventControls.args anonymous) := by
  unfold StaticEventControls.args
  repeat constructor

end Solidity.Yul.World.LocalEventBoundary
