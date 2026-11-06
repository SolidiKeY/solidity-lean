import Solidity.Backend.WorldCalls.Callbacks
import Solidity.Lowering.Readonly.CallerResume

/-! G42.02 conditional consumers of the actual fetched execution and raw
producers. P10's optional reference relation must be adapted to FetchedPremises;
no Bridge import or automatic source/world/ABI refinement enters the core. -/
namespace Solidity.Backend.WorldCalls.ExternalCalls
open Solidity.Source Solidity.Roadmap
open Solidity.Lowering.Readonly
variable {E : Env} {Γ : RCtx} {dn : DeclName} {ps rs : List STy}
variable {i : InvocationFrame.Invocation E Γ dn ps rs}

theorem fetched (p : Premises i) (f : FetchedPremises i p)
    (initial : Evm.Machine) (raw : Except Halt Outcome) (final : St E) (target : Evm.Out)
    (h : f.Fetched initial raw final target) :
    (∃ call : FetchedCall p.code.full initial, f.Returndata (identity i) call target raw) ∧
      Evm.run p.code.full initial = target ∧ i.RawAt raw final :=
  ⟨⟨f.fetch _ _ _ _ h, f.returndata _ _ _ _ h⟩,
    p.execution _ _ _ _ _ (f.step _ _ _ _ h), p.sourceRaw _ _ _ _ _ (f.step _ _ _ _ h)⟩

/-- Declared result decoding is the REAL Source.extReturn at the actual
post-argument caller locals and exact callee final state. There is no assumed
successful decode, discarded-result shortcut, or favorable byte array. -/
theorem declared_return (p : Premises i) (f : FetchedPremises i p)
    (initial : Evm.Machine) (out : Outcome) (final : St E) (target : Evm.Out)
    (h : f.Fetched initial (.ok out) final target) :
    (evalE i.global i.frame (i.horizon + 1)
      (.extCall i.target i.declaration i.signature i.value i.arguments)).run i.before =
      (extReturn rs out).run (i.after.1, final) :=
  CallerResume.invocation i out final (p.sourceRaw _ _ _ _ _ (f.step _ _ _ _ h))

theorem call_halt (p : Premises i) (f : FetchedPremises i p)
    (initial : Evm.Machine) (halt : Halt) (final : St E) (target : Evm.Out)
    (h : f.Fetched initial (.error halt) final target) :
    (evalE i.global i.frame (i.horizon + 1)
      (.extCall i.target i.declaration i.signature i.value i.arguments)).run i.before =
      (.error halt, (i.after.1, final)) :=
  CallerResume.invocation_halted i halt final (p.sourceRaw _ _ _ _ _ (f.step _ _ _ _ h))

/-- Physical return/restoration is the frozen P1 contract, not an arbitrary
frame-view equality. Callback.compiled_return composes it with this Step. -/
theorem target_return (p : Premises i) (f : FetchedPremises i p)
    (initial machine : Evm.Machine) (raw : Except Halt Outcome) (final : St E)
    (h : f.Fetched initial raw final (.ok machine 0)) :
    Evm.run p.code.full initial = .ok machine 0 :=
  p.execution _ _ _ _ _ (f.step _ _ _ _ h)

theorem continuation (p : Premises i) (f : FetchedPremises i p)
    (initial machine : Evm.Machine) (raw : Except Halt Outcome) (final : St E)
    (tail : List Evm.Instr) (h : f.Fetched initial raw final (.ok machine 0)) :
    Evm.run (p.code.full ++ tail) initial = Evm.run tail machine :=
  Callbacks.suffix p _ _ _ _ _ tail (f.step _ _ _ _ h)

/-- The concrete caller decoder result/failure is transported verbatim. -/
theorem decoded (p : Premises i) (f : FetchedPremises i p)
    (initial : Evm.Machine) (out : Outcome) (final : St E) (target : Evm.Out)
    (h : f.Fetched initial (.ok out) final target)
    (result : Except Halt (RVal E.layout (STy.ret rs)))
    (after : Locals E.layout Γ × St E)
    (decoder : (extReturn rs out).run (i.after.1, final) = (result, after)) :
    (evalE i.global i.frame (i.horizon + 1)
      (.extCall i.target i.declaration i.signature i.value i.arguments)).run i.before = (result, after) :=
  (declared_return p f initial out final target h).trans decoder

end Solidity.Backend.WorldCalls.ExternalCalls
