import Solidity.Backend.WorldCalls.Premises
import Solidity.Lowering.Readonly.EnvironmentHistory

/-! G42.03 conditional compiler-side callback consumers. Target execution,
source/raw correspondence and structural histories remain explicit producer
premises. No claim that current payment-only CALL implements callbacks. -/
namespace Solidity.Backend.WorldCalls.Callbacks
open InternalFlow.RuntimeFrame.InterfaceV1 (Entry Returned PendingRestoration RestoredRepresentationClaim)
open InternalFlow.RuntimeFrame.InterfaceV3 (PendingCallProducer)
open Solidity.Source Solidity.Roadmap
open Solidity.Lowering.Readonly
variable {E : Env} {Γ : RCtx} {dn : DeclName} {ps rs : List STy}
variable {i : InvocationFrame.Invocation E Γ dn ps rs}

theorem restore {code : Code} {view : Evm.Machine → List Identity} {key : Identity}
    {initial final : Evm.Machine} (h : ReturnedFrame code view key initial final) :
    view final = view initial := by
  rw [h.popView, h.bodyView, h.pushView]
  rfl

/-- Returning callback boundaries execute their emitted code as stated by the supplied
`Step` (these are projections of producer premises). Physical frame
transport is supplied below by the unchanged frozen P1 contract. Arbitrary raw success/revert/error data
is retained in the producer's observation relation. -/
theorem returned (p : Premises i) (key : Identity) (initial machine : Evm.Machine)
    (raw : Except Halt Outcome) (final : St E)
    (step : p.Step key initial raw final (.ok machine 0)) :
    key = identity i ∧ Evm.run p.code.full initial = .ok machine 0 ∧
      p.Observed key initial (.ok machine 0) raw ∧ i.RawAt raw final :=
  ⟨p.bound _ _ _ _ _ step, p.execution _ _ _ _ _ step,
    p.observed _ _ _ _ _ step, p.sourceRaw _ _ _ _ _ step⟩

/-- A continuation keeps its actual writes/halts; frame restoration does not
silently restrict the continuation to read-only behavior. -/
theorem suffix (p : Premises i) (key : Identity) (initial machine : Evm.Machine)
    (raw : Except Halt Outcome) (final : St E) (tail : List Evm.Instr)
    (step : p.Step key initial raw final (.ok machine 0)) :
    Evm.run (p.code.full ++ tail) initial = Evm.run tail machine :=
  Evm.run_append_ok (p.execution _ _ _ _ _ step)

theorem deterministic (p : Premises i) (one two : Identity) (initial : Evm.Machine)
    (raw₁ raw₂ : Except Halt Outcome) (final₁ final₂ : St E) (out₁ out₂ : Evm.Out)
    (first : p.Step one initial raw₁ final₁ out₁) (second : p.Step two initial raw₂ final₂ out₂) :
    one = two ∧ raw₁ = raw₂ ∧ final₁ = final₂ ∧ out₁ = out₂ := by
  obtain ⟨raw, state⟩ := i.raw_unique _ _ _ _ (p.sourceRaw _ _ _ _ _ first) (p.sourceRaw _ _ _ _ _ second)
  exact ⟨(p.bound _ _ _ _ _ first).trans (p.bound _ _ _ _ _ second).symm,
    raw, state, (p.execution _ _ _ _ _ first).symm.trans (p.execution _ _ _ _ _ second)⟩

/-- Reuses P2's source-to-typed storage projection, without inferring ledger,
balance, memory or native representation from static mode. -/
theorem static_storage (p : Premises i) (key : Identity) (initial : Evm.Machine)
    (raw : Except Halt Outcome) (final : St E) (target : Evm.Out)
    (step : p.Step key initial raw final target) (mode : i.mode = true)
    {C : Contract} (rep : InvocationFrame.StorageRepresentation E C i.frame.this)
    (before after : Solidity.Storage C)
    (entry : rep.relates (i.after.2.ex.world.accounts i.frame.this).storage before)
    (exit : rep.relates (final.ex.world.accounts i.frame.this).storage after) : after = before :=
  InvocationFrame.typed_storage i raw final (p.sourceRaw _ _ _ _ _ step)
    ⟨mode, p.p2History _ _ _ _ _ step⟩ rep before after entry exit

/-- Direct use of the G22.02 source loop consumer: the P1 child histories are
still explicit and are not discharged by a target code label. -/
theorem source_environment (global : Glob E) (mode : Bool) (n depth : Nat) (state : St E)
    (children : EnvironmentHistory.CallbackHistories global mode n) :
    StaticJournal.History state.ex mode ((envLoop global n depth mode).run (L0 E, state)).2.2.ex :=
  EnvironmentHistory.loop global mode n children depth state

/-- Frozen P1's full successful-return predicate is retained unchanged.
The exact intrinsic call/run and entry are explicit, and emission is tied to
this boundary's ACTUAL code. Source/raw correspondence is still separate. -/
theorem compiled_return {C : Contract} {Ξ Ω params results bodyCtx : Ctx}
    {b : Nat} {F : Evm.Frag Ξ} {name : Name} {args : Solidity.Args C Ξ params}
    {ret : CallRet Ξ results Ω} {body : Prog C (results ++ params) bodyCtx}
    {approved admitted : InternalFlow.RuntimeFrame.InterfaceV3.Admission C Ξ}
    (producer : PendingCallProducer b F approved admitted name args ret body) (p : Premises i)
    (L frame : Nat) (caller : Solidity.State C Ξ) (base : Nat → Fin Evm.W)
    (initial target : Evm.Machine) (start : Nat) (out : Solidity.Out C caller.H Ω)
    (entry : Entry producer.plan L b frame F caller base initial start)
    (typedRun : (Solidity.Stmt.call name args ret body).run caller = .ok out)
    (emitted : p.code.full = producer.plan.code) (key : Identity)
    (raw : Except Halt Outcome) (sourceFinal : St E)
    (step : p.Step key initial raw sourceFinal (.ok target 0)) :
    Returned producer.plan L b frame caller base initial start out ∧
      Evm.run producer.plan.code initial = .ok target 0 ∧ i.RawAt raw sourceFinal := by
  refine ⟨producer.required_return L frame caller base initial start entry out typedRun, ?_,
    p.sourceRaw _ _ _ _ _ step⟩
  rw [← emitted]
  exact p.execution _ _ _ _ _ step

/-- The actual returned machine is unique for this emitted code. Together
with compiled_return this identifies the existential target in frozen Returned. -/
theorem target_unique (p : Premises i) (key : Identity) (initial target candidate : Evm.Machine)
    (raw : Except Halt Outcome) (final : St E)
    (step : p.Step key initial raw final (.ok target 0))
    (other : Evm.run p.code.full initial = .ok candidate 0) : candidate = target := by
  have eq := other.symm.trans (p.execution _ _ _ _ _ step)
  cases eq
  rfl

/-- No restoration premise is dropped or reconstructed from a marker view. -/
theorem restoration (producer : PendingRestoration) : RestoredRepresentationClaim := producer.required

end Solidity.Backend.WorldCalls.Callbacks
