import ExecutionCall
import Solidity.Backend.InternalFlow.RuntimeFrameP1V2CallAgreementControls

/-! Guard a freely chosen target image or desired source result being substituted
for a compiler-selected callee. The existing checked void-call family classifies
its actual typed-core source and supplies the entire frozen Returned contract,
then the same native image drives the emitted outer call prefix. No approved
profile or Source-resolved-body/world correspondence is defined here. This is
not full H121/G42.02, general P1, reference-return, gas/fork or nested-call adequacy. -/
namespace Solidity.H62.ReadonlyCalls.CheckedExecutionCall
open Solidity.Evm Solidity.Evm.Memory Solidity.Backend.Passes.SourceCallBytes
open Solidity.Backend.InternalFlow.RuntimeFrame
open Solidity.H62.ReadonlyCalls.ExecutionReplies

variable {C : Contract} {Γ ps Γf : Ctx} {b : Nat} {F : Frag Γ}
  {f : Name} {args : Args C Γ ps} {body : Prog C ps Γf}

def preparedInput (e : P1LangV2.Input C Γ) (caller : MachineV2)
    (a v o : Fin W) (input : List UInt8) : P1LangV2.Input C Γ :=
  {e with machine := prepare caller e.machine a v o input}

/-- A stack-only update preserves all original Entry fields, including capacity. -/
theorem entry_stack {Δ : Ctx} (plan : InterfaceV1.Emission C Γ Δ)
    (L frame : Nat) (caller : State C Γ) (base : Nat → Fin W)
    (machine : Machine) (start : Nat)
    (entry : InterfaceV1.Entry plan L b frame F caller base machine start) (tail : List Word) :
    InterfaceV1.Entry plan L b frame F caller base {machine with stack := tail} start := by
  refine ⟨entry.represented.stack tail,entry.callerBound,entry.resultBound,entry.workspace,
    entry.pointerAbove,entry.pointerBelow,entry.payloadAbove,entry.reserve,entry.controlSpace,
    entry.separate,entry.noWrap,entry.cursor,?_⟩
  rcases entry.capacity with zero | ⟨positive,cursor,allocated,room⟩
  · exact .inl zero
  · exact .inr ⟨positive,cursor,allocated.stack tail,room⟩

/-- Both actual compiler-supported source classes drive the SAME selected image.
The successful branch keeps InterfaceV1.Returned intact (representation, stack,
base extension, allocator, cursor and older words), not just its run projection. -/
theorem compiled_native
    (selected : Composition.Program b F (.cons (.call f args .none body) .nil))
    (lo pointer : Nat) (flags : InterfaceV1.NoAliasPromotion F selected.checked.frag .refl)
    (e : P1LangV2.Input C Γ) (caller : MachineV2) (a v o : Fin W) (input : List UInt8)
    (entry : InterfaceV1.Entry (NoneProducer.plan selected lo pointer)
      e.L b e.frame F e.caller e.base (prepare caller e.machine a v o input).base e.start)
    (small : input.length < W) (funded : v.1 ≤ caller.base.bal caller.base.self) :
    (∃ out : Solidity.Out C e.caller.H Γ,
      (Stmt.call f args .none body).run e.caller = .ok out ∧
      InterfaceV1.Returned (NoneProducer.plan selected lo pointer) e.L b e.frame
        e.caller e.base (prepare caller e.machine a v o input).base e.start out ∧
      ∃ childFinal configured final,
        runV2 (lift (NoneProducer.plan selected lo pointer).code)
          (prepare caller e.machine a v o input) = .ok childFinal 0 ∧
        attach (lift (NoneProducer.plan selected lo pointer).code) caller e.machine a v o input = some configured ∧
        runV2 (ExecutionCall.code a v o input) configured = .ok final 0 ∧
        final.returndata = [] ∧ final.calls = caller.calls ++ [⟨a,v,input,true,[]⟩] ∧
        final.base.stack = caller.base.stack ∧ final.base.store = caller.base.store) ∨
    ((Stmt.call f args .none body).run e.caller = .error .revert ∧
      runV2 (lift (NoneProducer.plan selected lo pointer).code)
        (prepare caller e.machine a v o input) = .revert e.machine.calls [] ∧
      ∃ configured final,
        attach (lift (NoneProducer.plan selected lo pointer).code) caller e.machine a v o input = some configured ∧
        runV2 (ExecutionCall.code a v o input) configured = .ok final 0 ∧
        final.returndata = [] ∧ final.calls = caller.calls ++ [⟨a,v,input,false,[]⟩] ∧
        final.base.stack = caller.base.stack ∧ final.base.store = caller.base.store) := by
  let actual := preparedInput e caller a v o input
  rcases P1V2CallAgreement.source_outcomes selected lo pointer actual entry with ⟨out,source⟩ | source
  · have framed : InterfaceV1.Returned (NoneProducer.plan selected lo pointer) e.L b e.frame
        e.caller e.base (prepare caller e.machine a v o input).base e.start out :=
      NoneProducer.returns selected lo pointer flags e.L e.frame e.caller e.base
        (prepare caller e.machine a v o input).base e.start entry out source
    obtain ⟨target,addresses,core,rest⟩ := framed
    have native : runV2 (lift (NoneProducer.plan selected lo pointer).code)
        (prepare caller e.machine a v o input) =
        .ok ((prepare caller e.machine a v o input).withBase target) 0 := run_lift_ok core
    have observed : observe (runV2 (lift (NoneProducer.plan selected lo pointer).code)
        (prepare caller e.machine a v o input)) = some (true,[]) := by rw [native]; rfl
    obtain ⟨configured,final,attached,run,data,calls,stack,store⟩ :=
      ExecutionCall.funded_native _ caller e.machine a v o input [] true small funded observed
    exact .inl ⟨out,source,⟨target,addresses,core,rest⟩,
      _,configured,final,native,attached,run,data,calls,stack,store⟩
  · have native : runV2 (lift (NoneProducer.plan selected lo pointer).code)
        (prepare caller e.machine a v o input) = .revert e.machine.calls [] :=
      P1V2FramedRevert.run_revert selected lo pointer actual entry source
    have observed : observe (runV2 (lift (NoneProducer.plan selected lo pointer).code)
        (prepare caller e.machine a v o input)) = some (false,[]) := by rw [native]; rfl
    obtain ⟨configured,final,attached,run,data,calls,stack,store⟩ :=
      ExecutionCall.funded_native _ caller e.machine a v o input [] false small funded observed
    exact .inr ⟨source,native,configured,final,attached,run,data,calls,stack,store⟩

/-- Outer funding and header are explicit; they are not a Source/world relation. -/
def outer (e : P1LangV2.Input C Γ) : MachineV2 :=
  e.machine.withBase {e.machine.base with self := e.machine.base.caller, bal := fun _ => W}

def cell : Fin W := ⟨64,by decide⟩

theorem prepared_empty (e : P1LangV2.Input C Γ) :
    prepare (outer e) e.machine e.machine.base.self e.machine.base.callvalue cell [] =
      e.machine.withBase {e.machine.base with stack := []} := by
  simp only [prepare,outer,MachineV2.withBase,chunks,storeMem]

theorem prepared_entry {Δ : Ctx} (plan : InterfaceV1.Emission C Γ Δ)
    (e : P1LangV2.Input C Γ)
    (entry : InterfaceV1.Entry plan e.L b e.frame F e.caller e.base e.machine.base e.start) :
    InterfaceV1.Entry plan e.L b e.frame F e.caller e.base
      (prepare (outer e) e.machine e.machine.base.self e.machine.base.callvalue cell []).base e.start := by
  rw [prepared_empty]
  exact entry_stack plan e.L e.frame e.caller e.base e.machine.base e.start entry []

/-- The positive fixture uses Mutation.compileCall's actual selected void image. -/
theorem selected_success (journal : List CallRec) (buffer : List UInt8) :
    let e := P1V2FramedRevertControls.input journal buffer
    ∃ configured final,
      attach (lift (NoneProducer.plan P1V2CallAgreementControls.selected 8 8).code)
        (outer e) e.machine e.machine.base.self e.machine.base.callvalue cell [] = some configured ∧
      runV2 (ExecutionCall.code e.machine.base.self e.machine.base.callvalue cell []) configured = .ok final 0 ∧
      final.calls = (outer e).calls ++ [⟨e.machine.base.self,e.machine.base.callvalue,[],true,[]⟩] := by
  let e := P1V2FramedRevertControls.input journal buffer
  have entry := V3BareRevertProducer.coverage P1V2CallAgreementControls.selected 8 8
    1 16 V3BareRevertProducer.Checks.caller V3BareRevertProducer.Checks.P.base
    V3BareRevertProducer.Checks.machine 10 P1V2CallAgreementControls.physical
  have reached := compiled_native P1V2CallAgreementControls.selected 8 8
    (NoneProducer.init_flags _ .refl) e (outer e) e.machine.base.self e.machine.base.callvalue cell []
    (prepared_entry _ e entry) (by decide)
    (Nat.le_of_lt e.machine.base.callvalue.isLt)
  rcases reached with ⟨out,source,framed,childFinal,configured,final,native,attached,run,_,calls,_,_⟩ | ⟨source,_⟩
  · exact ⟨configured,final,attached,run,calls⟩
  · change Except.ok _ = Except.error _ at source
    cases source

/-- The other actual compiler-selected fixture writes its aliased object before
OOB; bare revert is retained, rather than filtered out by a success domain. -/
theorem selected_revert (journal : List CallRec) (buffer : List UInt8) :
    let e := P1V2FramedRevertControls.input journal buffer
    ∃ configured final,
      attach (lift (NoneProducer.plan V3BareRevertProducer.Checks.callSelected 8 8).code)
        (outer e) e.machine e.machine.base.self e.machine.base.callvalue cell [] = some configured ∧
      runV2 (ExecutionCall.code e.machine.base.self e.machine.base.callvalue cell []) configured = .ok final 0 ∧
      final.calls = (outer e).calls ++ [⟨e.machine.base.self,e.machine.base.callvalue,[],false,[]⟩] := by
  let e := P1V2FramedRevertControls.input journal buffer
  have reached := compiled_native V3BareRevertProducer.Checks.callSelected 8 8
    (NoneProducer.init_flags _ .refl) e (outer e) e.machine.base.self e.machine.base.callvalue cell []
    (prepared_entry _ e (P1V2FramedRevertControls.physical_entry journal buffer))
    (by decide) (Nat.le_of_lt e.machine.base.callvalue.isLt)
  rcases reached with ⟨out,source,_⟩ | ⟨source,native,configured,final,attached,run,_,calls,_,_⟩
  · change Stmt.run V3BareRevertProducer.Checks.caller V3BareRevertProducer.Checks.call = .ok out at source
    have failed := V3BareRevertProducer.Checks.call_source
    rw [failed] at source
    cases source
  · exact ⟨configured,final,attached,run,calls⟩

end Solidity.H62.ReadonlyCalls.CheckedExecutionCall
