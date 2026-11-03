import Solidity.Lowering.P8.FrozenInterface
import Solidity.Lowering.V08.ConstructorContinuations
import Solidity.Backend.InternalFlow.RuntimeFrameInterfaceV1

/-! Relative constructor-to-installation composition (`ssNew_body` supplies the
constructor run as a producer duty; `creation` is not evidence for it). Every missing producer is
explicit: frozen P8a, V17's future SS-NEW invocation binding, V07 constructor
body, layout/heap correspondence and P1 return/restoration. The supplied EM
operation is an existing typed Source computation, NOT a replacement evaluator
or an assertion that resolved new/try-new exists. Until V17 binds this parameter
to its actual resolved syntax, this is only a constructor-phase consumer.
No V1 RealizableEntry fact is used or inferred.
The `admission : P8a.Producer …` field makes these inputs uninhabited until
P8-SPEC-LAW1 is resolved (`Lowering/P8/ResourceContractLaw1.lean`), so the
results here are vacuous for now. -/
namespace Solidity.Lowering.V08.CreationPremises
open Solidity ContractWorld
open Solidity.Lowering.P8
open Solidity.Backend.InternalFlow.RuntimeFrame
variable {E : Source.Env} {K : Type} [DecidableEq K] {cs : K → Contract}

/-- The producer obligations for ONE reached constructor phase. `relation`
must come from independent local/storage/heap layout producers. No field
assumes World.create or tryCreate, so installation/handler selection is derived.
P8a's reference/origins/roots remain external and no inhabitant is fabricated. -/
structure Inputs (S : P8a.Spec) (reference : P8a.OperationalReference)
    (origins : P8a.SourceOrigins S) (roots : P8a.RootModel S)
    (resolved : S.Resolved) (wf : S.WellFormed resolved) (profile : S.InProfile resolved)
    (artifact : Roadmap.Artifact) (program : Source.SrcProg E)
    (operation : Source.EM E [] Unit) (before after : Source.St E)
    (w : World cs) (kind : K) (address : Address)
    (ctor : Prog (cs kind) [] []) (ctx : Context)
    (relation : Source.St E → State (cs kind) [] → Prop) where
  admission : P8a.Producer S reference origins roots
  origin : origins.meaning resolved wf profile artifact = ⟨E,program⟩
  environment : Roadmap.SessionEnv
  sourceFrame : Source.Fr
  horizon : Nat
  contractName : String
  constructorArgs : Source.Locals E.layout (program.prog.ctorLocals contractName)
  invocation : operation = Source.construct (program.glob environment) sourceFrame horizon
    contractName constructorArgs
  frameAgreement : ConstructorScalarTransport.FrameInputs sourceFrame address ctx
  source : operation.run (Source.L0 E,before) = (.ok (),(Source.L0 E,after))
  caller : State (cs kind) []
  related : relation before caller
  /-- Missing V17/V07 constructor-body preservation producer. This field is
  NOT implementation evidence; V17 must also bind its eventual new syntax to
  this actual constructor phase, including argument/base/initializer order. -/
  ssNew_body : operation.run (Source.L0 E,before) = (.ok (),(Source.L0 E,after)) →
    ∃ out : Out (cs kind) caller.H [], ctor.run caller = .ok out ∧ relation after out.st
  ordinary : w.isLibrary kind = false
  available : w.accounts address = none
  different : address ≠ ctx.sender
  mutable : ctx.isStatic = false
  entered : w.enter address ctx (Storage.init (cs kind))
    (((cs kind).ctor.map (·.payable)).getD false) = .ok caller
  emission : InterfaceV1.Emission (cs kind) [] []
  fragment : Evm.Frag []
  runtime_return : InterfaceV1.ReturnClaim 0 fragment (.block ctor) emission
  restoration : InterfaceV1.PendingRestoration

variable {S : P8a.Spec} {reference : P8a.OperationalReference}
  {origins : P8a.SourceOrigins S} {roots : P8a.RootModel S}
  {resolved : S.Resolved} {wf : S.WellFormed resolved} {profile : S.InProfile resolved}
  {artifact : Roadmap.Artifact} {program : Source.SrcProg E}
  {operation : Source.EM E [] Unit} {before after : Source.St E}
  {w : World cs} {kind : K} {address : Address}
  {ctor : Prog (cs kind) [] []} {ctx : Context}
  {relation : Source.St E → State (cs kind) [] → Prop}

omit [DecidableEq K] in
/-- Consume the actual frozen P8a meaning-origin obligation, without a local
SourceSpec carrier equality or invented admission/profile bound. -/
theorem meaning_origin (p : Inputs S reference origins roots resolved wf profile artifact program
    operation before after w kind address ctor ctx relation) :
    p.admission.realization.program (S.meaning resolved wf profile artifact) = ⟨E,program⟩ :=
  (p.admission.realization.meaning_origin resolved wf profile artifact).trans p.origin

omit [DecidableEq K] in
/-- The source action is the actual published constructor invocation of the
same source program selected by the frozen P8a origin obligation. -/
theorem actual_source (p : Inputs S reference origins roots resolved wf profile artifact program
    operation before after w kind address ctor ctx relation) :
    (Source.construct (program.glob p.environment) p.sourceFrame p.horizon
      p.contractName p.constructorArgs).run (Source.L0 E,before) =
      (.ok (),(Source.L0 E,after)) := by
  rw [← p.invocation]
  exact p.source

omit [DecidableEq K] in
/-- Actual constructor execution is a V17/V07 producer obligation. The
conclusion explicitly retains the reached independent layout/heap relation. -/
theorem reached_body (p : Inputs S reference origins roots resolved wf profile artifact program
    operation before after w kind address ctor ctx relation) :
    ∃ out : Out (cs kind) p.caller.H [], ctor.run p.caller = .ok out ∧ relation after out.st :=
  p.ssNew_body p.source

omit [DecidableEq K] in
/-- Guards and entry are consumed separately; settlement may still fail.
In particular no assumption of whole creation preservation is a field. -/
theorem creation (p : Inputs S reference origins roots resolved wf profile artifact program
    operation before after w kind address ctor ctx relation) :
    ∃ out : Out (cs kind) p.caller.H [], ctor.run p.caller = .ok out ∧ relation after out.st ∧
      w.create kind address ctor ctx = (do
        let next ← w.finish address out.st
        pure (next,(⟨address⟩ : Handle kind))) := by
  obtain ⟨out,ran,related⟩ := reached_body p
  refine ⟨out,ran,related,?_⟩
  simp only [World.create,p.ordinary,Bool.false_eq_true,if_false]
  change ((if (w.accounts address).isSome || decide (address = ctx.sender) || ctx.isStatic
    then .error .revert else do
      let caller ← w.enter address ctx (Storage.init (cs kind))
        (((cs kind).ctor.map (·.payable)).getD false)
      let out ← ctor.run caller
      let next ← w.finish address out.st
      pure (next,(⟨address⟩ : Handle kind))) : TRes (World cs × Handle kind)) = _
  simp only [p.available,Option.isSome_none,p.different,decide_false,p.mutable,
    Bool.or_false,Bool.false_eq_true,if_false,p.entered,bind,Except.bind,ran]

/-- Installation is derived from actual successful settlement, not assumed
as SS-NEW body semantics. The returned handle has the selected code type. -/
theorem installed (p : Inputs S reference origins roots resolved wf profile artifact program
    operation before after w kind address ctor ctx relation) (next : World cs)
    (settled : ∀ out : Out (cs kind) p.caller.H [], ctor.run p.caller = .ok out →
      w.finish address out.st = .ok next) :
    w.create kind address ctor ctx = .ok (next,⟨address⟩) ∧
    ∃ store : Storage (cs kind), next.accounts address = some ⟨kind,store⟩ := by
  obtain ⟨out,ran,_,created⟩ := creation p
  rw [settled out ran] at created
  have actual : w.create kind address ctor ctx = .ok (next,⟨address⟩) := created
  exact ⟨actual,World.create_installs actual⟩

/-- Success continuation selection, preserving its EXACT status/payload.
A later failure is outside the constructor catch and is not recaught. -/
theorem try_success {β : Type} (p : Inputs S reference origins roots resolved wf profile artifact program
    operation before after w kind address ctor ctx relation) (next : World cs)
    (settled : ∀ out : Out (cs kind) p.caller.H [], ctor.run p.caller = .ok out →
      w.finish address out.st = .ok next)
    (success : World cs → Handle kind → TRes (World cs × β))
    (handler : World cs → THalt → TRes (World cs × β)) :
    w.tryCreate (.ok ()) kind (fun _ => address) (fun _ => ctor) (fun _ => ctx) success handler =
      success next ⟨address⟩ :=
  ConstructorContinuations.from_created w next kind address ctor ctx ⟨address⟩ success handler
    p.mutable (installed p next settled).1

omit [DecidableEq K] in
/-- The ordinary constructor is a block in the existing intrinsic program.
The exact frozen runtime return claim stays a parameter, not a proven producer. -/
theorem runtime_success (p : Inputs S reference origins roots resolved wf profile artifact program
    operation before after w kind address ctor ctx relation) (L frame : Nat) (base : Nat → Fin Evm.W)
    (machine : Evm.Machine) (start : Nat)
    (entry : InterfaceV1.Entry p.emission L 0 frame p.fragment p.caller base machine start) :
    ∃ out : Out (cs kind) p.caller.H [], ctor.run p.caller = .ok out ∧
      InterfaceV1.Returned p.emission L 0 frame p.caller base machine start
        ⟨out.st.drop ctor.ext,out.ext⟩ := by
  obtain ⟨out,ran,_⟩ := reached_body p
  refine ⟨out,ran,?_⟩
  apply p.runtime_return L frame p.caller base machine start entry
  change (do
    let o ← ctor.run p.caller
    pure (⟨o.st.drop ctor.ext,o.ext⟩ : Out (cs kind) p.caller.H [])) = _
  rw [ran]
  rfl

omit [DecidableEq K] in
/-- Finish/settlement failure preserves its exact THalt. It does not imply
any Source catch branch or expose an intrinsic failure world. -/
theorem settlement_failure (p : Inputs S reference origins roots resolved wf profile artifact program
    operation before after w kind address ctor ctx relation) (halt : THalt)
    (failed : ∀ out : Out (cs kind) p.caller.H [], ctor.run p.caller = .ok out →
      w.finish address out.st = .error halt) :
    w.create kind address ctor ctx = .error halt := by
  obtain ⟨out,ran,_,created⟩ := creation p
  rw [failed out ran] at created
  exact created

omit [DecidableEq K] in
/-- Only a completed catchable failure invokes the handler, at the original
world. This is the existing intrinsic catchable predicate, not Source catch. -/
theorem try_failure {β : Type}
    (p : Inputs S reference origins roots resolved wf profile artifact program
      operation before after w kind address ctor ctx relation) (halt : THalt)
    (failed : ∀ out : Out (cs kind) p.caller.H [], ctor.run p.caller = .ok out →
      w.finish address out.st = .error halt)
    (success : World cs → Handle kind → TRes (World cs × β))
    (handler : World cs → THalt → TRes (World cs × β)) :
    w.tryCreate (.ok ()) kind (fun _ => address) (fun _ => ctor) (fun _ => ctx) success handler =
      if catchable halt then handler w halt else .error halt := by
  simp only [World.tryCreate,bind,Except.bind,p.mutable,Bool.false_eq_true,if_false,
    settlement_failure p halt failed]

/-- Inhabited component facts for BOTH pipelines/arbitrary bytes. This does
not fabricate the still-unimplemented P8a or runtime producer fields. Whole
Source machine, reached typed storage and funded installed world are retained. -/
theorem populated_components (pipeline : Roadmap.Pipeline) (bytes : Roadmap.Bytes)
    (n : Int) (h : ConstructorScalarTransport.range n) :
    (Source.construct (ConstructorScalarTransport.global pipeline) ConstructorScalarTransport.frame 8 "Cell"
      (ConstructorScalarTransport.locals n h)).run
      (Source.L0 ConstructorScalarTransport.E,ConstructorScalarTransport.initial bytes) =
      (.ok (),(Source.L0 ConstructorScalarTransport.E,ConstructorScalarTransport.written bytes n h)) ∧
    (ConstructorScalarTransport.targetBody n h).run ConstructorScalarTransport.entered =
      .ok ⟨ConstructorScalarTransport.targetWritten n h,List.prefix_refl _⟩ ∧
    ConstructorScalarTransport.targetRun n h =
      .ok (ConstructorScalarTransport.targetNext n h,⟨Controls.self⟩) :=
  ⟨ConstructorScalarTransport.source_construct pipeline 0 bytes n h,
    ConstructorScalarTransport.body_actual n h,ConstructorScalarTransport.creation_actual n h⟩

/-- Concrete wrong handler/rollback observations from the ACTUAL funded
creation continuation, not an assumed future Source catch implementation. -/
theorem negative_components (n : Int) (h : ConstructorScalarTransport.range n) :
    ConstructorContinuations.failingAttempt n h ≠
      .ok (ConstructorScalarTransport.targetNext n h,some (-1)) ∧
    (atomic ConstructorScalarTransport.targetInitial (ConstructorContinuations.failingAttempt n h)).1 ≠
      ConstructorScalarTransport.targetNext n h :=
  ⟨ConstructorContinuations.wrong_catch_value n h,
    ConstructorContinuations.wrong_rollback_snapshot n h⟩

end Solidity.Lowering.V08.CreationPremises

/-- info: 'Solidity.Lowering.V08.CreationPremises.meaning_origin' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Solidity.Lowering.V08.CreationPremises.meaning_origin

/-- info: 'Solidity.Lowering.V08.CreationPremises.actual_source' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Solidity.Lowering.V08.CreationPremises.actual_source

/-- info: 'Solidity.Lowering.V08.CreationPremises.reached_body' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Solidity.Lowering.V08.CreationPremises.reached_body

/-- info: 'Solidity.Lowering.V08.CreationPremises.creation' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Solidity.Lowering.V08.CreationPremises.creation

/-- info: 'Solidity.Lowering.V08.CreationPremises.installed' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Solidity.Lowering.V08.CreationPremises.installed

/-- info: 'Solidity.Lowering.V08.CreationPremises.try_success' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Solidity.Lowering.V08.CreationPremises.try_success

/-- info: 'Solidity.Lowering.V08.CreationPremises.runtime_success' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Solidity.Lowering.V08.CreationPremises.runtime_success

/-- info: 'Solidity.Lowering.V08.CreationPremises.settlement_failure' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Solidity.Lowering.V08.CreationPremises.settlement_failure

/-- info: 'Solidity.Lowering.V08.CreationPremises.try_failure' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Solidity.Lowering.V08.CreationPremises.try_failure

/-- info: 'Solidity.Lowering.V08.CreationPremises.populated_components' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Solidity.Lowering.V08.CreationPremises.populated_components

/-- info: 'Solidity.Lowering.V08.CreationPremises.negative_components' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Solidity.Lowering.V08.CreationPremises.negative_components
