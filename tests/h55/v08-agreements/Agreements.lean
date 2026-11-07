import Solidity.Lowering.V08.LibraryPremises
import Solidity.Lowering.V08.WorldContextComposition
import Solidity.Lowering.V08.SourceDispatchControls

/-! Original H55 migration candidate with additive production-frame correspondence
checks below. Full origin/body migration and concrete producer inhabitants remain
open. Existing legacy input structures and P8a are unchanged. -/
namespace Solidity.Lowering.V08.H55Agreements
open Solidity ContractWorld
open Solidity.Lowering.P8

/-- One exact input relation at the reached address. For delegation this is
caller storage identity; it is never the library code address. -/
structure FrameAgreement (f : Source.Fr) (address : Address) (ctx : Context) : Prop where
  address : (f.this.val : Int) = address.1.1
  sender : (f.sender.val : Int) = ctx.sender.1.1
  value : (f.value.val : Int) = ctx.value.1
  static : f.static = ctx.isStatic

/-- No clipping or extra premise: unsigned intrinsic words already contain
nonnegativity. This includes zero and the full unsigned range. -/
theorem nat_int_exact (n : Nat) (w : Semantics.Word) :
    n = w.1.toNat ↔ (n : Int) = w.1 := by
  have bound := w.2
  simp only [PrimTy.inRange, decide_eq_true_eq] at bound
  omega

def fromConstructor {f : Source.Fr} {address : Address} {ctx : Context}
    (p : ConstructorScalarTransport.FrameInputs f address ctx) : FrameAgreement f address ctx :=
  by
    rcases p with ⟨ha, hs, hv, ht⟩
    exact ⟨(nat_int_exact _ _).mp ha, (nat_int_exact _ _).mp hs,
      (nat_int_exact _ _).mp hv, ht⟩

def toConstructor {f : Source.Fr} {address : Address} {ctx : Context}
    (p : FrameAgreement f address ctx) : ConstructorScalarTransport.FrameInputs f address ctx :=
  ⟨(nat_int_exact _ _).mpr p.address, (nat_int_exact _ _).mpr p.sender,
    (nat_int_exact _ _).mpr p.value, p.static⟩

def fromLibrary {K : Type} {caller : K} {f : Source.Fr} {owner : Handle caller} {ctx : Context}
    (p : LibraryFrameTransport.FrameInputs f owner ctx) : FrameAgreement f owner.address ctx :=
  ⟨p.caller, p.sender, p.value, p.static⟩

def toLibrary {K : Type} {caller : K} {f : Source.Fr} {owner : Handle caller} {ctx : Context}
    (p : FrameAgreement f owner.address ctx) : LibraryFrameTransport.FrameInputs f owner ctx :=
  ⟨p.sender, p.value, p.address, p.static⟩

theorem constructor_roundtrip {f : Source.Fr} {address : Address} {ctx : Context}
    (p : ConstructorScalarTransport.FrameInputs f address ctx) :
    toConstructor (fromConstructor p) = p := rfl

theorem constructor_shared_roundtrip {f : Source.Fr} {address : Address} {ctx : Context}
    (p : FrameAgreement f address ctx) : fromConstructor (toConstructor p) = p := rfl

theorem library_roundtrip {K : Type} {caller : K} {f : Source.Fr} {owner : Handle caller} {ctx : Context}
    (p : LibraryFrameTransport.FrameInputs f owner ctx) : toLibrary (fromLibrary p) = p := rfl

theorem library_shared_roundtrip {K : Type} {caller : K} {f : Source.Fr} {owner : Handle caller} {ctx : Context}
    (p : FrameAgreement f owner.address ctx) : fromLibrary (toLibrary (owner := owner) p) = p := rfl

theorem constructor_exact {f : Source.Fr} {address : Address} {ctx : Context} :
    ConstructorScalarTransport.FrameInputs f address ctx ↔ FrameAgreement f address ctx :=
  ⟨fromConstructor, toConstructor⟩

theorem library_exact {K : Type} {caller : K} {f : Source.Fr} {owner : Handle caller} {ctx : Context} :
    LibraryFrameTransport.FrameInputs f owner ctx ↔ FrameAgreement f owner.address ctx :=
  ⟨fromLibrary, toLibrary⟩

/-- Exact indexed frozen origin obligation, without a second SourceOrigins. -/
abbrev OriginWitness {S : P8a.Spec} {E : Source.Env} (origins : P8a.SourceOrigins S)
    (program : Source.SrcProg E) (resolved : S.Resolved) (wf : S.WellFormed resolved)
    (profile : S.InProfile resolved) (artifact : Roadmap.Artifact) : Prop :=
  origins.meaning resolved wf profile artifact = ⟨E, program⟩

/-- Library's existing existential quantifiers, retaining proof dependencies. -/
abbrev SomeOriginWitness {S : P8a.Spec} {E : Source.Env} (origins : P8a.SourceOrigins S)
    (program : Source.SrcProg E) : Prop :=
  ∃ resolved wf profile artifact, OriginWitness origins program resolved wf profile artifact

/-- Exactly the library's three metadata equalities. Runtime environment,
timestamp and main contract are deliberately not additional fields. -/
structure GlobProgramAgreement {E : Source.Env} (g : Source.Glob E)
    (program : Source.SrcProg E) : Prop where
  prog : g.prog = program.prog
  pipeline : g.pipeline = program.pipeline
  fixed : g.fixed = program.fixed

theorem glob_exact {E : Source.Env} (g : Source.Glob E) (program : Source.SrcProg E) :
    GlobProgramAgreement g program ↔
      g.prog = program.prog ∧ g.pipeline = program.pipeline ∧ g.fixed = program.fixed :=
  ⟨fun p => ⟨p.prog, p.pipeline, p.fixed⟩, fun p => ⟨p.1, p.2.1, p.2.2⟩⟩

theorem session_glob {E : Source.Env} (program : Source.SrcProg E) (env : Roadmap.SessionEnv) :
    GlobProgramAgreement (program.glob env) program := ⟨rfl, rfl, rfl⟩

/-- Exact ssNew_body obligation. Naming it provides no producer implementation. -/
abbrev ConstructorBodyObligation {E : Source.Env} {C : Contract}
    (operation : Source.EM E [] Unit) (before after : Source.St E)
    (caller : State C []) (ctor : Prog C [] [])
    (relation : Source.St E → State C [] → Prop) : Prop :=
  operation.run (Source.L0 E, before) = (.ok (), (Source.L0 E, after)) →
    ∃ out : Out C caller.H [], ctor.run caller = .ok out ∧ relation after out.st

/-- Exact g42_body obligation: caller-typed delegated body, result, state and
value relations. This does not assert whole World.libraryCall preservation. -/
abbrev LibraryBodyObligation {E : Source.Env} {C : Contract} {rs : List Source.STy} {α : Type}
    (operation : Source.EM E [] (Source.RVal E.layout (Source.STy.ret rs)))
    (before after : Source.St E) (sourceValue : Source.RVal E.layout (Source.STy.ret rs))
    (caller : State C []) (entry : Entry C α)
    (stateRelation : {Γ : Ctx} → Source.St E → State C Γ → Prop)
    (valueRelation : Source.RVal E.layout (Source.STy.ret rs) → α → Prop) : Prop :=
  operation.run (Source.L0 E, before) = (.ok sourceValue, (Source.L0 E, after)) →
    ∃ (out : Out C caller.H entry.locals) (value : α),
      entry.body.run caller = .ok out ∧ entry.result out.st = .ok value ∧
      stateRelation after out.st ∧ valueRelation sourceValue value

/-- Owner migration adapter for read-only V07.P8Bindings. It preserves the
actual accepted source carrier and the frozen admission profile witnesses. -/
theorem accepted_origin {S : P8a.Spec} {reference : P8a.OperationalReference}
    {origins : P8a.SourceOrigins S} {roots : P8a.RootModel S}
    (producer : P8a.Producer S reference origins roots)
    (input : S.Input) (resolved : S.Resolved)
    (accepted : producer.admission.frontend input = some resolved) (artifact : Roadmap.Artifact) :
    OriginWitness origins (V07.P8Bindings.acceptedSource producer input resolved accepted artifact).2
      resolved (V07.P8Bindings.accepted_profile producer input resolved accepted).1
      (V07.P8Bindings.accepted_profile producer input resolved accepted).2 artifact := rfl

/-- Inhabited frame component, independent of any missing P8/runtime producer. -/
theorem populated_frame : FrameAgreement ConstructorScalarTransport.frame Controls.self
    ConstructorScalarTransport.targetContext := fromConstructor ConstructorScalarTransport.frame_inputs

/-- The same reached address is a caller identity at any catalogue kind. -/
theorem populated_library_frame : LibraryFrameTransport.FrameInputs ConstructorScalarTransport.frame
    (⟨Controls.self⟩ : Handle ()) ConstructorScalarTransport.targetContext := toLibrary populated_frame

/-- Sender corruption is rejected by the actual shared relation. -/
theorem wrong_sender : ¬ FrameAgreement
    {ConstructorScalarTransport.frame with sender := SourcePayableDeploymentControls.self}
    Controls.self ConstructorScalarTransport.targetContext := by
  intro p
  have wrong : (2 : Int) = 1 := p.sender
  cases wrong

/-- Value corruption is independent of sender and address agreement. -/
theorem wrong_value : ¬ FrameAgreement
    {ConstructorScalarTransport.frame with value := SourcePayableDeploymentControls.word 8}
    Controls.self ConstructorScalarTransport.targetContext := by
  intro p
  have wrong : (8 : Int) = 7 := p.value
  cases wrong

/-- Static restriction is retained, including when all numeric fields agree. -/
theorem wrong_static : ¬ FrameAgreement
    {ConstructorScalarTransport.frame with static := true}
    Controls.self ConstructorScalarTransport.targetContext := by
  intro p
  have wrong : true = false := p.static
  cases wrong

/-- Corruption of the reached address is rejected independently of sender/value. -/
theorem wrong_address : ¬ FrameAgreement
    {ConstructorScalarTransport.frame with this := SourcePayableDeploymentControls.sender}
    Controls.self ConstructorScalarTransport.targetContext := by
  intro p
  have wrong : (1 : Int) = 2 := p.address
  cases wrong

/-- A linked code address cannot replace the reached caller storage address. -/
theorem library_code_is_not_caller : ¬ FrameAgreement ConstructorScalarTransport.frame
    LibraryHandlerControls.link ConstructorScalarTransport.targetContext := by
  intro p
  have wrong : (2 : Int) = 4 := p.address
  cases wrong

/-- Static zero-value contexts are supported, rather than excluded. -/
theorem populated_static : FrameAgreement
    {ConstructorScalarTransport.frame with value := SourcePayableDeploymentControls.word 0, static := true}
    Controls.self {ConstructorScalarTransport.targetContext with mode := .readOnly} :=
  ⟨rfl, rfl, rfl, rfl⟩

/-- Metadata agreement permits changing every session field. -/
theorem session_fields_free {E : Source.Env} (g : Source.Glob E) (program : Source.SrcProg E)
    (p : GlobProgramAgreement g program) (env : Roadmap.SessionEnv) (timestamp : Roadmap.Word) :
    GlobProgramAgreement
      {g with
        balance0 := env.balance
        hasCode := env.hasCode
        callee := env.callee
        timestamp := timestamp} program := ⟨p.prog, p.pipeline, p.fixed⟩

/-- Main-contract selection is outside the original three-field contract. -/
theorem main_free {E : Source.Env} (g : Source.Glob E) (program : Source.SrcProg E)
    (p : GlobProgramAgreement g program) (name : String) :
    GlobProgramAgreement g {program with main := name} := ⟨p.prog, p.pipeline, p.fixed⟩

theorem wrong_program {E : Source.Env} (g : Source.Glob E) (program : Source.SrcProg E)
    (different : g.prog ≠ program.prog) : ¬ GlobProgramAgreement g program :=
  fun p => different p.prog

theorem wrong_pipeline {E : Source.Env} (g : Source.Glob E) (program : Source.SrcProg E)
    (different : g.pipeline ≠ program.pipeline) : ¬ GlobProgramAgreement g program :=
  fun p => different p.pipeline

theorem wrong_fixed {E : Source.Env} (g : Source.Glob E) (program : Source.SrcProg E)
    (different : g.fixed ≠ program.fixed) : ¬ GlobProgramAgreement g program :=
  fun p => different p.fixed

section CreationConsumer
variable {E : Source.Env} {K : Type} [DecidableEq K] {cs : K → Contract}
  {S : P8a.Spec} {reference : P8a.OperationalReference}
  {origins : P8a.SourceOrigins S} {roots : P8a.RootModel S}
  {resolved : S.Resolved} {wf : S.WellFormed resolved} {profile : S.InProfile resolved}
  {artifact : Roadmap.Artifact} {program : Source.SrcProg E}
  {operation : Source.EM E [] Unit} {before after : Source.St E}
  {w : World cs} {kind : K} {address : Address}
  {ctor : Prog (cs kind) [] []} {ctx : Context}
  {relation : Source.St E → State (cs kind) [] → Prop}
  (p : CreationPremises.Inputs S reference origins roots resolved wf profile artifact program
    operation before after w kind address ctor ctx relation)

def creationOrigin : OriginWitness origins program resolved wf profile artifact := p.origin

omit [DecidableEq K] in
theorem creationOrigin_correspondence : creationOrigin p = p.origin := rfl

def creationFrame : FrameAgreement p.sourceFrame address ctx := fromConstructor p.frameAgreement

omit [DecidableEq K] in
theorem creationFrame_correspondence : toConstructor (creationFrame p) = p.frameAgreement := rfl

def creationBody : ConstructorBodyObligation operation before after p.caller ctor relation := p.ssNew_body

omit [DecidableEq K] in
theorem creationBody_correspondence : creationBody p = p.ssNew_body := rfl
end CreationConsumer

section LibraryConsumer
variable {E : Source.Env} {K : Type} [DecidableEq K] {cs : K → Contract}
  {S : P8a.Spec} {reference : P8a.OperationalReference}
  {origins : P8a.SourceOrigins S} {roots : P8a.RootModel S}
  {g : Source.Glob E} {frame : Source.Fr} {declaration : Source.Decl}
  {ps rs : List Source.STy} {values : Source.Vals E.layout ps} {horizon : Nat}
  {before after : Source.St E} {sourceValue : Source.RVal E.layout (Source.STy.ret rs)}
  {w : World cs} {caller : K} {owner : Handle caller} {α : Type}
  {library : Library cs caller α} {ctx : Context} {kindOf : String → Option K}
  {stateRelation : {Γ : Ctx} → Source.St E → State (cs caller) Γ → Prop}
  {valueRelation : Source.RVal E.layout (Source.STy.ret rs) → α → Prop}
  (p : LibraryPremises.Inputs S reference origins roots g frame declaration ps rs values horizon
    before after sourceValue w caller owner library ctx kindOf stateRelation valueRelation)

def libraryProgram : GlobProgramAgreement g p.program :=
  ⟨p.programAgreement, p.pipelineAgreement, p.fixedAgreement⟩

omit [DecidableEq K] in
theorem libraryProgram_correspondence :
    (libraryProgram p).prog = p.programAgreement ∧
    (libraryProgram p).pipeline = p.pipelineAgreement ∧
    (libraryProgram p).fixed = p.fixedAgreement := ⟨rfl, rfl, rfl⟩

def libraryOrigin : SomeOriginWitness origins p.program := p.origin

omit [DecidableEq K] in
theorem libraryOrigin_correspondence : libraryOrigin p = p.origin := rfl

def libraryFrame : FrameAgreement frame owner.address ctx := fromLibrary p.frameAgreement

omit [DecidableEq K] in
theorem libraryFrame_correspondence : toLibrary (libraryFrame p) = p.frameAgreement := rfl

def libraryBody : LibraryBodyObligation
    (Source.callInternal g frame horizon declaration values rs) before after sourceValue
    (LibraryFrameTransport.emptyFrame w owner ctx p.runtime.store) library.entry
    stateRelation valueRelation := p.g42_body

omit [DecidableEq K] in
theorem libraryBody_correspondence : libraryBody p = p.g42_body := rfl
end LibraryConsumer

/-- An actually reached constructor component. The antecedent is proved,
and both complete source/target post-states are retained by the relation.
This is not a canonical body producer or an inhabitant of CreationPremises.Inputs. -/
theorem populated_constructor_body (pipeline : Roadmap.Pipeline) (bytes : Roadmap.Bytes)
    (n : Int) (h : ConstructorScalarTransport.range n) :
    let operation := Source.construct (ConstructorScalarTransport.global pipeline)
      ConstructorScalarTransport.frame 8 "Cell" (ConstructorScalarTransport.locals n h)
    operation.run (Source.L0 ConstructorScalarTransport.E, ConstructorScalarTransport.initial bytes) =
      (.ok (), (Source.L0 ConstructorScalarTransport.E, ConstructorScalarTransport.written bytes n h)) ∧
    ConstructorBodyObligation operation (ConstructorScalarTransport.initial bytes)
      (ConstructorScalarTransport.written bytes n h) ConstructorScalarTransport.entered
      (ConstructorScalarTransport.targetBody n h)
      (fun source target => source = ConstructorScalarTransport.written bytes n h ∧
        target = ConstructorScalarTransport.targetWritten n h) := by
  refine ⟨ConstructorScalarTransport.source_construct pipeline 0 bytes n h, ?_⟩
  intro _
  exact ⟨⟨ConstructorScalarTransport.targetWritten n h, List.prefix_refl _⟩,
    ConstructorScalarTransport.body_actual n h, rfl, rfl⟩

/-- A false reached postcondition cannot be hidden behind the implication. -/
theorem impossible_constructor_body (pipeline : Roadmap.Pipeline) (bytes : Roadmap.Bytes)
    (n : Int) (h : ConstructorScalarTransport.range n) :
    ¬ ConstructorBodyObligation
      (Source.construct (ConstructorScalarTransport.global pipeline) ConstructorScalarTransport.frame
        8 "Cell" (ConstructorScalarTransport.locals n h))
      (ConstructorScalarTransport.initial bytes) (ConstructorScalarTransport.written bytes n h)
      ConstructorScalarTransport.entered (ConstructorScalarTransport.targetBody n h)
      (fun _ _ => False) := by
  intro duty
  obtain ⟨_, _, impossible⟩ := duty (ConstructorScalarTransport.source_construct pipeline 0 bytes n h)
  exact impossible

/-- Populated metadata for both actual source pipelines. -/
def fixtureProgram (pipeline : Roadmap.Pipeline) : Source.SrcProg ConstructorScalarTransport.E :=
  ⟨ConstructorScalarTransport.program, pipeline, Source.SemanticsExamples.toyFixed, "Cell"⟩

theorem populated_glob (pipeline : Roadmap.Pipeline) :
    GlobProgramAgreement (ConstructorScalarTransport.global pipeline) (fixtureProgram pipeline) :=
  ⟨rfl, rfl, rfl⟩

theorem changed_contracts : ¬ GlobProgramAgreement (ConstructorScalarTransport.global .legacy)
    {fixtureProgram .legacy with prog := {ConstructorScalarTransport.program with contracts := ["Wrong"]}} := by
  intro p
  have wrong : (["Cell"] : List String) = ["Wrong"] := congrArg Source.Program.contracts p.prog
  exact (by decide +kernel : (["Cell"] : List String) ≠ ["Wrong"]) wrong

theorem changed_pipeline : ¬ GlobProgramAgreement (ConstructorScalarTransport.global .legacy)
    (fixtureProgram .viaIR) := by
  intro p
  have wrong : Roadmap.Pipeline.legacy = .viaIR := p.pipeline
  cases wrong

theorem changed_fixed : ¬ GlobProgramAgreement (ConstructorScalarTransport.global .legacy)
    {fixtureProgram .legacy with fixed :=
      {Source.SemanticsExamples.toyFixed with rootSlots := Source.SemanticsExamples.toyFixed.rootSlots + 1}} := by
  intro p
  have wrong : Source.SemanticsExamples.toyFixed.rootSlots =
      Source.SemanticsExamples.toyFixed.rootSlots + 1 := congrArg Roadmap.Fixed.rootSlots p.fixed
  omega

/-- Actual source library execution paired with an independent caller-typed
observer entry. Both full post-states and exact results are retained.
This fixture supplies neither the missing canonical G42 body producer nor a
LibraryPremises.Inputs inhabitant, catalogue linkage or layout adequacy. -/
theorem populated_library_body (pipeline : Roadmap.Pipeline) :
    let operation := Source.callInternal (SourceDispatchControls.global pipeline)
      SourceDispatchControls.frame 25 SourceDispatchControls.libraryFunction
      SourceDispatchControls.params SourceDispatchControls.returnTypes
    operation.run (Source.L0 SourceDispatchControls.E, SourceDispatchControls.populated) =
      (.ok SourceDispatchControls.result, (Source.L0 SourceDispatchControls.E,
        SourceKeccak.afterLiteral SourceDispatchControls.populated SourceDispatchControls.binary)) ∧
    LibraryBodyObligation (rs := SourceDispatchControls.returnTypes) operation
      SourceDispatchControls.populated
      (SourceKeccak.afterLiteral SourceDispatchControls.populated SourceDispatchControls.binary)
      SourceDispatchControls.result ConstructorScalarTransport.entered
      (LibraryFrameTransport.entry ConstructorScalarTransport.Cell)
      (fun {_} source target =>
        source = SourceKeccak.afterLiteral SourceDispatchControls.populated SourceDispatchControls.binary ∧
        HEq target ConstructorScalarTransport.entered)
      (fun source target => source = SourceDispatchControls.result ∧ target = (1, 7, 2)) := by
  refine ⟨SourceDispatchControls.library_call pipeline, ?_⟩
  intro _
  exact ⟨⟨ConstructorScalarTransport.entered, List.prefix_refl _⟩, (1, 7, 2),
    rfl, rfl, ⟨rfl, HEq.rfl⟩, ⟨rfl, rfl⟩⟩

/-- A false reached library relation is rejected with an inhabited antecedent. -/
theorem impossible_library_body (pipeline : Roadmap.Pipeline) :
    ¬ LibraryBodyObligation (rs := SourceDispatchControls.returnTypes)
      (Source.callInternal (SourceDispatchControls.global pipeline) SourceDispatchControls.frame
        25 SourceDispatchControls.libraryFunction SourceDispatchControls.params SourceDispatchControls.returnTypes)
      SourceDispatchControls.populated
      (SourceKeccak.afterLiteral SourceDispatchControls.populated SourceDispatchControls.binary)
      SourceDispatchControls.result ConstructorScalarTransport.entered
      (LibraryFrameTransport.entry ConstructorScalarTransport.Cell)
      (fun {_} _ _ => False) (fun _ _ => True) := by
  intro duty
  obtain ⟨_, _, _, _, impossible, _⟩ := duty (SourceDispatchControls.library_call pipeline)
  exact impossible

#print axioms nat_int_exact
#print axioms constructor_exact
#print axioms library_exact
#print axioms accepted_origin
#print axioms creationBody_correspondence
#print axioms libraryBody_correspondence
#print axioms populated_constructor_body
#print axioms impossible_constructor_body
#print axioms populated_library_body
#print axioms impossible_library_body


/-! Guarded regression: publishing a common frame relation must preserve the
legacy constructor/library contracts and reject a linked code address used in
place of caller storage. These are frame witnesses, not whole producer inputs. -/
def toProductionFrame {f : Source.Fr} {address : Address} {ctx : Context}
    (p : FrameAgreement f address ctx) : EnvironmentProjection.FrameAgreement f address ctx :=
  ⟨p.address, p.sender, p.value, p.static⟩

def fromProductionFrame {f : Source.Fr} {address : Address} {ctx : Context}
    (p : EnvironmentProjection.FrameAgreement f address ctx) : FrameAgreement f address ctx :=
  ⟨p.address, p.sender, p.value, p.static⟩

theorem production_frame_exact {f : Source.Fr} {address : Address} {ctx : Context} :
    EnvironmentProjection.FrameAgreement f address ctx ↔ FrameAgreement f address ctx :=
  ⟨fromProductionFrame, toProductionFrame⟩

theorem production_constructor_correspondence {f : Source.Fr} {address : Address}
    {ctx : Context} (p : ConstructorScalarTransport.FrameInputs f address ctx) :
    fromProductionFrame (ConstructorScalarTransport.toFrameAgreement p) = fromConstructor p := rfl

theorem production_library_correspondence {K : Type} {caller : K} {f : Source.Fr}
    {owner : Handle caller} {ctx : Context} (p : LibraryFrameTransport.FrameInputs f owner ctx) :
    fromProductionFrame (LibraryFrameTransport.toFrameAgreement p) = fromLibrary p := rfl

theorem production_populated_frame :
    EnvironmentProjection.FrameAgreement ConstructorScalarTransport.frame Controls.self
      ConstructorScalarTransport.targetContext := toProductionFrame populated_frame

theorem production_populated_static : EnvironmentProjection.FrameAgreement
    {ConstructorScalarTransport.frame with value := SourcePayableDeploymentControls.word 0, static := true}
    Controls.self {ConstructorScalarTransport.targetContext with mode := .readOnly} :=
  toProductionFrame populated_static

theorem production_wrong_sender : ¬ EnvironmentProjection.FrameAgreement
    {ConstructorScalarTransport.frame with sender := SourcePayableDeploymentControls.self}
    Controls.self ConstructorScalarTransport.targetContext :=
  fun p => wrong_sender (fromProductionFrame p)

theorem production_wrong_library_address : ¬ EnvironmentProjection.FrameAgreement
    ConstructorScalarTransport.frame LibraryHandlerControls.link
    ConstructorScalarTransport.targetContext :=
  fun p => library_code_is_not_caller (fromProductionFrame p)

#print axioms production_frame_exact
#print axioms production_constructor_correspondence
#print axioms production_library_correspondence
#print axioms production_populated_frame
#print axioms production_populated_static
#print axioms production_wrong_sender
#print axioms production_wrong_library_address


/-! Guarded regression: shared production obligation names preserve the exact
legacy quantifiers and real fixture antecedents; they do not fabricate a
CreationPremises/LibraryPremises producer inhabitant. -/
theorem production_origin_exact {S : P8a.Spec} {E : Source.Env}
    (origins : P8a.SourceOrigins S) (program : Source.SrcProg E)
    (resolved : S.Resolved) (wf : S.WellFormed resolved) (profile : S.InProfile resolved)
    (artifact : Roadmap.Artifact) :
    CreationPremises.OriginWitness origins program resolved wf profile artifact ↔
      OriginWitness origins program resolved wf profile artifact := Iff.rfl

theorem production_someOrigin_exact {S : P8a.Spec} {E : Source.Env}
    (origins : P8a.SourceOrigins S) (program : Source.SrcProg E) :
    CreationPremises.SomeOriginWitness origins program ↔ SomeOriginWitness origins program := Iff.rfl

def toProductionProgram {E : Source.Env} {g : Source.Glob E} {program : Source.SrcProg E}
    (p : GlobProgramAgreement g program) : CreationPremises.GlobProgramAgreement g program :=
  ⟨p.prog, p.pipeline, p.fixed⟩

def fromProductionProgram {E : Source.Env} {g : Source.Glob E} {program : Source.SrcProg E}
    (p : CreationPremises.GlobProgramAgreement g program) : GlobProgramAgreement g program :=
  ⟨p.prog, p.pipeline, p.fixed⟩

theorem production_program_exact {E : Source.Env} (g : Source.Glob E) (program : Source.SrcProg E) :
    CreationPremises.GlobProgramAgreement g program ↔ GlobProgramAgreement g program :=
  ⟨fromProductionProgram, toProductionProgram⟩

theorem production_session_fields_free {E : Source.Env} (g : Source.Glob E)
    (program : Source.SrcProg E) (p : CreationPremises.GlobProgramAgreement g program)
    (env : Roadmap.SessionEnv) (timestamp : Roadmap.Word) :
    CreationPremises.GlobProgramAgreement
      {g with
        balance0 := env.balance
        hasCode := env.hasCode
        callee := env.callee
        timestamp := timestamp} program :=
  toProductionProgram (session_fields_free g program (fromProductionProgram p) env timestamp)

theorem production_main_free {E : Source.Env} (g : Source.Glob E) (program : Source.SrcProg E)
    (p : CreationPremises.GlobProgramAgreement g program) (name : String) :
    CreationPremises.GlobProgramAgreement g {program with main := name} :=
  toProductionProgram (main_free g program (fromProductionProgram p) name)

theorem production_wrong_program {E : Source.Env} (g : Source.Glob E) (program : Source.SrcProg E)
    (different : g.prog ≠ program.prog) : ¬ CreationPremises.GlobProgramAgreement g program :=
  fun p => wrong_program g program different (fromProductionProgram p)

theorem production_wrong_pipeline {E : Source.Env} (g : Source.Glob E) (program : Source.SrcProg E)
    (different : g.pipeline ≠ program.pipeline) : ¬ CreationPremises.GlobProgramAgreement g program :=
  fun p => wrong_pipeline g program different (fromProductionProgram p)

theorem production_wrong_fixed {E : Source.Env} (g : Source.Glob E) (program : Source.SrcProg E)
    (different : g.fixed ≠ program.fixed) : ¬ CreationPremises.GlobProgramAgreement g program :=
  fun p => wrong_fixed g program different (fromProductionProgram p)

theorem production_constructor_obligation_exact {E : Source.Env} {C : Contract}
    (operation : Source.EM E [] Unit) (before after : Source.St E) (caller : State C [])
    (ctor : Prog C [] []) (relation : Source.St E → State C [] → Prop) :
    CreationPremises.ConstructorBodyObligation operation before after caller ctor relation ↔
      ConstructorBodyObligation operation before after caller ctor relation := Iff.rfl

theorem production_library_obligation_exact {E : Source.Env} {C : Contract}
    {rs : List Source.STy} {α : Type}
    (operation : Source.EM E [] (Source.RVal E.layout (Source.STy.ret rs)))
    (before after : Source.St E) (sourceValue : Source.RVal E.layout (Source.STy.ret rs))
    (caller : State C []) (entry : Entry C α)
    (stateRelation : {Γ : Ctx} → Source.St E → State C Γ → Prop)
    (valueRelation : Source.RVal E.layout (Source.STy.ret rs) → α → Prop) :
    LibraryPremises.LibraryBodyObligation operation before after sourceValue caller entry
      stateRelation valueRelation ↔ LibraryBodyObligation operation before after sourceValue
        caller entry stateRelation valueRelation := Iff.rfl

theorem production_populated_constructor_body (pipeline : Roadmap.Pipeline)
    (bytes : Roadmap.Bytes) (n : Int) (h : ConstructorScalarTransport.range n) :
    let operation := Source.construct (ConstructorScalarTransport.global pipeline)
      ConstructorScalarTransport.frame 8 "Cell" (ConstructorScalarTransport.locals n h)
    operation.run (Source.L0 ConstructorScalarTransport.E, ConstructorScalarTransport.initial bytes) =
      (.ok (), (Source.L0 ConstructorScalarTransport.E, ConstructorScalarTransport.written bytes n h)) ∧
    CreationPremises.ConstructorBodyObligation operation (ConstructorScalarTransport.initial bytes)
      (ConstructorScalarTransport.written bytes n h) ConstructorScalarTransport.entered
      (ConstructorScalarTransport.targetBody n h)
      (fun source target => source = ConstructorScalarTransport.written bytes n h ∧
        target = ConstructorScalarTransport.targetWritten n h) :=
  populated_constructor_body pipeline bytes n h

theorem production_false_constructor_post (pipeline : Roadmap.Pipeline)
    (bytes : Roadmap.Bytes) (n : Int) (h : ConstructorScalarTransport.range n) :
    ¬ CreationPremises.ConstructorBodyObligation
      (Source.construct (ConstructorScalarTransport.global pipeline) ConstructorScalarTransport.frame
        8 "Cell" (ConstructorScalarTransport.locals n h))
      (ConstructorScalarTransport.initial bytes) (ConstructorScalarTransport.written bytes n h)
      ConstructorScalarTransport.entered (ConstructorScalarTransport.targetBody n h)
      (fun _ _ => False) := impossible_constructor_body pipeline bytes n h

#print axioms production_origin_exact
#print axioms production_someOrigin_exact
#print axioms production_program_exact
#print axioms production_session_fields_free
#print axioms production_main_free
#print axioms production_wrong_program
#print axioms production_wrong_pipeline
#print axioms production_wrong_fixed
#print axioms production_constructor_obligation_exact
#print axioms production_library_obligation_exact
#print axioms production_populated_constructor_body
#print axioms production_false_constructor_post


/-- Read-only V07 consumer adapter; the actual accepted Source carrier and all
profile proof indices are retained. No producer inhabitant is supplied. -/
theorem production_accepted_origin {S : P8a.Spec} {reference : P8a.OperationalReference}
    {origins : P8a.SourceOrigins S} {roots : P8a.RootModel S}
    (producer : P8a.Producer S reference origins roots)
    (input : S.Input) (resolved : S.Resolved)
    (accepted : producer.admission.frontend input = some resolved) (artifact : Roadmap.Artifact) :
    CreationPremises.OriginWitness origins
      (V07.P8Bindings.acceptedSource producer input resolved accepted artifact).2 resolved
      (V07.P8Bindings.accepted_profile producer input resolved accepted).1
      (V07.P8Bindings.accepted_profile producer input resolved accepted).2 artifact :=
  accepted_origin producer input resolved accepted artifact

#print axioms production_accepted_origin


/-- The actual library component's full Source and target observations remain
available under the production name; this is not a canonical body producer. -/
theorem production_populated_library_body (pipeline : Roadmap.Pipeline) :
    let operation := Source.callInternal (SourceDispatchControls.global pipeline)
      SourceDispatchControls.frame 25 SourceDispatchControls.libraryFunction
      SourceDispatchControls.params SourceDispatchControls.returnTypes
    operation.run (Source.L0 SourceDispatchControls.E, SourceDispatchControls.populated) =
      (.ok SourceDispatchControls.result, (Source.L0 SourceDispatchControls.E,
        SourceKeccak.afterLiteral SourceDispatchControls.populated SourceDispatchControls.binary)) ∧
    LibraryPremises.LibraryBodyObligation (rs := SourceDispatchControls.returnTypes) operation
      SourceDispatchControls.populated
      (SourceKeccak.afterLiteral SourceDispatchControls.populated SourceDispatchControls.binary)
      SourceDispatchControls.result ConstructorScalarTransport.entered
      (LibraryFrameTransport.entry ConstructorScalarTransport.Cell)
      (fun {_} source target =>
        source = SourceKeccak.afterLiteral SourceDispatchControls.populated SourceDispatchControls.binary ∧
        HEq target ConstructorScalarTransport.entered)
      (fun source target => source = SourceDispatchControls.result ∧ target = (1, 7, 2)) :=
  populated_library_body pipeline

theorem production_false_library_post (pipeline : Roadmap.Pipeline) :
    ¬ LibraryPremises.LibraryBodyObligation (rs := SourceDispatchControls.returnTypes)
      (Source.callInternal (SourceDispatchControls.global pipeline) SourceDispatchControls.frame
        25 SourceDispatchControls.libraryFunction SourceDispatchControls.params SourceDispatchControls.returnTypes)
      SourceDispatchControls.populated
      (SourceKeccak.afterLiteral SourceDispatchControls.populated SourceDispatchControls.binary)
      SourceDispatchControls.result ConstructorScalarTransport.entered
      (LibraryFrameTransport.entry ConstructorScalarTransport.Cell)
      (fun {_} _ _ => False) (fun _ _ => True) :=
  impossible_library_body pipeline

#print axioms production_populated_library_body
#print axioms production_false_library_post


/-! Capture shared-contract axiom reports once in this non-default consumer,
instead of repeating diagnostics during every production-module build. -/
#print axioms Solidity.Lowering.V08.CreationPremises.globAgreement_exact
#print axioms Solidity.Lowering.V08.CreationPremises.session_globAgreement
#print axioms Solidity.Lowering.V08.CreationPremises.Inputs.originAgreement
#print axioms Solidity.Lowering.V08.CreationPremises.Inputs.programMetadata
#print axioms Solidity.Lowering.V08.CreationPremises.Inputs.sharedFrame
#print axioms Solidity.Lowering.V08.CreationPremises.Inputs.bodyObligation
#print axioms Solidity.Lowering.V08.CreationPremises.sharedContracts_exact
#print axioms Solidity.Lowering.V08.LibraryPremises.Inputs.programMetadata
#print axioms Solidity.Lowering.V08.LibraryPremises.Inputs.originAgreement
#print axioms Solidity.Lowering.V08.LibraryPremises.Inputs.sharedFrame
#print axioms Solidity.Lowering.V08.LibraryPremises.Inputs.bodyObligation
#print axioms Solidity.Lowering.V08.LibraryPremises.sharedContracts_exact

end Solidity.Lowering.V08.H55Agreements

/-! Guards the component-witness regression where four separate field witnesses
are mistaken for a simultaneous frame. These queries concern only frame inputs,
not global SourceSpec, constructor/library bodies or admission producers. -/
#print axioms Solidity.Lowering.V08.EnvironmentProjection.frameForContext_agrees
#print axioms Solidity.Lowering.V08.EnvironmentProjection.frameForContext_preserves

namespace Solidity.Lowering.V08.H55Agreements

/-- One arbitrary template supplies all three input relations at the caller
storage address. No library code address or global producer is substituted. -/
theorem production_frame_joint {K : Type} {caller : K}
    (owner : ContractWorld.Handle caller) (template : Source.Fr)
    (ctx : ContractWorld.Context) :
    ∃ frame : Source.Fr,
      EnvironmentProjection.FrameAgreement frame owner.address ctx ∧
      ConstructorScalarTransport.FrameInputs frame owner.address ctx ∧
      LibraryFrameTransport.FrameInputs frame owner ctx ∧
      frame.contract = template.contract ∧ frame.checked = template.checked ∧
      frame.depth = template.depth ∧ frame.cd = template.cd := by
  let frame := EnvironmentProjection.frameForContext template owner.address ctx
  have agreement := EnvironmentProjection.frameForContext_agrees template owner.address ctx
  exact ⟨frame, agreement, ConstructorScalarTransport.ofFrameAgreement agreement,
    LibraryFrameTransport.ofFrameAgreement agreement,
    EnvironmentProjection.frameForContext_preserves template owner.address ctx⟩

#print axioms production_frame_joint
end Solidity.Lowering.V08.H55Agreements

namespace Solidity.Lowering.V08.H55Agreements

/-- Exact legacy constructor correspondence retains the complete reached frame. -/
theorem constructor_frame_rebuild (frame : Source.Fr) (address : ContractWorld.Address)
    (ctx : ContractWorld.Context) (agreement : ConstructorScalarTransport.FrameInputs frame address ctx) :
    EnvironmentProjection.frameForContext frame address ctx = frame :=
  EnvironmentProjection.frameForContext_eq_self frame address ctx
    (ConstructorScalarTransport.toFrameAgreement agreement)

/-- Delegated library correspondence rebuilds at caller storage, never code. -/
theorem library_frame_rebuild {K : Type} {caller : K}
    (owner : ContractWorld.Handle caller) (frame : Source.Fr) (ctx : ContractWorld.Context)
    (agreement : LibraryFrameTransport.FrameInputs frame owner ctx) :
    EnvironmentProjection.frameForContext frame owner.address ctx = frame :=
  EnvironmentProjection.frameForContext_eq_self frame owner.address ctx
    (LibraryFrameTransport.toFrameAgreement agreement)

#print axioms constructor_frame_rebuild
#print axioms library_frame_rebuild
#print axioms EnvironmentProjection.frameForContext_fixed_iff
end Solidity.Lowering.V08.H55Agreements

namespace Solidity.Lowering.V08.H55Agreements
open ContractWorld

/-- Guards repeated-call observation collapse: paid and read-only contexts
must keep their distinct ordered values at actual reset boundaries. -/
theorem mixed_context_history :
    transactPrefix LibraryHandlerControls.outer
      ([Controls.paidCtx, {Controls.paidCtx with mode := .readOnly}].map
        (WorldContextComposition.frame false true (⟨Controls.self⟩ : Handle false)
          LibraryHandlerControls.link)) =
      (LibraryHandlerControls.outer.resetTransient, [.ok (1,7,2), .ok (1,0,2)]) := by
  obtain ⟨runtime⟩ := LibraryFrameTransport.runtime_of_success
    (contracts := LibraryHandlerControls.Catalog)
    LibraryHandlerControls.outer LibraryHandlerControls.handled (⟨Controls.self⟩ : Handle false)
    LibraryHandlerControls.library Controls.paidCtx LibraryHandlerControls.expected
    LibraryHandlerControls.delegated_reached
  exact WorldContextComposition.context_history LibraryHandlerControls.outer false true
    (⟨Controls.self⟩ : Handle false) LibraryHandlerControls.link runtime
    [Controls.paidCtx, {Controls.paidCtx with mode := .readOnly}]

#print axioms mixed_context_history
end Solidity.Lowering.V08.H55Agreements

namespace Solidity.Lowering.V08.H55Agreements
open ContractWorld

/-- Guards refusal-history truncation: a real wrong-code-role revert precedes
paid/read-only successes while the complete normalized world is retained. -/
theorem role_refusal_mixed_history :
    transactPrefix LibraryHandlerControls.outer
      (WorldContextComposition.frame false false (⟨Controls.self⟩ : Handle false)
        LibraryHandlerControls.link Controls.paidCtx ::
       [Controls.paidCtx, {Controls.paidCtx with mode := .readOnly}].map
        (WorldContextComposition.frame false true (⟨Controls.self⟩ : Handle false)
          LibraryHandlerControls.link)) =
      (LibraryHandlerControls.outer.resetTransient,
       [.error .revert, .ok (1,7,2), .ok (1,0,2)]) := by
  obtain ⟨runtime⟩ := LibraryFrameTransport.runtime_of_success
    (contracts := LibraryHandlerControls.Catalog)
    LibraryHandlerControls.outer LibraryHandlerControls.handled (⟨Controls.self⟩ : Handle false)
    LibraryHandlerControls.library Controls.paidCtx LibraryHandlerControls.expected
    LibraryHandlerControls.delegated_reached
  exact WorldContextComposition.role_refusal_then_history LibraryHandlerControls.outer false true
    (⟨Controls.self⟩ : Handle false) LibraryHandlerControls.link Controls.paidCtx runtime
    [Controls.paidCtx, {Controls.paidCtx with mode := .readOnly}]

#print axioms role_refusal_mixed_history
end Solidity.Lowering.V08.H55Agreements

namespace Solidity.Lowering.V08.H55Agreements
open ContractWorld

section CanonicalContextComponent
open LibraryFrameTransport
variable {K : Type} [DecidableEq K] {contracts : K → Contract}

/-- Actual Source sender/value reads paired with the existing intrinsic
context-read body, on the canonical frame. Its input agreement is constructed,
not supplied. Source admission, dispatch and general body lowering stay separate. -/
theorem canonical_context_transport {E : Source.Env} {Γ : Source.RCtx}
    (g : Source.Glob E) (template : Source.Fr) (fuel : Nat)
    (locals : Source.Locals E.layout Γ) (state : Source.St E)
    (w : World contracts) (caller kind : K) (self : Handle caller) (address : Address)
    (ctx : Context) (runtime : RuntimeInputs w caller kind self address) :
    let f := EnvironmentProjection.frameForContext template self.address ctx
    (Source.evalPair g f (fuel+2)
      (.magic .msg "sender" rfl : Source.RExpr E Γ (.address false))
      (.magic .msg "value" rfl : Source.RExpr E Γ (.int Source.IntTy.u256))).run (locals,state) =
      (.ok (.val (.address f.sender),.val (SourceEnvironment.sourceWord f.value)),(locals,state)) ∧
    w.libraryCall self (library caller kind address) ctx =
      .ok (w,((f.sender.val : Int),(f.value.val : Int),(f.this.val : Int))) :=
by
  let f := EnvironmentProjection.frameForContext template self.address ctx
  have agreement : FrameInputs f self ctx :=
    ofFrameAgreement (EnvironmentProjection.frameForContext_agrees template self.address ctx)
  exact context_transport g f fuel locals state w caller kind self address ctx runtime agreement

end CanonicalContextComponent

/-- Guards field-only substitution being mistaken for execution: actual Source
reads preserve a populated machine in either pipeline, while the real target
context body preserves its world. This is not a Source library dispatch theorem. -/
theorem populated_canonical_context (pipeline : Roadmap.Pipeline) (bytes : Roadmap.Bytes) :
    let f := EnvironmentProjection.frameForContext ConstructorScalarTransport.frame
      Controls.self Controls.paidCtx
    (Source.evalPair (ConstructorScalarTransport.global pipeline) f 2
      (.magic .msg "sender" rfl : Source.RExpr ConstructorScalarTransport.E [] (.address false))
      (.magic .msg "value" rfl : Source.RExpr ConstructorScalarTransport.E [] (.int Source.IntTy.u256))).run
      (Source.L0 ConstructorScalarTransport.E, ConstructorScalarTransport.initial bytes) =
      (.ok (.val (.address f.sender),.val (SourceEnvironment.sourceWord f.value)),
       (Source.L0 ConstructorScalarTransport.E, ConstructorScalarTransport.initial bytes)) ∧
    LibraryHandlerControls.outer.libraryCall (⟨Controls.self⟩ : Handle false)
      (LibraryFrameTransport.library false true LibraryHandlerControls.link) Controls.paidCtx =
      .ok (LibraryHandlerControls.outer,(1,7,2)) := by
  obtain ⟨runtime⟩ := LibraryFrameTransport.runtime_of_success
    (contracts := LibraryHandlerControls.Catalog)
    LibraryHandlerControls.outer LibraryHandlerControls.handled (⟨Controls.self⟩ : Handle false)
    LibraryHandlerControls.library Controls.paidCtx LibraryHandlerControls.expected
    LibraryHandlerControls.delegated_reached
  exact canonical_context_transport
    (ConstructorScalarTransport.global pipeline) ConstructorScalarTransport.frame 0
    (Source.L0 ConstructorScalarTransport.E) (ConstructorScalarTransport.initial bytes)
    LibraryHandlerControls.outer false true (⟨Controls.self⟩ : Handle false)
    LibraryHandlerControls.link Controls.paidCtx runtime

#print axioms populated_canonical_context
end Solidity.Lowering.V08.H55Agreements
