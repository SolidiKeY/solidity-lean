import Solidity.Lowering.V08.CreationPremises
import Solidity.Lowering.V08.LibraryFrameTransport

/-! Source code-index/catalogue linkage and relative general library bodies.
P4 dispatch and G42.04 body/result lowering are EXPLICIT producer duties.
This relation uses existing Source states and typed World accounts; no new
state or execution semantics is introduced. Code linkage alone proves neither
storage/heap layout nor body adequacy or SourceSpec admission.
The `admission : DeclarationGraphAdmission.Producer …` field makes these inputs uninhabited until
P8-SPEC-LAW1 is resolved (`Lowering/P8/ResourceContractLaw1.lean`), so the
results here are vacuous for now. -/
namespace Solidity.Lowering.V08.LibraryPremises
open Solidity ContractWorld
open Solidity.Lowering.P8
/-! The exact existing delegated body/result duty. Guarded regression: a
shared name must retain both full post-states, actual result extraction and
its value relation; it must not become an assumed World.libraryCall run. -/
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

variable {E : Source.Env} {K : Type} [DecidableEq K] {cs : K → Contract}

theorem instance_code {Γ : Source.RCtx} (g : Source.Glob E)
    (state : Source.St E) (locals : Source.Locals E.layout Γ)
    (address : Roadmap.Address) (index : Nat)
    (code : (state.ex.world.accounts address).code = some index) :
    (Source.instanceAt (Γ:=Γ) g address).run (locals,state) =
      (.ok (g.contractAt index),(locals,state)) := by
  have read : (Source.EM.st : Source.EM E Γ (Source.St E)).run (locals,state) =
      (.ok state,(locals,state)) := rfl
  change (do
    let s ← (Source.EM.st : Source.EM E Γ (Source.St E))
    match (s.ex.world.accounts address).code with
    | some k => pure (g.contractAt k)
    | none => pure none).run (locals,state) = _
  rw [Source.Hoare.run_bind,read]
  dsimp only
  rw [code]
  rfl


/-- Exact metadata/body obligations for a selected library invocation. P8a,
P4 and G42.04 duties are not implemented here. `kindOf` is the supplied typed
source-name to intrinsic-catalogue linkage, not a second interpreter. -/
structure Inputs (S : P8a.Spec) (reference : P8a.OperationalReference)
    (origins : P8a.SourceOrigins S) (roots : P8a.RootModel S)
    (g : Source.Glob E) (frame : Source.Fr) (declaration : Source.Decl)
    (ps rs : List Source.STy) (values : Source.Vals E.layout ps) (horizon : Nat)
    (before after : Source.St E) (sourceValue : Source.RVal E.layout (Source.STy.ret rs))
    (w : World cs) (caller : K) (owner : Handle caller) {α : Type}
    (library : Library cs caller α) (ctx : Context)
    (kindOf : String → Option K)
    (stateRelation : {Γ : Ctx} → Source.St E → State (cs caller) Γ → Prop)
    (valueRelation : Source.RVal E.layout (Source.STy.ret rs) → α → Prop) where
  admission : DeclarationGraphAdmission.Producer S reference origins roots
  program : Source.SrcProg E
  programAgreement : g.prog = program.prog
  pipelineAgreement : g.pipeline = program.pipeline
  fixedAgreement : g.fixed = program.fixed
  origin : ∃ resolved wf profile artifact, origins.meaning resolved wf profile artifact = ⟨E,program⟩
  libraryName : String
  sourceLibraryAddress : Roadmap.Address
  libraryAddressAgreement : sourceLibraryAddress.val = library.address.1.1.toNat
  callerCode : Nat
  libraryCode : Nat
  callerInstalled : (before.ex.world.accounts frame.this).code = some callerCode
  libraryInstalled : (before.ex.world.accounts sourceLibraryAddress).code = some libraryCode
  callerClass : g.contractAt callerCode = some frame.contract
  libraryClass : g.contractAt libraryCode = some libraryName
  callerKind : kindOf frame.contract = some caller
  libraryKind : kindOf libraryName = some library.kind
  callerDeclared : ∃ d ∈ E.decls, d.kind = .contract ∧ d.name = frame.contract
  libraryDeclared : ∃ d ∈ E.decls, d.kind = .library ∧ d.name = libraryName
  functionDeclared : declaration ∈ E.decls ∧ declaration.kind = .function
  functionOwner : declaration.scope = some libraryName
  signature : declaration.fnSig E = some (ps,rs)
  sourceBody : Source.RBody E
  p4_dispatch : g.prog.body (g.dispatchFn frame.contract declaration) = some sourceBody
  frameAgreement : LibraryFrameTransport.FrameInputs frame owner ctx
  runtime : LibraryFrameTransport.RuntimeInputs w caller library.kind owner library.address
  different : library.address ≠ owner.address
  staticAllowed : (ctx.isStatic && !(emptyBody library.entry.body)) = false
  initialRelated : stateRelation before (LibraryFrameTransport.emptyFrame w owner ctx runtime.store)
  sourceExecution : (Source.callInternal g frame horizon declaration values rs).run
    (Source.L0 E,before) = (.ok sourceValue,(Source.L0 E,after))
  /-- Missing G42.04/P4 body/result/layout producer, not World.libraryCall.
  Success is related at the actual caller-typed delegated frame, without any
  second incoming payment or substitution of the library's own storage. -/
  g42_body : (Source.callInternal g frame horizon declaration values rs).run
    (Source.L0 E,before) = (.ok sourceValue,(Source.L0 E,after)) →
    ∃ (out : Out (cs caller) (LibraryFrameTransport.emptyFrame w owner ctx runtime.store).H library.entry.locals)
      (value : α),
      library.entry.body.run (LibraryFrameTransport.emptyFrame w owner ctx runtime.store) = .ok out ∧
      library.entry.result out.st = .ok value ∧ stateRelation after out.st ∧ valueRelation sourceValue value

variable {S : P8a.Spec} {reference : P8a.OperationalReference}
  {origins : P8a.SourceOrigins S} {roots : P8a.RootModel S}
  {g : Source.Glob E} {frame : Source.Fr} {declaration : Source.Decl}
  {ps rs : List Source.STy} {values : Source.Vals E.layout ps} {horizon : Nat}
  {before after : Source.St E} {sourceValue : Source.RVal E.layout (Source.STy.ret rs)}
  {w : World cs} {caller : K} {owner : Handle caller} {α : Type}
  {library : Library cs caller α} {ctx : Context} {kindOf : String → Option K}
  {stateRelation : {Γ : Ctx} → Source.St E → State (cs caller) Γ → Prop}
  {valueRelation : Source.RVal E.layout (Source.STy.ret rs) → α → Prop}
  (p : Inputs S reference origins roots g frame declaration ps rs values horizon before after
    sourceValue w caller owner library ctx kindOf stateRelation valueRelation)

include p in
omit [DecidableEq K] in
theorem source_caller :
    (Source.instanceAt g frame.this).run (Source.L0 E,before) =
      (.ok (some frame.contract),(Source.L0 E,before)) := by
  rw [instance_code g before (Source.L0 E) frame.this p.callerCode p.callerInstalled,p.callerClass]

omit [DecidableEq K] in
theorem source_library :
    (Source.instanceAt g p.sourceLibraryAddress).run (Source.L0 E,before) =
      (.ok (some p.libraryName),(Source.L0 E,before)) := by
  rw [instance_code g before (Source.L0 E) p.sourceLibraryAddress p.libraryCode p.libraryInstalled,
    p.libraryClass]

omit [DecidableEq K] in
/-- The actual initial delegated frame has no second incoming ledger entry.
No assertion about balances after a body that transfers funds is made. -/
theorem no_second_payment :
    (LibraryFrameTransport.emptyFrame w owner ctx p.runtime.store).net = [] ∧
    (LibraryFrameTransport.emptyFrame w owner ctx p.runtime.store).selfBalance = w.funds owner.address ∧
    (LibraryFrameTransport.emptyFrame w owner ctx p.runtime.store).storage = p.runtime.store :=
  ⟨rfl,rfl,rfl⟩

/-- General reached library body, result and exact settlement. All primitive
body/layout duties remain explicit; no whole World preservation is assumed. -/
theorem delegated :
    ∃ (out : Out (cs caller) (LibraryFrameTransport.emptyFrame w owner ctx p.runtime.store).H library.entry.locals)
      (value : α),
      library.entry.body.run (LibraryFrameTransport.emptyFrame w owner ctx p.runtime.store) = .ok out ∧
      stateRelation after out.st ∧ valueRelation sourceValue value ∧
      w.libraryCall owner library ctx = (do
        let next ← w.finish owner.address out.st
        pure (next,value)) := by
  obtain ⟨out,value,body,result,related,observed⟩ := p.g42_body p.sourceExecution
  refine ⟨out,value,body,related,observed,?_⟩
  have linked : w.storage? (⟨library.address⟩ : Handle library.kind) = some p.runtime.linked := by
    simp only [World.storage?,p.runtime.linkedAccount,bind,Option.bind]
    rfl
  have stored : w.storage? owner = some p.runtime.store := by
    simp only [World.storage?,p.runtime.callerAccount,bind,Option.bind]
    rfl
  unfold World.libraryCall
  simp only [p.runtime.libraryRole,p.runtime.callerRole,p.staticAllowed,Bool.not_true,
    Bool.false_or,linked,stored,TRes.ofOpt,bind,Except.bind]
  change (do
    let o ← library.entry.body.run (LibraryFrameTransport.emptyFrame w owner ctx p.runtime.store)
    let next ← w.finish owner.address o.st
    let value ← library.entry.result o.st
    pure (next,value)) = _
  rw [body]
  simp only [bind,Except.bind,result,pure,Except.pure]

/-- Code/account identity at the library address is framed by actual finish;
its FUNDS may still change through a body ledger, so no readonly claim follows. -/
theorem library_account_preserved
    (out : Out (cs caller) (LibraryFrameTransport.emptyFrame w owner ctx p.runtime.store).H library.entry.locals)
    (next : World cs) (finished : w.finish owner.address out.st = .ok next) :
    next.accounts library.address = w.accounts library.address :=
  World.finish_other finished p.different

omit [DecidableEq K] in
/-- One source class name cannot denote both these opposite typed roles.
This is catalogue identity, not a theorem about compiled dispatch or values. -/
theorem source_roles_separate : p.libraryName ≠ frame.contract := by
  intro same
  have other : kindOf frame.contract = some library.kind := by
    rw [← same]
    exact p.libraryKind
  have kinds : caller = library.kind := Option.some.inj (p.callerKind.symm.trans other)
  have role := p.runtime.callerRole
  rw [kinds,p.runtime.libraryRole] at role
  cases role

/-- Wrong runtime library role rejects before any body/account substitution.
The actual role fact is explicit; no giant closed-world reduction is needed. -/
theorem role_rejected (world : World cs) (owner : Handle caller)
    (lib : Library cs caller α) (context : Context) (bad : world.isLibrary lib.kind = false) :
    world.libraryCall owner lib context = .error .revert := by
  simp only [World.libraryCall,bad,Bool.not_false,Bool.true_or,if_true]

namespace Controls
open SourceEnvironmentControls (sender self saved scratch)

def unit : Source.Syn .unit := .unit (.cons
  (.contract false "C" .none .nil (.cons SourceEnvironmentControls.savedDecl.node
    (.cons SourceEnvironmentControls.scratchDecl.node .nil)))
  (.cons (.library "L" .nil) .nil))
def Env : Source.Env := unit.env
def program : Source.Program Env :=
  {body:=fun _ => none,consts:=fun _ => none,inits:=fun _ => [],ctor:=fun _ => none,
    ctorLocals:=fun _ => [],baseArgs:=fun _ => [],contracts:=["C","L"]}
def global (pipeline : Roadmap.Pipeline) : Source.Glob Env :=
  {prog:=program,pipeline:=pipeline,fixed:=Roadmap.Controls.toyFixed,
    balance0:=fun _ => ⟨100,by decide +kernel⟩,hasCode:=fun _ _ => false,
    callee:=fun _ => .answer (.success []),timestamp:=⟨12345,by decide +kernel⟩}
def link : Roadmap.Address := ⟨4,by decide +kernel⟩
def populated (bytes : Roadmap.Bytes) : Source.St Env :=
  {Source.St.init Env with
    ex:=(Source.St.init Env).ex.run [
      .account sender (fun a => {a with balance := 93,nonce:=3}),
      .account self (fun a => {a with balance := 7,nonce:=1,code:=some 0,storage:=a.storage.write saved (.bool true)}),
      .account link (fun a => {a with nonce:=1,code:=some 1}),
      .transient self (fun t => t.write scratch (.bool true)),
      .transient sender (fun t => t.write scratch (.bool true))]
    heap:=((Source.Heap.empty.alloc ⟨.bytes .memory,.bytes bytes⟩).1.alloc
      ⟨.bytes .memory,.bytes [0,255,128]⟩).1
    events:=[.call self ⟨7,by decide +kernel⟩ bytes false]
    logs:=[(self,bytes),(link,[0,255])]
    fnLocals:=⟨[.bool],.cons (.bool true) .nil⟩}

theorem caller_declared :
    ∃ d ∈ Env.decls, d.kind = .contract ∧ d.name = "C" := by
  exact ⟨⟨.contract,"C",none,true,.contract false "C" .none .nil
    (.cons SourceEnvironmentControls.savedDecl.node (.cons SourceEnvironmentControls.scratchDecl.node .nil))⟩,
    List.mem_cons_self,rfl,rfl⟩

theorem library_declared :
    ∃ d ∈ Env.decls, d.kind = .library ∧ d.name = "L" := by
  refine ⟨⟨.library,"L",none,true,.library "L" .nil⟩,?_,rfl,rfl⟩
  exact List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ List.mem_cons_self))

/-- Complete source machine is retained by both ACTUAL lookup operations.
Arbitrary binary bytes and both pipelines are retained without a payload bound. -/
theorem source_client (pipeline : Roadmap.Pipeline) (bytes : Roadmap.Bytes) :
    (Source.instanceAt (global pipeline) self).run (Source.L0 Env,populated bytes) =
      (.ok (some "C"),(Source.L0 Env,populated bytes)) ∧
    (Source.instanceAt (global pipeline) link).run (Source.L0 Env,populated bytes) =
      (.ok (some "L"),(Source.L0 Env,populated bytes)) := by
  cases pipeline <;> exact ⟨rfl,rfl⟩

/-- Ordered observations complement, rather than replace, full state equality. -/
theorem populated_vector (bytes : Roadmap.Bytes) :
    ((populated bytes).ex.world.accounts sender).balance = 93 := rfl

theorem retained_fields (bytes : Roadmap.Bytes) :
    ((populated bytes).ex.world.accounts self).balance = 7 ∧
    ((populated bytes).ex.world.accounts self).nonce = 1 ∧
    ((populated bytes).ex.world.accounts self).code = some 0 ∧
    ((populated bytes).ex.world.accounts link).nonce = 1 ∧
    ((populated bytes).ex.world.accounts link).code = some 1 ∧
    ((populated bytes).ex.world.accounts self).storage.read saved = some (.bool true) ∧
    ((populated bytes).ex.transient.cells self).read scratch = some (.bool true) ∧
    ((populated bytes).ex.transient.cells sender).read scratch = some (.bool true) ∧
    (populated bytes).ex.journal.length = 5 ∧ (populated bytes).heap.next = 2 ∧
    (populated bytes).heap.get 0 = some ⟨.bytes .memory,.bytes bytes⟩ ∧
    (populated bytes).heap.get 1 = some ⟨.bytes .memory,.bytes [0,255,128]⟩ ∧
    (populated bytes).events = [.call self ⟨7,by decide +kernel⟩ bytes false] ∧
    (populated bytes).logs = [(self,bytes),(link,[0,255])] ∧
    (populated bytes).fnLocals = ⟨[.bool],.cons (.bool true) .nil⟩ :=
  ⟨rfl,rfl,rfl,rfl,rfl,rfl,rfl,rfl,rfl,rfl,rfl,rfl,rfl,rfl,rfl⟩

/-- Genuine caller/library declaration identities plus real target library
work are inhabited component facts, NOT an inhabitant of the pending Inputs. -/
theorem source_and_target (pipeline : Roadmap.Pipeline) (bytes : Roadmap.Bytes) :
    (Source.instanceAt (global pipeline) link).run (Source.L0 Env,populated bytes) =
      (.ok (some "L"),(Source.L0 Env,populated bytes)) ∧
    LibraryHandlerControls.delegated LibraryHandlerControls.outer =
      .ok (LibraryHandlerControls.handled,LibraryHandlerControls.expected) :=
  ⟨(source_client pipeline bytes).2,LibraryHandlerControls.delegated_reached⟩

theorem wrong_source_class (pipeline : Roadmap.Pipeline) (bytes : Roadmap.Bytes) :
    (Source.instanceAt (global pipeline) link).run (Source.L0 Env,populated bytes) ≠
      (.ok (some "C"),(Source.L0 Env,populated bytes)) := by
  rw [(source_client pipeline bytes).2]
  intro wrong
  have names : ("L" : String) = "C" := Option.some.inj (Except.ok.inj (congrArg Prod.fst wrong))
  exact (by decide +kernel : ("L" : String) ≠ "C") names

theorem wrong_target_kind :
    LibraryHandlerControls.outer.libraryCall (⟨Solidity.Lowering.V08.Controls.self⟩ : Handle false)
      {LibraryHandlerControls.library with kind:=false} Solidity.Lowering.V08.Controls.paidCtx =
      .error .revert := by
  obtain ⟨runtime⟩ := LibraryFrameTransport.runtime_of_success
    (contracts:=LibraryHandlerControls.Catalog) LibraryHandlerControls.outer LibraryHandlerControls.handled
    (⟨Solidity.Lowering.V08.Controls.self⟩ : Handle false) LibraryHandlerControls.library
    Solidity.Lowering.V08.Controls.paidCtx LibraryHandlerControls.expected
    LibraryHandlerControls.delegated_reached
  exact role_rejected LibraryHandlerControls.outer
    (⟨Solidity.Lowering.V08.Controls.self⟩ : Handle false)
    {LibraryHandlerControls.library with kind:=false} Solidity.Lowering.V08.Controls.paidCtx
    runtime.callerRole

end Controls

section SharedContractAdapters
omit [DecidableEq K]

def Inputs.programMetadata (p : Inputs S reference origins roots g frame declaration ps rs values horizon before after
      sourceValue w caller owner library ctx kindOf stateRelation valueRelation) :
    CreationPremises.GlobProgramAgreement g p.program :=
  ⟨p.programAgreement, p.pipelineAgreement, p.fixedAgreement⟩

def Inputs.originAgreement (p : Inputs S reference origins roots g frame declaration ps rs values horizon before after
      sourceValue w caller owner library ctx kindOf stateRelation valueRelation) :
    CreationPremises.SomeOriginWitness origins p.program := p.origin

def Inputs.sharedFrame (p : Inputs S reference origins roots g frame declaration ps rs values horizon before after
      sourceValue w caller owner library ctx kindOf stateRelation valueRelation) :
    EnvironmentProjection.FrameAgreement frame owner.address ctx :=
  LibraryFrameTransport.toFrameAgreement p.frameAgreement

def Inputs.bodyObligation (p : Inputs S reference origins roots g frame declaration ps rs values horizon before after
      sourceValue w caller owner library ctx kindOf stateRelation valueRelation) :
    LibraryBodyObligation (Source.callInternal g frame horizon declaration values rs)
      before after sourceValue (LibraryFrameTransport.emptyFrame w owner ctx p.runtime.store)
      library.entry stateRelation valueRelation := p.g42_body

theorem sharedContracts_exact (p : Inputs S reference origins roots g frame declaration ps rs values horizon before after
      sourceValue w caller owner library ctx kindOf stateRelation valueRelation) :
    p.originAgreement = p.origin ∧
      LibraryFrameTransport.ofFrameAgreement p.sharedFrame = p.frameAgreement ∧
      p.bodyObligation = p.g42_body := ⟨rfl, rfl, rfl⟩

end SharedContractAdapters

end Solidity.Lowering.V08.LibraryPremises

/-- info: 'Solidity.Lowering.V08.LibraryPremises.instance_code' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Solidity.Lowering.V08.LibraryPremises.instance_code

/-- info: 'Solidity.Lowering.V08.LibraryPremises.source_caller' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Solidity.Lowering.V08.LibraryPremises.source_caller

/-- info: 'Solidity.Lowering.V08.LibraryPremises.source_library' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Solidity.Lowering.V08.LibraryPremises.source_library

/-- info: 'Solidity.Lowering.V08.LibraryPremises.no_second_payment' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Solidity.Lowering.V08.LibraryPremises.no_second_payment

/-- info: 'Solidity.Lowering.V08.LibraryPremises.delegated' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Solidity.Lowering.V08.LibraryPremises.delegated

/-- info: 'Solidity.Lowering.V08.LibraryPremises.library_account_preserved' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms Solidity.Lowering.V08.LibraryPremises.library_account_preserved

/-- info: 'Solidity.Lowering.V08.LibraryPremises.source_roles_separate' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Solidity.Lowering.V08.LibraryPremises.source_roles_separate

/-- info: 'Solidity.Lowering.V08.LibraryPremises.Controls.library_declared' does not depend on any axioms -/
#guard_msgs in
#print axioms Solidity.Lowering.V08.LibraryPremises.Controls.library_declared

/-- info: 'Solidity.Lowering.V08.LibraryPremises.Controls.source_client' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms Solidity.Lowering.V08.LibraryPremises.Controls.source_client

/-- info: 'Solidity.Lowering.V08.LibraryPremises.Controls.populated_vector' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms Solidity.Lowering.V08.LibraryPremises.Controls.populated_vector

/-- info: 'Solidity.Lowering.V08.LibraryPremises.Controls.retained_fields' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms Solidity.Lowering.V08.LibraryPremises.Controls.retained_fields

/-- info: 'Solidity.Lowering.V08.LibraryPremises.Controls.source_and_target' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms Solidity.Lowering.V08.LibraryPremises.Controls.source_and_target

/-- info: 'Solidity.Lowering.V08.LibraryPremises.Controls.wrong_source_class' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms Solidity.Lowering.V08.LibraryPremises.Controls.wrong_source_class

/-- info: 'Solidity.Lowering.V08.LibraryPremises.Controls.wrong_target_kind' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms Solidity.Lowering.V08.LibraryPremises.Controls.wrong_target_kind

/-- info: 'Solidity.Lowering.V08.LibraryPremises.role_rejected' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Solidity.Lowering.V08.LibraryPremises.role_rejected

/-- info: 'Solidity.Lowering.V08.LibraryPremises.Controls.caller_declared' does not depend on any axioms -/
#guard_msgs in
#print axioms Solidity.Lowering.V08.LibraryPremises.Controls.caller_declared
