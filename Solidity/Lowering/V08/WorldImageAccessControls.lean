import Solidity.Lowering.V08.WorldImageAccess
import Solidity.Lowering.V08.WorldCatalogueControls
import Solidity.Lowering.V08.RoleControls

/-! Concrete clients of typed image lookup. These retain the actual source
persistent/transient relation before/after reset and complete intrinsic stores.
They do not establish body execution, admission, runtime frames or bytecode. -/
namespace Solidity.Lowering.V08.WorldImageAccessControls
open Solidity

def located (pipeline : Roadmap.Pipeline) :
    ∃ store : Storage WorldResetControls.Cell,
      (WorldCatalogueControls.world pipeline).accounts
        (EnvironmentProjection.liftAddress SourceEnvironmentControls.self) = some ⟨(),store⟩ ∧
      WorldResetControls.relation SourceEnvironmentControls.self ()
        (SourceEnvironmentControls.populated.ex.world.accounts SourceEnvironmentControls.self).storage
        (SourceEnvironmentControls.populated.ex.transient.cells SourceEnvironmentControls.self) store :=
  WorldImageAccess.installed_store (WorldCatalogueControls.initial_image pipeline)
    SourceEnvironmentControls.self 0 "C" () rfl rfl rfl

def reset_located (pipeline : Roadmap.Pipeline) :
    ∃ store : Storage WorldResetControls.Cell,
      (WorldCatalogueControls.world pipeline).resetTransient.accounts
        (EnvironmentProjection.liftAddress SourceEnvironmentControls.self) = some ⟨(),store⟩ ∧
      WorldResetControls.relation SourceEnvironmentControls.self ()
        ((SourceTransient.endExecution SourceEnvironmentControls.populated).ex.world.accounts SourceEnvironmentControls.self).storage
        ((SourceTransient.endExecution SourceEnvironmentControls.populated).ex.transient.cells SourceEnvironmentControls.self) store :=
  WorldImageAccess.installed_store (WorldCatalogueControls.reset_image pipeline)
    SourceEnvironmentControls.self 0 "C" () rfl rfl rfl

theorem storage_values (pipeline : Roadmap.Pipeline) :
    ((WorldCatalogueControls.world pipeline).storage?
      (⟨EnvironmentProjection.liftAddress SourceEnvironmentControls.self⟩ : ContractWorld.Handle ()),
     (WorldCatalogueControls.world pipeline).resetTransient.storage?
      (⟨EnvironmentProjection.liftAddress SourceEnvironmentControls.self⟩ : ContractWorld.Handle ()),
     (WorldCatalogueControls.world pipeline).storage?
      (⟨EnvironmentProjection.liftAddress SourceEnvironmentControls.sender⟩ : ContractWorld.Handle ())) =
    (some (WorldResetControls.store true true), some (WorldResetControls.store true false), none) := by
  rfl

theorem no_sender_alias (pipeline : Roadmap.Pipeline) :
    ((WorldCatalogueControls.world pipeline).storage?
      (⟨EnvironmentProjection.liftAddress SourceEnvironmentControls.sender⟩ : ContractWorld.Handle ())).isSome ≠
    ((WorldCatalogueControls.world pipeline).storage?
      (⟨EnvironmentProjection.liftAddress SourceEnvironmentControls.self⟩ : ContractWorld.Handle ())).isSome := by
  change false ≠ true
  decide +kernel

/-- Actual lookup clients before and after explicit transaction-end reset.
The existing complete store vector and missing-sender negative remain above. -/
def related_lookup (pipeline : Roadmap.Pipeline) :
    ∃ store : Storage WorldResetControls.Cell,
      (WorldCatalogueControls.world pipeline).storage?
        (⟨EnvironmentProjection.liftAddress SourceEnvironmentControls.self⟩ : ContractWorld.Handle ()) = some store ∧
      WorldResetControls.relation SourceEnvironmentControls.self ()
        (SourceEnvironmentControls.populated.ex.world.accounts SourceEnvironmentControls.self).storage
        (SourceEnvironmentControls.populated.ex.transient.cells SourceEnvironmentControls.self) store :=
  WorldImageAccess.installed_lookup (WorldCatalogueControls.initial_image pipeline)
    SourceEnvironmentControls.self 0 "C" () rfl rfl rfl

def reset_related_lookup (pipeline : Roadmap.Pipeline) :
    ∃ store : Storage WorldResetControls.Cell,
      (WorldCatalogueControls.world pipeline).resetTransient.storage?
        (⟨EnvironmentProjection.liftAddress SourceEnvironmentControls.self⟩ : ContractWorld.Handle ()) = some store ∧
      WorldResetControls.relation SourceEnvironmentControls.self ()
        ((SourceTransient.endExecution SourceEnvironmentControls.populated).ex.world.accounts SourceEnvironmentControls.self).storage
        ((SourceTransient.endExecution SourceEnvironmentControls.populated).ex.transient.cells SourceEnvironmentControls.self) store :=
  WorldImageAccess.installed_lookup (WorldCatalogueControls.reset_image pipeline)
    SourceEnvironmentControls.self 0 "C" () rfl rfl rfl

/-- The assembled world uses the actual Source global clock. Both pipelines,
static flags and target contexts retain the complete populated Source machine. -/
theorem timestamp_transport (pipeline : Roadmap.Pipeline) (static : Bool)
    (context : ContractWorld.Context) (horizon : Nat) :
    (Source.evalE (SourceEnvironmentControls.global pipeline)
      {SourceEnvironmentControls.frame with static := static} (horizon+1)
      (.magic .block "timestamp" rfl : Source.RExpr SourceEnvironmentControls.E [.bool]
        (.int Source.IntTy.u256))).run (SourceEnvironmentControls.locals,SourceEnvironmentControls.populated) =
      (.ok (.val (SourceEnvironment.sourceWord (SourceEnvironmentControls.global pipeline).timestamp)),
        (SourceEnvironmentControls.locals,SourceEnvironmentControls.populated)) ∧
    (Solidity.Val.simple (.env .timestamp rfl) : Solidity.Val WorldResetControls.Cell [] .uint).evalT
      (LibraryFrameTransport.emptyFrame (WorldCatalogueControls.world pipeline)
        (⟨EnvironmentProjection.liftAddress SourceEnvironmentControls.self⟩ : ContractWorld.Handle ())
        context (WorldResetControls.store true true)) =
      .ok (EnvironmentProjection.liftWord (SourceEnvironmentControls.global pipeline).timestamp) :=
  WorldImageAccess.timestamp_frame
    (g:=SourceEnvironmentControls.global pipeline) (source:=SourceEnvironmentControls.populated)
    (target:=WorldCatalogueControls.world pipeline) (by rfl)
    {SourceEnvironmentControls.frame with static := static} horizon
    SourceEnvironmentControls.locals () _ context (WorldResetControls.store true true)

/-- The full account image also holds at zero time, so it cannot supply clock
agreement. This is an actual different World, not a source rollback. -/
theorem same_image_wrong_clock (pipeline : Roadmap.Pipeline) :
    WorldImage.Image (SourceEnvironmentControls.global pipeline) WorldResetControls.kindOf
      WorldResetControls.relation WorldCatalogueControls.environment SourceEnvironmentControls.populated.events
      SourceEnvironmentControls.populated ((WorldCatalogueControls.world pipeline).atTime (PrimTy.dflt .uint)) ∧
    ¬ WorldImage.TimeAligned (SourceEnvironmentControls.global pipeline)
      ((WorldCatalogueControls.world pipeline).atTime (PrimTy.dflt .uint)) := by
  refine ⟨WorldImageAccess.image_atTime (WorldCatalogueControls.initial_image pipeline) _, ?_⟩
  intro clock
  have impossible := congrArg (fun word : Semantics.Word => word.1) clock
  change (0 : Int) = 12345 at impossible
  omega

theorem timestamp_zero (pipeline : Roadmap.Pipeline) (static : Bool) :
    (Source.evalE (SourceEnvironmentControls.global pipeline)
      {SourceEnvironmentControls.frame with static := static} 0
      (.magic .block "timestamp" rfl : Source.RExpr SourceEnvironmentControls.E [.bool]
        (.int Source.IntTy.u256))).run (SourceEnvironmentControls.locals,SourceEnvironmentControls.populated) =
      (.error .timeout,(SourceEnvironmentControls.locals,SourceEnvironmentControls.populated)) := by
  rfl

theorem wrong_clock_read (pipeline : Roadmap.Pipeline) (context : ContractWorld.Context) :
    (Solidity.Val.simple (.env .timestamp rfl) : Solidity.Val WorldResetControls.Cell [] .uint).evalT
      (LibraryFrameTransport.emptyFrame ((WorldCatalogueControls.world pipeline).atTime (PrimTy.dflt .uint))
        (⟨EnvironmentProjection.liftAddress SourceEnvironmentControls.self⟩ : ContractWorld.Handle ())
        context (WorldResetControls.store true true)) = .ok (PrimTy.dflt .uint) := by
  rfl

theorem wrong_clock_observation (pipeline : Roadmap.Pipeline) (context : ContractWorld.Context) :
    ((Solidity.Val.simple (.env .timestamp rfl) : Solidity.Val WorldResetControls.Cell [] .uint).evalT
      (LibraryFrameTransport.emptyFrame ((WorldCatalogueControls.world pipeline).atTime (PrimTy.dflt .uint))
        (⟨EnvironmentProjection.liftAddress SourceEnvironmentControls.self⟩ : ContractWorld.Handle ())
        context (WorldResetControls.store true true))).toOption.map (fun word => word.1) ≠ some 12345 := by
  simp only [wrong_clock_read]
  decide +kernel

theorem complete_time_frame (pipeline : Roadmap.Pipeline) :
    (((WorldCatalogueControls.world pipeline).atTime (PrimTy.dflt .uint)).accounts,
      ((WorldCatalogueControls.world pipeline).atTime (PrimTy.dflt .uint)).funds,
      ((WorldCatalogueControls.world pipeline).atTime (PrimTy.dflt .uint)).roles,
      ((WorldCatalogueControls.world pipeline).atTime (PrimTy.dflt .uint)).timestamp) =
    ((WorldCatalogueControls.world pipeline).accounts,(WorldCatalogueControls.world pipeline).funds,
      (WorldCatalogueControls.world pipeline).roles,PrimTy.dflt .uint) := by
  rfl

namespace LibraryClient
open ContractWorld

def E : Source.Env := ⟨[RoleControls.libraryDecl]⟩
def caller : Roadmap.Address := SourceEnvironmentControls.self
def link : Roadmap.Address := ⟨4, by decide +kernel⟩
def codeAt (a : Roadmap.Address) : Option Nat :=
  if a = caller then some 0 else if a = link then some 1 else none
def source : Source.St E :=
  ⟨⟨⟨fun a => {Source.Account.empty _ with code := codeAt a, balance := ⟨if a = caller then 7 else 93, by split <;> decide +kernel⟩}⟩,
      Source.Transient.empty, []⟩, Source.Heap.empty, [], [], ⟨[],.nil⟩, Source.FailureExecution.Cursor.empty⟩
def program : Source.Program E :=
  {body := fun _ => none, consts := fun _ => none, inits := fun _ => [], ctor := fun _ => none,
    ctorLocals := fun _ => [], baseArgs := fun _ => [], contracts := ["C","L"]}
def global (pipeline : Roadmap.Pipeline) : Source.Glob E :=
  {prog := program, pipeline, fixed := Roadmap.Controls.toyFixed,
    balance0 := fun _ => ⟨100,by decide +kernel⟩, hasCode := fun _ _ => false,
    callee := fun _ => .answer (.success []), timestamp := ⟨12345,by decide +kernel⟩}
def catalog : Bool → Contract := fun _ => LibraryControls.Empty
def kindOf (name : String) : Option Bool :=
  if name = "C" then some false else if name = "L" then some true else none
def relation : WorldImage.StoreRelation E catalog := fun _ _ persistent temporary store =>
  persistent = Source.Storage.empty ∧ temporary = Source.Storage.empty ∧ store = .nil

def inputs (pipeline : Roadmap.Pipeline) : WorldCatalogue.Inputs (global pipeline) kindOf relation source where
  installed address code present := by
    change codeAt address = some code at present
    by_cases c : address = caller
    · simp only [codeAt,c,if_pos] at present
      have same : code = 0 := (Option.some.inj present).symm
      subst code
      exact ⟨"C", false, .nil, rfl, rfl, ⟨rfl,rfl,rfl⟩⟩
    · by_cases l : address = link
      · simp only [codeAt,if_neg c,if_pos l] at present
        have same : code = 1 := (Option.some.inj present).symm
        subst code
        exact ⟨"L", true, .nil, rfl, rfl, ⟨rfl,rfl,rfl⟩⟩
      · simp only [codeAt,if_neg c,if_neg l] at present
        cases present
  roles := fun kind => if kind then .libraryCode else .contractCode
  library_role name kind selected := by
    by_cases c : name = "C"
    · subst name
      change some false = some kind at selected
      cases selected
      rfl
    · by_cases l : name = "L"
      · subst name
        change some true = some kind at selected
        cases selected
        rfl
      · simp only [kindOf,if_neg c,if_neg l] at selected
        cases selected

def world (pipeline : Roadmap.Pipeline) : World catalog :=
  WorldCatalogue.assemble (inputs pipeline) WorldCatalogueControls.environment []
    (EnvironmentProjection.liftWord (global pipeline).timestamp)

def runtime (pipeline : Roadmap.Pipeline) :
    Nonempty (LibraryFrameTransport.RuntimeInputs (world pipeline) false true
      ⟨EnvironmentProjection.liftAddress caller⟩ (EnvironmentProjection.liftAddress link)) :=
  WorldImageAccess.library_inputs (WorldCatalogue.assembled_image (inputs pipeline)
    WorldCatalogueControls.environment [] _) caller link 0 1 "C" "L" false true
    rfl rfl rfl rfl rfl rfl rfl rfl

theorem reached (pipeline : Roadmap.Pipeline) (context : Context) :
    (world pipeline).libraryCall ⟨EnvironmentProjection.liftAddress caller⟩
      (LibraryFrameTransport.library false true (EnvironmentProjection.liftAddress link)) context =
      .ok (world pipeline,(context.sender.1.1,context.value.1,(EnvironmentProjection.liftAddress caller).1.1)) := by
  obtain ⟨certificate⟩ := runtime pipeline
  exact LibraryFrameTransport.library_actual _ false true _ _ context certificate

/-- Complete account/store/role/funding probe; source catalogue evidence is
not a Source call/body admission proof (this fixture has no source bodies). -/
theorem snapshot (pipeline : Roadmap.Pipeline) :
    ((world pipeline).storage? (⟨EnvironmentProjection.liftAddress caller⟩ : Handle false),
      (world pipeline).storage? (⟨EnvironmentProjection.liftAddress link⟩ : Handle true),
      (world pipeline).storage? (⟨EnvironmentProjection.liftAddress caller⟩ : Handle true),
      (world pipeline).isLibrary false, (world pipeline).isLibrary true,
      ((world pipeline).balance (EnvironmentProjection.liftAddress caller)).1,
      ((world pipeline).balance (EnvironmentProjection.liftAddress link)).1,
      source.ex.journal.length, source.heap.next) =
      (some .nil, some .nil, none, false, true, 7, 93, 0, 0) := by
  rfl

theorem wrong_role (pipeline : Roadmap.Pipeline) :
    ({world pipeline with roles := fun _ => .contractCode}).libraryCall
      (⟨EnvironmentProjection.liftAddress caller⟩ : Handle false)
      (LibraryFrameTransport.library false true (EnvironmentProjection.liftAddress link)) Controls.paidCtx =
      .error .revert := by
  rfl

theorem wrong_context (pipeline : Roadmap.Pipeline) :
    ((world pipeline).libraryCall (⟨EnvironmentProjection.liftAddress caller⟩ : Handle false)
      (LibraryFrameTransport.library false true (EnvironmentProjection.liftAddress link)) Controls.paidCtx).toOption.map Prod.snd ≠
      some (1,7,4) := by
  rw [reached]
  change some (1,7,2) ≠ some (1,7,4)
  decide +kernel

theorem source_selected (pipeline : Roadmap.Pipeline) :
    (Source.instanceAt (Γ:=[]) (global pipeline) caller).run (Source.L0 E,source) =
      (.ok (some "C"),(Source.L0 E,source)) ∧
    (Source.instanceAt (Γ:=[]) (global pipeline) link).run (Source.L0 E,source) =
      (.ok (some "L"),(Source.L0 E,source)) := by
  exact ⟨rfl,rfl⟩

theorem missing_library (pipeline : Roadmap.Pipeline) :
    ({world pipeline with accounts := fun a =>
      if a = EnvironmentProjection.liftAddress link then none else (world pipeline).accounts a}).libraryCall
      (⟨EnvironmentProjection.liftAddress caller⟩ : Handle false)
      (LibraryFrameTransport.library false true (EnvironmentProjection.liftAddress link)) Controls.paidCtx =
      .error .revert := by
  rfl

/-- info: 'Solidity.Lowering.V08.WorldImageAccessControls.LibraryClient.missing_library' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms missing_library
/-- info: 'Solidity.Lowering.V08.WorldImageAccessControls.LibraryClient.runtime' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms runtime
/-- info: 'Solidity.Lowering.V08.WorldImageAccessControls.LibraryClient.reached' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms reached
/-- info: 'Solidity.Lowering.V08.WorldImageAccessControls.LibraryClient.snapshot' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms snapshot
/-- info: 'Solidity.Lowering.V08.WorldImageAccessControls.LibraryClient.wrong_role' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms wrong_role
/-- info: 'Solidity.Lowering.V08.WorldImageAccessControls.LibraryClient.wrong_context' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms wrong_context
/-- info: 'Solidity.Lowering.V08.WorldImageAccessControls.LibraryClient.source_selected' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms source_selected

end LibraryClient

/-- info: 'Solidity.Lowering.V08.WorldImageAccessControls.located' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms located
/-- info: 'Solidity.Lowering.V08.WorldImageAccessControls.reset_located' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms reset_located
/-- info: 'Solidity.Lowering.V08.WorldImageAccessControls.storage_values' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms storage_values
/-- info: 'Solidity.Lowering.V08.WorldImageAccessControls.no_sender_alias' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms no_sender_alias
/-- info: 'Solidity.Lowering.V08.WorldImageAccessControls.related_lookup' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms related_lookup
/-- info: 'Solidity.Lowering.V08.WorldImageAccessControls.reset_related_lookup' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms reset_related_lookup
/-- info: 'Solidity.Lowering.V08.WorldImageAccessControls.timestamp_transport' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms timestamp_transport
/-- info: 'Solidity.Lowering.V08.WorldImageAccessControls.same_image_wrong_clock' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms same_image_wrong_clock
/-- info: 'Solidity.Lowering.V08.WorldImageAccessControls.timestamp_zero' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms timestamp_zero
/-- info: 'Solidity.Lowering.V08.WorldImageAccessControls.wrong_clock_read' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms wrong_clock_read
/-- info: 'Solidity.Lowering.V08.WorldImageAccessControls.wrong_clock_observation' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms wrong_clock_observation
/-- info: 'Solidity.Lowering.V08.WorldImageAccessControls.complete_time_frame' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms complete_time_frame
end Solidity.Lowering.V08.WorldImageAccessControls


namespace Solidity.Lowering.V08.CatalogueReflectionControls
open Solidity

theorem reflected_before (p : Roadmap.Pipeline) :
    ∃ code name, (SourceEnvironmentControls.populated.ex.world.accounts SourceEnvironmentControls.self).code = some code ∧
      (SourceEnvironmentControls.global p).contractAt code = some name ∧ WorldResetControls.kindOf name = some () ∧
      WorldResetControls.relation SourceEnvironmentControls.self ()
        (SourceEnvironmentControls.populated.ex.world.accounts SourceEnvironmentControls.self).storage
        (SourceEnvironmentControls.populated.ex.transient.cells SourceEnvironmentControls.self) (WorldResetControls.store true true) :=
  WorldImageAccess.lookup_reflect (WorldCatalogueControls.initial_image p) SourceEnvironmentControls.self () _ rfl

theorem reflected_after_reset (p : Roadmap.Pipeline) :
    ∃ code name, ((SourceTransient.endExecution SourceEnvironmentControls.populated).ex.world.accounts SourceEnvironmentControls.self).code = some code ∧
      (SourceEnvironmentControls.global p).contractAt code = some name ∧ WorldResetControls.kindOf name = some () ∧
      WorldResetControls.relation SourceEnvironmentControls.self ()
        ((SourceTransient.endExecution SourceEnvironmentControls.populated).ex.world.accounts SourceEnvironmentControls.self).storage
        ((SourceTransient.endExecution SourceEnvironmentControls.populated).ex.transient.cells SourceEnvironmentControls.self)
        (WorldResetControls.store true false) :=
  WorldImageAccess.lookup_reflect (WorldCatalogueControls.reset_image p) SourceEnvironmentControls.self () _ rfl

def probe (p : Roadmap.Pipeline) (address : Roadmap.Address) :=
  (Source.instanceAt (Γ:=[.bool]) (SourceEnvironmentControls.global p) address).run
    (SourceEnvironmentControls.locals,SourceEnvironmentControls.populated)

theorem actual_source_probes (p : Roadmap.Pipeline) :
    (probe p SourceEnvironmentControls.self,probe p SourceEnvironmentControls.sender) =
      ((.ok (some "C"),(SourceEnvironmentControls.locals,SourceEnvironmentControls.populated)),
       (.ok none,(SourceEnvironmentControls.locals,SourceEnvironmentControls.populated))) := by
  rfl

/-- The external sender has funds but no tracked installed code. -/
theorem absent_code_not_absent_funds (p : Roadmap.Pipeline) :
    (WorldCatalogueControls.world p).storage?
        (⟨EnvironmentProjection.liftAddress SourceEnvironmentControls.sender⟩ : ContractWorld.Handle ()) = none ∧
    ((WorldCatalogueControls.world p).balance (EnvironmentProjection.liftAddress SourceEnvironmentControls.sender)).1 = 100 := by
  exact ⟨WorldImageAccess.lookup_none_of_code_absent (WorldCatalogueControls.initial_image p)
    SourceEnvironmentControls.sender () rfl,rfl⟩

/-- The full original ordered world and Source probe states are retained. -/
theorem complete_observations (p : Roadmap.Pipeline) :
    ((WorldCatalogueControls.world p).accounts (EnvironmentProjection.liftAddress SourceEnvironmentControls.self),
     (WorldCatalogueControls.world p).accounts (EnvironmentProjection.liftAddress SourceEnvironmentControls.sender),
     ((WorldCatalogueControls.world p).balance (EnvironmentProjection.liftAddress SourceEnvironmentControls.sender)).1,
     ((WorldCatalogueControls.world p).balance (EnvironmentProjection.liftAddress SourceEnvironmentControls.self)).1,
     (WorldCatalogueControls.world p).timestamp.1,
     (WorldCatalogueControls.world p).storage? (⟨EnvironmentProjection.liftAddress SourceEnvironmentControls.self⟩ : ContractWorld.Handle ()),
     (WorldCatalogueControls.world p).resetTransient.storage? (⟨EnvironmentProjection.liftAddress SourceEnvironmentControls.self⟩ : ContractWorld.Handle ()),
     probe p SourceEnvironmentControls.self) =
    (some ⟨(),WorldResetControls.store true true⟩,none,100,7,12345,
     some (WorldResetControls.store true true),some (WorldResetControls.store true false),
     (.ok (some "C"),(SourceEnvironmentControls.locals,SourceEnvironmentControls.populated))) := by
  rfl

theorem wrong_code (p : Roadmap.Pipeline) :
    ¬ ∃ name, (SourceEnvironmentControls.populated.ex.world.accounts SourceEnvironmentControls.self).code = some 1 ∧
      (SourceEnvironmentControls.global p).contractAt 1 = some name ∧ WorldResetControls.kindOf name = some () := by
  rintro ⟨name,code,_,_⟩
  cases code

theorem stale_transient_relation :
    ¬ WorldResetControls.relation SourceEnvironmentControls.self ()
      ((SourceTransient.endExecution SourceEnvironmentControls.populated).ex.world.accounts SourceEnvironmentControls.self).storage
      ((SourceTransient.endExecution SourceEnvironmentControls.populated).ex.transient.cells SourceEnvironmentControls.self)
      (WorldResetControls.store true true) := by
  rintro ⟨saved,scratch,persistent,temporary,stored⟩
  cases persistent
  cases temporary
  cases stored

/-- Extra catalogue kind is uninstalled: no nonempty library storage or source
library declaration is invented. This witnesses a genuine wrong-kind lookup. -/
def catalogue : Bool → Contract
  | false => WorldResetControls.Cell
  | true => { vars := [] }
def kindOf (name : String) : Option Bool := (WorldResetControls.kindOf name).map (fun _ => false)
def relation : WorldImage.StoreRelation SourceEnvironmentControls.E catalogue
  | address,false,persistent,temporary,store => WorldResetControls.relation address () persistent temporary store
  | _,true,_,_,_ => False

def world (p : Roadmap.Pipeline) : ContractWorld.World catalogue :=
  { accounts:=fun address => ((WorldCatalogueControls.world p).accounts address).map (fun entry => ⟨false,entry.2⟩)
    funds:=(WorldCatalogueControls.world p).funds
    roles:=fun kind => if kind then .libraryCode else .contractCode
    timestamp:=(WorldCatalogueControls.world p).timestamp }

theorem image (p : Roadmap.Pipeline) :
    WorldImage.Image (SourceEnvironmentControls.global p) kindOf relation WorldCatalogueControls.environment
      SourceEnvironmentControls.populated.events SourceEnvironmentControls.populated (world p) where
  accounts address := by
    have original := (WorldCatalogueControls.initial_image p).accounts address
    unfold WorldImage.AccountImage at original ⊢
    dsimp only at original ⊢
    cases code : (SourceEnvironmentControls.populated.ex.world.accounts (EnvironmentProjection.lowerAddress address)).code with
    | none =>
      simp only [code] at original ⊢
      change Option.map _ ((WorldCatalogueControls.world p).accounts address) = none
      rw [original];rfl
    | some index =>
      simp only [code] at original ⊢
      obtain ⟨name,kind,store,selected,linked,installed,represented⟩ := original
      cases kind
      refine ⟨name,false,store,selected,?_,?_,represented⟩
      · change Option.map _ (WorldResetControls.kindOf name) = some false
        rw [linked];rfl
      · change Option.map _ ((WorldCatalogueControls.world p).accounts address) = some (⟨false,store⟩ : (kind : Bool) × Storage (catalogue kind))
        rw [installed];rfl
  funds := (WorldCatalogueControls.initial_image p).funds
  roles name kind linked := by
    cases kind with
    | false => rfl
    | true =>
      unfold kindOf at linked
      cases h : WorldResetControls.kindOf name with
      | none => rw [h] at linked;cases linked
      | some value => rw [h] at linked;cases linked

theorem actual_wrong_kind (p : Roadmap.Pipeline) :
    (world p).storage? (⟨EnvironmentProjection.liftAddress SourceEnvironmentControls.self⟩ : ContractWorld.Handle true) = none ∧
    (world p).storage? (⟨EnvironmentProjection.liftAddress SourceEnvironmentControls.self⟩ : ContractWorld.Handle false) =
      some (WorldResetControls.store true true) :=
  ⟨WorldImageAccess.lookup_none_of_kind_mismatch (image p) SourceEnvironmentControls.self 0 "C" true rfl rfl (by decide +kernel),rfl⟩


theorem actual_reset_probe (p : Roadmap.Pipeline) :
    (Source.instanceAt (Γ:=[.bool]) (SourceEnvironmentControls.global p) SourceEnvironmentControls.self).run
      (SourceEnvironmentControls.locals,SourceTransient.endExecution SourceEnvironmentControls.populated) =
      (.ok (some "C"),(SourceEnvironmentControls.locals,SourceTransient.endExecution SourceEnvironmentControls.populated)) := by
  rfl

theorem code_present_wrong_kind (p : Roadmap.Pipeline) :
    (probe p SourceEnvironmentControls.self,
     (world p).storage? (⟨EnvironmentProjection.liftAddress SourceEnvironmentControls.self⟩ : ContractWorld.Handle true)) =
      ((.ok (some "C"),(SourceEnvironmentControls.locals,SourceEnvironmentControls.populated)),none) := by
  rfl


theorem no_extra_installation (p : Roadmap.Pipeline) (address : ContractWorld.Address) :
    (world p).storage? (⟨address⟩ : ContractWorld.Handle true) = none := by
  unfold ContractWorld.World.storage?
  dsimp only [world]
  cases present : (WorldCatalogueControls.world p).accounts address with
  | none => rfl
  | some pair => rcases pair with ⟨kind,store⟩;cases kind;rfl

theorem two_kind_observations (p : Roadmap.Pipeline) :
    ((world p).accounts (EnvironmentProjection.liftAddress SourceEnvironmentControls.self),
     (world p).accounts (EnvironmentProjection.liftAddress SourceEnvironmentControls.sender),
     ((world p).balance (EnvironmentProjection.liftAddress SourceEnvironmentControls.sender)).1,
     ((world p).balance (EnvironmentProjection.liftAddress SourceEnvironmentControls.self)).1,
     (world p).timestamp.1,(world p).isLibrary false,(world p).isLibrary true,
     (world p).storage? (⟨EnvironmentProjection.liftAddress SourceEnvironmentControls.self⟩ : ContractWorld.Handle false),
     (world p).storage? (⟨EnvironmentProjection.liftAddress SourceEnvironmentControls.self⟩ : ContractWorld.Handle true),
     probe p SourceEnvironmentControls.self) =
    (some (⟨false,WorldResetControls.store true true⟩ : (kind : Bool) × Storage (catalogue kind)),none,
     100,7,12345,false,true,some (WorldResetControls.store true true),none,
     (.ok (some "C"),(SourceEnvironmentControls.locals,SourceEnvironmentControls.populated))) := by
  rfl

/-- info: 'Solidity.Lowering.V08.CatalogueReflectionControls.reflected_before' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms Solidity.Lowering.V08.CatalogueReflectionControls.reflected_before
/-- info: 'Solidity.Lowering.V08.CatalogueReflectionControls.reflected_after_reset' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms Solidity.Lowering.V08.CatalogueReflectionControls.reflected_after_reset
/-- info: 'Solidity.Lowering.V08.CatalogueReflectionControls.actual_source_probes' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms Solidity.Lowering.V08.CatalogueReflectionControls.actual_source_probes
/-- info: 'Solidity.Lowering.V08.CatalogueReflectionControls.absent_code_not_absent_funds' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms Solidity.Lowering.V08.CatalogueReflectionControls.absent_code_not_absent_funds
/-- info: 'Solidity.Lowering.V08.CatalogueReflectionControls.complete_observations' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms Solidity.Lowering.V08.CatalogueReflectionControls.complete_observations
/-- info: 'Solidity.Lowering.V08.CatalogueReflectionControls.wrong_code' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms Solidity.Lowering.V08.CatalogueReflectionControls.wrong_code
/-- info: 'Solidity.Lowering.V08.CatalogueReflectionControls.stale_transient_relation' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms Solidity.Lowering.V08.CatalogueReflectionControls.stale_transient_relation
/-- info: 'Solidity.Lowering.V08.CatalogueReflectionControls.image' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Solidity.Lowering.V08.CatalogueReflectionControls.image
/-- info: 'Solidity.Lowering.V08.CatalogueReflectionControls.actual_wrong_kind' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms Solidity.Lowering.V08.CatalogueReflectionControls.actual_wrong_kind
/-- info: 'Solidity.Lowering.V08.CatalogueReflectionControls.actual_reset_probe' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms Solidity.Lowering.V08.CatalogueReflectionControls.actual_reset_probe
/-- info: 'Solidity.Lowering.V08.CatalogueReflectionControls.code_present_wrong_kind' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms Solidity.Lowering.V08.CatalogueReflectionControls.code_present_wrong_kind
/-- info: 'Solidity.Lowering.V08.CatalogueReflectionControls.no_extra_installation' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms Solidity.Lowering.V08.CatalogueReflectionControls.no_extra_installation
/-- info: 'Solidity.Lowering.V08.CatalogueReflectionControls.two_kind_observations' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms Solidity.Lowering.V08.CatalogueReflectionControls.two_kind_observations
end Solidity.Lowering.V08.CatalogueReflectionControls
