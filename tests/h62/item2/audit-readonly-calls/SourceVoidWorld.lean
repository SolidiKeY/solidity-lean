import SourceVoidSelection
import Solidity.Lowering.V08.WorldCatalogueTransport

/-! Guard a declared Source function being mistaken for an installed typed
account. The existing catalogue assembler consumes actual code/name/kind and
exact empty persistent/transient store evidence for the same nil-function
Source state. Funds, roles and timestamp are retained. These empty-contract
stores have no fields; no general layout/body lowering, native world-image
provenance, Source-to-core caller relation, call commit or H121 is inferred. -/
namespace Solidity.H62.ReadonlyCalls.SourceVoidWorld
open Solidity
open Solidity.Lowering.V08
open Solidity.H62.ReadonlyCalls.SourceVoidSelection

def catalogue : Unit → Contract := fun _ => Evm.Memory.CompileExamples.C
def kindOf (name : String) : Option Unit := if name = "C" then some () else none
def relation : WorldImage.StoreRelation environment catalogue :=
  fun _ _ persistent temporary store =>
    persistent = Source.Storage.empty ∧ temporary = Source.Storage.empty ∧ store = Storage.init _

theorem source_code (address : Roadmap.Address) :
    (initialSource.ex.world.accounts address).code =
      if address = receiver then some 0 else none := by
  by_cases same : address = receiver
  · subst address; rfl
  · rw [if_neg same]
    unfold initialSource
    dsimp only
    rw [Source.World.set_other _ same]
    rfl

theorem locate (address : Roadmap.Address) (code : Nat)
    (installed : (initialSource.ex.world.accounts address).code = some code) :
    address = receiver ∧ code = 0 := by
  rw [source_code] at installed
  by_cases same : address = receiver
  · rw [if_pos same] at installed
    exact ⟨same,(Option.some.inj installed).symm⟩
  · rw [if_neg same] at installed
    cases installed

def inputs : WorldCatalogue.Inputs global kindOf relation initialSource where
  installed address code installed := by
    obtain ⟨same,zero⟩ := locate address code installed
    subst address;subst code
    exact ⟨"C",(),Storage.init _,rfl,rfl,rfl,rfl,rfl⟩
  roles := fun _ => .contractCode
  library_role name kind _ := by cases kind; rfl

def session : Roadmap.SessionEnv where
  deployer := receiver
  deployNonce := ⟨0,by decide⟩
  deployValue := Source.SemanticsExamples.word 0
  deployArgs := []
  balance := fun _ => Source.SemanticsExamples.word 0
  hasCode := fun _ _ => false
  requests := fun _ _ => none
  callee := global.callee

def target : ContractWorld.World catalogue := WorldCatalogue.assemble inputs session []
  (EnvironmentProjection.liftWord global.timestamp)

theorem image : WorldImage.Image global kindOf relation session [] initialSource target :=
  WorldCatalogue.assembled_image inputs session [] _

theorem time_aligned : WorldImage.TimeAligned global target := rfl

theorem installed_account :
    target.accounts (EnvironmentProjection.liftAddress receiver) =
      some ⟨(),Storage.init (catalogue ())⟩ := by
  have account := image.accounts (EnvironmentProjection.liftAddress receiver)
  unfold WorldImage.AccountImage at account
  dsimp only at account
  rw [EnvironmentProjection.lower_lift_address] at account
  obtain ⟨name,kind,store,selected,linked,installed,represented⟩ := account
  cases kind
  rw [represented.2.2] at installed
  exact installed

theorem storage_lookup :
    target.storage? (⟨EnvironmentProjection.liftAddress receiver⟩ : ContractWorld.Handle ()) =
      some (Storage.init (catalogue ())) := by
  simp only [ContractWorld.World.storage?,installed_account,bind,Option.bind]
  rfl

theorem funds_at_receiver :
    target.funds (EnvironmentProjection.liftAddress receiver) =
      EnvironmentProjection.liftWord (Source.SemanticsExamples.word 0) := rfl

theorem caller_storage (journal : List Evm.CallRec) (buffer : List UInt8) :
    (Backend.InternalFlow.RuntimeFrame.P1V2FramedRevertControls.input journal buffer).caller.storage =
      Storage.init (catalogue ()) := rfl

/-- The SAME image holds at the actual Source call result, whose state is retained. -/
theorem reached_image : ∃ final,
    (Source.callAddr global sourceFrame 12 receiver (Source.SemanticsExamples.word 0) selector true).run
      (Source.L0 environment,initialSource) = (.ok (.success []),(Source.L0 environment,final)) ∧
    WorldImage.Image global kindOf relation session [] final target ∧
    WorldImage.TimeAligned global target := ⟨initialSource,source_call,image,time_aligned⟩

theorem wrong_name : kindOf "Other" = none := rfl

theorem missing_account_refused :
    ¬ WorldImage.Image global kindOf relation session [] initialSource
      {target with accounts := fun _ => none} := by
  intro falseImage
  have account := falseImage.accounts (EnvironmentProjection.liftAddress receiver)
  unfold WorldImage.AccountImage at account
  dsimp only at account
  rw [EnvironmentProjection.lower_lift_address] at account
  obtain ⟨name,kind,store,selected,linked,absent,represented⟩ := account
  cases absent

theorem wrong_funds_refused :
    ¬ WorldImage.Image global kindOf relation session [] initialSource
      {target with funds := fun _ => EnvironmentProjection.liftWord (Source.SemanticsExamples.word 1)} := by
  intro falseImage
  have funds := congrFun falseImage.funds (EnvironmentProjection.liftAddress receiver)
  have unequal : EnvironmentProjection.liftWord (Source.SemanticsExamples.word 1) ≠
      EnvironmentProjection.liftWord (Source.SemanticsExamples.word 0) := by decide
  exact unequal funds

end Solidity.H62.ReadonlyCalls.SourceVoidWorld
