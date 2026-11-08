import SourceVoidWorld
import Solidity.Lowering.V08.CallableBodyPremises

/-! Guard an installed account or body label being mistaken for an executed
callable. The image-backed handle runs the existing paid entry, nil body,
settlement and decoder. Existing body-phase Inputs are jointly supplied with
actual Source phases and exact singleton state/value pairs. These are closed
empty-contract controls, NOT general Source lowering/state simulation, native
code provenance, child commit, approved admission or full H121/G42.02. -/
namespace Solidity.H62.ReadonlyCalls.SourceVoidCallable
open Solidity Solidity.Lowering.V08
open Solidity.H62.ReadonlyCalls.SourceVoidSelection
open Solidity.H62.ReadonlyCalls.SourceVoidWorld

def owner : ContractWorld.Handle () := ⟨EnvironmentProjection.liftAddress receiver⟩
def context : ContractWorld.Context := {sender := owner.address,mode := .readOnly}
def entry : ContractWorld.Entry (catalogue ()) Unit := .unit .nil
def ready : State (catalogue ()) [] :=
  {storage := Storage.init _,H := [],heap := Heap.empty,env := (),net := [],
    selfBalance := EnvironmentProjection.liftWord (Source.SemanticsExamples.word 0),
    tx := context.tx target owner.address}

theorem entered : target.enter owner.address context (Storage.init (catalogue ())) false = .ok ready := rfl

theorem settled : target.finish owner.address ready = .ok target := by
  have accounts : (fun address => if address = owner.address then
      some (⟨(),Storage.init (catalogue ())⟩ : ContractWorld.Account catalogue)
      else target.accounts address) = target.accounts := by
    funext address
    by_cases same : address = owner.address
    · subst address
      exact (if_pos rfl).trans installed_account.symm
    · exact if_neg same
  have funds : (fun address => if address = owner.address then
      EnvironmentProjection.liftWord (Source.SemanticsExamples.word 0)
      else target.funds address) = target.funds := by
    funext address
    by_cases same : address = owner.address
    · subst address
      exact (if_pos rfl).trans funds_at_receiver.symm
    · exact if_neg same
  change (Except.ok {target with accounts := _,funds := _} : TRes (ContractWorld.World catalogue)) = Except.ok target
  dsimp only [ready]
  rw [accounts,funds]

theorem frame_run : target.callFrame owner entry context = .ok (target,ready) := by
  unfold ContractWorld.World.callFrame
  change (do
    let st ← TRes.ofOpt (target.storage? owner)
    let caller ← target.enter owner.address context st false
    let out ← (Prog.nil : Prog (catalogue ()) [] []).run caller
    let next ← target.finish owner.address out.st
    pure (next,out.st)) = .ok (target,ready)
  have lookup : target.storage? owner = some (Storage.init (catalogue ())) := storage_lookup
  rw [lookup]
  change (do
    let caller ← target.enter owner.address context (Storage.init (catalogue ())) false
    let out ← (Prog.nil : Prog (catalogue ()) [] []).run caller
    let next ← target.finish owner.address out.st
    pure (next,out.st)) = .ok (target,ready)
  rw [entered]
  change (do let next ← target.finish owner.address ready; pure (next,ready)) = .ok (target,ready)
  rw [settled]
  rfl

theorem call_run : target.call owner entry context = .ok (target,()) := by
  unfold ContractWorld.World.call
  rw [frame_run]
  rfl

/-- Exact complete states for this fixture, not a generic simulation relation. -/
def statePair (Δ : Ctx) (source : Source.St environment) (typed : State (catalogue ()) Δ) : Prop :=
  source = initialSource ∧ HEq typed ready

def resultPair (source : Source.RVal environment.layout (Source.STy.ret [])) (typed : Unit) : Prop :=
  source = Source.mkRet [] (.nil : Source.RVals environment.layout []) ∧ typed = ()

def phases : CallableBodyPremises.Inputs global sourceFrame 8 declaration
    (.nil : Source.Vals environment.layout []) functionBody entry ready
    initialSource initialSource initialSource statePair resultPair where
  selected := resolved_body
  zero := .nil
  fits := rfl
  returned := Source.L0 environment
  outputs := .nil
  initialization := rfl
  sourceBody := rfl
  extraction := rfl
  targetOut := ⟨ready,List.prefix_refl _⟩
  targetBody := rfl
  bodyRelated := ⟨rfl,HEq.rfl⟩
  value := ()
  targetResult := rfl
  resultRelated := ⟨rfl,rfl⟩

theorem source_internal :
    (Source.callInternal global sourceFrame 9 declaration
      (.nil : Source.Vals environment.layout []) []).run (Source.L0 environment,initialSource) =
    (.ok (Source.mkRet [] (.nil : Source.RVals environment.layout [])),
      (Source.L0 environment,initialSource)) :=
  (CallableBodyPremises.complete phases).1

theorem phase_complete :
    (Source.callInternal global sourceFrame 9 declaration
      (.nil : Source.Vals environment.layout []) []).run (Source.L0 environment,initialSource) =
      (.ok (Source.mkRet [] (.nil : Source.RVals environment.layout [])),
        (Source.L0 environment,initialSource)) ∧
    (do let out ← entry.body.run ready;let value ← entry.result out.st;pure (out,value)) =
      (.ok (⟨ready,List.prefix_refl _⟩,()) : TRes (Out (catalogue ()) ready.H [] × Unit)) ∧
    statePair [] initialSource ready ∧
    resultPair (Source.mkRet [] (.nil : Source.RVals environment.layout [])) () :=
  CallableBodyPremises.complete phases

theorem context_fields :
    EnvironmentProjection.lowerAddress context.sender = sourceFrame.sender ∧
    EnvironmentProjection.lowerAddress owner.address = sourceFrame.this ∧
    EnvironmentProjection.lowerWord context.value = sourceFrame.value ∧
    context.isStatic = sourceFrame.static := ⟨rfl,rfl,rfl,rfl⟩

theorem source_and_typed :
    (Source.callAddr global sourceFrame 12 receiver (Source.SemanticsExamples.word 0) selector true).run
      (Source.L0 environment,initialSource) = (.ok (.success []),(Source.L0 environment,initialSource)) ∧
    target.call owner entry context = .ok (target,()) := ⟨source_call,call_run⟩

theorem missing_account_refused :
    ({target with accounts := fun _ => none} : ContractWorld.World catalogue).call owner entry context =
      .error .revert := rfl

def badDecoder : ContractWorld.Entry (catalogue ()) Unit := {entry with result := fun _ => .error .revert}

theorem decoder_frame : target.callFrame owner badDecoder context = .ok (target,ready) := frame_run

/-- The body succeeds, but the caller-side decoder can still fail. This proves
no rollback law: the nil frame changes no world in this fixture. -/
theorem decoder_failed : target.call owner badDecoder context = .error .revert := by
  unfold ContractWorld.World.call
  rw [decoder_frame]
  rfl

end Solidity.H62.ReadonlyCalls.SourceVoidCallable
