import Solidity.Lowering.V08.WorldCatalogueTransport
import Solidity.Lowering.V08.WorldResetControls

/-! Inhabited complete Image and reset Image over the existing populated source
fixture. The supplied toy ledger ignores history: external sender balance100
differs from its raw account93; installed owner uses7. This is not the approved
ledger/admission/compiler theorem. Source probes retain full locals/machines. -/
namespace Solidity.Lowering.V08.WorldCatalogueControls
open Solidity
theorem source_code (address : Roadmap.Address) :
    (SourceEnvironmentControls.populated.ex.world.accounts address).code =
      if address = SourceEnvironmentControls.self then some 0 else none := by
  by_cases same : address = SourceEnvironmentControls.self
  · subst address; rfl
  · by_cases sender : address = SourceEnvironmentControls.sender
    · subst address; rfl
    · simp only [SourceEnvironmentControls.populated, SourceEnvironmentControls.empty,
        Source.ExecState.run, Source.ExecState.apply, Source.World.set, Source.Account.empty,
        same, sender, dite_false, ite_false]

theorem locate {address : Roadmap.Address} {code : Nat}
    (installed : (SourceEnvironmentControls.populated.ex.world.accounts address).code = some code) :
    address = SourceEnvironmentControls.self ∧ code = 0 := by
  rw [source_code] at installed
  by_cases same : address = SourceEnvironmentControls.self
  · rw [if_pos same] at installed
    exact ⟨same, (Option.some.inj installed).symm⟩
  · rw [if_neg same] at installed
    cases installed

open WorldResetControls in
def inputs (pipeline : Roadmap.Pipeline) :
    WorldCatalogue.Inputs (SourceEnvironmentControls.global pipeline) kindOf relation SourceEnvironmentControls.populated where
  installed address code atCode :=
    { name := "C", kind := (), store := store true true
      selected := by rw [(locate atCode).2]; rfl
      linked := rfl
      represented := by
        have atSelf := (locate atCode).1
        subst address
        exact ⟨true, true, rfl, rfl, rfl⟩ }
  roles := fun _ => .contractCode
  library_role _ _ _ := rfl

def environment : Roadmap.SessionEnv :=
  { deployer := SourceEnvironmentControls.sender
    deployNonce := ⟨0, by decide⟩, deployValue := ⟨0, by decide⟩, deployArgs := []
    balance := (SourceEnvironmentControls.global .legacy).balance0
    hasCode := (SourceEnvironmentControls.global .legacy).hasCode
    requests := fun _ _ => none
    callee := (SourceEnvironmentControls.global .legacy).callee }

def world (pipeline : Roadmap.Pipeline) : ContractWorld.World WorldResetControls.catalog :=
  WorldCatalogue.assemble (inputs pipeline) environment SourceEnvironmentControls.populated.events
    (EnvironmentProjection.liftWord (SourceEnvironmentControls.global pipeline).timestamp)

def initial_image (pipeline : Roadmap.Pipeline) :
    WorldImage.Image (SourceEnvironmentControls.global pipeline) WorldResetControls.kindOf
      WorldResetControls.relation environment SourceEnvironmentControls.populated.events
      SourceEnvironmentControls.populated (world pipeline) :=
  WorldCatalogue.assembled_image (inputs pipeline) environment SourceEnvironmentControls.populated.events _

def reset_image (pipeline : Roadmap.Pipeline) :
    WorldImage.Image (SourceEnvironmentControls.global pipeline) WorldResetControls.kindOf
      WorldResetControls.relation environment SourceEnvironmentControls.populated.events
      (SourceTransient.endExecution SourceEnvironmentControls.populated) (world pipeline).resetTransient :=
  WorldImage.image_reset WorldResetControls.slots (initial_image pipeline)

theorem ordered_world (pipeline : Roadmap.Pipeline) :
    ((world pipeline).accounts (EnvironmentProjection.liftAddress SourceEnvironmentControls.self),
      (world pipeline).accounts (EnvironmentProjection.liftAddress SourceEnvironmentControls.sender),
      ((world pipeline).balance (EnvironmentProjection.liftAddress SourceEnvironmentControls.sender)).1,
      ((world pipeline).balance (EnvironmentProjection.liftAddress SourceEnvironmentControls.self)).1,
      (world pipeline).timestamp.1) =
    (some ⟨(), WorldResetControls.store true true⟩, none, 100, 7, 12345) := by
  rfl

theorem ordered_reset (pipeline : Roadmap.Pipeline) :
    ((world pipeline).resetTransient.accounts (EnvironmentProjection.liftAddress SourceEnvironmentControls.self),
      (world pipeline).resetTransient.accounts (EnvironmentProjection.liftAddress SourceEnvironmentControls.sender),
      ((world pipeline).resetTransient.balance (EnvironmentProjection.liftAddress SourceEnvironmentControls.sender)).1,
      ((world pipeline).resetTransient.balance (EnvironmentProjection.liftAddress SourceEnvironmentControls.self)).1,
      (world pipeline).resetTransient.timestamp.1) =
    (some ⟨(), WorldResetControls.store true false⟩, none, 100, 7, 12345) := by
  rfl

theorem source_external_balance (pipeline : Roadmap.Pipeline) (static : Bool) :
    (Source.evalE (SourceEnvironmentControls.global pipeline) {SourceEnvironmentControls.frame with static := static} 3
      (.balance (.magic .msg "sender" rfl) : Source.RExpr SourceEnvironmentControls.E [.bool] (.int Source.IntTy.u256))).run
      (SourceEnvironmentControls.locals, SourceEnvironmentControls.populated) =
      (.ok (.val (Source.intWrap Source.IntTy.u256 100)),
        (SourceEnvironmentControls.locals, SourceEnvironmentControls.populated)) := by
  rfl

theorem source_installed_balance (pipeline : Roadmap.Pipeline) (static : Bool) :
    (Source.evalE (SourceEnvironmentControls.global pipeline) {SourceEnvironmentControls.frame with static := static} 3
      (.balance (.addressLit [⟨2, by decide⟩]) : Source.RExpr SourceEnvironmentControls.E [.bool] (.int Source.IntTy.u256))).run
      (SourceEnvironmentControls.locals, SourceEnvironmentControls.populated) =
      (.ok (.val (Source.intWrap Source.IntTy.u256 7)),
        (SourceEnvironmentControls.locals, SourceEnvironmentControls.populated)) := by
  rfl

theorem wrong_raw_funds (pipeline : Roadmap.Pipeline) :
    ((world pipeline).balance (EnvironmentProjection.liftAddress SourceEnvironmentControls.sender)).1 ≠
      (SourceEnvironmentControls.populated.ex.world.accounts SourceEnvironmentControls.sender).balance := by
  change (100 : Int) ≠ 93
  decide +kernel

theorem no_dropped_installation (pipeline : Roadmap.Pipeline) :
    ((world pipeline).accounts (EnvironmentProjection.liftAddress SourceEnvironmentControls.self)).isSome ≠ false := by
  change true ≠ false
  decide +kernel

theorem source_balance_timeout (pipeline : Roadmap.Pipeline) (static : Bool) :
    (Source.evalE (SourceEnvironmentControls.global pipeline) {SourceEnvironmentControls.frame with static := static} 0
      (.balance (.magic .msg "sender" rfl) : Source.RExpr SourceEnvironmentControls.E [.bool] (.int Source.IntTy.u256))).run
      (SourceEnvironmentControls.locals, SourceEnvironmentControls.populated) =
      (.error .timeout, (SourceEnvironmentControls.locals, SourceEnvironmentControls.populated)) := by
  rfl

/-- info: 'Solidity.Lowering.V08.WorldCatalogueControls.source_code' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms source_code
/-- info: 'Solidity.Lowering.V08.WorldCatalogueControls.locate' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms locate
/-- info: 'Solidity.Lowering.V08.WorldCatalogueControls.inputs' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms inputs
/-- info: 'Solidity.Lowering.V08.WorldCatalogueControls.initial_image' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms initial_image
/-- info: 'Solidity.Lowering.V08.WorldCatalogueControls.reset_image' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms reset_image
/-- info: 'Solidity.Lowering.V08.WorldCatalogueControls.ordered_world' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms ordered_world
/-- info: 'Solidity.Lowering.V08.WorldCatalogueControls.ordered_reset' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms ordered_reset
/-- info: 'Solidity.Lowering.V08.WorldCatalogueControls.source_external_balance' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms source_external_balance
/-- info: 'Solidity.Lowering.V08.WorldCatalogueControls.source_installed_balance' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms source_installed_balance
/-- info: 'Solidity.Lowering.V08.WorldCatalogueControls.wrong_raw_funds' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms wrong_raw_funds
/-- info: 'Solidity.Lowering.V08.WorldCatalogueControls.no_dropped_installation' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms no_dropped_installation
/-- info: 'Solidity.Lowering.V08.WorldCatalogueControls.source_balance_timeout' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms source_balance_timeout
end Solidity.Lowering.V08.WorldCatalogueControls
