import Solidity.Lowering.V08.WorldCatalogueTransport

/-! Typed installed-store lookup from the actual image and independent source
code/name/kind equations. No name-map injectivity, runtime producer or desired
execution-preservation equation is assumed. -/
namespace Solidity.Lowering.V08.WorldImageAccess
open Solidity
variable {E : Source.Env} {K : Type} {contracts : K → Contract}
  {g : Source.Glob E} {kindOf : String → Option K}
  {relation : WorldImage.StoreRelation E contracts}
  {environment : Roadmap.SessionEnv} {history : List Roadmap.Event}
  {source : Source.St E} {target : ContractWorld.World contracts}

theorem installed_store
    (image : WorldImage.Image g kindOf relation environment history source target)
    (address : Roadmap.Address) (code : Nat) (name : String) (kind : K)
    (atCode : (source.ex.world.accounts address).code = some code)
    (selected : g.contractAt code = some name) (linked : kindOf name = some kind) :
    ∃ store : Storage (contracts kind),
      target.accounts (EnvironmentProjection.liftAddress address) = some ⟨kind,store⟩ ∧
      relation address kind (source.ex.world.accounts address).storage
        (source.ex.transient.cells address) store := by
  have account := image.accounts (EnvironmentProjection.liftAddress address)
  unfold WorldImage.AccountImage at account
  dsimp only at account
  rw [EnvironmentProjection.lower_lift_address, atCode] at account
  obtain ⟨otherName, otherKind, store, otherSelected, otherLinked, installed, represented⟩ := account
  have sameName : otherName = name := Option.some.inj (otherSelected.symm.trans selected)
  subst otherName
  have sameKind : otherKind = kind := Option.some.inj (otherLinked.symm.trans linked)
  subst otherKind
  exact ⟨store, installed, represented⟩

/-- info: 'Solidity.Lowering.V08.WorldImageAccess.installed_store' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms installed_store
end Solidity.Lowering.V08.WorldImageAccess
