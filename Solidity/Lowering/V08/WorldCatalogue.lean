import Solidity.Lowering.V08.WorldReset

/-! Generated typed initial-world assembly over existing Source.St and ContractWorld.World.
Installed-store/code coverage and library-role linkage are explicit producer duties.
No SourceSpec admission, execution, bytecode or new state/interpreter is supplied. -/
namespace Solidity.Lowering.V08.WorldCatalogue
open Solidity

structure InstalledStore {E : Source.Env} {K : Type} {contracts : K → Contract}
    (g : Source.Glob E) (kindOf : String → Option K) (relation : WorldImage.StoreRelation E contracts)
    (source : Source.St E) (address : Roadmap.Address) (code : Nat) where
  name : String
  kind : K
  store : Storage (contracts kind)
  selected : g.contractAt code = some name
  linked : kindOf name = some kind
  represented : relation address kind (source.ex.world.accounts address).storage
    (source.ex.transient.cells address) store

structure Inputs {E : Source.Env} {K : Type} {contracts : K → Contract}
    (g : Source.Glob E) (kindOf : String → Option K) (relation : WorldImage.StoreRelation E contracts)
    (source : Source.St E) where
  installed : (address : Roadmap.Address) → (code : Nat) →
    (source.ex.world.accounts address).code = some code →
    InstalledStore g kindOf relation source address code
  roles : K → ContractWorld.Role
  library_role : ∀ name kind, kindOf name = some kind →
    (match roles kind with | .contractCode => false | .libraryCode => true) =
      WorldImage.sourceLibrary E name

def assemble {E : Source.Env} {K : Type} {contracts : K → Contract}
    {g : Source.Glob E} {kindOf : String → Option K} {relation : WorldImage.StoreRelation E contracts}
    {source : Source.St E} (inputs : Inputs g kindOf relation source)
    (environment : Roadmap.SessionEnv) (history : List Roadmap.Event)
    (timestamp : Semantics.Word) : ContractWorld.World contracts :=
  { accounts := fun address =>
      let a := EnvironmentProjection.lowerAddress address
      match code : (source.ex.world.accounts a).code with
      | none => none
      | some index => let entry := inputs.installed a index code
                      some ⟨entry.kind, entry.store⟩
    funds := EnvironmentProjection.sessionFunds source.ex.world g.fixed environment history
    roles := inputs.roles
    timestamp }

end Solidity.Lowering.V08.WorldCatalogue
