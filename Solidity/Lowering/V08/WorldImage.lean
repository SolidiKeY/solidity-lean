import Solidity.Lowering.V08.LibraryPremises
import Solidity.Lowering.V08.SourceTransient

/-! Proof-side account/session image, not a state layer or interpreter.
It covers tracked code identities, typed store relation, supplied session funds
and code roles only. It does not assert complete nonce/heap/event/log/admission
or SourceSpec/compiler correspondence. ResetInputs is an UNPROVED per-store
P7/layout duty. Relative reset transport is proved in WorldReset. -/
namespace Solidity.Lowering.V08.WorldImage
open Solidity

abbrev StoreRelation (E : Source.Env) {K : Type} (contracts : K → Contract) : Type :=
  (address : Roadmap.Address) → (kind : K) →
    Source.Storage E.layout (E.lay address) →
    Source.Storage E.layout (E.lay address) → Storage (contracts kind) → Prop

def sourceLibrary (E : Source.Env) (name : String) : Bool :=
  E.decls.any (fun declaration => decide (declaration.kind = .library) && decide (declaration.name = name))

def AccountImage {E : Source.Env} {K : Type} {contracts : K → Contract}
    (g : Source.Glob E) (kindOf : String → Option K) (relation : StoreRelation E contracts)
    (source : Source.St E) (target : ContractWorld.World contracts)
    (address : ContractWorld.Address) : Prop :=
  let a := EnvironmentProjection.lowerAddress address
  match (source.ex.world.accounts a).code with
  | none => target.accounts address = none
  | some code => ∃ (name : String) (kind : K) (store : Storage (contracts kind)),
      g.contractAt code = some name ∧ kindOf name = some kind ∧
      target.accounts address = some ⟨kind,store⟩ ∧
      relation a kind (source.ex.world.accounts a).storage (source.ex.transient.cells a) store

structure Image {E : Source.Env} {K : Type} {contracts : K → Contract}
    (g : Source.Glob E) (kindOf : String → Option K) (relation : StoreRelation E contracts)
    (environment : Roadmap.SessionEnv) (history : List Roadmap.Event)
    (source : Source.St E) (target : ContractWorld.World contracts) : Prop where
  accounts : ∀ address, AccountImage g kindOf relation source target address
  funds : target.funds = EnvironmentProjection.sessionFunds source.ex.world g.fixed environment history
  roles : ∀ name kind, kindOf name = some kind → target.isLibrary kind = sourceLibrary E name

structure ResetInputs {E : Source.Env} {K : Type} {contracts : K → Contract}
    (relation : StoreRelation E contracts) : Prop where
  slots : ∀ (address : Roadmap.Address) (kind : K)
      (persistent temporary : Source.Storage E.layout (E.lay address)) (store : Storage (contracts kind)),
    relation address kind persistent temporary store →
    relation address kind persistent Source.Storage.empty (Storage.resetTransient store)

end Solidity.Lowering.V08.WorldImage
