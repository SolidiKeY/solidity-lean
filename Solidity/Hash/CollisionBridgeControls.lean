import Solidity.Hash.CollisionBridgeCompiler
import Solidity.Roadmap.Controls

namespace Solidity.Hash.CollisionBridge.Compiler.Controls

open Solidity.Roadmap Solidity.Roadmap.Controls

theorem quiet_compiler_prefix :
    PrefixRefines toySource toyEvm (.quiet [1]) (artOf [3, 1]) quietEnv quietEnv
      (⟨0, fun _ => 0⟩ : EvmBound) := by
  exact prefix_empty toy_publicCorrectness
    (i := ({ text := [3, 1] } : ToyInput))
    (r := (⟨.quiet [1], .legacy, .v2⟩ : ToyRes))
    ((admitted_iff _ _).mpr rfl) trivial trivial rfl quietEnv_allowed trivial rfl rfl

theorem quiet_success :
    (toyEvm.lang.sem (toyEvm.load (artOf [3, 1])) quietEnv
      (⟨0, fun _ => 0⟩ : EvmBound)).final = some (.success [1]) := rfl

theorem quiet_premise :
    HashPremise toyEvm.fixed
      (toyEvm.hashed (toyEvm.load (artOf [3, 1])) quietEnv (⟨0, fun _ => 0⟩ : EvmBound))
      (toyEvm.slotHashed (toyEvm.load (artOf [3, 1])) quietEnv (⟨0, fun _ => 0⟩ : EvmBound)) :=
  HashPremise.nil _

end Solidity.Hash.CollisionBridge.Compiler.Controls
