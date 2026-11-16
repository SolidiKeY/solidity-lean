import Solidity.Hash.CollisionBridgeCompiler
import Solidity.Roadmap.Controls

/-! # Inhabited compiler instance of the empty hash-premise bridge

The existing toy compiler has a proved PublicCorrectness instance and a
quiet program returning nonempty bytes without querying the hash. This is
a semantic compiler execution, not merely an inhabited premise.
-/

namespace Solidity.Hash.CollisionBridge.Compiler.Controls

open Solidity.Roadmap Solidity.Roadmap.Controls

/-- A compiled quiet program has an admissible source prefix above its
whole target prefix, using HashPremise.nil to discharge the actual guard. -/
theorem quiet_compiler_prefix :
    PrefixRefines toySource toyEvm (.quiet [1]) (artOf [3, 1]) quietEnv quietEnv
      (⟨0, fun _ => 0⟩ : EvmBound) := by
  exact prefix_empty toy_publicCorrectness
    (i := ({ text := [3, 1] } : ToyInput))
    (r := (⟨.quiet [1], .legacy, .v2⟩ : ToyRes))
    ((admitted_iff _ _).mpr rfl) trivial trivial rfl quietEnv_allowed trivial rfl rfl

/-- The same execution actually succeeds with nonempty return bytes. -/
theorem quiet_success :
    (toyEvm.lang.sem (toyEvm.load (artOf [3, 1])) quietEnv
      (⟨0, fun _ => 0⟩ : EvmBound)).final = some (.success [1]) := rfl

/-- Its premise is the empty instance, with no unknown hash fact. -/
theorem quiet_premise :
    HashPremise toyEvm.fixed
      (toyEvm.hashed (toyEvm.load (artOf [3, 1])) quietEnv (⟨0, fun _ => 0⟩ : EvmBound))
      (toyEvm.slotHashed (toyEvm.load (artOf [3, 1])) quietEnv (⟨0, fun _ => 0⟩ : EvmBound)) :=
  HashPremise.nil _

end Solidity.Hash.CollisionBridge.Compiler.Controls
