import Solidity.Optimizer.Pass
import Solidity.Roadmap.Contracts

/-!
# Composition adapter to the existing G49 certificate boundary

This adapter reuses Roadmap.Cert.comp unchanged. It does not manufacture the
optimizer certificate, compiler coverage, D6 relation or artifact linking proof.
-/
namespace Solidity.Optimizer
open Solidity.Roadmap

/-- Embed a total intrinsic optimizer in the existing compiler-pass interface. -/
def asRoadmapPass {E O : Type} (L : Lang E O) (pass : Optimizer.Pass L.Prog) :
    Roadmap.Pass L L where
  Dom _ := True
  run p _ := pass p
  envAbs e := e

/-- A certified optimizer followed by a certified compiler retains the original
resource, environment, hash-guard, forward and backward obligations. Compiler
coverage of optimizer outputs must be proved by its producer. -/
def beforeCompilation {E O : Type} {L T : Lang E O} (pass : Optimizer.Pass L.Prog)
    (optimizer : Roadmap.Cert (asRoadmapPass L pass))
    (compiler : Roadmap.Pass L T) (correct : Roadmap.Cert compiler)
    (coverage : ∀ p, compiler.Dom (pass p)) :
    Roadmap.Cert ((asRoadmapPass L pass).comp compiler (fun p _ => coverage p)) :=
  optimizer.comp correct (fun p _ => coverage p)

end Solidity.Optimizer
