import Solidity.Backend.CompilerOptimizerDomain.StmtFold

/-! Integration controls for the constant-fold stage only. These check both
resource and fragment consequences against the unchanged public compiler domain;
they do not assert preservation by the remaining optimizer stages or iteration. -/
namespace Solidity.Backend.CompilerOptimizerDomain.Controls
open Solidity Solidity.Evm
open Solidity.Backend.AbiWorld.PublicCompilerTotal
variable {C : Contract} {Γ Δ : Ctx} {P : Solidity.Prog C Γ Δ}

-- Push-freedom follows from the accepted domain after the actual statement pass.
example (hP : ProgOk [] P) : Evm.Prog.pushes P.cfold = 0 :=
  (prog_cfold_ok hP).quiet.1

-- Exercise fresh-frame matching and the existing fragment-success producer.
example (hP : ProgOk [] P) : ∃ G, inFragP (Frag.init Γ) P.cfold = some G := by
  obtain ⟨G, h, _⟩ := (prog_cfold_ok hP).frag (Frag.init Γ) (Matches.init Γ)
  exact ⟨G, h⟩

end Solidity.Backend.CompilerOptimizerDomain.Controls
