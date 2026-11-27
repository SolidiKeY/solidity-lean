import Solidity.Backend.CompilerOptimizerDomain.StmtFold
import Solidity.Backend.CompilerOptimizerDomain.DeadCode
import Solidity.Backend.CompilerOptimizerDomain.DeadStore

/-! Integration controls for the proved constant-fold and removal stages only. These check both
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

-- Compose the proved stages and check both required consequences together.
-- This deliberately makes no claim about the unproved intervening passes.
example (hP : ProgOk [] P) :
    let Q := Optimizer.ConstFold.Prog.dstore
      (Optimizer.ConstFold.Prog.dse (Optimizer.ConstFold.Prog.dce P.cfold))
    Evm.Prog.pushes Q = 0 ∧ ∃ G, inFragP (Frag.init Γ) Q = some G := by
  dsimp only
  have hQ := prog_dstore_ok (prog_dse_ok (prog_dce_ok (prog_cfold_ok hP)))
  obtain ⟨G, h, _⟩ := hQ.frag (Frag.init Γ) (Matches.init Γ)
  exact ⟨hQ.quiet.1, G, h⟩

end Solidity.Backend.CompilerOptimizerDomain.Controls
