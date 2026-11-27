import Solidity.Backend.CompilerOptimizerDomain.StmtFold
import Solidity.Backend.CompilerOptimizerDomain.DeadCode
import Solidity.Backend.CompilerOptimizerDomain.DeadStore
import Solidity.Backend.CompilerOptimizerDomain.LICM
import Solidity.Backend.CompilerOptimizerDomain.Simplify
import Solidity.Backend.CompilerOptimizerDomain.Weakening

/-! Integration controls for the proved constant-fold, simplification, removal and LICM stages only. These check both
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

-- LICM must preserve both compiler-domain consequences, including hoisted loops.
example (hP : ProgOk [] P) :
    Evm.Prog.pushes (Optimizer.ConstFold.Prog.licm P) = 0 ∧
      ∃ G, inFragP (Frag.init Γ) (Optimizer.ConstFold.Prog.licm P) = some G := by
  have hQ := prog_licm_ok hP
  obtain ⟨G, h, _⟩ := hQ.frag (Frag.init Γ) (Matches.init Γ)
  exact ⟨hQ.quiet.1, G, h⟩

-- The actual simplify pass includes simplification followed by constant folding.
example (hP : ProgOk [] P) :
    Evm.Prog.pushes P.simplify = 0 ∧
      ∃ G, inFragP (Frag.init Γ) P.simplify = some G := by
  have hQ := prog_simplify_ok hP
  obtain ⟨G, h, _⟩ := hQ.frag (Frag.init Γ) (Matches.init Γ)
  exact ⟨hQ.quiet.1, G, h⟩

-- Expression-domain weakening accepts every extension of the original context.
example {p : PrimTy} {v : Val C Γ p} (w : Thin Γ Δ) (hv : ValOk v) :
    ValOk (v.wk w) := val_wk_ok w hv

example {ps : Ctx} {as : Args C Γ ps} (w : Thin Γ Δ) (ha : ArgsOk as) :
    ArgsOk (as.wk w) := args_wk_ok w ha

end Solidity.Backend.CompilerOptimizerDomain.Controls
