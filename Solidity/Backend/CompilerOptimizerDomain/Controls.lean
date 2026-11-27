import Solidity.Backend.CompilerOptimizerDomain.StmtFold
import Solidity.Backend.CompilerOptimizerDomain.DeadCode
import Solidity.Backend.CompilerOptimizerDomain.DeadStore
import Solidity.Backend.CompilerOptimizerDomain.LICM
import Solidity.Backend.CompilerOptimizerDomain.Simplify
import Solidity.Backend.CompilerOptimizerDomain.Weakening
import Solidity.Backend.CompilerOptimizerDomain.Inline
import Solidity.Backend.CompilerOptimizerDomain.CSE
import Solidity.Backend.CompilerOptimizerDomain.Propagate
import Solidity.Backend.CompilerOptimizerDomain.Strengthening

/-! Integration controls for the proved folding, simplification, removal, LICM,
weakening/strengthening, inlining, CSE and constant-propagation results. These check both
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

example {p : PrimTy} {l : OpLoc C Γ p} (w : Thin Γ Δ) (h : OpLocOk l) : OpLocOk (l.wk w) := opLoc_wk_ok w h

-- Every accepted program can move into an arbitrary larger context.
example {Θ : Ctx} (hP : ProgOk [] P) (w : Thin Γ Θ) :
    Evm.Prog.pushes (P.wk w).2.2 = 0 ∧
      ∃ G, inFragP (Frag.init Θ) (P.wk w).2.2 = some G := by
  have hQ := prog_wk_ok hP w (KindsWk.empty w)
  obtain ⟨G, h, _⟩ := hQ.frag (Frag.init Θ) (Matches.init Θ)
  exact ⟨hQ.quiet.1, G, h⟩

-- The actual inlining pass accepts the unchanged whole public domain.
example (hP : ProgOk [] P) :
    Evm.Prog.pushes (Optimizer.ConstFold.Prog.inl P) = 0 ∧
      ∃ G, inFragP (Frag.init Γ) (Optimizer.ConstFold.Prog.inl P) = some G := by
  have hQ := prog_inl_ok hP
  obtain ⟨G, h, _⟩ := hQ.frag (Frag.init Γ) (Matches.init Γ)
  exact ⟨hQ.quiet.1, G, h⟩

-- CSE preserves the domain even for an arbitrary availability table.
example (hP : ProgOk [] P) (A : List (Optimizer.ConstFold.Avail C Γ)) :
    Evm.Prog.pushes (Optimizer.ConstFold.Prog.cse A P) = 0 ∧
      ∃ G, inFragP (Frag.init Γ) (Optimizer.ConstFold.Prog.cse A P) = some G := by
  have hQ := prog_cse_ok hP A
  obtain ⟨G, h, _⟩ := hQ.frag (Frag.init Γ) (Matches.init Γ)
  exact ⟨hQ.quiet.1, G, h⟩

-- The actual initial facts table needs no new premise on accepted programs.
example (hP : ProgOk [] P) :
    Evm.Prog.pushes (Optimizer.ConstFold.Prog.cprop Optimizer.ConstFold.Facts.empty P) = 0 ∧
      ∃ G, inFragP (Frag.init Γ) (Optimizer.ConstFold.Prog.cprop Optimizer.ConstFold.Facts.empty P) = some G := by
  have hQ := prog_cprop_ok hP facts_empty_ok
  obtain ⟨G, h, _⟩ := hQ.frag (Frag.init Γ) (Matches.init Γ)
  exact ⟨hQ.quiet.1, G, h⟩

-- Successful strengthening carries the original input acceptance proof.
example {Θ : Ctx} (hP : ProgOk [] P) (w : Thin Θ Γ)
    {Q : Optimizer.ConstFold.Str C Θ Δ} (he : Optimizer.ConstFold.Prog.str? w P = some Q) :
    Evm.Prog.pushes Q.2.2 = 0 ∧ ∃ G, inFragP (Frag.init Θ) Q.2.2 = some G := by
  have hQ := prog_str_ok hP w he []
  obtain ⟨G, h, _⟩ := hQ.frag (Frag.init Θ) (Matches.init Θ)
  exact ⟨hQ.quiet.1, G, h⟩

end Solidity.Backend.CompilerOptimizerDomain.Controls
