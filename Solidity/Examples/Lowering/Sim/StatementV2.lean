import Solidity.Correctness.Lowering.Sim.Match.CompositionV2

/-! # The statement-level contract, v2: its laws suffice for the per-run obligation

Checks of the contract's shape only (ls3v-p1-statement-v2): every law is a
hypothesis here, none is proved. -/
namespace Solidity.Examples.Lowering.Sim.StatementV2

open Solidity.Goals.Shrink.Lowering
open Solidity.Lowering.V07 (ContextMap)
open Solidity.Correctness.Lowering.Sim
open Solidity.Correctness.Lowering.Sim.StatementV2
open Solidity.Correctness.Lowering.Sim.CompositionV2

variable [FreshNames]

/-- **End to end**: the assembled induction, the step, the block law with
splitting readings and the site law at a covering interpretation give the v2
per-run obligation at every associated production run of the fragment. -/
example (C : Contract) (I : Interp) (induction : AssembledInduction C) (step : KnotStep C I)
    (block : BlockLaw C I) (splits : I.Splits C (elabStmtP C)) (site : SiteLaw C I)
    (fuel : I.fuel = diagram.fuel) (covers : I.Covers C) (b : Body) (Γ : Ctx)
    (o : Solidity.Correctness.Lowering.Checker.Output C Γ) (m : ContextMap b.ctx Γ) (production : Production b ⟨C, Γ, o⟩)
    (accepted : Accepted ⟨C, Γ, o⟩) (assoc : diagram.Assoc b ⟨C, Γ, o⟩ m) :
    RunSim₂ b ⟨C, Γ, o⟩ m :=
  runs₂_of_segments C I (site fuel covers)
    (knot_blocks C I block splits (knot_genSeg C I induction step)) b Γ o m production accepted
    assoc

/-- The statement conclusions of `CasesV2` at the knot's record, from its
arms and block step. -/
example (C : Contract) (I : Interp) (sites : Sites C I) (single : SingletonLaw C I)
    (armP : Solidity.Goals.ElabSat (stmtQ C I) (elabStmtPWith C (elabRec C ())))
    (arm1 : Solidity.Goals.ElabSat (stmtQ C I) (elabStmt1With C (elabRec C ())))
    (block : Solidity.Goals.ElabSat (blockQ C I) (Solidity.Goals.elabStmtsStep C (elabRec C ()))) :
    CasesV2.StmtCases C (elabRec C ()) :=
  (stmtCases_of_segments C I sites single _ armP arm1 block).1

/-- The knot's `hoistTop`, which v1 `RecSim` leaves free, is the derived form
of its `hoist`. -/
example (C : Contract) : (elabRec C ()).hoistTop = hoistTopWith C (hoist C) :=
  (assembled_fields C (hoist C) (elabStmtP C) _).2.2.1

/-- The body's Source run is the statement-level Source computation of its
resolved statement. -/
example (b : Body) (G : Source.Glob b.E) (F : Source.Fr) (n nps : Nat)
    (ph : Option (Source.Ph b.E)) (src : Source.EMState b.E b.ctx) :
    sourceRun b G F n nps ph src = SrcRun.ofStmt b.input.resolved G F n nps ph src :=
  sourceRun_eq b G F n nps ph src

end Solidity.Examples.Lowering.Sim.StatementV2
