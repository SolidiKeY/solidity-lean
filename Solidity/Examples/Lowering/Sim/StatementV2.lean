import Solidity.Correctness.Lowering.Sim.Match.CompositionV2

/-! # The statement-level contract, v2: shape checks

Every law and every obligation of the interpretation is a hypothesis here;
none is proved and no interpretation is exhibited (ls3v-p1-statement-v2). -/
namespace Solidity.Examples.Lowering.Sim.StatementV2

open Solidity.Goals.Shrink.Lowering
open Solidity.Lowering.V07 (ContextMap)
open Solidity.Correctness.Lowering.Sim
open Solidity.Correctness.Lowering.Sim.StatementV2
open Solidity.Correctness.Lowering.Sim.CompositionV2

variable [FreshNames]

/-- **End to end**: the induction, the step, the block and site laws at a
covering, splitting interpretation give the v2 per-run obligation. -/
example (C : Contract) (I : Interp) (induction : AssembledInduction C) (step : KnotStep C I)
    (block : BlockLaw C I) (splits : I.Splits C (elabStmtP C)) (site : SiteLaw C I)
    (fuel : I.fuel = diagram.fuel) (covers : I.Covers C) (b : Body) (Γ : Ctx)
    (o : Solidity.Correctness.Lowering.Checker.Output C Γ) (m : ContextMap b.ctx Γ) (production : Production b ⟨C, Γ, o⟩)
    (accepted : Accepted ⟨C, Γ, o⟩) (assoc : diagram.Assoc b ⟨C, Γ, o⟩ m) :
    RunSim₂ b ⟨C, Γ, o⟩ m :=
  runs₂_of_segments C I (site fuel covers)
    (block _ splits (knot_genSeg C I induction step).2.1) b Γ o m production accepted
    assoc

end Solidity.Examples.Lowering.Sim.StatementV2
