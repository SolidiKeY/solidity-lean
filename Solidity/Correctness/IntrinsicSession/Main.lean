import Solidity.Goals.IntrinsicSession
import Solidity.Correctness.IntrinsicSession.Laws.Structure
import Solidity.Correctness.IntrinsicSession.Laws.Boundary
import Solidity.Correctness.IntrinsicSession.Laws.Frames

/-!
# The intrinsic session semantics: assembly

The goal `Solidity.Goals.intrinsicSessionSemantics` (plan step
`is0-intrinsic-session`, H556 option A): for every fixed parameters `F`, the
concrete `spec F` read through `view F` satisfies every law of
`Solidity.Goals.IntrinsicSession.Laws`. Each field is the theorem of the same
name in `Laws/Structure.lean`, `Laws/Boundary.lean` or `Laws/Frames.lean`;
nothing is proved here. The module is under `Solidity/Correctness` because it
imports a Goals module, which the layers gate forbids for core modules.
-/

namespace Solidity.Semantics.IntrinsicSession

/-- **The concrete intrinsic session semantics satisfies its laws.** -/
theorem session_semantics_correct : Solidity.Goals.intrinsicSessionSemantics := fun F =>
  ⟨spec F, view F,
    { fixed := Laws.fixed F
      precompiles := Laws.precompiles F
      this := Laws.this F
      directed := Laws.directed F
      worlds_consistent := Laws.worlds_consistent F
      hashed_consistent := Laws.hashed_consistent F
      slotHashed_sub := Laws.slotHashed_sub F
      final_last := Laws.final_last F
      answered := Laws.answered F
      typed_resume := Laws.typed_resume F
      initial_code := Laws.initial_code F
      worlds_code := Laws.worlds_code F
      listed_resumes := Laws.listed_resumes F
      stored_hashed := Laws.stored_hashed F
      starts := Laws.starts F
      boundary_observed := Laws.boundary_observed F
      boundary_code := Laws.boundary_code F
      listed_boundary := Laws.listed_boundary F
      idle := Laws.idle F
      dropped := Laws.dropped F
      credited := Laws.credited F
      transacts := Laws.transacts F
      resumes := Laws.resumes F
      deploys := Laws.deploys F }⟩

end Solidity.Semantics.IntrinsicSession
