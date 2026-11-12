import Solidity.Goals.Total

/-! Accepted-fragment compiler totality (plan `t0-endpoint-total`): the public compiler
accepts every program of the intrinsic `ProgOk []` domain from its fresh frame through the
core branch, and that result passes the static refusal check for every array bound
`L ≤ Lmax` and every frame. This is acceptance only: the domain is the core fragment, not
all of Solidity, and nothing here says the compiled program terminates. -/

namespace Solidity.Backend

open Solidity.Backend.AbiWorld.PublicCompilerTotal

/-- The public compiler is total on `ProgOk []` and its result is not statically refused:
the core branch compiles, and a quiet program pushes nothing, so `L ≤ Lmax` suffices. -/
theorem compiler_total : Solidity.Goals.compilerTotal := by
  intro C Gamma Delta P hP b L frame hL
  obtain ⟨G, h, eq⟩ := compile_core b (Matches.init Gamma) hP
  refine ⟨.core G h, eq, ?_⟩
  simp only [Passes.WholeProgram.staticRefused, hP.quiet.1, Nat.add_zero,
    decide_eq_false_iff_not, Nat.not_lt]
  exact hL

end Solidity.Backend
