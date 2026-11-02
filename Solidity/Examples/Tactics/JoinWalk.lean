import Solidity.Calculus.Closers
import Solidity.Tools.ProofTree
import Solidity.Tools.Counterexample
/-! # Joined walks through the production automatic tactic
The raw program/leaf metrics are distinct from closer context costs and call
sharing. Full source theorems use the unchanged automatic strategy. -/
namespace Solidity.Examples.Tactics.JoinWalk
open Solidity
open scoped Solidity.Scoped
local instance : InContract := ⟨StandardExample⟩
/-- Two dependent assignments per arm retain their source order and one joined leaf. -/
theorem rootW2 : ⊨ᶠ dl!{ ⟨ uint x = 0; uint y = 0; if (a == 1) { x = x + 1; y = x + 1; } else { x = 2; y = x + 1;  }; ⟩ y >= x } := by
  sol_auto

/-- Four dependent assignments per arm close through the production automatic tactic. -/
theorem rootW4 : ⊨ᶠ dl!{ ⟨ uint x = 0; uint y = 0; if (a == 1) { x = x + 1; y = x + 1; x = x + 1; y = x + 1; } else { x = 2; y = x + 1; x = x + 1; y = x + 1; }; ⟩ y >= x } := by
  sol_auto

/-- Eight dependent assignments per arm keep the final assigned value above its predecessor. -/
theorem rootW8 : ⊨ᶠ dl!{ ⟨ uint x = 0; uint y = 0; if (a == 1) { x = x + 1; y = x + 1; x = x + 1; y = x + 1; x = x + 1; y = x + 1; x = x + 1; y = x + 1; } else { x = 2; y = x + 1; x = x + 1; y = x + 1; x = x + 1; y = x + 1; x = x + 1; y = x + 1; }; ⟩ y >= x } := by
  sol_auto

/-- Two sequential joined conditionals compose without substituting their RHS terms. -/
theorem rootS2 : ⊨ᶠ dl!{ ⟨ uint x = 0; uint y = 0; if (a == 1) { x = x + 1; y = x + 1; } else { x = 2; y = x + 1; }; if (b == 1) { x = x + 1; y = x + 1; } else { x = 2; y = x + 1; }; ⟩ y >= x } := by
  sol_auto

/-- Three sequential joined conditionals preserve every dependent update. -/
theorem rootS3 : ⊨ᶠ dl!{ ⟨ uint x = 0; uint y = 0; if (a == 1) { x = x + 1; y = x + 1; } else { x = 2; y = x + 1; }; if (b == 1) { x = x + 1; y = x + 1; } else { x = 2; y = x + 1; }; if (c == 1) { x = x + 1; y = x + 1; } else { x = 2; y = x + 1; }; ⟩ y >= x } := by
  sol_auto

/-- Seven independent guards join two certified bases past the existing split limit. -/
theorem rootC7 : ⊨ᶠ dl!{ ⟨ uint x = 0; uint y = 0; if (k1 == 1) { x = x + 1; } else { x = y + 1; }; if (k2 == 1) { y = x + 1; } else { y = y + 1; }; if (k3 == 1) { x = x + 1; } else { x = y + 1; }; if (k4 == 1) { y = x + 1; } else { y = y + 1; }; if (k5 == 1) { x = x + 1; } else { x = y + 1; }; if (k6 == 1) { y = x + 1; } else { y = y + 1; }; if (k7 == 1) { x = x + 1; } else { x = y + 1; }; ⟩ x <= 7 } := by
  sol_auto

/-- Twelve independent guards retain certified bounds without enumerating their paths. -/
theorem rootC12 : ⊨ᶠ dl!{ ⟨ uint x = 0; uint y = 0; if (k1 == 1) { x = x + 1; } else { x = y + 1; }; if (k2 == 1) { y = x + 1; } else { y = y + 1; }; if (k3 == 1) { x = x + 1; } else { x = y + 1; }; if (k4 == 1) { y = x + 1; } else { y = y + 1; }; if (k5 == 1) { x = x + 1; } else { x = y + 1; }; if (k6 == 1) { y = x + 1; } else { y = y + 1; }; if (k7 == 1) { x = x + 1; } else { x = y + 1; }; if (k8 == 1) { y = x + 1; } else { y = y + 1; }; if (k9 == 1) { x = x + 1; } else { x = y + 1; }; if (k10 == 1) { y = x + 1; } else { y = y + 1; }; if (k11 == 1) { x = x + 1; } else { x = y + 1; }; if (k12 == 1) { y = x + 1; } else { y = y + 1; }; ⟩ x <= 12 } := by
  sol_auto


-- Measurement commands use the production proof tree and its closer.
/--
info: 17 node(s), 1 branch(es), 0 open, largest leaf 57 term node(s)
-/
#guard_msgs in
#proof_size dl!{ ⟨ uint x = 0; uint y = 0; if (a == 1) { x = x + 1; y = x + 1; } else { x = 2; y = x + 1;  }; ⟩ y >= x }

/--
info: 21 node(s), 1 branch(es), 0 open, largest leaf 89 term node(s)
-/
#guard_msgs in
#proof_size dl!{ ⟨ uint x = 0; uint y = 0; if (a == 1) { x = x + 1; y = x + 1; x = x + 1; y = x + 1; } else { x = 2; y = x + 1; x = x + 1; y = x + 1; }; ⟩ y >= x }

/--
info: 29 node(s), 1 branch(es), 0 open, largest leaf 153 term node(s)
-/
#guard_msgs in
#proof_size dl!{ ⟨ uint x = 0; uint y = 0; if (a == 1) { x = x + 1; y = x + 1; x = x + 1; y = x + 1; x = x + 1; y = x + 1; x = x + 1; y = x + 1; } else { x = 2; y = x + 1; x = x + 1; y = x + 1; x = x + 1; y = x + 1; x = x + 1; y = x + 1; }; ⟩ y >= x }

/--
info: 29 node(s), 1 branch(es), 0 open, largest leaf 101 term node(s)
-/
#guard_msgs in
#proof_size dl!{ ⟨ uint x = 0; uint y = 0; if (a == 1) { x = x + 1; y = x + 1; } else { x = 2; y = x + 1; }; if (b == 1) { x = x + 1; y = x + 1; } else { x = 2; y = x + 1; }; ⟩ y >= x }

/--
info: 41 node(s), 1 branch(es), 0 open, largest leaf 145 term node(s)
-/
#guard_msgs in
#proof_size dl!{ ⟨ uint x = 0; uint y = 0; if (a == 1) { x = x + 1; y = x + 1; } else { x = 2; y = x + 1; }; if (b == 1) { x = x + 1; y = x + 1; } else { x = 2; y = x + 1; }; if (c == 1) { x = x + 1; y = x + 1; } else { x = 2; y = x + 1; }; ⟩ y >= x }

/--
info: 40 node(s), 1 branch(es), 0 open, largest leaf 139 term node(s)
-/
#guard_msgs in
#proof_size dl!{ ⟨ uint x = 0; uint y = 0; if (k1 == 1) { x = x + 1; } else { x = y + 1; }; if (k2 == 1) { y = x + 1; } else { y = y + 1; }; if (k3 == 1) { x = x + 1; } else { x = y + 1; }; if (k4 == 1) { y = x + 1; } else { y = y + 1; }; if (k5 == 1) { x = x + 1; } else { x = y + 1; }; if (k6 == 1) { y = x + 1; } else { y = y + 1; }; if (k7 == 1) { x = x + 1; } else { x = y + 1; }; ⟩ x <= 7 }

/--
info: 65 node(s), 1 branch(es), 0 open, largest leaf 229 term node(s)
-/
#guard_msgs in
#proof_size dl!{ ⟨ uint x = 0; uint y = 0; if (k1 == 1) { x = x + 1; } else { x = y + 1; }; if (k2 == 1) { y = x + 1; } else { y = y + 1; }; if (k3 == 1) { x = x + 1; } else { x = y + 1; }; if (k4 == 1) { y = x + 1; } else { y = y + 1; }; if (k5 == 1) { x = x + 1; } else { x = y + 1; }; if (k6 == 1) { y = x + 1; } else { y = y + 1; }; if (k7 == 1) { x = x + 1; } else { x = y + 1; }; if (k8 == 1) { y = x + 1; } else { y = y + 1; }; if (k9 == 1) { x = x + 1; } else { x = y + 1; }; if (k10 == 1) { y = x + 1; } else { y = y + 1; }; if (k11 == 1) { x = x + 1; } else { x = y + 1; }; if (k12 == 1) { y = x + 1; } else { y = y + 1; }; ⟩ x <= 12 }

abbrev badOverflow := dl!{ ⟨ uint x = a; uint y = 0;
  if (b == 1) { x = x + 1; } else { x = y + 1; };
  if (c == 1) { y = x + 1; } else { y = y + 1; }; ⟩ y >= 0 }
abbrev badDivision := dl!{ ⟨ uint x = 0; uint y = 0;
  if (b == 1) { x = 1 / 0; } else { x = 1; };
  if (c == 1) { y = x + 1; } else { y = y + 1; }; ⟩ y >= 0 }
abbrev badCorrelation := dl!{ ⟨ uint x = 0; uint y = 0;
  if (a == 1) { x = x + 1; y = x + 1; } else { x = 2; y = x + 1; }; ⟩ y < x }

/-- A selected checked overflow has an inhabited source countermodel. -/
theorem overflowCountermodel : ¬ Fml.Valid badOverflow := by
  sol_refute

/-- Selecting division by zero prevents the required returning execution. -/
theorem divisionCountermodel : ¬ Fml.Valid badDivision := by
  sol_refute

/-- The opposite dependent-value comparison is refuted by a concrete source execution. -/
theorem correlationCountermodel : ¬ Fml.Valid badCorrelation := by
  sol_refute

/-- The production automatic tactic preserves the non-evaluation of an untaken failing RHS. -/
theorem untakenDivision : ⊨ᶠ dl!{ b == 1 → ⟨ uint x = 0; uint y = 0;
    if (b == 1) { x = 1; } else { x = 1 / 0; };
    if (c == 1) { y = x + 1; } else { y = x + 1; }; ⟩ y == 2 } := by
  sol_auto
end Solidity.Examples.Tactics.JoinWalk
