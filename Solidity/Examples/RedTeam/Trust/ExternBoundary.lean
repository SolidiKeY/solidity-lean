/-!
# The source trust lint does not inventory external implementations

Claim: a safe definition can have different kernel and native values without
being reported by `scripts/check-trust.mjs:77` (`findings`). The companion test adds an external attribute to a temporary copy of this
module, using the two-Nat calling convention of the runtime addition
symbol. Its theorem proves the logical value is zero at `(0, 1)`; the compiled
program prints one. The theorem below is checked in ordinary library builds; the test compiles
and runs its temporary copy outside this library. The library itself installs no external implementation.

This is a checker-coverage witness, not a proof of a false proposition or a
counterexample to either compiler theorem. Suggested fix: inventory external
attributes in the source lint and reconcile with the environment audit.
`scripts/trust/trust-implemented-by.mjs:50` already rejects external sites;
that stronger audit is not invoked by `scripts/ci/checks-fast.sh:25`.
-/
namespace Solidity.Examples.RedTeam.Trust.ExternBoundary

-- NATIVE_IMPLEMENTATION_FIXTURE
def first (a b : Nat) : Nat := a + (b - b)

/-- The kernel evaluates the declared body, independently of the native symbol. -/
theorem kernel_zero : first 0 1 = 0 := rfl

/-- info: 'Solidity.Examples.RedTeam.Trust.ExternBoundary.kernel_zero' does not depend on any axioms -/
#guard_msgs in
#print axioms kernel_zero
end Solidity.Examples.RedTeam.Trust.ExternBoundary
