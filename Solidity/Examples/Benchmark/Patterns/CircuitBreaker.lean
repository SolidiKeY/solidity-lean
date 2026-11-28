import Solidity.Calculus.ProvesDerive
import Solidity.Calculus.DecideComplete
import Solidity.Calculus.SurfaceSpec
import Solidity.Calculus.Surface
import Solidity.Calculus.Closers
/-!
# Patterns benchmark: circuit breaker (emergency stop)

Source: ConsenSys Diligence, Smart Contract Best Practices, "Circuit Breakers":
<https://github.com/ConsenSysDiligence/smart-contract-best-practices/blob/f3a9741ce3954a8dac3b3cbdcdafda14d8f4d948/docs/development-recommendations/precautions/circuit-breakers.md>.

Unlike OpenZeppelin's `Pausable` (`Benchmark/Governance/Pausable.lean`), the
breaker is one admin toggle and its modifiers skip the body silently
(`if (!stopped) _;`) instead of reverting. Changes: the fragment is wrapped in
a contract, the modifiers' `if` bodies are braced, and a constructor `owner = msg.sender;` is added, without which
`owner` stays `0` and `isAdmin` admits no real caller. The bodies stay
empty ("some code"). Natural `@custom:key` clauses: only the admin flips the
breaker; `deposit` and `withdraw` never change it or the admin.

Verdicts: constructor, toggleContractActive, deposit, withdraw proved.
-/
namespace Solidity.Examples.Benchmark.Patterns.CircuitBreaker
def CircuitBreaker : Contract := contract!{
  bool private stopped = false;
  address private owner;
  ensures owner == msg.sender && !stopped;
  constructor() { owner = msg.sender; }
  modifier isAdmin() {
    require(msg.sender == owner);
    _;
  }
  ensures msg.sender == owner && owner == \old(owner) && (stopped <-> !\old(stopped));
  function toggleContractActive() isAdmin public {
    stopped = !stopped;
  }
  modifier stopInEmergency { if (!stopped) { _; } }
  modifier onlyInEmergency { if (stopped) { _; } }
  ensures (stopped <-> \old(stopped)) && owner == \old(owner);
  function deposit() stopInEmergency public {
  }
  ensures (stopped <-> \old(stopped)) && owner == \old(owner);
  function withdraw() onlyInEmergency public {
  }
}
local instance : InContract := ⟨CircuitBreaker⟩
open scoped Scoped
theorem spec_constructor : ⊢ spec!{ constructor } := by
  sol_prove
theorem spec_toggleContractActive : ⊢ spec!{ toggleContractActive } := by
  sol_prove
theorem spec_deposit : ⊢ spec!{ deposit } := by
  sol_prove
theorem spec_withdraw : ⊢ spec!{ withdraw } := by
  sol_prove
end Solidity.Examples.Benchmark.Patterns.CircuitBreaker
