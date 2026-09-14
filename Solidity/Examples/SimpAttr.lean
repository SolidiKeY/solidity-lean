import Lean

/-!
Registers the `rule_simp_set` simp attribute used by the step-case navigation
tactics in `Examples/Common.lean`. Lives in its own module because a simp
attribute must be initialized in a module imported by its users.

(4.24 note: the former `rule_simp` macro passed ~100 lemmas literally to
`simp only`, and each invocation re-elaborated the whole set — ~3s per call on
Lean 4.24, × ~190 skip proofs per `single_step`. A registered set is built
once per module instead.)
-/

register_simp_attr rule_simp_set

/-- Trace the rules `steps!` picks, one line per step plus a pasteable
`steps [...]` summary:

```
set_option trace.solidity.steps true in
sol_runs deepFieldWrite { alice.account.balance = amount }
```

Registered here for the same reason the simp set is: a trace class must be
initialized in a module imported by its users. -/
initialize Lean.registerTraceClass `solidity.steps
