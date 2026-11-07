# Static-call audit fixture registration fragment

`StaticCallWitness.lean` is an additive test fixture importing the reachable V2
controls. Its joint tuple includes every input to `SourceDispatchV2.static_call_storage`
and the actual static-mode premise. `client` applies that unchanged statement.
Both declarations depend only on propext, Classical.choice and Quot.sound.
This is no compiler-success, gas/fork, callee-world or global-coverage claim.
No generated root/module map or central axiom pin is edited by this fragment.
