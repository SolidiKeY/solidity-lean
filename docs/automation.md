# Proof automation

Use the implemented tactics and their suggestion twins (`sol_prove`,
`sol_exact`, `sol_derive?`, `sol_chain?`) in
[Calculus](../Solidity/Calculus/) and [Tools](../Solidity/Tools/). The source declarations and regression
examples define accepted syntax and replay behavior; see
[calculus.md](calculus.md) for use.

A search timeout or unsupported construct is unknown, not a certificate.
Modeled execution exhaustion follows the declared halt policy. A computed/native answer is distinct
from a per-result kernel certificate; see [correctness.md](correctness.md).
Completeness theorems apply only to their explicit recognized fragments and
hypotheses, not to all Solidity or all reachable states.

## Automation gate

```sh
node scripts/check-automatic.mjs --strict
```

This checks the TestSuite's recorded obligations and replay requirements.
It does not establish source/compiler completeness.

<a id="m7-next--a-checkpoint-of-the-theorem-not-started"></a>
The remaining full-pipeline obligations are in [coverage-plan.md](coverage-plan.md).

## Guarded symmetric cancellation

Cancellation must retain successful-evaluation and range conditions. The
implemented recognizers and negative controls are authoritative; do not replace
checked arithmetic with unrestricted ring cancellation.
