# TestSuite proofs

The obligations and statuses are authoritative in
[Solidity/TestSuite](../Solidity/TestSuite/) and
[tests/solkey/expected.tsv](../tests/solkey/expected.tsv). Run:

```sh
./scripts/check-testsuite.sh
node scripts/check-automatic.mjs --strict
```

A derived row requires a theorem of the exact recorded obligation under the
standard axiom policy; a refuted row requires a checked refutation. Admission,
execution and a proof of an altered premise are not substitutes. Model choices
such as panic handling, exhausted diamonds and starting-state assumptions are
in [correctness.md](correctness.md) and [solc-alignment.md](solc-alignment.md).
Do not present a TestSuite proof as whole-source/EVM equivalence.
