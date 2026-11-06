# G25-IMUL-CHECKED-1105: checked int256 multiplication

Coordinator refill (H10/H12 idle-lane rebalance), finished on the
expression-uniqueness lane. Integrator: V09. Template: the closer
`Backend/PrimitivePackets/SignedCheckedSub/**` packet (itself shaped like
`CheckedAdd/**`), read-only.

## Modules

| Module | Content |
|---|---|
| `Source.lean` | `source_success`, `source_overflow`: checked `Source.evalE` of `a * b` on arbitrary int256 locals, exact value or exact `Panic(0x11)` bytes; the state is unchanged. |
| `Selected.lean` | `public_selection`: `Memory.compileVal` selects `binaryCode .int .mul`; `original_guard`: the selected code is the two loads followed by the literal `sTail .mul` guard (solc's `checked_mul_t_int256`); `guard_is_sTail`: that guard is `sTail .mul`. |
| `Target.lean` | `value_success`, `value_overflow` (`Val.evalT` classification), `target_success`, `target_overflow`: selected-code execution on any `StateRepr` machine with an arbitrary saved stack, through `Backend.Passes.value_success_tail` / `value_revert_iff`. |
| `Agreement.lean` | `success`, `overflow`: Source and selected target from one `IntegerLocalFamily`; `overflow_iff`. |
| `Controls.lean` | Joint controls on the populated six-cell frame of `SignedDiv.Controls` with arbitrary `tail`. |

No arithmetic producer is duplicated: the selected code's correctness comes from
the existing compiler certificate, whose signed `*` case is `Evm.smul_tail`
(`Evm/Signed.lean`, from `smul_ok`); `Controls.guard_classification` restates
`smul_tail` at the selected guard.

## Controls

Positive (overflow detected, exact Source panic, coarse target revert):
`minimum_minus` and `minus_minimum` (`-2^255 * -1` in both operand orders),
`upper` (`(2^255-1) * 2`), `upper_negative` (`-2^255 * -2^255`), `lower`,
`lower_swapped` (`-2^255 * 2`, `2 * -2^255`), `lower_maximum` (`(2^255-1) * -9`).

Positive (product fits, exact value): `regular` (`-7 * 9`), `regular_swapped`
(`9 * -7`), `regular_positive` (`-7 * -9`), `regular_both_positive` (`7 * 9`), `minimum_one`, `one_minimum`, `maximum_minus`,
`minus_maximum` (`-(2^255-1)` fits), `minimum_zero`, `zero_minimum`, and
`regular_exact` (the exact pushed word `sword (-63)`).

Negative: `minimum_minus_not_wrap` / `minus_minimum_not_wrap` (the checked code
does not push the wrapped `-2^255`), `wrong_result` (the pushed word for
`-7 * 9` is not `63`), `low_fuel`
(fuel 0 times out), `exact_panic` (the panic bytes).

`tests/primitive-packets-1105/SignedCheckedMul/Observations.lean` evaluates
the 16 operand pairs on both pipelines; `check.py` re-derives every row
(panic bytes, coarse revert, exact stack over the saved `[77, 88]`, unchanged
memory cells). `axioms.txt` there is the axiom inventory.

## Scope

The target overflow verdict is the coarse `Evm.Out.revert`; no equality with the
Source panic payload is claimed. Only local operands are covered, as in the
template.

## Register

New modules (already in `Solidity.lean` through `register.sh`):
`Solidity.Backend.PrimitivePackets.SignedCheckedMul.{Source,Selected,Target,Agreement,Controls}`.
Module-map rows: `docs/module-map/v08-adapters.d/expression-uniqueness.md`.
Axiom pins: `scripts/g07-axiom-pins.d/Solidity/Backend/PrimitivePackets/SignedCheckedMul/Controls.json`.

## Reviews

Read-only finder and skeptic reviews, neither using the Lean server. The finder
found no blocking defect and four minor ones, all fixed: "every sign"
overclaimed (`regular_both_positive`, `7 * 9`, added); `regular_exact` was
listed as negative; the doc did not name the product sign; and the guard tied
to `sTail .mul` only by inspection (`guard_is_sTail` added).

The skeptic found no refutation. It confirmed four things:

- `U` is signed 256-bit (`lo = -2^255`, `hi = 2^255-1`).
- The premises are only the local reads, the ranges, the side condition,
  `IntegerLocalFamily` and `StateRepr`. None is vacuous or circular; they are
  instantiated in Controls.
- The target `.mul` on `int` classifies by `PrimTy.int.ofInt?`, and the
  certificate is indexed by exactly `binaryCode .int .mul`, that is `sTail .mul`,
  which is solc's `checked_mul_t_int256`.
- The panic bytes are `0x4e487b71 ‖ word(0x11)`.

It noted, and this document already states, that a target revert carries no
payload.
