# Correctness statements

`⊨ φ` accepts `φ : Spec C []` only. `Spec.sat` reads intrinsically typed
statements directly over `Prog.run`: equations, storage well-formedness,
connectives, typed universal quantification and frameless modalities.
Internal formula validity is `Fml.Valid`, written `⊨ᶠ`; `dl!{…}` still builds
an internal `Fml`. There is no implicit conversion of internal formulas to
correctness statements.

An equation in `Spec` requires both `Tm.eval` calls to return the same
value. Two failed evaluations cannot satisfy it. Internal `Fml.eq` retains
KeY's total equality (`key-equality.md`). `Spec.toFml` represents strict
equality by two parallel operand captures and a negated box; this rejects
all failed captures, including exhaustion.

`Spec.sat_iff_holds` and `Spec.valid_iff` prove the translation exact.
`Proves.valid` proves `⊢ φ.toFml → ⊨ φ`; `Proves.fmlValid` gives internal
formula validity. For example:

```lean
example : ⊨ (Spec.tt : Spec C []) := by
  apply Proves.valid (R := .all)
  exact .closeHolds (fun _ => trivial)
```

For callbacks, `Spec.satC I pay` quantifies over every `ExecP` outcome,
including invariant violations. Write `⊨[I] φ` with transfer callbacks or
`⊨ₙ[I] φ` without them. `Spec.satC_iff_holdsC` and `Spec.validC_iff` prove
the bridge; `ProvesC.valid` proves the direct statement from a derivation
of its translation. Internal callback validity is written `⊨ᶠ[I]` or
`⊨ᶠₙ[I]`, with theorem `ProvesC.fmlValid`.

The halt policies are unchanged: boxes accept revert, divergence and
exhaustion, but reject panic. Diamonds accept a successful postcondition
or exhaustion. Callback readings additionally reject invariant violation.
These are model choices, not claims that execution terminates or has gas.

Whole-contract properties compose successful deployment and interface calls
in the [lifetime layer](lifetime.md). Its `AG`, `EF` and `AGEF` describe
transaction-boundary safety and possible reachability; commits require actual
successful outcomes, so an exhausted diamond does not witness reachability.

## October 2026 audit repairs

Transfers and sends check both available funds and the transaction's
payment response. A successful payment to another address debits
`selfBalance` and its ledger entry; self-payment moves neither. Refused
transfers revert, and refused sends return false with unchanged balances.
The EVM simulation relates spendable funds and payment responses explicitly;
its fresh-state theorem requires `balance = bal self`.

The symbolic payment update records the hypothetical successful branch,
including its balance debit, and prints as `pay(receiver, amount)` in both
Lean and LaTeX output. The historical net-only conditional payment spelling is rejected because
it conceals that balance change. It does not assert that the recipient accepts:
the transfer box rule is an overapproximation, while send rules prove both
success and refusal. Payment updates are excluded from the restricted
decision language until that language models their balance effects;
semantic closing remains available.

Callbacks may replace storage, ledger and balance. Pure/view frames preserve
them. The callback self-call rule proves the resumed external success body
directly under the non-self guard captured in the caller's state: it does
not re-read that guard after a callback changes the state.

Constant arithmetic folds the whole rational expression before typing or
operand sequencing, so intermediate negative or fractional literals do not
force a word operation. Earlier call arguments and payment receivers are
captured before later effects, under both configured evaluation schedules.
Parenthesized compound assignments remain unchecked inside `unchecked`.

The runner selects callback validity from the actual obligation, including
specified rows and bare external calls. Mutability metadata is diagnostic;
the operational call type does not yet encode static calls, so even view
calls conservatively receive callback semantics.

Read-only finder and skeptic reviews identified whole-expression folding
at `hoistTop`, wrapping-operator preservation, unfunded legacy examples,
fresh EVM balance agreement and recursive callback balance propagation.
These findings are addressed by the source changes and regressions in
`Examples/Tactics/AuditRepairs.lean`, `Examples/Tactics/Net.lean` and
`Examples/Tactics/RunnerAudit.lean`. This remains correctness relative to
the model: full solc/EVM equivalence, gas and static-call restrictions are
outside the proved fragment.

The final TestSuite pass also exposed a proof-cost regression in the storage
loop's exit leaf. Its focused replay uses the invariant and stopped guard
directly, without storage-frame saturation or a larger heartbeat budget.
Finder and skeptic reviews confirmed that the obligation and assumptions
are unchanged.

Validation passed for the default library, `SolkeyTestSuite`, `SolidityCorpus`,
six focused runner tests, and the frozen SolKey sort annotations (377
taclets, 131 read-bearing annotations). The corpus also needed its remaining
internal validity call renamed and its outcome printer made exhaustive for
data-carrying reverts; read-only reviews confirmed these compatibility fixes.

Separate checks still report existing issues: the TestSuite trust scan flags
the preceding loop theorem's 205,000-heartbeat override, the path checker
flags missing vendored references, and the orphan checker sees ignored scratch
modules. The optional `Bridge` package's validity names are migrated, but its
build still fails on separate Mathlib/CSLib port issues in `Loop.lean`,
`Rewriting.lean` and `ModelTheory.lean`; it is not part of the passing core
validation.
