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

A function statement can also be read only at a contract's reachable
starting states: `ValidStart (.reachable M) φ`
([options.md, O12](options.md#o12-reachable-starting-states-lean-only),
`Theory/Reachable/Mode.lean`), discharged by a contract invariant proved once
over the entry points; `ValidTail .clean` statements carry over
(`ValidTail.validStart_reachable`).

## Model choices behind the statements

- **Payments.** Transfers and sends check both available funds and the
  transaction's payment response. A successful payment to another address
  debits `selfBalance` and its ledger entry; self-payment moves neither.
  Refused transfers revert; refused sends return false with balances
  unchanged. The EVM simulation's fresh-state theorem requires
  `balance = bal self`.
- **The payment update** records the hypothetical successful branch,
  balance debit included, and prints as `pay(receiver, amount)` in Lean and
  LaTeX. It does not assert that the recipient accepts: the transfer box
  rule overapproximates, the send rules prove both success and refusal.
  Payment updates are outside `sol_decide`'s language until it models their
  balance effects; semantic closing still works.
- **Callbacks** may replace storage, ledger and balance; pure/view frames
  preserve them. The callback self-call rule proves the resumed body under
  the non-self guard captured in the caller's state, not re-read after the
  callback.
- **Evaluation.** Constant arithmetic folds the whole rational expression
  before typing or operand sequencing. Earlier call arguments and payment
  receivers are captured before later effects under both evaluation
  schedules. Parenthesized compound assignments stay unchecked inside
  `unchecked`.
- **The runner** selects callback validity from the actual obligation
  (specified rows and bare external calls included). The call type does not
  encode static calls, so view calls conservatively get callback semantics.

Regressions: `Examples/Tactics/AuditRepairs.lean`,
`Examples/Tactics/Net.lean`, `Examples/Tactics/RunnerAudit.lean`.
Correctness is relative to the model: full solc/EVM equivalence, gas and
static-call restrictions are outside the proved fragment.

## Caller models (O11)

`ValidM M ts φ` (`⊨ᶠₘ[M; ts] φ`, `Calculus/CallerModel.lean`) reads `φ`
with callees that call back as the caller model `M` allows: `none` (no
callback: `Fml.Valid`), `staticOnly` (read, change nothing),
`nonReentrant R` (call back into `R`'s entries, a guarded one only while the
lock is free) or
`any` (`ValidT ts`, `validM_any`). It is an internal formula validity like
`ValidT`; no `Spec` statement reads it yet. A box proved under a stronger
model holds under a weaker one (`ValidM.weaken`, positive modalities only),
so a `ValidT` proof is one under every model (`ValidM.of_validT`); the
converse fails at each level, `none < staticOnly` by the invariant owed on
exit (`Examples/Tactics/CallerModel.lean`). See
[options.md](options.md#o11-caller-models-lean-only).
