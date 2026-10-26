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
