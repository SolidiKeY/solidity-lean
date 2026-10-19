import Solidity.Calculus.Logic

/-!
# Clean array tails as an option (`docs/options.md`, O6)

A storage array keeps the slots past its live end (`SVal.array`'s shadow,
`Semantics/Storage.lean`), and an empty `push` on an array of references
recycles the first of them as it is (`pushSlot`), as solc does.  A write
through an alias left dangling by a `pop` reappears after a later `push`
(`Examples/Tactics/CleanTail.lean`, `Tokens.dangling`), so nothing tells
what a recycled slot holds.

The option says whether the starting storage is assumed to have clean
tails, every shadow an ordinary default (`Storage.CleanTail`,
`Typing/CleanTail.lean`): `.solc` assumes nothing, the reading of `Valid`;
`.clean` assumes it, as the premise `cleanTail(storage) = true`
(`Fml.cleanTail`, the symbol `Op1.cleanTail`).  As every option here it is
an argument of the validity proved (`ValidTail m φ`), and the premise is a
formula, so `Proves.valid` proves `.clean` unchanged: `impRight` puts it in
the antecedent, where the closer reads it (`Calculus/DecideCleanTail.lean`).

It is an assumption on the starting storage, not a property a program
keeps: one that pops an aliased element and writes through the alias
leaves a dirty tail (`leaveDirty_boundary_rejected`), and a callback may
observe it (`interruptRepair_callback_boundary_rejected`,
`Calculus/CleanTailBoundary.lean`).
-/

namespace Solidity

variable {C : Contract}

/-- `cleanTail(storage) = true`: the arrays' tails of the storage are clean,
as its observations show them (`TSto.CleanTails`). -/
def Fml.cleanTail (C : Contract) {Γ : Ctx} : Fml C Γ :=
  .eq (.app1 .cleanTail (.app0 .storage)) (.app0 (.lit (p := .bool) true))

/-- `cleanTail(storage) = true` holds where the storage's observations show
clean tails. -/
theorem holds_cleanTail {Γ : Ctx} {σ : State C Γ} :
    holds σ (Fml.cleanTail C) ↔ TSto.CleanTails σ.storage.obs := by
  show (open Classical in if TSto.CleanTails σ.storage.obs then some true else none) =
    (some true : Option Bool) ↔ _
  by_cases h : TSto.CleanTails σ.storage.obs
  · exact iff_of_true (if_pos h) h
  · exact iff_of_false (by rw [if_neg h]; exact nofun) h

/-- A storage with clean tails satisfies `cleanTail(storage) = true`. -/
theorem holds_cleanTail_of {Γ : Ctx} {σ : State C Γ} (h : σ.storage.CleanTail) :
    holds σ (Fml.cleanTail C) :=
  holds_cleanTail.2 (Storage.cleanTails_obs h)

/-- **Whether the starting storage's arrays have clean tails**: `solc`
assumes nothing (an empty `push` may recycle a dirty slot), `clean`
assumes every shadow an ordinary default. -/
inductive TailMode where
  | solc
  | clean
  deriving DecidableEq, Repr

/-- **Valid under a tail mode**: `.solc` is `Valid`; `.clean` is `Valid` of
the formula under the premise `cleanTail(storage) = true`. -/
def ValidTail : TailMode → Fml C [] → Prop
  | .solc, φ => Valid φ
  | .clean, φ => Valid (.imp (Fml.cleanTail C) φ)

theorem validTail_solc {φ : Fml C []} : ValidTail .solc φ ↔ Valid φ := Iff.rfl

theorem validTail_clean {φ : Fml C []} :
    ValidTail .clean φ ↔ Valid (.imp (Fml.cleanTail C) φ) := Iff.rfl

/-- What `.clean` proves holds in every state whose storage has clean
tails. -/
theorem ValidTail.holds_of_clean {φ : Fml C []} (h : ValidTail .clean φ) (σ : State C [])
    (hσ : σ.storage.CleanTail) : holds σ φ :=
  h σ (holds_cleanTail_of hσ)

/-- The initial storage has clean tails: what `.clean` proves holds there. -/
theorem ValidTail.holds_init {φ : Fml C []} (h : ValidTail .clean φ) : holds (State.init C) φ :=
  h.holds_of_clean _ (Storage.init_cleanTail C)

/-- `.solc` assumes less. -/
theorem ValidTail.clean_of_solc {φ : Fml C []} (h : ValidTail .solc φ) : ValidTail .clean φ :=
  fun σ _ => h σ

end Solidity
