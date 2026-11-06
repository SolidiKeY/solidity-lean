import Solidity.Calculus.TailMode
import Solidity.Calculus.CallbackHolds

/-!
# The assumption record of a verdict (`docs/options.md`, O10)

A verdict is proved under readings O1–O9 fix: who may call back (O1, O7), how
arithmetic out of range is read (O2, O5), whether the starting storage's
array tails are clean (O6), the expression order (O9), and two readings the
model has only one of: hashes are `keccakBytes`, read as an atom (no
collision resistance), and address `0` holds no code (O8).  `Assumptions`
records them, one field each, and `ValidA I a φ` is the validity they
select: as for every option here (`ValidT`, `ValidTail`) the record is an
argument of the statement, never a setting.  `ValidA` reads three fields
(`callback`, `tail`, `order`); the other three are labels it does not read
(`ValidA.labels`): `overflow` because the blocks are syntax of the formula
already (`Prog.withOF`), `hash` and `zeroAddress` because the model has one
reading of each.  A policy on a label is enforced on the label, which the
CLI derives from what the runner does (`docs/options.md`, O10).

What a policy refuses (`Policy`, the CLI's `--require`/`--deny`,
`docs/cli.md`) is decided on the record: a row is reported proved only when
some record it entails is allowed (`Policy.verdict_proved_iff`), and the
entailment is proved, not assumed (`ValidA.weaken`: a `.solc` row holds
under `.clean`, `ValidTail.clean_of_solc`).  So what is reported proved is
valid under an allowed record (`Policy.admits_sound`, `ProvedRow.holds`),
and a row whose record entails no allowed one is not reported proved
(`Policy.verdict_refused`).

The fields:

* `callback`: the payment flag of `ValidC` (`TransferSem.pay`): `false` is
  `transferSemantics:noCallback` with fix 5A (a `try` and a value call may
  call back), `true` is `withCallback`.  The callee's invariant is the
  statement's other argument.  This is the existing flag, not a lattice:
  VC2's caller models (O11, `none < staticOnly < nonReentrant < any`)
  replace it, and their weakening theorem becomes a case of `Entails`.
* `overflow`: how the source's arithmetic was elaborated, a label of the
  formula's programs (`Prog.withOF`, `Syntax/Checked.lean`): `default`
  (neither block), `checked` (`checkingOF`), `ignoring` (`ignoringOF`, an
  overflowing run assumed away).  The blocks are in the formula already,
  so `ValidA` does not re-read the label; it is what a policy refuses.
* `tail`: `TailMode` (O6), read by `ValidA` as `ValidTail` reads it.
* `order`: `OrderReading` (O9), read off the contract (`C.evalOrder`).
* `hash`, `zeroAddress`: the model's only readings; refusing one refuses
  every row (no certificate records that a proof does not depend on it).

O13's target profile, which ties `order` to a compiler pipeline, is
`Calculus/TargetProfile.lean`.
-/

namespace Solidity

variable {C : Contract}

/-! ## The readings -/

/-- How the source's arithmetic out of range was read (`docs/options.md`,
O2, O5): neither block, `checked { … }`, `ignoringOverflow { … }`. -/
inductive OverflowReading where
  | default
  | checked
  | ignoring
  deriving DecidableEq, Repr, Inhabited

/-- The expression order (`docs/options.md`, O9): solc's legacy code
generator, or its IR code generator's source order. -/
inductive OrderReading where
  | legacy
  | viaIR
  deriving DecidableEq, Repr, Inhabited

/-- The elaboration preset of an order. -/
def OrderReading.toEvalOrder : OrderReading → EvalOrder
  | .legacy => {}
  | .viaIR => .viaIR

/-- Whether a contract's elaboration preset is the order's.  A preset that
mixes the flags (a legacy fixture's custom order, `Frontend/Import.lean`)
is neither, so no record reads it. -/
def OrderReading.matches : OrderReading → EvalOrder → Bool
  | .legacy, o => !o.binaryLeftToRight && !o.modularLeftToRight && !o.modifierFrames
  | .viaIR, o => o.binaryLeftToRight && o.modularLeftToRight && o.modifierFrames

theorem OrderReading.matches_iff (r : OrderReading) (o : EvalOrder) :
    r.matches o = true ↔ o = r.toEvalOrder := by
  rcases o with ⟨b, m, f⟩
  cases r <;> cases b <;> cases m <;> cases f <;>
    simp only [OrderReading.matches, OrderReading.toEvalOrder, EvalOrder.viaIR, EvalOrder.mk.injEq]
    <;> decide

/-- How a hash is read: `keccakBytes` (Keccak-256 of the bytes,
`Semantics/Heap.lean`), `@[irreducible]`, so an atom to the closers, with no
collision resistance assumed.  The model's only reading. -/
inductive HashReading where
  | opaque
  deriving DecidableEq, Repr, Inhabited

/-- What address `0` holds: no code, so a call to it reverts (`TRun.tryCall`,
`docs/options.md` O8, `docs/solc-alignment.md`).  The model's only
reading. -/
inductive ZeroAddressReading where
  | noCode
  deriving DecidableEq, Repr, Inhabited

/-- **The assumption record of a verdict**: one reading per option.  The
defaults are the solc runner's (`scripts/test-solidity.mjs`). -/
structure Assumptions where
  /-- Whether a `transfer` and a `send` call back (`TransferSem.pay`).
  VC2's caller-model lattice (O11) replaces this flag. -/
  callback : Bool := false
  overflow : OverflowReading := .default
  tail : TailMode := .solc
  order : OrderReading := .legacy
  hash : HashReading := .opaque
  zeroAddress : ZeroAddressReading := .noCode
  deriving DecidableEq, Repr

instance : Inhabited Assumptions := ⟨{}⟩

/-- The formula a tail mode states (`ValidTail`'s). -/
def TailMode.wrap (C : Contract) : TailMode → Fml C [] → Fml C []
  | .solc, φ => φ
  | .clean, φ => .imp (Fml.cleanTail C) φ

/-- **Validity under an assumption record**: the contract elaborates in the
record's order, and the formula, under the record's tail premise, is valid
with callbacks at the callee invariant `I` and the record's payment flag. -/
def ValidA (I : Invariant C) (a : Assumptions) (φ : Fml C []) : Prop :=
  a.order.matches C.evalOrder = true ∧ ValidC I (a.tail.wrap C φ) a.callback

/-- **The labels**: `ValidA` does not read `overflow`, `hash` or
`zeroAddress`. -/
theorem ValidA.labels (I : Invariant C) (a : Assumptions) (φ : Fml C [])
    (o : OverflowReading) (h : HashReading) (z : ZeroAddressReading) :
    ValidA I { a with overflow := o, hash := h, zeroAddress := z } φ ↔ ValidA I a φ :=
  Iff.rfl

/-! ## The runner's statements are cases -/

theorem TailMode.callsBack_wrap (t : TailMode) (φ : Fml C []) (pay : Bool) :
    (t.wrap C φ).callsBack pay = φ.callsBack pay := by
  cases t
  · rfl
  · show (false || φ.callsBack pay) = φ.callsBack pay
    exact Bool.false_or _

theorem TailMode.validTail_iff (t : TailMode) (φ : Fml C []) :
    ValidTail t φ ↔ Fml.Valid (t.wrap C φ) := by
  cases t <;> exact Iff.rfl

/-- `ValidT` is `ValidA` at the semantics' invariant and flag, `.solc`. -/
theorem validA_iff_validT (ts : TransferSem C) (φ : Fml C [])
    (h : C.evalOrder = OrderReading.legacy.toEvalOrder) :
    ValidA ts.inv { callback := ts.pay } φ ↔ ValidT ts φ :=
  ⟨fun h' => h'.2, fun h' => ⟨(OrderReading.matches_iff _ _).2 h, h'⟩⟩

/-- **A plain obligation** (`⊢ N.f.problem`, or under `.clean`
`⊢ cleanTail(storage) = true → N.f.problem`): where nothing calls back,
`ValidTail` is `ValidA` with no payment calling back, at any invariant
(`validC_false_iff`). -/
theorem validA_of_validTail (I : Invariant C) (t : TailMode) (φ : Fml C [])
    (hcb : φ.callsBack false = false) (h : C.evalOrder = OrderReading.legacy.toEvalOrder)
    (hv : ValidTail t φ) : ValidA I { tail := t } φ :=
  ⟨(OrderReading.matches_iff _ _).2 h,
    (validC_false_iff ((t.callsBack_wrap φ false).trans hcb)).2 ((t.validTail_iff φ).1 hv)⟩

/-! ## Entailment between records -/

/-- `a` entails `b` when every formula valid under `a` is valid under `b`,
by a proved implication: equal records, or `.solc` tails weakened to
`.clean` (`ValidTail.clean_of_solc`).  VC2's caller lattice (O11) adds its
weakening here. -/
def Assumptions.Entails (a b : Assumptions) : Prop :=
  b = a ∨ (a.tail = .solc ∧ b = { a with tail := .clean })

/-- The records `a` entails, listed. -/
def Assumptions.weakenings (a : Assumptions) : List Assumptions :=
  a :: (if a.tail = .solc then [{ a with tail := .clean }] else [])

theorem Assumptions.mem_weakenings {a b : Assumptions} :
    b ∈ a.weakenings ↔ a.Entails b := by
  unfold weakenings Entails
  by_cases h : a.tail = .solc
  · simp only [h, if_true, List.mem_cons, List.not_mem_nil, or_false,
      true_and]
  · simp only [h, if_false, List.mem_cons, List.not_mem_nil, or_false, false_and]

theorem Assumptions.Entails.refl (a : Assumptions) : a.Entails a := Or.inl rfl

theorem TailMode.wrap_clean_of_solc {φ : Fml C []} {I : Fml C []} {pay : Bool}
    (h : ∀ σ : State C [], holdsC I pay σ φ) (σ : State C []) :
    holdsC I pay σ (TailMode.clean.wrap C φ) :=
  fun _ => h σ

/-- **What a record proves holds under every record it entails.** -/
theorem ValidA.weaken {I : Invariant C} {a b : Assumptions} {φ : Fml C []}
    (hab : a.Entails b) (h : ValidA I a φ) : ValidA I b φ := by
  rcases hab with rfl | ⟨ht, rfl⟩
  · exact h
  · refine ⟨h.1, ?_⟩
    have h2 : ValidC I φ a.callback := by
      have := h.2
      rw [ht] at this
      exact this
    exact TailMode.wrap_clean_of_solc h2

/-! ## Policies -/

/-- One reading of one option, as the CLI names it (`callback=noCallback`,
`tails=clean`, …; `docs/cli.md`). -/
inductive Atom where
  | callback (pay : Bool)
  | overflow (o : OverflowReading)
  | tail (t : TailMode)
  | order (o : OrderReading)
  | hash (h : HashReading)
  | zeroAddress (z : ZeroAddressReading)
  deriving DecidableEq, Repr

/-- The option an atom reads. -/
def Atom.key : Atom → Nat
  | .callback _ => 0
  | .overflow _ => 1
  | .tail _ => 2
  | .order _ => 3
  | .hash _ => 4
  | .zeroAddress _ => 5

/-- A record's readings, one atom per option. -/
def Assumptions.atoms (a : Assumptions) : List Atom :=
  [.callback a.callback, .overflow a.overflow, .tail a.tail, .order a.order,
    .hash a.hash, .zeroAddress a.zeroAddress]

/-- **A policy**: the readings required (one per option at most; the CLI
refuses two) and the readings denied. -/
structure Policy where
  require : List Atom := []
  deny : List Atom := []
  deriving DecidableEq, Repr

/-- The policy accepts a record: none of its readings is denied, and each
reading is the required one where its option has a requirement. -/
def Policy.allows (P : Policy) (a : Assumptions) : Bool :=
  a.atoms.all fun x => !(P.deny.contains x) && (P.require.all fun r => r.key != x.key || r == x)

/-- The policy admits a proof under `a` when it accepts a record `a`
entails. -/
def Policy.admits (P : Policy) (a : Assumptions) : Bool :=
  a.weakenings.any P.allows

theorem Policy.admits_iff (P : Policy) (a : Assumptions) :
    P.admits a = true ↔ ∃ b, a.Entails b ∧ P.allows b = true := by
  unfold admits
  rw [List.any_eq_true]
  exact ⟨fun ⟨b, hb, h⟩ => ⟨b, Assumptions.mem_weakenings.1 hb, h⟩,
    fun ⟨b, hb, h⟩ => ⟨b, Assumptions.mem_weakenings.2 hb, h⟩⟩

/-- **An admitted proof is a proof under an accepted record.** -/
theorem Policy.admits_sound {P : Policy} {I : Invariant C} {a : Assumptions} {φ : Fml C []}
    (hP : P.admits a = true) (h : ValidA I a φ) :
    ∃ b, P.allows b = true ∧ ValidA I b φ :=
  let ⟨b, hab, hb⟩ := (P.admits_iff a).1 hP
  ⟨b, hb, h.weaken hab⟩

/-- The verdict a report row gets under a policy. -/
inductive Verdict where
  | proved
  /-- Proved, but only under records the policy refuses. -/
  | refused
  | notProved
  deriving DecidableEq, Repr

/-- The row's verdict: a proof under `a` stays proved only when the policy
admits `a`. -/
def Policy.verdict (P : Policy) (a : Assumptions) (proved : Bool) : Verdict :=
  if proved then (if P.admits a then .proved else .refused) else .notProved

theorem Policy.verdict_proved_iff (P : Policy) (a : Assumptions) (proved : Bool) :
    P.verdict a proved = .proved ↔ proved = true ∧ P.admits a = true := by
  unfold verdict
  cases proved <;> cases P.admits a <;> decide

/-- **A row whose record entails no allowed record is never reported
proved.**  What a proved row does give is `admits_sound`. -/
theorem Policy.verdict_refused (P : Policy) (a : Assumptions) (proved : Bool)
    (h : ∀ b, a.Entails b → P.allows b = false) : P.verdict a proved ≠ .proved := by
  intro hv
  obtain ⟨b, hab, hb⟩ := (P.admits_iff a).1 ((P.verdict_proved_iff a proved).1 hv).2
  rw [h b hab] at hb
  exact Bool.false_ne_true hb

/-- **A proved row, as the report states it**: the record the proof is
under, the proof, and the policy's admission.  It holds under a record the
policy accepts (`ProvedRow.holds`). -/
structure ProvedRow (I : Invariant C) (P : Policy) (φ : Fml C []) where
  modes : Assumptions
  valid : ValidA I modes φ
  admitted : P.admits modes = true

theorem ProvedRow.holds {I : Invariant C} {P : Policy} {φ : Fml C []} (r : ProvedRow I P φ) :
    ∃ b, P.allows b = true ∧ ValidA I b φ :=
  Policy.admits_sound r.admitted r.valid

end Solidity
