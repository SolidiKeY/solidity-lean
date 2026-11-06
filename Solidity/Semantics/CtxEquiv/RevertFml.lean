import Solidity.Calculus.Logic
import Solidity.Semantics.CtxEquiv.Basic

/-!
# Revert data in formulas (S6.2)

`docs/semantic-gaps.md` ("Revert data in formulas") records that no formula
reads the data a run halts with.  This module adds the reading as a third
outcome of a modality, over the scoped formulas of `Calculus/Fml.lean`,
without changing `Fml` (whose constructors every rule, printer and closer
matches):

`RFml.revModal m P κ φ ψ`, printed `dl{ [ P ] φ ↯ ψ }` (box) or
`dl{ ⟨ P ⟩ φ ↯ ψ }` (diamond), runs `P` and its frames with the typed run
(`Prog.runFrames`, as `Fml.modal` does) and asks

- of a normal end: `φ` in the state it ends in;
- of a revert with data `d` (`THalt.revertData?`: a `revert` without data
  is the empty data, `revertWith d` is `d`): the data predicate `ψ` of `d`;
- of any other halt: what the modality asks of it already (`onTHalt`: the
  box accepts divergence and exhaustion, the diamond exhaustion only), and
  never a panic.

So `[ P ] φ ↯ _` is `[ P ] φ` (`revModal_box_any`), and
`⟨ P ⟩ φ ↯ ⊥` is `⟨ P ⟩ φ` (`revModal_diamond_none`): the new modality is a
conservative extension.  `⟨ P ⟩ false ↯ ψ` says that `P` reverts with data
satisfying `ψ`, or exhausts.

**Data predicates** (`DataPred`, decidable by `DataPred.eval`): any data,
exact bytes, `Error(m)` (`encodeError`), any decodable `Error(string)`,
`Panic(c)` (`encodePanic`), a selector prefix, and their Boolean
combinations.  They name the encodings of `Solidity/RevertBytes.lean`, so a
formula's data and the run's agree by definition.

**What the run computes.**  The modality reads the data the typed run
returns.  The elaborator keeps a revert's data where a `catch` can read it
(a self-call's callee) and for a literal reason written as bytes
(`revert(hex"…")`, the solc import's form); elsewhere `revert("m")` and
`require(c, "m")` elaborate to a data-free `revert` (`docs/semantic-gaps.md`,
"Revert data", *Where data is computed*), so a top-level `[ revert("m"); ]`
reverts with empty data in the model, and so does a failed index, `pop` or
checked operation outside `checked { }`; `assert` panics, which no `↯`
formula accepts (`revModal_not_panic`).  This is less data than solc returns
(`docs/solc-alignment.md`, "Revert data read in formulas").
`Examples/Tactics/RevertFormulas.lean` pins the readings.

**At the ABI boundary.**  `THalt.toOutcome?` maps a halt with revert data
to the `Outcome.revert` that would carry it, and `DataPred.outcome` reads a
predicate there; a panic has no outcome here.  No theorem yet relates a
typed run's halt to a session's outcome in `Basic.lean`.
-/

namespace Solidity

open Solidity (Modality)

/-! ## Revert data of a halt -/

/-- The data a halt reverts with: `some []` for a data-free `revert`, `some d`
for `revertWith d`, `none` for a panic, divergence or exhaustion. -/
def THalt.revertData? : THalt → Option (List UInt8)
  | .revert => some []
  | .revertWith d => some d
  | _ => none

/-- `THalt.ofData d` reverts with exactly `d`. -/
@[simp] theorem THalt.revertData?_ofData (d : List UInt8) : (THalt.ofData d).revertData? = some d := by
  cases d <;> rfl

/-- The outcome a reverting halt shows at the ABI boundary. -/
def THalt.toOutcome? (h : THalt) : Option Roadmap.Outcome :=
  h.revertData?.map Roadmap.Outcome.revert

/-! ## Data predicates -/

/-- A predicate on revert data, written in formulas. -/
inductive DataPred where
  /-- Any data. -/
  | any
  /-- Exactly these bytes. -/
  | bytes (d : List UInt8)
  /-- `Error(m)`'s ABI encoding, the data of `revert("m")`. -/
  | error (m : List UInt8)
  /-- Some `Error(string)` that decodes (`decodeError`). -/
  | errorAny
  /-- `Panic(c)`'s ABI encoding. -/
  | panic (c : Nat)
  /-- Data starting with these bytes (a selector). -/
  | selector (s : List UInt8)
  | not (ψ : DataPred)
  | and (ψ χ : DataPred)
  | or (ψ χ : DataPred)
  deriving Repr, DecidableEq, Inhabited

/-- No data. -/
abbrev DataPred.none : DataPred := .not .any

/-- Whether data satisfies a predicate. -/
def DataPred.eval : DataPred → List UInt8 → Bool
  | .any, _ => true
  | .bytes e, d => d == e
  | .error m, d => d == Semantics.encodeError m
  | .errorAny, d => (Semantics.decodeError d).isSome
  | .panic c, d => d == Semantics.encodePanic c
  | .selector s, d => s.isPrefixOf d
  | .not ψ, d => !ψ.eval d
  | .and ψ χ, d => ψ.eval d && χ.eval d
  | .or ψ χ, d => ψ.eval d || χ.eval d

/-- A data predicate read on an ABI outcome: the revert's data satisfies it;
a success does not. -/
def DataPred.outcome (ψ : DataPred) : Roadmap.Outcome → Prop
  | .revert d => ψ.eval d = true
  | .success _ => False

theorem DataPred.outcome_toOutcome {ψ : DataPred} {h : THalt} {d : List UInt8}
    (hd : h.revertData? = some d) : ∀ o, h.toOutcome? = some o → (ψ.outcome o ↔ ψ.eval d = true) := by
  intro o ho
  simp only [THalt.toOutcome?, hd, Option.map_some, Option.some.injEq] at ho
  subst ho
  exact Iff.rfl

/-! ## The revert-reading modality -/

variable {C : Contract}

/-- `p` after a typed run under `m`, reading revert data with `ψ`. -/
def _root_.Solidity.Modality.afterRunRev {α : Type} (m : Modality) (p : α → Prop) (ψ : DataPred)
    (r : TRes α) : Prop :=
  (match r with
    | .ok a => p a
    | .error e => match e.revertData? with
      | some d => ψ.eval d = true
      | none => m.onTHalt e) ∧ r ≠ .error .panic

/-- Formulas reading revert data: a scoped formula, the revert-reading
modality, and their Boolean combinations. -/
inductive RFml (C : Contract) : Ctx → Type where
  | fml {Γ : Ctx} (φ : Fml C Γ) : RFml C Γ
  /-- `[ P κ ] φ ↯ ψ` or `⟨ P κ ⟩ φ ↯ ψ`. -/
  | revModal {Γ Γ₁ Γ₀ : Ctx} (m : Modality) (P : Prog C Γ Γ₁) (κ : Frames C Γ₁ Γ₀)
      (φ : Fml C Γ₀) (ψ : DataPred) : RFml C Γ
  | not {Γ : Ctx} (χ : RFml C Γ) : RFml C Γ
  | and {Γ : Ctx} (χ ξ : RFml C Γ) : RFml C Γ
  | imp {Γ : Ctx} (χ ξ : RFml C Γ) : RFml C Γ

/-- The revert-reading modality of a modal formula, with its postcondition;
any other formula reads no program and stays as it is.  What the notation
`dl{ φ ↯ ψ }` builds. -/
def RFml.ofModal {Γ : Ctx} : Fml C Γ → DataPred → RFml C Γ
  | .modal m P κ φ, ψ => .revModal m P κ φ ψ
  | φ, _ => .fml φ

/-- **Whether a revert-reading formula holds in a typed state.** -/
def RFml.holds : {Γ : Ctx} → State C Γ → RFml C Γ → Prop
  | _, σ, .fml φ => Solidity.holds σ φ
  | _, σ, .revModal m P κ φ ψ => m.afterRunRev (Solidity.holds · φ) ψ (Prog.runFrames σ P κ)
  | _, σ, .not χ => ¬ RFml.holds σ χ
  | _, σ, .and χ ξ => RFml.holds σ χ ∧ RFml.holds σ ξ
  | _, σ, .imp χ ξ => RFml.holds σ χ → RFml.holds σ ξ

/-- Valid: true in every typed state of the empty context. -/
def RFml.Valid (χ : RFml C []) : Prop := ∀ σ : State C [], RFml.holds σ χ

/-! ## Conservativity -/

/-- **A box that accepts any data is the box.** -/
theorem revModal_box_any {Γ Γ₁ Γ₀ : Ctx} (σ : State C Γ) (P : Prog C Γ Γ₁)
    (κ : Frames C Γ₁ Γ₀) (φ : Fml C Γ₀) :
    RFml.holds σ (.revModal .box P κ φ .any) ↔ Solidity.holds σ (.modal .box P κ φ) := by
  rw [RFml.holds, Solidity.holds]
  unfold Modality.afterRunRev Modality.afterRunTR
  cases Prog.runFrames σ P κ with
  | ok a => exact Iff.rfl
  | error e =>
    cases e <;> simp only [THalt.revertData?, DataPred.eval, Modality.onTHalt]

/-- **A diamond that accepts no data is the diamond.** -/
theorem revModal_diamond_none {Γ Γ₁ Γ₀ : Ctx} (σ : State C Γ) (P : Prog C Γ Γ₁)
    (κ : Frames C Γ₁ Γ₀) (φ : Fml C Γ₀) :
    RFml.holds σ (.revModal .diamond P κ φ .none) ↔ Solidity.holds σ (.modal .diamond P κ φ) := by
  rw [RFml.holds, Solidity.holds]
  unfold Modality.afterRunRev Modality.afterRunTR
  cases Prog.runFrames σ P κ with
  | ok a => exact Iff.rfl
  | error e =>
    cases e <;> simp only [THalt.revertData?, DataPred.eval, Modality.onTHalt, Bool.not_true,
      Bool.false_eq_true, reduceCtorEq]

/-- `ofModal` of a modal formula is the revert-reading modality. -/
theorem RFml.ofModal_modal {Γ Γ₁ Γ₀ : Ctx} (m : Modality) (P : Prog C Γ Γ₁) (κ : Frames C Γ₁ Γ₀)
    (φ : Fml C Γ₀) (ψ : DataPred) : RFml.ofModal (.modal m P κ φ) ψ = .revModal m P κ φ ψ := rfl

/-! ## Runs that revert -/

/-- **A run reverting with `d`**: the modality holds exactly when `ψ` accepts
`d`, under either modality. -/
theorem revModal_of_revert {Γ Γ₁ Γ₀ : Ctx} {σ : State C Γ} {P : Prog C Γ Γ₁}
    {κ : Frames C Γ₁ Γ₀} {d : List UInt8} (m : Modality) (φ : Fml C Γ₀) (ψ : DataPred)
    (h : Prog.runFrames σ P κ = .error (THalt.ofData d)) :
    RFml.holds σ (.revModal m P κ φ ψ) ↔ ψ.eval d = true := by
  rw [RFml.holds]
  unfold Modality.afterRunRev
  rw [h]
  cases d with
  | nil => exact ⟨fun h => h.1, fun h => ⟨h, fun e => nomatch e⟩⟩
  | cons b bs => exact ⟨fun h => h.1, fun h => ⟨h, fun e => nomatch e⟩⟩

/-- A run that ends normally reads no data: the modality is the
postcondition. -/
theorem revModal_of_ok {Γ Γ₁ Γ₀ : Ctx} {σ : State C Γ} {P : Prog C Γ Γ₁}
    {κ : Frames C Γ₁ Γ₀} {τ : State C Γ₀} (m : Modality) (φ : Fml C Γ₀) (ψ : DataPred)
    (h : Prog.runFrames σ P κ = .ok τ) :
    RFml.holds σ (.revModal m P κ φ ψ) ↔ Solidity.holds τ φ := by
  rw [RFml.holds]
  unfold Modality.afterRunRev
  rw [h]
  exact ⟨fun h => h.1, fun h => ⟨h, fun e => nomatch e⟩⟩

/-- `revert` with literal bytes runs to a revert with them. -/
theorem runFrames_revertBytes {Γ Γ₁ Γ₀ : Ctx} (σ : State C Γ) (bs : List UInt8)
    (P : Prog C Γ Γ₁) (κ : Frames C Γ₁ Γ₀) :
    Prog.runFrames σ (.cons (.revertData [.bytes bs]) P) κ = .error (THalt.ofData bs) := by
  have h : Prog.runFrames σ (.cons (.revertData [.bytes bs]) P) κ =
      .error (THalt.ofData [bs].flatten) := rfl
  rw [h, List.flatten_singleton]

/-- **`revert(bytes)` satisfies exactly the data predicates its bytes do.** -/
theorem revModal_revertBytes {Γ Γ₁ Γ₀ : Ctx} (σ : State C Γ) (bs : List UInt8) (m : Modality)
    (P : Prog C Γ Γ₁) (κ : Frames C Γ₁ Γ₀) (φ : Fml C Γ₀) (ψ : DataPred) :
    RFml.holds σ (.revModal m (.cons (.revertData [.bytes bs]) P) κ φ ψ) ↔ ψ.eval bs = true :=
  revModal_of_revert m φ ψ (runFrames_revertBytes σ bs P κ)

/-- **A panic satisfies no revert-reading formula**, under either modality. -/
theorem revModal_not_panic {Γ Γ₁ Γ₀ : Ctx} {σ : State C Γ} {P : Prog C Γ Γ₁}
    {κ : Frames C Γ₁ Γ₀} (m : Modality) (φ : Fml C Γ₀) (ψ : DataPred)
    (h : Prog.runFrames σ P κ = .error .panic) : ¬ RFml.holds σ (.revModal m P κ φ ψ) := by
  rw [RFml.holds]
  unfold Modality.afterRunRev
  rw [h]
  exact fun hh => hh.2 rfl

/-- A data-free `revert` reverts with the empty data. -/
theorem revModal_revert {Γ Γ₁ Γ₀ : Ctx} (σ : State C Γ) (m : Modality)
    (P : Prog C Γ Γ₁) (κ : Frames C Γ₁ Γ₀) (φ : Fml C Γ₀) (ψ : DataPred) :
    RFml.holds σ (.revModal m (.cons .revert P) κ φ ψ) ↔ ψ.eval [] = true :=
  revModal_of_revert m φ ψ rfl

end Solidity
