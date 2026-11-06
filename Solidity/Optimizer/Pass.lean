import Solidity.Syntax.Scoped
import Solidity.Yul.Syntax

/-!
# Typed optimizer pass and translation-validation boundary

A pass preserves the intrinsic program indices. The observation relation is an
explicit argument: this module does not define or weaken the shared D6 contract.
A validator is executable code paired with a kernel proof of acceptance soundness;
an untrusted proposal cannot supply that proof itself.
-/
namespace Solidity.Optimizer

universe u

/-- Total optimizer at a fixed intrinsic program type. -/
abbrev Pass (Prog : Type u) := Prog → Prog

/-- Every input is related to the actual output; no input-domain exclusion. -/
def Preserves {Prog : Type u} (Related : Prog → Prog → Prop) (pass : Pass Prog) : Prop :=
  ∀ p, Related p (pass p)

/-- Executable translation validation. Soundness is a proof, not an assumption
added to each accepted program's public correctness theorem. -/
structure Validator {Prog : Type u} (Related : Prog → Prog → Prop) where
  validate : Prog → Prog → Bool
  sound : ∀ p q, validate p q = true → Related p q

/-- The only trusted bridge from validator acceptance to preservation. -/
theorem validate_sound {Prog : Type u} {Related : Prog → Prog → Prop}
    (validator : Validator Related) {p q : Prog}
    (accepted : validator.validate p q = true) : Related p q :=
  validator.sound p q accepted

/-- Execute passes in pipeline order. -/
def Pass.comp {Prog : Type u} (first second : Pass Prog) : Pass Prog :=
  fun p => second (first p)

/-- Composition needs exactly transitivity of the supplied observation relation. -/
theorem Preserves.comp {Prog : Type u} {Related : Prog → Prog → Prop}
    (trans : ∀ {p q r}, Related p q → Related q r → Related p r)
    {first second : Pass Prog} (hfirst : Preserves Related first)
    (hsecond : Preserves Related second) : Preserves Related (first.comp second) :=
  fun p => trans (hfirst p) (hsecond (first p))

/-- Rejecting a proposal returns the original program. -/
def validated {Prog : Type u} {Related : Prog → Prog → Prop}
    (validator : Validator Related) (proposal : Pass Prog) : Pass Prog :=
  fun p => if validator.validate p (proposal p) then proposal p else p

/-- A sound validator makes an arbitrary proposal safe, including rejection. -/
theorem validated_preserves {Prog : Type u} {Related : Prog → Prog → Prop}
    (refl : ∀ p, Related p p) (validator : Validator Related) (proposal : Pass Prog) :
    Preserves Related (validated validator proposal) := by
  intro p
  unfold validated
  split
  next accepted => exact validator.sound p (proposal p) accepted
  next _ => exact refl p

namespace Lowering
/-- Existing intrinsically typed lowering IR, preserving both contexts. -/
abbrev Pass (C : Contract) (Γ Δ : Ctx) := Optimizer.Pass (Solidity.Prog C Γ Δ)
end Lowering

namespace Yul
/-- Existing Yul syntax, preserving signatures, externals, control and locals. -/
abbrev Pass (F : List Solidity.Yul.Sig) (X : List Solidity.Yul.ExternalType)
    (c : Solidity.Yul.Control) (n : Nat) := Optimizer.Pass (Solidity.Yul.Stmt F X c n)
end Yul

end Solidity.Optimizer
