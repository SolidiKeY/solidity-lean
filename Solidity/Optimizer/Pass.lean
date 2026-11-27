import Solidity.Syntax.Scoped
import Solidity.Yul.Syntax

namespace Solidity.Optimizer

universe u

abbrev Pass (Prog : Type u) := Prog → Prog

def Preserves {Prog : Type u} (Related : Prog → Prog → Prop) (pass : Pass Prog) : Prop :=
  ∀ p, Related p (pass p)

structure Validator {Prog : Type u} (Related : Prog → Prog → Prop) where
  validate : Prog → Prog → Bool
  sound : ∀ p q, validate p q = true → Related p q

theorem validate_sound {Prog : Type u} {Related : Prog → Prog → Prop}
    (validator : Validator Related) {p q : Prog}
    (accepted : validator.validate p q = true) : Related p q :=
  validator.sound p q accepted

def Pass.comp {Prog : Type u} (first second : Pass Prog) : Pass Prog :=
  fun p => second (first p)

theorem Preserves.comp {Prog : Type u} {Related : Prog → Prog → Prop}
    (trans : ∀ {p q r}, Related p q → Related q r → Related p r)
    {first second : Pass Prog} (hfirst : Preserves Related first)
    (hsecond : Preserves Related second) : Preserves Related (first.comp second) :=
  fun p => trans (hfirst p) (hsecond (first p))

def validated {Prog : Type u} {Related : Prog → Prog → Prop}
    (validator : Validator Related) (proposal : Pass Prog) : Pass Prog :=
  fun p => if validator.validate p (proposal p) then proposal p else p

theorem validated_of_rejected {Prog : Type u} {Related : Prog → Prog → Prop}
    (validator : Validator Related) (proposal : Pass Prog) (p : Prog)
    (rejected : validator.validate p (proposal p) = false) :
    validated validator proposal p = p := by
  simp [validated, rejected]

theorem validated_of_accepted {Prog : Type u} {Related : Prog → Prog → Prop}
    (validator : Validator Related) (proposal : Pass Prog) (p : Prog)
    (accepted : validator.validate p (proposal p) = true) :
    validated validator proposal p = proposal p := by
  simp [validated, accepted]

theorem validated_preserves {Prog : Type u} {Related : Prog → Prog → Prop}
    (refl : ∀ p, Related p p) (validator : Validator Related) (proposal : Pass Prog) :
    Preserves Related (validated validator proposal) :=
  fun p => match h : validator.validate p (proposal p) with
    | true =>
      Eq.mpr (congrArg (Related p) (validated_of_accepted validator proposal p h))
        (validator.sound p (proposal p) h)
    | false =>
      Eq.mpr (congrArg (Related p) (validated_of_rejected validator proposal p h)) (refl p)

namespace Lowering
abbrev Pass (C : Contract) (Γ Δ : Ctx) := Optimizer.Pass (Solidity.Prog C Γ Δ)
end Lowering

namespace Yul
abbrev Pass (F : List Solidity.Yul.Sig) (X : List Solidity.Yul.ExternalType)
    (c : Solidity.Yul.Control) (n : Nat) := Optimizer.Pass (Solidity.Yul.Stmt F X c n)
end Yul

end Solidity.Optimizer
