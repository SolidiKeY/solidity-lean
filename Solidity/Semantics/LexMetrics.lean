import Solidity.Semantics.Termination

/-!
# Strict loop certificates for typed lexicographic metrics

`LoopMetrics C Γ n` retains every component at its Solidity type and scope.
Its semantic values are length-indexed tuples of natural numbers, ordered
lexicographically using `Prod.Lex`. A later component may increase when an
earlier one decreases; the tuple is never packed into a bounded Solidity word.

`Certificate` requires every invariant head to define every source component,
a successful body step preserving the invariant, and a strictly decreasing
pair of defined metric values. `SourceCertificate` retains the actual statement
as its type index, including the exact tuple stored in the source annotation.
Its validity theorem concludes an actual successful `Stmt.run`. Successful-run
propositions alone do not retain annotations, because execution erases them.
A modal proof that accepts exhaustion is not such a certificate. The semantic
invariant and terminal postcondition remain explicit proof parameters.

These are sufficient conditions: the tuple must be defined at every invariant
head and decrease after every successful body, including its final turn. This
is not a claim of automatic Dafny VC parity for break/return or partial metrics.
-/
namespace Solidity

namespace LoopMetrics

/-- A tuple with its arity in its type, without bounded-word packing. -/
def NatTuple : Nat → Type
  | 0 => Unit
  | n + 1 => Nat × NatTuple n

namespace NatTuple

def zero : (n : Nat) → NatTuple n
  | 0 => ()
  | n + 1 => (0, zero n)

def Lt : {n : Nat} → NatTuple n → NatTuple n → Prop
  | 0, _, _ => False
  | n + 1, a, b => Prod.Lex Nat.lt (@Lt n) a b

/-- Lexicographic order is well founded at every fixed arity. -/
theorem wellFounded : (n : Nat) → WellFounded (@Lt n)
  | 0 => ⟨fun a => .intro a fun _ h => h.elim⟩
  | n + 1 => (Prod.lex Nat.lt_wfRel ⟨@Lt n, wellFounded n⟩).wf

def decLt : (n : Nat) → DecidableRel (@Lt n)
  | 0, _, _ => isFalse (fun h => h)
  | n + 1, (a, x), (b, y) =>
    if hab : a < b then isTrue (.left x y hab)
    else if heq : a = b then
      match decLt n x y with
      | isTrue hxy => isTrue (by subst b; exact .right a hxy)
      | isFalse hxy => isFalse (by
          intro h
          cases h with
          | left _ _ h => exact hab h
          | right _ h => exact hxy h)
    else isFalse (by
      intro h
      cases h with
      | left _ _ h => exact hab h
      | right _ _ => exact heq rfl)

instance (n : Nat) : DecidableRel (@Lt n) := decLt n

/-- A source tuple cannot strictly decrease to itself. -/
theorem irrefl : {n : Nat} → (x : NatTuple n) → ¬ Lt x x
  | 0, _ => fun h => h
  | n + 1, x => by
    intro h
    cases h with
    | left _ _ h => exact Nat.lt_irrefl _ h
    | right _ h => exact irrefl _ h

end NatTuple

variable {C : Contract} {Γ Γ₁ : Ctx} {n : Nat}

/-- Read all source components at their typed state, preserving evaluation errors. -/
def eval (σ : State C Γ) : {n : Nat} → LoopMetrics C Γ n → TRes (NatTuple n)
  | 0, .nil => .ok ()
  | _ + 1, .cons head tail => do
    let value ← head.evalT σ
    let rest ← eval σ tail
    pure (value.1.toNat, rest)

/-- This total helper is used only under the certificate's explicit definedness
premise; its default cannot justify an undefined source metric. -/
def rank (metrics : LoopMetrics C Γ n) (σ : State C Γ) : NatTuple n :=
  match eval σ metrics with
  | .ok values => values
  | .error _ => NatTuple.zero n

theorem rank_of_eval (metrics : LoopMetrics C Γ n) (σ : State C Γ) {values : NatTuple n}
    (h : eval σ metrics = .ok values) : rank metrics σ = values := by
  simp only [rank, h]

/-- A certificate is indexed by the actual condition and scoped body. All
invariant heads must define every metric, including a false-guard exit head. -/
structure Certificate (metrics : LoopMetrics C Γ n) (c : Val C Γ .bool)
    (body : Prog C Γ Γ₁) (I G : State C Γ → Prop) : Prop where
  condition : ∀ σ, I σ → c.evalT σ = .ok true ∨ c.evalT σ = .ok false
  defined : ∀ σ, I σ → ∃ values, eval σ metrics = .ok values
  iteration : ∀ σ, I σ → c.evalT σ = .ok true →
    ∃ o, Prog.run σ body = .ok o ∧ I (o.st.drop body.ext)
  decreases : ∀ σ (o : Out C σ.H Γ₁) before after,
    I σ → c.evalT σ = .ok true → Prog.run σ body = .ok o →
    eval σ metrics = .ok before → eval (o.st.drop body.ext) metrics = .ok after →
    NatTuple.Lt after before
  exit : ∀ σ, I σ → c.evalT σ = .ok false → G σ

/-- Explicit metric definedness and decrease prove actual successful execution. -/
theorem Certificate.valid {metrics : LoopMetrics C Γ n} {c : Val C Γ .bool}
    {body : Prog C Γ Γ₁} {I G : State C Γ → Prop}
    (certificate : Certificate metrics c body I G) (σ : State C Γ) (hI : I σ)
    (a : LoopAnn C Γ) : ∃ o, Stmt.run σ (.loop a c body) = .ok o ∧ G o.st := by
  apply Stmt.loop_terminates_of_wellFounded σ a c body (NatTuple.wellFounded n)
    (rank metrics) hI certificate.condition
  · intro τ hI hc
    obtain ⟨o, ho, hI'⟩ := certificate.iteration τ hI hc
    obtain ⟨before, hbefore⟩ := certificate.defined τ hI
    obtain ⟨after, hafter⟩ := certificate.defined (o.st.drop body.ext) hI'
    refine ⟨o, ho, hI', ?_⟩
    rw [rank_of_eval metrics τ hbefore, rank_of_eval metrics (o.st.drop body.ext) hafter]
    exact certificate.decreases τ o before after hI hc ho hbefore hafter
  · exact certificate.exit

/-- An undefined tuple on even one invariant head rules out this certificate. -/
theorem no_certificate_of_undefined {metrics : LoopMetrics C Γ n} {c : Val C Γ .bool}
    {body : Prog C Γ Γ₁} {I G : State C Γ → Prop} {σ : State C Γ} {error : THalt}
    (hI : I σ) (he : eval σ metrics = .error error) : ¬ Certificate metrics c body I G := by
  intro certificate
  obtain ⟨values, hvalues⟩ := certificate.defined σ hI
  rw [he] at hvalues
  cases hvalues

/-- An actual halting body cannot satisfy a successful-iteration certificate,
including when the existing modal policy would accept its exhaustion. -/
theorem no_certificate_of_body_halt {metrics : LoopMetrics C Γ n} {c : Val C Γ .bool}
    {body : Prog C Γ Γ₁} {I G : State C Γ → Prop} {σ : State C Γ} {error : THalt}
    (hI : I σ) (hc : c.evalT σ = .ok true) (he : Prog.run σ body = .error error) :
    ¬ Certificate metrics c body I G := by
  intro certificate
  obtain ⟨o, ho, _⟩ := certificate.iteration σ hI hc
  rw [he] at ho
  cases ho

/-- A semantic successful-run helper for a loop carrying this tuple. Execution
erases annotations, so its result alone cannot establish that a source tuple was
checked; use `SourceCertificate` to retain that syntactic claim. The semantic
invariant `I` remains explicit and need not equal the annotation's invariant. -/
theorem Certificate.validLex {metrics : LoopMetrics C Γ (n + 2)} {c : Val C Γ .bool}
    {body : Prog C Γ Γ₁} {I G : State C Γ → Prop}
    (certificate : Certificate metrics c body I G) (σ : State C Γ) (hI : I σ)
    (inv : Val C Γ .bool) (brk : Bool) (qs : List (LoopQ C Γ)) :
    ∃ o, Stmt.run σ (.loop (.invLex inv metrics brk qs) c body) = .ok o ∧ G o.st :=
  certificate.valid σ hI (.invLex inv metrics brk qs)

/-- A checked source loop, indexed by its actual syntax rather than by the
annotation-erasing run. Its only constructor retains the certificate for the
exact stored metric tuple, condition and body. The semantic invariant and post
remain explicit parameters; no equivalence to annotation clauses is assumed. -/
inductive SourceCertificate (I G : State C Γ → Prop) : Stmt C Γ Γ → Prop where
  | lex {n : Nat} {metrics : LoopMetrics C Γ (n + 2)}
      {inv c : Val C Γ .bool} {brk : Bool} {qs : List (LoopQ C Γ)} {Γb : Ctx}
      {body : Prog C Γ Γb} (checked : Certificate metrics c body I G) :
      SourceCertificate I G (.loop (.invLex inv metrics brk qs) c body)

/-- Projecting a source certificate forgets its syntactic evidence and produces
the successful-run proposition for the indexed statement. -/
theorem SourceCertificate.valid {I G : State C Γ → Prop} {s : Stmt C Γ Γ}
    (source : SourceCertificate I G s) (σ : State C Γ) (hI : I σ) :
    ∃ o, Stmt.run σ s = .ok o ∧ G o.st := by
  cases source with
  | lex checked => exact checked.valid σ hI .auto

/-- Unlike a successful-run proposition, the indexed source certificate recovers
the check of the exact tuple stored in this loop. -/
theorem SourceCertificate.checks {metrics : LoopMetrics C Γ (n + 2)}
    {inv c : Val C Γ .bool} {brk : Bool} {qs : List (LoopQ C Γ)}
    {body : Prog C Γ Γ₁} {I G : State C Γ → Prop}
    (source : SourceCertificate I G (.loop (.invLex inv metrics brk qs) c body)) :
    Certificate metrics c body I G := by
  cases source with
  | lex checked => exact checked

end LoopMetrics

end Solidity

/-- info: 'Solidity.LoopMetrics.Certificate.valid' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Solidity.LoopMetrics.Certificate.valid
/-- info: 'Solidity.LoopMetrics.Certificate.validLex' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Solidity.LoopMetrics.Certificate.validLex
/-- info: 'Solidity.LoopMetrics.SourceCertificate.valid' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Solidity.LoopMetrics.SourceCertificate.valid
