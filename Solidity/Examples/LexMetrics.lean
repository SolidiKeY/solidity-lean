import Solidity.Semantics.LexMetrics
import Solidity.Examples.Termination

/-!
# Source tuple metrics and strict successful termination

The source loop resets its inner phase when clearing its outer phase. Its stored
uint-valued tuple decreases lexicographically even though the inner component
increases. Equal, increasing and undefined tuples cannot satisfy its certificate.
This is a successful-run proof, independent of modal acceptance of exhaustion.
-/
namespace Solidity.Examples.LexMetrics

open Solidity.Examples.Termination
open LoopMetrics

private def bit (i : Idx FlagCtx (.val .bool)) : Val Flags FlagCtx .uint :=
  .ternary (.simple (.local i)) (.simple (.lit 1 (by decide))) (.simple (.lit 0 (by decide)))

def metrics : LoopMetrics Flags FlagCtx 2 := .cons (bit (.there .here)) (.cons (bit .here) .nil)

def phaseValues (σ : State Flags FlagCtx) : NatTuple 2 :=
  ((Examples.Termination.rank σ).1, (Examples.Termination.rank σ).2, ())

/-- The source ternaries `outer ? 1 : 0` and `inner ? 1 : 0` retain their order. -/
theorem metrics_eval (σ : State Flags FlagCtx) : LoopMetrics.eval σ metrics = .ok (phaseValues σ) := by
  rcases σ with ⟨st, H, hp, ⟨i, o, ⟨⟩⟩, net, bal, tx⟩
  cases i <;> cases o <;> rfl

/-- The source phase loop has a strict certificate for its two-component rank. -/
theorem phase_certificate : Certificate metrics guard body (fun _ => True)
    (fun σ => outer σ = false ∧ inner σ = false) where
  condition := by
    intro σ _
    rcases σ with ⟨st, H, hp, ⟨i, o, ⟨⟩⟩, net, bal, tx⟩
    cases i <;> cases o
    · exact Or.inr rfl
    · exact Or.inl rfl
    · exact Or.inl rfl
    · exact Or.inl rfl
  defined := fun σ _ => ⟨phaseValues σ, metrics_eval σ⟩
  iteration := fun σ _ _ => ⟨⟨next σ, List.prefix_refl _⟩, body_run σ, trivial⟩
  decreases := by
    intro σ o before after _ hc ho hbefore hafter
    rw [body_run] at ho
    cases ho
    rw [metrics_eval] at hbefore hafter
    cases hbefore
    cases hafter
    rcases σ with ⟨st, H, hp, ⟨i, o, ⟨⟩⟩, net, bal, tx⟩
    cases i <;> cases o
    · cases hc
    · exact Prod.Lex.left _ _ (show (0 : Nat) < 1 by decide)
    · exact Prod.Lex.right _ (Prod.Lex.left _ _ (show (0 : Nat) < 1 by decide))
    · exact Prod.Lex.right _ (Prod.Lex.left _ _ (show (0 : Nat) < 1 by decide))
  exit := by
    intro σ _ hc
    rcases σ with ⟨st, H, hp, ⟨i, o, ⟨⟩⟩, net, bal, tx⟩
    cases i <;> cases o
    · exact ⟨rfl, rfl⟩
    · cases hc
    · cases hc
    · cases hc

/-- The source certificate retains the exact tuple on the annotated statement. -/
theorem phase_source_certificate : SourceCertificate (fun _ => True)
    (fun σ => outer σ = false ∧ inner σ = false)
    (.loop (.invLex (.simple (.bool true)) metrics false []) guard body) :=
  .lex phase_certificate

/-- The source-indexed certificate projects to a successful semantic run. -/
theorem phase_success (σ : State Flags FlagCtx) :
    ∃ o, Stmt.run σ (.loop (.invLex (.simple (.bool true)) metrics false []) guard body) = .ok o ∧
      outer o.st = false ∧ inner o.st = false :=
  phase_source_certificate.valid σ trivial

example : NatTuple.Lt (n := 2) ((0, 100, ()) : NatTuple 2) (1, 0, ()) :=
  Prod.Lex.left _ _ (Nat.zero_lt_succ 0)

example : ¬ NatTuple.Lt (n := 2) ((1, 0, ()) : NatTuple 2) (0, 100, ()) := by decide
example : ¬ NatTuple.Lt (n := 2) ((1, 100, ()) : NatTuple 2) (1, 100, ()) := NatTuple.irrefl _

def initial : State Flags FlagCtx :=
  (State.init Flags).push (t := .val .bool) true |>.push (t := .val .bool) false

def constantMetrics : LoopMetrics Flags FlagCtx 2 :=
  .cons (.simple (.lit 0 (by decide))) (.cons (.simple (.lit 0 (by decide))) .nil)

/-- `decreases (0, 0)` cannot certify this loop, although the loop itself terminates. -/
theorem equal_metrics_rejected : ¬ Certificate constantMetrics guard body (fun _ => True)
    (fun σ => outer σ = false ∧ inner σ = false) := by
  intro certificate
  have decreased := certificate.decreases initial ⟨next initial, List.prefix_refl _⟩
    (0, 0, ()) (0, 0, ()) trivial rfl (body_run initial) rfl rfl
  exact NatTuple.irrefl _ decreased

/-- Indexed elimination cannot retag the valid source certificate with `(0, 0)`. -/
theorem equal_source_rejected : ¬ SourceCertificate (fun _ => True)
    (fun σ => outer σ = false ∧ inner σ = false)
    (.loop (.invLex (.simple (.bool true)) constantMetrics false []) guard body) := by
  intro source
  cases source with
  | lex checked => exact equal_metrics_rejected checked

/-- The same two annotation choices are indistinguishable after execution is
applied, which is why the source checker must retain the indexed object. -/
theorem run_erases_metric_choice (σ : State Flags FlagCtx) :
    Stmt.run σ (.loop (.invLex (.simple (.bool true)) metrics false []) guard body) =
      Stmt.run σ (.loop (.invLex (.simple (.bool true)) constantMetrics false []) guard body) := rfl

def reversedMetrics : LoopMetrics Flags FlagCtx 2 :=
  .cons (bit .here) (.cons (bit (.there .here)) .nil)

/-- Swapping the source components makes the first phase transition increase. -/
theorem increasing_metrics_rejected : ¬ Certificate reversedMetrics guard body (fun _ => True)
    (fun σ => outer σ = false ∧ inner σ = false) := by
  intro certificate
  have decreased := certificate.decreases initial ⟨next initial, List.prefix_refl _⟩
    (0, 1, ()) (1, 0, ()) trivial rfl (body_run initial) rfl rfl
  exact (by decide : ¬ NatTuple.Lt (n := 2) (1, 0, ()) (0, 1, ())) decreased

/-- A source certificate cannot attach the checked proof to the increasing tuple. -/
theorem increasing_source_rejected : ¬ SourceCertificate (fun _ => True)
    (fun σ => outer σ = false ∧ inner σ = false)
    (.loop (.invLex (.simple (.bool true)) reversedMetrics false []) guard body) := by
  intro source
  cases source with
  | lex checked => exact increasing_metrics_rejected checked

def undefinedMetrics : LoopMetrics Flags FlagCtx 2 :=
  .cons (.binop .div rfl rfl (.simple (.lit 0 (by decide))) (.simple (.lit 0 (by decide))))
    (.cons (.simple (.lit 0 (by decide))) .nil)

/-- `decreases (0 / 0, 0)` fails explicit source-metric definedness. -/
theorem undefined_rejected : ¬ Certificate undefinedMetrics guard body (fun _ => True)
    (fun σ => outer σ = false ∧ inner σ = false) := by
  apply no_certificate_of_undefined (σ := (State.init Flags).push (t := .val .bool) true |>.push (t := .val .bool) false)
    trivial (error := .revert)
  rfl

/-- The indexed source object also refuses the undefined tuple annotation. -/
theorem undefined_source_rejected : ¬ SourceCertificate (fun _ => True)
    (fun σ => outer σ = false ∧ inner σ = false)
    (.loop (.invLex (.simple (.bool true)) undefinedMetrics false []) guard body) := by
  intro source
  cases source with
  | lex checked => exact undefined_rejected checked

/-- `assume(false)` cannot discharge the successful body-run requirement. -/
theorem exhausted_body_rejected : ¬ Certificate constantMetrics (.simple (.bool true))
    (.cons .assumeFalse (.nil : Prog Flags FlagCtx FlagCtx)) (fun _ => True) (fun _ => True) :=
  no_certificate_of_body_halt (σ := initial) trivial rfl (error := .exhausted) rfl

/-- The tuple is retained directly from NatSpec-style source annotations. -/
def sourceProgram := sol[Flags]{
  bool outer = true;
  bool inner = false;
  /// @custom:key invariant true
  /// @custom:key decreases (outer ? 1 : 0, inner ? 1 : 0)
  while (outer || inner) {
    if (inner) { inner = false; }
    else { outer = false; inner = true; }
  }
}

/-- Source elaboration preserves the exact typed metric tuple and scoped body. -/
theorem sourceProgram_shape : sourceProgram =
    Prog.cons (.declLocal .bool (.user "outer") (some (.simple (.bool true))))
      (.cons (.declLocal .bool (.user "inner") (some (.simple (.bool false))))
        (.cons (.loop (.invLex (.simple (.bool true)) metrics false []) guard body) .nil)) := by
  rfl

/-- The complete annotated source has an actual successful run, certified by
its stored tuple rather than by the modal erasure rule. -/
theorem sourceProgram_success (σ : State Flags []) :
    ∃ o, Prog.run σ sourceProgram = .ok o ∧ outer o.st = false ∧ inner o.st = false := by
  let afterOuter := σ.push (t := .val .bool) true
  let afterInner := afterOuter.push (t := .val .bool) false
  have first : Stmt.run σ (.declLocal .bool (.user "outer") (some (.simple (.bool true)))) =
      .ok ⟨afterOuter, List.prefix_refl _⟩ := rfl
  have second : Stmt.run afterOuter
      (.declLocal .bool (.user "inner") (some (.simple (.bool false)))) =
      .ok ⟨afterInner, List.prefix_refl _⟩ := rfl
  obtain ⟨o, ho, hpost⟩ := phase_source_certificate.valid afterInner trivial
  refine ⟨o, ?_, hpost⟩
  rw [sourceProgram_shape, Prog.run_cons_ok first, Prog.run_cons_ok second,
    Prog.run_cons_ok ho, Prog.run_nil]
  rfl

end Solidity.Examples.LexMetrics

/-- info: 'Solidity.Examples.LexMetrics.phase_success' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Solidity.Examples.LexMetrics.phase_success
/-- info: 'Solidity.Examples.LexMetrics.sourceProgram_success' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Solidity.Examples.LexMetrics.sourceProgram_success
