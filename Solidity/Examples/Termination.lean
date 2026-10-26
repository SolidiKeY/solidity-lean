import Solidity.Semantics.Termination
import Solidity.Syntax.Splice

/-!
# Successful termination of a scoped Solidity loop

The two boolean phases use a lexicographic measure. Clearing the outer phase
resets the inner phase from false to true, so the inner component increases;
the pair nevertheless decreases. These proofs concern `Stmt.run` itself,
without modal acceptance of exhaustion or a finite unwinding bound.
-/

namespace Solidity.Examples.Termination

/-- The mathematical counters of `if (j == 0) { i--; j = cap; } else { j--; }`. -/
def resetBody (cap : Nat) : Nat × Nat → TRes (Nat × Nat)
  | (i, 0) => .ok (i - 1, cap)
  | (i, j + 1) => .ok (i, j)

def resetGuard : Nat × Nat → TRes Bool
  | (0, 0) => .ok false
  | _ => .ok true

/-- An arbitrary second-counter reset is permitted by lexicographic decrease.
There is no constant bound on the second component in the theorem's hypotheses. -/
theorem arbitrary_reset_terminates (cap : Nat) (σ : Nat × Nat) :
    TLoop.run (resetBody cap) resetGuard σ = .ok (0, 0) := by
  apply TLoop.run_lex (I := fun _ => True) (Q := fun r => r = .ok (0, 0)) id
  · intro _ _ _ _
    trivial
  · intro ⟨i, j⟩ τ _ he
    cases i <;> cases j
    · cases he
    · cases he
      exact Prod.Lex.right 0 (Nat.lt_succ_self _)
    · cases he
      exact Prod.Lex.left _ _ (Nat.lt_succ_self _)
    · cases he
      exact Prod.Lex.right _ (Nat.lt_succ_self _)
  · intro ⟨i, j⟩ r _ he
    cases i <;> cases j
    · cases he
      rfl
    · cases he
    · cases he
    · cases he
  · trivial

def Flags : Contract := contract!{ }
abbrev FlagCtx : Ctx := [.val .bool, .val .bool]

def inner (σ : State Flags FlagCtx) : Bool := TEnv.get .here σ.env
def outer (σ : State Flags FlagCtx) : Bool := TEnv.get (.there .here) σ.env

def guard : Val Flags FlagCtx .bool :=
  .binop .or rfl rfl (.simple (.local (.there .here))) (.simple (.local .here))

/-- `if (inner) { inner = false; } else { outer = false; inner = true; }` -/
def body : Prog Flags FlagCtx FlagCtx :=
  .cons (.ite (.simple (.local .here))
    (.cons (.assignLocal .here (.simple (.bool false))) .nil)
    (.cons (.assignLocal (.there .here) (.simple (.bool false)))
      (.cons (.assignLocal .here (.simple (.bool true))) .nil))) .nil

/-- The same loop elaborated directly from Solidity source. -/
def sourceProgram := sol[Flags]{
  bool outer = true;
  bool inner = false;
  while (outer || inner) {
    if (inner) { inner = false; }
    else { outer = false; inner = true; }
  }
}

/-- Source elaboration emits exactly the scoped loop proved below. -/
theorem sourceProgram_shape : sourceProgram =
    Prog.cons (.declLocal .bool (.user "outer") (some (.simple (.bool true))))
      (.cons (.declLocal .bool (.user "inner") (some (.simple (.bool false))))
        (.cons (.loop .auto guard body) .nil)) := by
  rfl

def next (σ : State Flags FlagCtx) : State Flags FlagCtx :=
  { σ with env := if inner σ then (false, σ.env.2) else (true, false, σ.env.2.2) }

def rank (σ : State Flags FlagCtx) : Nat × Nat :=
  (if outer σ then 1 else 0, if inner σ then 1 else 0)

/-- The source phase body runs to its next typed state without changing the heap. -/
theorem body_run (σ : State Flags FlagCtx) :
    Prog.run σ body = .ok ⟨next σ, List.prefix_refl _⟩ := by
  rcases σ with ⟨st, H, hp, ⟨i, o, ⟨⟩⟩, net, bal, tx⟩
  cases i <;> cases o <;> rfl

/-- Each live phase turn decreases the pair, including the inner-phase reset. -/
theorem rank_decreases (σ : State Flags FlagCtx) (hc : guard.evalT σ = .ok true) :
    Prod.Lex Nat.lt Nat.lt (rank (next σ)) (rank σ) := by
  rcases σ with ⟨st, H, hp, ⟨i, o, ⟨⟩⟩, net, bal, tx⟩
  cases i <;> cases o
  · cases hc
  · exact Prod.Lex.left 1 0 (show (0 : Nat) < 1 by decide)
  · exact Prod.Lex.right 0 (show (0 : Nat) < 1 by decide)
  · exact Prod.Lex.right 1 (show (0 : Nat) < 1 by decide)

/-- `while (outer || inner) { if (inner) inner = false;
else { outer = false; inner = true; } }` returns with both flags false,
from every typed initial state, even though the inner phase can increase. -/
theorem flags_terminate (σ : State Flags FlagCtx) :
    ∃ o, Stmt.run σ (.loop .auto guard body) = .ok o ∧
      outer o.st = false ∧ inner o.st = false := by
  apply Stmt.loop_terminates_of_wellFounded σ .auto guard body
    TLoop.lexNat_wellFounded rank (I := fun _ => True)
    (G := fun τ => outer τ = false ∧ inner τ = false) trivial
  · intro τ _
    rcases τ with ⟨st, H, hp, ⟨i, o, ⟨⟩⟩, net, bal, tx⟩
    cases i <;> cases o
    · exact Or.inr rfl
    · exact Or.inl rfl
    · exact Or.inl rfl
    · exact Or.inl rfl
  · intro τ _ hc
    refine ⟨⟨next τ, List.prefix_refl _⟩, body_run τ, trivial, ?_⟩
    exact rank_decreases τ hc
  · intro τ _ hc
    rcases τ with ⟨st, H, hp, ⟨i, o, ⟨⟩⟩, net, bal, tx⟩
    cases i <;> cases o
    · exact ⟨rfl, rfl⟩
    · cases hc
    · cases hc
    · cases hc

/-- The complete source block, including its two declarations, successfully
terminates from every initial typed state with both phase flags false. -/
theorem sourceProgram_terminates (σ : State Flags []) :
    ∃ o, Prog.run σ sourceProgram = .ok o ∧ outer o.st = false ∧ inner o.st = false := by
  let afterOuter := σ.push (t := .val .bool) true
  let afterInner := afterOuter.push (t := .val .bool) false
  have first : Stmt.run σ (.declLocal .bool (.user "outer") (some (.simple (.bool true)))) =
      .ok ⟨afterOuter, List.prefix_refl _⟩ := rfl
  have second : Stmt.run afterOuter
      (.declLocal .bool (.user "inner") (some (.simple (.bool false)))) =
      .ok ⟨afterInner, List.prefix_refl _⟩ := rfl
  obtain ⟨o, ho, hpost⟩ := flags_terminate afterInner
  refine ⟨o, ?_, hpost⟩
  rw [sourceProgram_shape, Prog.run_cons_ok first, Prog.run_cons_ok second,
    Prog.run_cons_ok ho, Prog.run_nil]
  rfl

/-- An unchanged state cannot be assigned a genuinely decreasing measure. -/
theorem unchanged_not_decreasing {α β : Type} {rel : β → β → Prop}
    (wf : WellFounded rel) (measure : α → β) (σ : α) : ¬ rel (measure σ) (measure σ) := by
  have irrefl : ∀ b, ¬ rel b b := fun b =>
    wf.induction (C := fun b => ¬ rel b b) b (fun b ih self => ih b self self)
  exact irrefl (measure σ)

/-- `while (true) { }` has no finite finishing iteration. -/
theorem spin_iter {α : Type} (σ : α) (n : Nat) :
    TLoop.iterN (fun τ : α => .ok τ) (fun _ => .ok true) n σ = .inl σ := by
  induction n with
  | zero => rfl
  | succ n ih => exact ih

/-- `while (true) { }` actually diverges, rather than ending by exhaustion. -/
theorem spin_diverges {α : Type} (σ : α) :
    TLoop.run (fun τ : α => .ok τ) (fun _ => .ok true) σ = .error .diverge := by
  have never : ¬ ∃ r n, TLoop.iterN (fun τ : α => .ok τ) (fun _ => .ok true) n σ = .inr r := by
    rintro ⟨r, n, hn⟩
    rw [spin_iter] at hn
    cases hn
  simp only [TLoop.run, never, dite_false]

/-- A scoped Solidity `while (true) { }` has the same divergent outcome. -/
theorem scoped_spin_diverges (σ : State Flags FlagCtx) :
    Stmt.run σ (.loop .auto (.simple (.bool true)) (.nil : Prog Flags FlagCtx FlagCtx)) =
      .error .diverge := by
  rw [Stmt.run_loop]
  exact spin_diverges (⟨σ, List.prefix_refl _⟩ : Out Flags σ.H FlagCtx)

/-- `while (true) { assume(false); }` is exhausted by its actual first turn. -/
theorem exhausted_loop (σ : State Flags FlagCtx) :
    Stmt.run σ (.loop .auto (.simple (.bool true))
      (.cons .assumeFalse (.nil : Prog Flags FlagCtx FlagCtx))) = .error .exhausted := by
  rw [Stmt.run_loop]
  apply TLoop.run_of_iterN (n := 1)
  rfl

/-- An exhausted scoped loop is not a successful-termination witness. -/
theorem exhausted_loop_not_success (σ : State Flags FlagCtx) :
    ¬ ∃ o, Stmt.run σ (.loop .auto (.simple (.bool true))
      (.cons .assumeFalse (.nil : Prog Flags FlagCtx FlagCtx))) = .ok o := by
  rw [exhausted_loop]
  rintro ⟨_, h⟩
  cases h

/-- `while (true) { revert(); }` halts finitely with a revert. -/
theorem reverted_loop (σ : State Flags FlagCtx) :
    Stmt.run σ (.loop .auto (.simple (.bool true))
      (.cons .revert (.nil : Prog Flags FlagCtx FlagCtx))) = .error .revert := by
  rw [Stmt.run_loop]
  apply TLoop.run_of_iterN (n := 1)
  rfl

/-- A reverting scoped loop is not a successful-termination witness. -/
theorem reverted_loop_not_success (σ : State Flags FlagCtx) :
    ¬ ∃ o, Stmt.run σ (.loop .auto (.simple (.bool true))
      (.cons .revert (.nil : Prog Flags FlagCtx FlagCtx))) = .ok o := by
  rw [reverted_loop]
  rintro ⟨_, h⟩
  cases h

end Solidity.Examples.Termination

/-- info: 'Solidity.Examples.Termination.flags_terminate' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Solidity.Examples.Termination.flags_terminate
/-- info: 'Solidity.Examples.Termination.sourceProgram_terminates' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Solidity.Examples.Termination.sourceProgram_terminates
