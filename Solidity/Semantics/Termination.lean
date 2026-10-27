import Solidity.Semantics.Run

/-!
# Finite loops from well-founded measures

The measure decreases at each continuing turn of the actual typed loop.
An explicit finite `iterN` witness precedes the theorem about `TLoop.run`:
neither divergence nor exhaustion is a successful termination witness.
The caller chooses the allowed terminal outcomes. Natural and lexicographic
measures are special cases; no scalar bound on the number of turns is assumed.

`Stmt.loop_terminates_of_wellFounded` applies the same result to scoped Solidity
statements. Its heads retain the initial heap extension in `Out`; its measure
reads their typed states. Loop annotations and the modal treatment of exhaustion
play no part in this separate successful-termination claim.
-/

namespace Solidity

namespace TLoop

variable {α β : Type} {body : α → TRes α} {c : α → TRes Bool}

/-- A decreasing well-founded measure supplies a finite, permitted outcome. -/
theorem finite_of_wellFounded {I : α → Prop} {Q : TRes α → Prop}
    {rel : β → β → Prop} (wf : WellFounded rel) (rank : α → β)
    (keep : ∀ σ τ, I σ → step body c σ = .inl τ → I τ)
    (decreases : ∀ σ τ, I σ → step body c σ = .inl τ → rel (rank τ) (rank σ))
    (stop : ∀ σ r, I σ → step body c σ = .inr r → Q r)
    {σ : α} (hI : I σ) : ∃ n r, iterN body c n σ = .inr r ∧ Q r := by
  have finite : ∀ b s, rank s = b → I s → ∃ n r, iterN body c n s = .inr r ∧ Q r := by
    intro b
    induction b using wf.induction with
    | h b ih =>
      intro s hv hs
      cases he : step body c s with
      | inr r => exact ⟨1, r, by simp only [iterN, he], stop s r hs he⟩
      | inl t =>
        obtain ⟨n, r, hn, hQ⟩ :=
          ih (rank t) (hv ▸ decreases s t hs he) t rfl (keep s t hs he)
        exact ⟨n + 1, r, by simp only [iterN, he]; exact hn, hQ⟩
  exact finite (rank σ) σ rfl hI

/-- The actual loop has an allowed result, with no accepted-divergence premise. -/
theorem run_wellFounded {I : α → Prop} {Q : TRes α → Prop}
    {rel : β → β → Prop} (wf : WellFounded rel) (rank : α → β)
    (keep : ∀ σ τ, I σ → step body c σ = .inl τ → I τ)
    (decreases : ∀ σ τ, I σ → step body c σ = .inl τ → rel (rank τ) (rank σ))
    (stop : ∀ σ r, I σ → step body c σ = .inr r → Q r)
    {σ : α} (hI : I σ) : Q (run body c σ) := by
  obtain ⟨n, r, hn, hQ⟩ := finite_of_wellFounded wf rank keep decreases stop hI
  rw [run_of_iterN hn]
  exact hQ

/-- A natural-valued measure is a special case of well-founded decrease. -/
theorem run_measure {I : α → Prop} {Q : TRes α → Prop} (rank : α → Nat)
    (keep : ∀ σ τ, I σ → step body c σ = .inl τ → I τ)
    (decreases : ∀ σ τ, I σ → step body c σ = .inl τ → rank τ < rank σ)
    (stop : ∀ σ r, I σ → step body c σ = .inr r → Q r)
    {σ : α} (hI : I σ) : Q (run body c σ) :=
  run_wellFounded Nat.lt_wfRel.wf rank keep decreases stop hI

/-- The standard lexicographic order on two natural components is well founded. -/
theorem lexNat_wellFounded : WellFounded (Prod.Lex Nat.lt Nat.lt) :=
  (Prod.lex Nat.lt_wfRel Nat.lt_wfRel).wf

/-- Lexicographic decrease permits an arbitrary reset of the second component
when the first decreases. Larger tuples use nested products and `run_wellFounded`. -/
theorem run_lex {I : α → Prop} {Q : TRes α → Prop} (rank : α → Nat × Nat)
    (keep : ∀ σ τ, I σ → step body c σ = .inl τ → I τ)
    (decreases : ∀ σ τ, I σ → step body c σ = .inl τ →
      Prod.Lex Nat.lt Nat.lt (rank τ) (rank σ))
    (stop : ∀ σ r, I σ → step body c σ = .inr r → Q r)
    {σ : α} (hI : I σ) : Q (run body c σ) :=
  run_wellFounded lexNat_wellFounded rank keep decreases stop hI

end TLoop

/-- Successful termination of an actual scoped `while`. Every live body run
returns in the invariant with a smaller measure; the false guard gives the post.
The result is an actual `Out`, so exhaustion is never a successful witness. -/
theorem Stmt.loop_terminates_of_wellFounded {C : Contract} {Γ Γ₁ : Ctx} {β : Type}
    (σ : State C Γ) (a : LoopAnn C Γ) (c : Val C Γ .bool) (body : Prog C Γ Γ₁)
    {rel : β → β → Prop} (wf : WellFounded rel) (rank : State C Γ → β)
    {I G : State C Γ → Prop} (hI : I σ)
    (condition : ∀ τ, I τ → c.evalT τ = .ok true ∨ c.evalT τ = .ok false)
    (iteration : ∀ τ, I τ → c.evalT τ = .ok true →
      ∃ o, Prog.run τ body = .ok o ∧ I (o.st.drop body.ext) ∧
        rel (rank (o.st.drop body.ext)) (rank τ))
    (exit : ∀ τ, I τ → c.evalT τ = .ok false → G τ) :
    ∃ o, Stmt.run σ (.loop a c body) = .ok o ∧ G o.st := by
  let B : Out C σ.H Γ → TRes (Out C σ.H Γ) := fun o =>
    (Prog.run o.st body).map fun o' => ⟨o'.st.drop body.ext, o.ext.trans o'.ext⟩
  let K : Out C σ.H Γ → TRes Bool := fun o => c.evalT o.st
  have done : ∃ o, TLoop.run B K ⟨σ, List.prefix_refl _⟩ = .ok o ∧ G o.st := by
    apply TLoop.run_wellFounded (I := fun o : Out C σ.H Γ => I o.st)
      (Q := fun r => ∃ o, r = .ok o ∧ G o.st) wf (fun o => rank o.st)
    · intro o o' ho he
      rcases condition o.st ho with hc | hc
      · obtain ⟨p, hp, hI', _⟩ := iteration o.st ho hc
        simp only [TLoop.step, K, hc, B, hp, Except.map] at he
        cases he
        exact hI'
      · simp only [TLoop.step, K, hc] at he
        cases he
    · intro o o' ho he
      rcases condition o.st ho with hc | hc
      · obtain ⟨p, hp, _, hdec⟩ := iteration o.st ho hc
        simp only [TLoop.step, K, hc, B, hp, Except.map] at he
        cases he
        exact hdec
      · simp only [TLoop.step, K, hc] at he
        cases he
    · intro o r ho he
      rcases condition o.st ho with hc | hc
      · obtain ⟨p, hp, _, _⟩ := iteration o.st ho hc
        simp only [TLoop.step, K, hc, B, hp, Except.map] at he
        cases he
      · simp only [TLoop.step, K, hc] at he
        cases he
        exact ⟨o, rfl, exit o.st ho hc⟩
    · exact hI
  exact done

end Solidity

/-- info: 'Solidity.TLoop.finite_of_wellFounded' depends on axioms: [propext] -/
#guard_msgs in #print axioms Solidity.TLoop.finite_of_wellFounded
/-- info: 'Solidity.TLoop.run_wellFounded' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Solidity.TLoop.run_wellFounded
/-- info: 'Solidity.Stmt.loop_terminates_of_wellFounded' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Solidity.Stmt.loop_terminates_of_wellFounded
