import Solidity.Calculus.LinearDecision

/-! A small proof-producing propositional fast path before the derivative walk.
It only introduces implications, projects conjunctions and reuses an identical
hypothesis. Failure retains the complete arithmetic decision unchanged. -/
namespace Solidity.Linear

/-- Conjuncts are available independently after assuming their conjunction. -/
def AFml.hypotheses : AFml → List AFml
  | .and a b => a.hypotheses ++ b.hypotheses
  | a => [a]

theorem AFml.hypotheses_hold (x : Nat → Nat) (a : AFml) :
    a.holds x → ∀ b ∈ a.hypotheses, b.holds x := by
  induction a with
  | and a b ha hb =>
    intro h c hc
    rcases List.mem_append.mp hc with hc | hc
    · exact ha h.1 c hc
    · exact hb h.2 c hc
  | _ =>
    intro h b hb
    simp only [hypotheses, List.mem_singleton] at hb
    subst b
    exact h

/-- Every successful result carries its proof. The bound limits only this
cheap fast path; it is never interpreted as a false arithmetic verdict. -/
def AFml.hypProof? : (fuel : Nat) → (hs : List AFml) → (f : AFml) →
    Option (PLift (∀ x, (∀ a ∈ hs, a.holds x) → f.holds x))
  | 0, _, _ => none
  | n + 1, hs, f =>
    if hf : f ∈ hs then some ⟨fun _ h => h f hf⟩ else
    match f with
    | .tt => some ⟨fun _ _ => True.intro⟩
    | .and a b => do
      let ha ← hypProof? n hs a
      let hb ← hypProof? n hs b
      pure ⟨fun x h => ⟨ha.down x h, hb.down x h⟩⟩
    | .imp a b => do
      let hb ← hypProof? n (a.hypotheses ++ hs) b
      pure ⟨fun x h ha => hb.down x (fun c hc =>
        (List.mem_append.mp hc).elim
          (fun hc => a.hypotheses_hold x ha c hc) (fun hc => h c hc))⟩
    | _ => none

/-- A closed, certified propositional proof, or no answer. -/
def AFml.hypVerify? (f : AFml) : Option (PLift f.Valid) := do
  let h ← hypProof? 128 [] f
  pure ⟨fun x => h.down x (fun _ h => nomatch h)⟩

/-- info: 'Solidity.Linear.AFml.hypotheses_hold' depends on axioms: [propext] -/
#guard_msgs in #print axioms AFml.hypotheses_hold

end Solidity.Linear
