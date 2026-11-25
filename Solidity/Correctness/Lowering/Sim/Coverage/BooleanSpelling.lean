import Solidity.Correctness.Lowering.Sim.Coverage.BooleanDomain
import Solidity.Correctness.Lowering.Total.Spells

/-! Raw-syntax decoding of the H1361 domain toward
`Solidity.Goals.loweringBySimulation`, using the existing decoder's spelling
relation. This is not Source typing or resolved-program decoder completeness. -/
namespace Solidity.Correctness.Lowering.Sim.Coverage.BooleanDomain

variable {names : List String}

/-- Every expression in the domain has an existing-decoder spelling. -/
theorem Expr.spells : ∀ {e}, Expr names e → ∃ t, Total.Spells.Expr e t
  | _, .name _ => ⟨_, .name _⟩
  | _, .bool _ => ⟨_, .bool _⟩
  | _, .assign _ h => by
    obtain ⟨t, ht⟩ := h.spells
    exact ⟨_, .assign (.name _) ht⟩
  | _, .not h => by
    obtain ⟨t, ht⟩ := h.spells
    exact ⟨_, .not ht⟩
  | _, .and a b | _, .or a b | _, .eq a b => by
    obtain ⟨a', ha⟩ := a.spells
    obtain ⟨b', hb⟩ := b.spells
    exact ⟨_, .binop rfl ha hb rfl⟩

mutual
  /-- Statement spelling preserves the loop-control context. -/
  theorem Stmt.spells : ∀ {inside s}, Stmt names inside s →
      ∃ t, Total.Spells.Stmt ⟨inside, false⟩ s t
    | _, _, .assign _ h => by
      obtain ⟨t, ht⟩ := h.spells
      exact ⟨_, .simple (.assign (.name _) ht)⟩
    | _, _, .block h => by
      obtain ⟨t, ht⟩ := h.spells
      exact ⟨_, .block ht⟩
    | _, _, @Stmt.ite _ inside c a b hc ha hb => by
      obtain ⟨c', hc⟩ := hc.spells
      obtain ⟨a', ha⟩ := ha.spells
      obtain ⟨b', hb⟩ := hb.spells
      cases b with
      | nil => exact ⟨_, .ite hc ha⟩
      | cons _ _ => exact ⟨_, .iteElse hc ha hb⟩
    | _, _, .whileLoop hc hs => by
      obtain ⟨c', hc⟩ := hc.spells
      obtain ⟨s', hs⟩ := hs.spells
      exact ⟨_, .whileLoop _ hc hs⟩
    | _, _, .brk => ⟨_, .brk⟩
    | _, _, .cont => ⟨_, .cont⟩

  /-- Sequence spelling has no length or nesting bound. -/
  theorem Stmts.spells : ∀ {inside ss}, Stmts names inside ss →
      ∃ t, Total.Spells.Items ⟨inside, false⟩ ss t
    | _, _, .nil => ⟨_, .nil⟩
    | _, _, .cons h hs => by
      obtain ⟨t, ht⟩ := h.spells
      obtain ⟨ts, hts⟩ := hs.spells
      exact ⟨_, .stmt ht hts⟩
end

/-- The existing raw-syntax decoder succeeds on domain sequences. -/
theorem Stmts.syntax_decoded {inside ss} (h : Stmts names inside ss) :
    ∃ t, Total.Decode.items ⟨inside, false⟩ ss = some t := by
  obtain ⟨t, ht⟩ := h.spells
  exact ⟨t, ht.decode⟩

/-- Syntax decoding for the whole approved input boundary. Source inference
and resolution, required by `Total.Decode.decode`, are still separate. -/
theorem Input.syntax_decoded {b u} (h : Input b u) :
    ∃ t, Total.Decode.items .body b.input.raw = some t := by
  obtain ⟨_, _, _, _, names, c, ss, _, raw, hc, hs⟩ := h
  rw [raw]
  exact (Stmts.cons (Stmt.whileLoop hc hs) Stmts.nil).syntax_decoded

end Solidity.Correctness.Lowering.Sim.Coverage.BooleanDomain
