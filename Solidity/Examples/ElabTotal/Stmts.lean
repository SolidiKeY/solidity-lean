import Solidity.Correctness.Elab.Total

/-!
# Checks: the block's two equations

`elabStmtsP` is total (`elabStmtsPWith` at the knot's `elabStmtP`), so a
block of two statements unfolds by `elabStmtsP_cons` twice and
`elabStmtsP_nil` once, with no `native_decide`; the per-statement producer
`elabStmtP` stays opaque (partial). The elaborator's run on a concrete
two-statement block agrees with the unfolded form, state included.
(`#print axioms`: `propext` for the two equations, `propext, Quot.sound` for
the `runFrom` form; not pinned here, the pin inventory lies outside this module.)
-/

namespace Solidity.Examples.ElabTotal.Stmts

open Solidity

variable [FreshNames]

/-- Two statements: the head, the second, the empty rest, concatenated. -/
theorem elabStmtsP_two (C : Contract) (s₁ s₂ : RawStmt) :
    elabStmtsP C [s₁, s₂] = (do
      let P ← elabStmtP C s₁
      let Q ← (do
        let P' ← elabStmtP C s₂
        let Q' ← pure []
        pure (P' ++ Q'))
      pure (P ++ Q)) := by
  rw [elabStmtsP_cons, elabStmtsP_cons, elabStmtsP_nil]

/-- The same unfolding through `runFrom`, the form downstream proofs read. -/
theorem elabStmtsP_two_runFrom (C : Contract) (s₁ s₂ : RawStmt)
    (sc : ElabScope) (st : ECtx × Nat) :
    (elabStmtsP C [s₁, s₂]).runFrom sc st =
      (do
        let P ← elabStmtP C s₁
        let Q ← elabStmtP C s₂
        pure (P ++ Q ++ [])).runFrom sc st := by
  rw [elabStmtsP_cons, elabStmtsP_cons, elabStmtsP_nil]
  simp only [bind_pure_comp, map_pure, bind_pure, List.append_nil]

private def C0 : Contract := { vars := [] }

/-- `uint x = 1; x = 2;`. -/
private def s₁ : RawStmt := .decl (.named "uint") "x" (some (.num 1))
private def s₂ : RawStmt := .assign (.name "x") (.num 2)

/-- The run's statement count and final locals, or its error. -/
private def summary (x : ElabM (SProg C0)) : Option (Nat × List String × Nat) :=
  ((x.runFrom { funs := [] } ([], 1)).map fun (P, (Γ, k)) => (P.length, Γ.map (·.1), k)).toOption

-- The block elaborates, and agrees with its statements run one after the other.
#guard summary (elabStmtsP C0 [s₁, s₂]) == some (2, ["x"], 1)
#guard summary (elabStmtsP C0 [s₁, s₂]) ==
  summary (do let P ← elabStmtP C0 s₁; let Q ← elabStmtP C0 s₂; pure (P ++ Q))
#guard summary (elabStmtsP C0 []) == some (0, [], 1)

/-- The closed statement arms are exactly the solutions of their direct equations. -/
example (C : Contract) (rc : ElabRec C) (g : RawStmt → ElabM (SProg C)) :
    (g = elabStmt1With C {rc with elabStmt1 := g}) ↔ g = elabStmt1ClosedWith C rc := by
  constructor
  · exact elabStmt1ClosedWith_unique C rc g
  · intro h; subst g; exact elabStmt1ClosedWith_eq C rc

example (C : Contract) (rc : ElabRec C) (g : RawStmt → ElabM (SProg C)) :
    (g = elabStmtPWith C {rc with elabStmtP := g}) ↔ g = elabStmtPClosedWith C rc := by
  constructor
  · exact elabStmtPClosedWith_unique C rc g
  · intro h; subst g; exact elabStmtPClosedWith_eq C rc

/-- Even a failing seed cannot change either closed arm's equation. -/
example (C : Contract) (rc : ElabRec C) (err : String) :
    elabStmt1ClosedWith C {rc with elabStmt1 := fun _ => throw err} =
      elabStmt1With C {rc with elabStmt1 := elabStmt1ClosedWith C rc} := by
  exact (elabStmt1ClosedWith_independent C rc _).trans (elabStmt1ClosedWith_eq C rc)

example (C : Contract) (rc : ElabRec C) (err : String) :
    elabStmtPClosedWith C {rc with elabStmtP := fun _ => throw err} =
      elabStmtPWith C {rc with elabStmtP := elabStmtPClosedWith C rc} := by
  exact (elabStmtPClosedWith_independent C rc _).trans (elabStmtPClosedWith_eq C rc)

/-- Nested arrays retain both dimensions and advance the width-lookup path twice. -/
example (ws : List (String × Nat)) (E : Ty) (k : String) :
    rawTyW ws (.ref (.array (.ref (.array E)))) k =
      .array (.array (rawTyW ws E ((k ++ "[]") ++ "[]"))) := by
  rw [rawTyW_array, rawTyW_array]


-- The public ABI equations use only propext and Quot.sound;
-- adding choice, sorry, or another axiom breaks these checked guards.
/-- info: 'Solidity.abiSizeGen_eq' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms abiSizeGen_eq

/-- info: 'Solidity.abiSeqSizeGen_eq' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms abiSeqSizeGen_eq

/-- info: 'Solidity.abiTupleSizeGen_eq' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms abiTupleSizeGen_eq

/-- info: 'Solidity.abiWriteGen_eq' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms abiWriteGen_eq

/-- info: 'Solidity.abiSeqWriteGen_eq' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms abiSeqWriteGen_eq

/-- info: 'Solidity.abiTupleWriteGen_eq' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms abiTupleWriteGen_eq

/-- info: 'Solidity.abiReadGen_eq' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms abiReadGen_eq

/-- info: 'Solidity.abiSeqReadGen_eq' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms abiSeqReadGen_eq

/-- info: 'Solidity.abiSeqSizeGen_result_name' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms abiSeqSizeGen_result_name

end Solidity.Examples.ElabTotal.Stmts

/-- info: 'Solidity.ElabHoist.hoistFuel_stable' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms Solidity.ElabHoist.hoistFuel_stable

/-- info: 'Solidity.ElabHoist.hoistStructural_eq' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms Solidity.ElabHoist.hoistStructural_eq

/-- info: 'Solidity.ElabHoist.hoistStructural_unique' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms Solidity.ElabHoist.hoistStructural_unique

/-- info: 'Solidity.ElabHoist.hoist_structural_eq' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms Solidity.ElabHoist.hoist_structural_eq

/-- info: 'Solidity.ElabHoist.namedClosure_eq' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms Solidity.ElabHoist.namedClosure_eq

/-- info: 'Solidity.ElabHoist.namedStructural_named' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms Solidity.ElabHoist.namedStructural_named

/-- info: 'Solidity.ElabHoist.namedStructural_eq' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms Solidity.ElabHoist.namedStructural_eq

/-- info: 'Solidity.ElabHoist.namedStructural_unique' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms Solidity.ElabHoist.namedStructural_unique

/-- info: 'Solidity.ElabHoist.hoist_named_eq' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms Solidity.ElabHoist.hoist_named_eq

/-- info: 'Solidity.ElabCallArgsGood.hoistCallArgsWith_preserves' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms Solidity.ElabCallArgsGood.hoistCallArgsWith_preserves

/-- info: 'Solidity.ElabCallArgsGood.hoistCallArgsWith_nil' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms Solidity.ElabCallArgsGood.hoistCallArgsWith_nil
