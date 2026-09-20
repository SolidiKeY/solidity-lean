import Solidity.Calculus.RewriteSoundness

/-!
# Proof-level if-then-else split (KeY `ifthenelse_split`)

The rewrite calculus is deliberately stuck on `Stmt.ite` with a simple
non-literal condition — exactly the residual `ifElseUnfold`
produces. KeY continues at that point with the sequent rule
`ifthenelse_split` (`ifThenElseRules.key`), which splits the proof into
a `#phi TRUE` and a `#phi FALSE` goal. A single-successor `BlockStep`
cannot produce two goals (plan decision D3), so the Lean analogue is a
theorem about `SolidityJudgment.Holds`, proved once against the
executable semantics:

* `SolidityJudgment.ite_split` — the general split, given the
  condition's evaluation;
* `SolidityJudgment.ite_split_pure` — the KeY shape for pure (simple)
  conditions, both goals stated over the *initial* state;
* `SolidityJudgment.ite_same_branches` — KeY
  `ifthenelse_same_branches`, a corollary (a `RuleName` port would
  overlap `ifElseTrue`/`ifElseFalse` and break uniqueness).
-/

namespace Solidity

open Semantics

/-- KeY `ifthenelse_split`: an ite-headed judgment holds iff the branch
selected by the condition's value, spliced onto the remaining block,
holds in the post-evaluation state. Box and diamond are handled
uniformly — both `check` outcomes transport unchanged through the
bind. -/
theorem SolidityJudgment.ite_split
    {m : SolidityModality} {c : WrappedExpr} {thn els rest : Block}
    {post : WrappedExpr} {s0 s1 : State} {b : Bool}
    (heval : evalValue s0 c = .ok (s1, .bool b)) :
    (SolidityJudgment.mk ⟨m, Stmt.ite c thn els :: rest⟩ post).Holds s0 ↔
      ((b = true ->
          (SolidityJudgment.mk ⟨m, thn ++ rest⟩ post).Holds s1) ∧
        (b = false ->
          (SolidityJudgment.mk ⟨m, els ++ rest⟩ post).Holds s1)) := by
  unfold SolidityJudgment.Holds SolidityJudgment.check
  rw [execBlock, execStmt, heval]
  cases b with
  | true =>
      simp only [RuleSoundness.resOk_bind, ← Semantics.execBlock_append]
      simp
  | false =>
      simp only [RuleSoundness.resOk_bind, ← Semantics.execBlock_append]
      simp

/-- The KeY shape: for a pure condition (in particular any simple one)
the split leaves the state untouched, so both goals live over the
initial state. -/
theorem SolidityJudgment.ite_split_pure
    {m : SolidityModality} {c : WrappedExpr} {thn els rest : Block}
    {post : WrappedExpr} {s0 t : State} {b : Bool}
    (hpure : RuleSoundness.pureExpr c = true)
    (heval : evalValue s0 c = .ok (t, .bool b)) :
    (SolidityJudgment.mk ⟨m, Stmt.ite c thn els :: rest⟩ post).Holds s0 ↔
      ((b = true ->
          (SolidityJudgment.mk ⟨m, thn ++ rest⟩ post).Holds s0) ∧
        (b = false ->
          (SolidityJudgment.mk ⟨m, els ++ rest⟩ post).Holds s0)) := by
  have hts : t = s0 := RuleSoundness.evalValue_pure hpure heval
  subst hts
  exact SolidityJudgment.ite_split heval

/-- KeY `ifthenelse_same_branches`: identical branches collapse the
conditional. -/
theorem SolidityJudgment.ite_same_branches
    {m : SolidityModality} {c : WrappedExpr} {thn rest : Block}
    {post : WrappedExpr} {s0 s1 : State} {b : Bool}
    (heval : evalValue s0 c = .ok (s1, .bool b)) :
    (SolidityJudgment.mk ⟨m, Stmt.ite c thn thn :: rest⟩ post).Holds s0 ↔
      (SolidityJudgment.mk ⟨m, thn ++ rest⟩ post).Holds s1 := by
  rw [SolidityJudgment.ite_split heval]
  cases b <;> simp

/-! Sanity: on literal conditions the split reproduces exactly the
residuals of `ifElseTrue`/`ifElseFalse`. -/

example {m : SolidityModality} {thn els rest : Block}
    {post : WrappedExpr} {s0 : State} :
    (SolidityJudgment.mk ⟨m, Stmt.ite (WrappedExpr.bool true) thn els ::
        rest⟩ post).Holds s0 ↔
      (SolidityJudgment.mk ⟨m, thn ++ rest⟩ post).Holds s0 := by
  rw [SolidityJudgment.ite_split (b := true) (s1 := s0) (by rw [evalValue])]
  simp

example {m : SolidityModality} {thn els rest : Block}
    {post : WrappedExpr} {s0 : State} :
    (SolidityJudgment.mk ⟨m, Stmt.ite (WrappedExpr.bool false) thn els ::
        rest⟩ post).Holds s0 ↔
      (SolidityJudgment.mk ⟨m, els ++ rest⟩ post).Holds s0 := by
  rw [SolidityJudgment.ite_split (b := false) (s1 := s0) (by rw [evalValue])]
  simp

end Solidity
