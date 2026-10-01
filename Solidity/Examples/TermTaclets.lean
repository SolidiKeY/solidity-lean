import Solidity.Calculus.Rewrite

/-!
# Term taclets on a sequent

`rw [findOnSave]` on a sequent applies the term taclet
`TermTaclet.findOnSave` (`Calculus/TermTaclets.lean`) by `Proves.rewrite`:
its paths are found in the sequent and its side conditions closed on them.
`sol_rw [find_delAt_same, …]` builds a rule from the Theory's own lemmas
instead (`TermTaclet.theory`, `Calculus/TheoryRewrite.lean`).
-/

namespace Solidity.Examples.TermTaclets

open Solidity Semantics Theory Theory.StValue Proves

variable {C : Contract}


/-- `alice.age = 42; alice.name = 7;` read back at `alice.age`: the frame
steps over the second write, `findOnSave` reads the first, and the goal
`42 ≐ 42` closes.  The taclets are named bare: their paths come from the
sequent, and `diverges` and `hasSeg` close on them. -/
example {R : RuleSet} :
    Proves R ([] : List (Hyp C))
      (.eq (.find (.save (.save .storage (.field (.root "alice") "age") (.val (.lit (.int 42))))
          (.field (.root "alice") "name") (.val (.lit (.int 7))))
        (.field (.root "alice") "age")) (.lit (.int 42))) := by
  rw [findOnSaveFrame, findOnSave]
  exact Proves.eqClose

/-- `alice.age = 42; delete alice.age;` reads `0` at `alice.age`. -/
example {R : RuleSet} :
    Proves R ([] : List (Hyp C))
      (.eq (.find (.delAt (.save .storage (.field (.root "alice") "age") (.val (.lit (.int 42))))
          (.field (.root "alice") "age")) (.field (.root "alice") "age")) (.lit (.int 0))) := by
  sol_rw [findOnDelAtSave]
  exact Proves.eqClose

/-- The same, with the Theory's own lemmas named instead of `findOnDelAtSave`:
the read of the delete (`find_delAt_same`), of the write under it
(`find_copyTo_same`, `copyVal`) and the reset of the word (`delValueDefault`,
`primDefault`), one step, since `delValue (findSt …)` alone is no term. -/
example {R : RuleSet} :
    Proves R ([] : List (Hyp C))
      (.eq (.find (.delAt (.save .storage (.field (.root "alice") "age") (.val (.lit (.int 42))))
          (.field (.root "alice") "age")) (.field (.root "alice") "age")) (.lit (.int 0))) := by
  sol_rw [find_delAt_same, find_copyTo_same, copyVal, delValueDefault, primDefault]
  exact Proves.eqClose

/-- A Theory frame lemma: a read off the deleted path, `alice` against
`bob.age`, whose `diverges` closes on the two literal paths. -/
example {R : RuleSet} :
    Proves R ([] : List (Hyp C))
      (.eq (.find (.delAt .storage (.root "alice")) (.field (.root "bob") "age"))
        (.find .storage (.field (.root "bob") "age"))) := by
  rw [find_delAt_frame]
  exact Proves.eqRefl

/- A frame law whose side condition fails: `alice` and `alice.age` do not
diverge, so `sol_rw` stops at the condition, and `rw` reports it. -/
/--
error: sol_rw: the side condition
  (PTerm.root "alice").diverges ((PTerm.root "alice").field "age") = true
of findOnSaveFrame closes by neither `rfl` nor `decide`
-/
#guard_msgs in
example {R : RuleSet} :
    Proves R ([] : List (Hyp C))
      (.eq (.find (.save .storage (.root "alice") (.val (.lit (.int 1))))
        (.field (.root "alice") "age")) (.lit (.int 0))) := by
  rw [findOnSaveFrame]

/-- A path named, as an argument: its side condition's default (`by rfl`)
runs once the other path is found. -/
example {R : RuleSet} :
    Proves R ([] : List (Hyp C))
      (.eq (.find (.save .storage (.field (.root "alice") "name") (.val (.lit (.int 7))))
        (.field (.root "alice") "age")) (.find .storage (.field (.root "alice") "age"))) := by
  rw [findOnSaveFrame (p := .field (.root "alice") "name")]
  exact Proves.eqRefl

/-- Not a sequent: `rw` is Lean's, and so is its error. -/
example (a b : Nat) (h : a = b) : a + 1 = b + 1 := by
  rw [h]

/--
error: Tactic `rewrite` failed: Did not find an occurrence of the pattern
  a
in the target expression
  b = b

C : Contract
a b : Nat
h : a = b
⊢ b = b
-/
#guard_msgs in
example (a b : Nat) (h : a = b) : b = b := by
  rw [h]

end Solidity.Examples.TermTaclets
