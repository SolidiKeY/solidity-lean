import Solidity.Calculus.Rewrite

/-!
# The Theory's laws as rewrite rules

A law of `Theory/Storage.lean` or `Theory/Copy.lean` is an equation between
`findSt`, `copyTo`, `delAt`, `pushT`, … over `List Seg`.  The terms of a
formula denote those operations (`Term.denote`, `Update.lean`), so the law,
read through `denote`, relates the terms whose denotations are its sides:
their values are equal, hence equivalent (`StValue.Equiv`), in every state,
which is a `Term.Theq` (`Calculus/TermRules.lean`).  `Proves.theoryRw`
(`Calculus/Logic.lean`) makes a `Term.Theq` a rule, and `rw [findOnSave]`
on a sequent applies it (`sol_rw`, `Calculus/Rewrite.lean`).  No law here
has a soundness proof of its own: each is `denote` unfolded and the Theory
lemma its docstring names, with no interpreter (`eval`) in the proof.

**Side conditions are syntactic.**  A Theory law is stated over paths
(`p ≠ []`, `diverges p q`); a term's path is a `PTerm`, whose denotation
depends on the state only through its indices and aliases.  So each premise
is a `Bool` on the `PTerm`s that implies the Theory's premise in every
state: `PTerm.hasSeg` (not a bare alias, so never `[]`) and `PTerm.diverges`
(both paths built from a root by members and literal indices, and diverging
as lists).  On closed paths they are computations, closed by `rfl`: a
default argument (`:= by rfl`) closes one wherever the law is applied with
its paths known.  On a sequent the law is named bare, `rw [findOnSave]`:
`sol_rw` finds its paths in the sequent first and closes each side condition
after, by `rfl` or `decide`, and names the one that does not close.

**Where a law is weaker than the Theory's.**  `find_copyTo_same` reads back
`copyVal (findSt s p) v`, the new value laid over the old one; it is `v`
itself only for a word, so `findOnSave` takes a literal.  A read of a delete
is the reset of what was there, which a term can name only when what was
there is a known word (`findOnDelAt`).
-/

namespace Solidity

open Semantics Theory Theory.StValue

variable {C : Contract}

/-! ## The side conditions -/

/-- The path is never empty: anything but a bare alias, whose denotation is
`[]` where the alias is unbound.  The syntactic form of the Theory's
`p ≠ []`. -/
def PTerm.hasSeg : PTerm C → Bool
  | .pv _ => false
  | _ => true

/-- A path built from a root by members and literal indices: its segments,
the same in every state. -/
def PTerm.segs? : PTerm C → Option (List Seg)
  | .root r => some [.field r]
  | .pv _ => none
  | .field p f => p.segs?.map (· ++ [.field f])
  | .at p (.lit (.int i)) => p.segs?.map (· ++ [.at i])
  | .at _ _ => none
  | .next _ => none

/-- The two paths are closed (`segs?`) and leave each other (`diverges`):
the syntactic form of the Theory's `diverges p q`.  A read through an alias
or a symbolic index is not decided. -/
def PTerm.diverges (p q : PTerm C) : Bool :=
  match p.segs?, q.segs? with
  | some a, some b => Theory.StValue.diverges a b
  | _, _ => false

/-- `hasSeg` gives the Theory's `p ≠ []` in every state. -/
theorem PTerm.denote_ne_nil {p : PTerm C} (hp : p.hasSeg = true) (σ : State) :
    p.denote σ ≠ [] := by
  cases p <;> simp only [hasSeg, Bool.false_eq_true, denote, ne_eq, List.cons_ne_nil,
    List.append_eq_nil_iff, and_false, not_false_eq_true] at hp ⊢

/-- A closed path denotes its segments in every state. -/
theorem PTerm.denote_of_segs? (σ : State) : (p : PTerm C) → {l : List Seg} →
    p.segs? = some l → p.denote σ = l
  | .root _, _, h => by
    simp only [segs?, Option.some.injEq] at h
    simp only [denote, h]
  | .pv _, _, h => nomatch h
  | .field p _, _, h => by
    simp only [segs?, Option.map_eq_some_iff] at h
    obtain ⟨a, ha, rfl⟩ := h
    simp only [denote, p.denote_of_segs? σ ha]
  | .at p (.lit (.int _)), _, h => by
    simp only [segs?, Option.map_eq_some_iff] at h
    obtain ⟨a, ha, rfl⟩ := h
    simp only [denote, p.denote_of_segs? σ ha, Term.denote, asInt]
  | .at _ (.lit (.bool _)), _, h | .at _ (.pv _), _, h | .at _ (.binop ..), _, h
  | .at _ (.unop ..), _, h | .at _ (.find ..), _, h | .at _ (.len ..), _, h
  | .at _ (.read ..), _, h | .at _ (.ite ..), _, h | .at _ (.mlen ..), _, h
  | .at _ (.env _), _, h | .at _ (.net _), _, h | .at _ (.netOf ..), _, h
  | .next _, _, h => nomatch h

/-- `PTerm.diverges` gives the Theory's `diverges` in every state. -/
theorem PTerm.diverges_denote {p q : PTerm C} (h : p.diverges q = true) (σ : State) :
    Theory.StValue.diverges (p.denote σ) (q.denote σ) = true := by
  unfold PTerm.diverges at h
  split at h
  · rename_i a b ha hb
    rw [p.denote_of_segs? σ ha, q.denote_of_segs? σ hb]
    exact h
  · exact absurd h Bool.false_ne_true

/-! ## Reading a write back -/

/-- **`findOnSave`**: `find(save(s, p, v), p) ≐ v` for a word `v` — the
Theory's `find_copyTo_same` (`Theory/Copy.lean`), where a word laid over
anything is itself (`copyVal`). -/
theorem findOnSave {s : STerm C} {p : PTerm C} {v : Value} (hp : p.hasSeg = true := by rfl) :
    Term.Theq (.find (.save s p (.val (.lit v))) p) (.lit v) := fun σ => by
  simp only [Term.denote, STerm.denote, SValT.denote,
    find_copyTo_same _ (p.denote_ne_nil hp σ), copyVal]
  exact Equiv.refl _

/-- **`findOnSaveFrame`**: a read at a path that leaves the written one does
not see the write, `find(save(s, p, v), q) ≐ find(s, q)` for any `v` — the
Theory's `find_copyTo_frame` (`Theory/Copy.lean`). -/
theorem findOnSaveFrame {s : STerm C} {p q : PTerm C} {v : SValT C}
    (h : p.diverges q = true := by rfl) :
    Term.Theq (.find (.save s p v) q) (.find s q) := fun σ => by
  simp only [Term.denote, STerm.denote, find_copyTo_frame _ _ _ _ (PTerm.diverges_denote h σ)]
  exact Equiv.refl _

/-! ## Reading a delete back -/

/-- **`findOnDelAt`**: where `s` holds the word `w` at `p`, the delete leaves
its default, `find(delAt(s, p), p) ≐ default(w)` — the Theory's
`find_delAt_same` (`Theory/Storage.lean`) and `delValueDefault`, with
`Equiv.prim_iff` turning the premise into the read it names. -/
theorem findOnDelAt {s : STerm C} {p : PTerm C} {w : Value}
    (hw : Term.Theq (.find s p) (.lit w)) (hp : p.hasSeg = true := by rfl) :
    Term.Theq (.find (.delAt s p) p) (.lit (primDefault w)) := fun σ => by
  have hr : findSt (s.denote σ) (p.denote σ) = .prim w := Equiv.prim_iff.1 (hw σ)
  simp only [Term.denote, STerm.denote, find_delAt_same _ (p.denote_ne_nil hp σ), hr,
    delValueDefault]
  exact Equiv.refl _

/-- **`findOnDelAtSave`**: a delete over a written word reads the word's
default, `find(delAt(save(s, p, v), p), p) ≐ default(v)` — `findOnDelAt`
with `findOnSave` as its premise, so `find_delAt_same` over
`find_copyTo_same`. -/
theorem findOnDelAtSave {s : STerm C} {p : PTerm C} {v : Value}
    (hp : p.hasSeg = true := by rfl) :
    Term.Theq (.find (.delAt (.save s p (.val (.lit v))) p) p) (.lit (primDefault v)) :=
  findOnDelAt (findOnSave hp) hp

/-- **`findOnDelAtFrame`**: a read off the deleted path does not see the
delete — the Theory's `find_delAt_frame` (`Theory/Storage.lean`). -/
theorem findOnDelAtFrame {s : STerm C} {p q : PTerm C} (h : p.diverges q = true := by rfl) :
    Term.Theq (.find (.delAt s p) q) (.find s q) := fun σ => by
  simp only [Term.denote, STerm.denote, find_delAt_frame _ (PTerm.diverges_denote h σ)]
  exact Equiv.refl _

/-! ## The array writes, off their path -/

/-- **`findOnPushFrame`**: a read off the array's path does not see a push —
the Theory's `find_pushT_frame` (`Theory/Copy.lean`). -/
theorem findOnPushFrame {s : STerm C} {p q : PTerm C} {v : SValT C}
    (h : p.diverges q = true := by rfl) :
    Term.Theq (.find (.push s p v) q) (.find s q) := fun σ => by
  simp only [Term.denote, STerm.denote, find_pushT_frame _ _ (PTerm.diverges_denote h σ)]
  exact Equiv.refl _

/-- **`findOnPopFrame`**: a read off the array's path does not see a pop —
the Theory's `find_popT_frame` (`Theory/Copy.lean`). -/
theorem findOnPopFrame {s : STerm C} {p q : PTerm C} (h : p.diverges q = true := by rfl) :
    Term.Theq (.find (.pop s p) q) (.find s q) := fun σ => by
  simp only [Term.denote, STerm.denote, find_popT_frame _ (PTerm.diverges_denote h σ)]
  exact Equiv.refl _

/-! ## The laws on a sequent -/

section Example

open Proves

/-- `alice.age = 42; alice.name = 7;` read back at `alice.age`: the frame
steps over the second write, `findOnSave` reads the first, and the goal
`42 ≐ 42` closes.  The laws are named bare: their paths come from the
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
  sol_rw findOnDelAtSave
  exact Proves.eqClose

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

end Example

end Solidity
