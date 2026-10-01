import Solidity.Calculus.TermRules

/-!
# Term taclets: the Theory's rules on terms

KeY rewrites the terms a program leaves with the theory's taclets, and a
derivation names the taclet it applies; why the taclet is sound is not part
of the derivation.  `TermTaclet t t'` is that judgement: one constructor per
rule, a schema over the terms of a formula (`find(save(s, p, v), p) ⇝ v`),
under the name the chains write on the arrow.  `Proves.rewrite` and
`Proves.updRw` (`Calculus/Logic.lean`) apply one, so `⊢` sees names and
terms only.

`TermTaclet.sound` is the other side, `⊨`: each rule's terms have the same
Theory value in every state (`Term.Theq`).  Its cases are the Theory's
lemmas read through `denote` — `find_copyTo_same`, `find_delAt_frame`, … —
so a rule is a name here and a lemma there, and nothing is stated twice.

**Side conditions are KeY's `\varcond`s.**  A Theory law is stated over
paths (`p ≠ []`, `diverges p q`); a term's path is a `PTerm`, whose
denotation depends on the state only through its indices and aliases.  So
each premise is a `Bool` on the `PTerm`s that implies the Theory's premise in
every state: `PTerm.hasSeg` (not a bare alias, so never `[]`) and
`PTerm.diverges` (both paths built from a root by members and literal
indices, and diverging as lists).  On closed paths they compute, so a
default argument (`:= by rfl`) closes one wherever the rule is applied with
its paths known; `rw [findOnSave]` on a sequent finds the paths first and
closes the conditions after (`sol_rw`, `Calculus/Rewrite.lean`).

**Where a rule is weaker than the Theory's lemma.**  `find_copyTo_same`
reads back `copyVal (findSt s p) v`, the new value laid over the old one; it
is `v` itself only for a word, so `findOnSave` takes a literal.  A read of a
delete is the reset of what was there, which a term can name only when what
was there is a known word: `findOnDelAt` takes that read as a taclet of its
own.

**Any law of the Theory** is a rule too, `TermTaclet.theory`: two terms with
one Theory value in every state.  It is the term-level counterpart of
`Proves.close`, the first-order oracle, and what `sol_rw [find_delAt_same,
…]` builds from the Theory's lemmas on the spot (`Calculus/TheoryRewrite.lean`).
A named rule is preferred where one exists: its instance is checked by the
kernel against a schema, with no semantic proof in the derivation.
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

/-- An integer literal. -/
def Term.litInt? : Term C → Option Int
  | .lit (.int i) => some i
  | _ => none

theorem Term.eq_of_litInt? {t : Term C} {i : Int} (h : t.litInt? = some i) : t = .lit (.int i) := by
  unfold Term.litInt? at h
  split at h
  · cases h; rfl
  · cases h

/-- A path built from a root by members and literal indices: its segments,
the same in every state. -/
def Tm.segs? : Tm C s → Option (List Seg)
  | .app0 (.root r) => some [.field r]
  | .app1 (.field f) p => p.segs?.map (· ++ [.field f])
  | .app2 .at p i => match Term.litInt? i with
    | some k => p.segs?.map (· ++ [Seg.at k])
    | none => none
  | _ => none

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
  match p, hp with
  | .pvP _, hp => nomatch hp
  | .app0 (.root _), _ => simp only [tm_denote, ne_eq, List.cons_ne_nil, not_false_eq_true]
  | .app1 (.field _) _, _ | .app1 .next _, _ | .app2 .at _ _, _ =>
    simp only [tm_denote, ne_eq, List.append_eq_nil_iff, List.cons_ne_nil, and_false,
      not_false_eq_true]

/-- A closed path denotes its segments in every state. -/
theorem PTerm.denote_of_segs? (σ : State) : (p : PTerm C) → {l : List Seg} →
    p.segs? = some l → p.denote σ = l
  | .pvP _, _, h => nomatch h
  | .app0 (.root _), _, h => by
    simp only [Tm.segs?, Option.some.injEq] at h
    simp only [tm_denote, h]
  | .app1 (.field _) p, _, h => by
    simp only [Tm.segs?, Option.map_eq_some_iff] at h
    obtain ⟨a, ha, rfl⟩ := h
    simp only [tm_denote, PTerm.denote_of_segs? σ p ha]
  | .app1 .next _, _, h => nomatch h
  | .app2 .at p i, _, h => by
    simp only [Tm.segs?] at h
    split at h
    · rename_i k hk
      simp only [Option.map_eq_some_iff] at h
      obtain ⟨a, ha, rfl⟩ := h
      rw [Term.eq_of_litInt? hk]
      simp only [tm_denote, PTerm.denote_of_segs? σ p ha, asInt]
    · cases h

/-- `PTerm.diverges` gives the Theory's `diverges` in every state. -/
theorem PTerm.diverges_denote {p q : PTerm C} (h : p.diverges q = true) (σ : State) :
    Theory.StValue.diverges (p.denote σ) (q.denote σ) = true := by
  unfold PTerm.diverges at h
  split at h
  · rename_i a b ha hb
    rw [p.denote_of_segs? σ ha, q.denote_of_segs? σ hb]
    exact h
  · exact absurd h Bool.false_ne_true

/-! ## The rules -/

/-- `t ⇝ t'`: a rule of the Theory rewrites `t` to `t'`. -/
inductive TermTaclet : Term C → Term C → Prop
  /-- **`findOnSave`**: `find(save(s, p, v), p) ⇝ v` for a word `v`
  (`find_copyTo_same`). -/
  | findOnSave {s : STerm C} {p : PTerm C} {v : Value} (hp : p.hasSeg = true := by rfl) :
      TermTaclet (.find (.save s p (.val (.lit v))) p) (.lit v)
  /-- **`findOnSaveFrame`**: a read at a path that leaves the written one does
  not see the write, `find(save(s, p, v), q) ⇝ find(s, q)` (`find_copyTo_frame`). -/
  | findOnSaveFrame {s : STerm C} {p q : PTerm C} {v : SValT C}
      (h : p.diverges q = true := by rfl) :
      TermTaclet (.find (.save s p v) q) (.find s q)
  /-- **`findMemberCons`**: `find(s, r.f) ⇝ find(select(s, r), f)`.  solkey
  reads a path from its head: the path `consr(consr(nil, r), f)` turned into
  `cons(r, cons(f, nil))` (`consRcons`, `consRnil`), then
  `findDefinitionMemberCons`. -/
  | findMemberCons {s : STerm C} {r f : Name} :
      TermTaclet (.find s (.field (.root r) f)) (.find (.select s r) (.root f))
  /-- **`selectOnSaveMember`**: the write at `r.f`, seen from `r`, is a write
  at `f`: `find(select(save(s, r.f, v), r), q) ⇝ find(save(select(s, r), f, v), q)`
  — solkey's `selectOnSaveCons` at `a1 = a2`. -/
  | selectOnSaveMember {s : STerm C} {r f : Name} {v : SValT C} {q : PTerm C} :
      TermTaclet (.find (.select (.save s (.field (.root r) f) v) r) q)
        (.find (.save (.select s r) (.root f) v) q)
  /-- **`findOnDelAt`**: where `s` reads the word `w` at `p`, the delete
  leaves its default, `find(delAt(s, p), p) ⇝ default(w)` (`find_delAt_same`,
  `delValueDefault`). -/
  | findOnDelAt {s : STerm C} {p : PTerm C} {w : Value}
      (hw : TermTaclet (.find s p) (.lit w)) (hp : p.hasSeg = true := by rfl) :
      TermTaclet (.find (.delAt s p) p) (.lit (primDefault w))
  /-- **`findOnDelAtFrame`**: a read off the deleted path does not see the
  delete (`find_delAt_frame`). -/
  | findOnDelAtFrame {s : STerm C} {p q : PTerm C} (h : p.diverges q = true := by rfl) :
      TermTaclet (.find (.delAt s p) q) (.find s q)
  /-- **`findOnPushFrame`**: a read off the array's path does not see a push
  (`find_pushT_frame`). -/
  | findOnPushFrame {s : STerm C} {p q : PTerm C} {v : SValT C}
      (h : p.diverges q = true := by rfl) :
      TermTaclet (.find (.push s p v) q) (.find s q)
  /-- **`findOnPopFrame`**: a read off the array's path does not see a pop
  (`find_popT_frame`). -/
  | findOnPopFrame {s : STerm C} {p q : PTerm C} (h : p.diverges q = true := by rfl) :
      TermTaclet (.find (.pop s p) q) (.find s q)
  /-- Any law of the Theory: `t` and `t'` have one Theory value in every
  state. -/
  | theory {t t' : Term C} (h : Term.Theq t t') : TermTaclet t t'
  /-- A rule read right to left, `rw [← r]`. -/
  | symm {t t' : Term C} (r : TermTaclet t t') : TermTaclet t' t

/-- **`findOnDelAtSave`**: a delete over a written word reads the word's
default, `find(delAt(save(s, p, v), p), p) ⇝ default(v)`: `findOnDelAt` with
`findOnSave` as its premise. -/
theorem TermTaclet.findOnDelAtSave {s : STerm C} {p : PTerm C} {v : Value}
    (hp : p.hasSeg = true := by rfl) :
    TermTaclet (.find (.delAt (.save s p (.val (.lit v))) p) p) (.lit (primDefault v)) :=
  .findOnDelAt (.findOnSave hp) hp

/-! ## Soundness -/

/-- **Each term taclet is sound**: its two terms have one Theory value in
every state.  A case is `denote` unfolded and the Theory's lemma. -/
theorem TermTaclet.sound {t t' : Term C} : TermTaclet t t' → Term.Theq t t'
  | .findOnSave hp => fun σ => by
    simp only [tm_denote, find_copyTo_same _ (PTerm.denote_ne_nil hp σ), copyVal]
    exact Equiv.refl _
  | .findOnSaveFrame h => fun σ => by
    simp only [tm_denote, find_copyTo_frame _ _ _ _ (PTerm.diverges_denote h σ)]
    exact Equiv.refl _
  | .findMemberCons => fun σ => by
    simp only [tm_denote, List.cons_append, List.nil_append]
    exact Equiv.refl _
  | .selectOnSaveMember => fun σ => by
    simp only [tm_denote, List.cons_append, List.nil_append, copyTo, StValue.selectOnSaveCons, if_true, List.isEmpty_cons, Bool.false_eq_true, if_false, asStruct_st]
    exact Equiv.refl _
  | @findOnDelAt _ s p w hw hp => fun σ => by
    have hr : findSt (s.denote σ) (p.denote σ) = .prim w := Equiv.prim_iff.1 (hw.sound σ)
    simp only [tm_denote, find_delAt_same _ (PTerm.denote_ne_nil hp σ), hr, delValueDefault]
    exact Equiv.refl _
  | .findOnDelAtFrame h => fun σ => by
    simp only [tm_denote, find_delAt_frame _ (PTerm.diverges_denote h σ)]
    exact Equiv.refl _
  | .findOnPushFrame h => fun σ => by
    simp only [tm_denote, find_pushT_frame _ _ (PTerm.diverges_denote h σ)]
    exact Equiv.refl _
  | .findOnPopFrame h => fun σ => by
    simp only [tm_denote, find_popT_frame _ (PTerm.diverges_denote h σ)]
    exact Equiv.refl _
  | .theory h => h
  | .symm r => r.sound.symm

end Solidity
