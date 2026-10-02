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

/-- `f` of some path on the way down to `t`'s root: `t` itself, the path it
selects from, and so on.  Generic in the sort, as structural recursion over
`Tm` asks. -/
def Tm.extendsAny (f : PTerm C → Bool) : Tm C u → Bool
  | .app1 (.field _) q => f q || q.extendsAny f
  | .app2 .at q _ => f q || q.extendsAny f
  | _ => false

/-- `q` goes on below `p`: `q` is `p` with one or more selectors after it. -/
def PTerm.extends (q p : PTerm C) : Bool := q.extendsAny (· == p)

/-- `q.extends p` gives the Theory's `q = p ++ r`, `r ≠ []`, in every state. -/
theorem PTerm.extends_denote {p : PTerm C} (σ : State) :
    (q : PTerm C) → q.extends p = true → ∃ r, r ≠ [] ∧ q.denote σ = p.denote σ ++ r
  | .app1 (.field f) q, h => by
    simp only [PTerm.extends, Tm.extendsAny, Bool.or_eq_true, beq_iff_eq] at h
    rcases h with rfl | h
    · exact ⟨[.field f], List.cons_ne_nil _ _, by simp only [tm_denote]⟩
    · obtain ⟨r, hr, hq⟩ := PTerm.extends_denote σ q h
      exact ⟨r ++ [.field f], by simp, by simp only [tm_denote, hq, List.append_assoc]⟩
  | .app2 .at q i, h => by
    simp only [PTerm.extends, Tm.extendsAny, Bool.or_eq_true, beq_iff_eq] at h
    rcases h with rfl | h
    · exact ⟨[.at (asInt (i.denote σ))], List.cons_ne_nil _ _, by simp only [tm_denote]⟩
    · obtain ⟨r, hr, hq⟩ := PTerm.extends_denote σ q h
      exact ⟨r ++ [.at (asInt (i.denote σ))], by simp, by simp only [tm_denote, hq, List.append_assoc]⟩
  | .pvP _, h | .app0 (.root _), h | .app1 .next _, h => nomatch h

/-- A path read from its head, as solkey reads it: the root, and the rest of
the path rooted at its first member — `alice.account.balance` is `alice` and
`account.balance`.  `none` for a root alone or a path through an alias. -/
def Tm.shift? : Tm C u → Option (Name × PTerm C)
  | .app1 (.field f) (.app0 (.root r)) => some (r, .root f)
  | .app1 (.field f) p => (Tm.shift? p).map fun (r, p') => (r, .field p' f)
  | .app2 .at (.app0 (.root _)) _ => none
  | .app2 .at p i => (Tm.shift? p).map fun (r, p') => (r, .at p' i)
  | _ => none

@[inherit_doc Tm.shift?]
def PTerm.shift? (p : PTerm C) : Option (Name × PTerm C) := Tm.shift? p

/-- `shift?` splits the Theory's path at its head, in every state. -/
theorem PTerm.shift?_denote (σ : State) : (p : PTerm C) → {r : Name} → {p' : PTerm C} →
    p.shift? = some (r, p') → p.denote σ = .field r :: p'.denote σ
  | .app1 (.field f) (.app0 (.root r)), _, _, h => by
    simp only [PTerm.shift?, Tm.shift?, Option.some.injEq, Prod.mk.injEq] at h
    obtain ⟨rfl, rfl⟩ := h
    simp only [tm_denote, List.singleton_append]
  | .app1 (.field f) (.app1 (.field g) p), _, _, h => by
    simp only [PTerm.shift?, Tm.shift?, Option.map_eq_some_iff] at h
    obtain ⟨⟨r, p'⟩, hp, h⟩ := h
    simp only [Prod.mk.injEq] at h
    obtain ⟨rfl, rfl⟩ := h
    have ih := PTerm.shift?_denote σ (.app1 (.field g) p) (by simpa only [PTerm.shift?] using hp)
    simp only [tm_denote] at ih ⊢
    rw [ih]
    rfl
  | .app1 (.field f) (.app2 .at p i), _, _, h => by
    simp only [PTerm.shift?, Tm.shift?, Option.map_eq_some_iff] at h
    obtain ⟨⟨r, p'⟩, hp, h⟩ := h
    simp only [Prod.mk.injEq] at h
    obtain ⟨rfl, rfl⟩ := h
    have ih := PTerm.shift?_denote σ (.app2 .at p i) (by simpa only [PTerm.shift?] using hp)
    simp only [tm_denote] at ih ⊢
    rw [ih]
    rfl
  | .app2 .at (.app1 (.field g) p) i, _, _, h => by
    simp only [PTerm.shift?, Tm.shift?, Option.map_eq_some_iff] at h
    obtain ⟨⟨r, p'⟩, hp, h⟩ := h
    simp only [Prod.mk.injEq] at h
    obtain ⟨rfl, rfl⟩ := h
    have ih := PTerm.shift?_denote σ (.app1 (.field g) p) (by simpa only [PTerm.shift?] using hp)
    simp only [tm_denote] at ih ⊢
    rw [ih]
    rfl
  | .app2 .at (.app2 .at p j) i, _, _, h => by
    simp only [PTerm.shift?, Tm.shift?, Option.map_eq_some_iff] at h
    obtain ⟨⟨r, p'⟩, hp, h⟩ := h
    simp only [Prod.mk.injEq] at h
    obtain ⟨rfl, rfl⟩ := h
    have ih := PTerm.shift?_denote σ (.app2 .at p j) (by simpa only [PTerm.shift?] using hp)
    simp only [tm_denote] at ih ⊢
    rw [ih]
    rfl
  | .app1 (.field _) (.pvP _), _, _, h | .app1 (.field _) (.app1 .next _), _, _, h
  | .app2 .at (.app0 (.root _)) _, _, _, h | .app2 .at (.pvP _) _, _, _, h
  | .app2 .at (.app1 .next _) _, _, _, h | .pvP _, _, _, h | .app0 (.root _), _, _, h
  | .app1 .next _, _, _, h => nomatch h

/-- The rest `shift?` leaves has a segment: it is rooted at the first member. -/
theorem PTerm.shift?_hasSeg : (p : PTerm C) → {r : Name} → {p' : PTerm C} →
    p.shift? = some (r, p') → p'.hasSeg = true
  | .app1 (.field f) (.app0 (.root r)), _, _, h => by
    simp only [PTerm.shift?, Tm.shift?, Option.some.injEq, Prod.mk.injEq] at h
    obtain ⟨rfl, rfl⟩ := h
    rfl
  | .app1 (.field f) (.app1 (.field g) p), _, _, h | .app1 (.field f) (.app2 .at p i), _, _, h => by
    simp only [PTerm.shift?, Tm.shift?, Option.map_eq_some_iff] at h
    obtain ⟨⟨r, p'⟩, -, h⟩ := h
    simp only [Prod.mk.injEq] at h
    obtain ⟨rfl, rfl⟩ := h
    rfl
  | .app2 .at (.app1 (.field g) p) i, _, _, h | .app2 .at (.app2 .at p j) i, _, _, h => by
    simp only [PTerm.shift?, Tm.shift?, Option.map_eq_some_iff] at h
    obtain ⟨⟨r, p'⟩, -, h⟩ := h
    simp only [Prod.mk.injEq] at h
    obtain ⟨rfl, rfl⟩ := h
    rfl
  | .app1 (.field _) (.pvP _), _, _, h | .app1 (.field _) (.app1 .next _), _, _, h
  | .app2 .at (.app0 (.root _)) _, _, _, h | .app2 .at (.pvP _) _, _, _, h
  | .app2 .at (.app1 .next _) _, _, _, h | .pvP _, _, _, h | .app0 (.root _), _, _, h
  | .app1 .next _, _, _, h => nomatch h


def SValT.lit? : SValT C → Option Value
  | .val (.lit v) => some v
  | _ => none

theorem SValT.lit?_eq : (v : SValT C) → {w : Value} → v.lit? = some w → v = .val (.lit w)
  | .val (.lit _), _, h => by cases h; rfl

/-- The word a storage term reads at a path, read off its writes: through a
`save` at that path of a word, and past a `save` at a path that leaves it.
`eq` and `div` are the path's `(· == q)` and `(·.diverges q)`, functions so
that the recursion is structural. -/
def Tm.findLitBy (eq div : PTerm C → Bool) : Tm C u → Option Value
  | .app3 .save s p v => if eq p then SValT.lit? v else if div p then s.findLitBy eq div else none
  | _ => none

/-- The word `s` reads at `q`, read off its writes (`Tm.findLitBy`); `none`
where its writes do not decide it. -/
def STerm.findLit? (s : STerm C) (q : PTerm C) : Option Value :=
  if q.hasSeg then s.findLitBy (· == q) (·.diverges q) else none

/-- The node at `p` in `s` is not a mapping, in every state (`kindFree`): what
a read below a delete needs, since a delete keeps a mapping's members. -/
def STerm.KindFreeAt (s : STerm C) (p : PTerm C) : Prop :=
  ∀ σ, (findSt (s.denote σ) (p.denote σ)).kindFree = true

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

/-! ## A storage term with a hole

solkey's `selectOnSaveCons` rewrites a storage term wherever it stands; a
term taclet here rewrites a value, so the member-wise laws take the storage
context the rewritten term stands in: `find(K[select(save(s, r.p, v), r)], q)`
for a context `K` of saves, deletes and selects around the hole, which the
arrow `~[selectOnSaveMemberIn]~>` finds (`Calculus/Chains.lean`). -/

/-- A storage term with a hole: the storage argument of saves, deletes and
selects, down to the hole. -/
inductive SCtx (C : Contract) where
  | hole
  | save (K : SCtx C) (p : PTerm C) (v : SValT C)
  | delAt (K : SCtx C) (p : PTerm C)
  | select (K : SCtx C) (r : Name)
  deriving DecidableEq, Repr

/-- The hole filled. -/
def SCtx.fill : SCtx C → STerm C → STerm C
  | .hole, s => s
  | .save K p v, s => .save (K.fill s) p v
  | .delAt K p, s => .delAt (K.fill s) p
  | .select K r, s => .select (K.fill s) r

/-- Two storages that denote alike fill a context alike. -/
theorem SCtx.fill_denote {s s' : STerm C} (h : ∀ σ, s.denote σ = s'.denote σ) :
    (K : SCtx C) → ∀ σ, (K.fill s).denote σ = (K.fill s').denote σ
  | .hole, σ => h σ
  | .save K p v, σ => by simp only [SCtx.fill, tm_denote, SCtx.fill_denote h K σ]
  | .delAt K p, σ => by simp only [SCtx.fill, tm_denote, SCtx.fill_denote h K σ]
  | .select K r, σ => by simp only [SCtx.fill, tm_denote, SCtx.fill_denote h K σ]

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
  /-- **`findMemberCons`**: `find(s, r.p) ⇝ find(select(s, r), p)`, the path read
  from its head (`shift?`), as solkey does: the path `consr(consr(nil, r), f)`
  turned into `cons(r, cons(f, nil))` (`consRcons`, `consRnil`), then
  `findDefinitionMemberCons`. -/
  | findMemberCons {s : STerm C} {p : PTerm C} {r : Name} {p' : PTerm C}
      (h : p.shift? = some (r, p') := by rfl) :
      TermTaclet (.find s p) (.find (.select s r) p')
  /-- **`selectOnSaveMember`**: the write at `r.p`, seen from `r`, is a write
  at `p`: `find(select(save(s, r.p, v), r), q) ⇝ find(save(select(s, r), p, v), q)`
  — solkey's `selectOnSaveCons` at `a1 = a2`. -/
  | selectOnSaveMember {s : STerm C} {p : PTerm C} {r : Name} {p' : PTerm C} {v : SValT C}
      {q : PTerm C} (h : p.shift? = some (r, p') := by rfl) :
      TermTaclet (.find (.select (.save s p v) r) q) (.find (.save (.select s r) p' v) q)
  /-- **`selectOnSaveFrame`**: a write under another root is not seen from `r`:
  `find(select(save(s, r'.p, v), r), q) ⇝ find(select(s, r), q)` — solkey's
  `selectOnSaveCons` at `a1 ≠ a2`. -/
  | selectOnSaveFrame {s : STerm C} {p : PTerm C} {r r' : Name} {p' : PTerm C} {v : SValT C}
      {q : PTerm C} (h : p.shift? = some (r', p') := by rfl) (hr : r' ≠ r := by decide) :
      TermTaclet (.find (.select (.save s p v) r) q) (.find (.select s r) q)
  /-- **`selectOnDelAtMember`**: the delete at `r.p`, seen from `r`, is a delete
  at `p`: `find(select(delAt(s, r.p), r), q) ⇝ find(delAt(select(s, r), p), q)`. -/
  | selectOnDelAtMember {s : STerm C} {p : PTerm C} {r : Name} {p' : PTerm C} {q : PTerm C}
      (h : p.shift? = some (r, p') := by rfl) :
      TermTaclet (.find (.select (.delAt s p) r) q) (.find (.delAt (.select s r) p') q)
  /-- **`selectOnDelAtFrame`**: a delete under another root is not seen from `r`. -/
  | selectOnDelAtFrame {s : STerm C} {p : PTerm C} {r r' : Name} {p' : PTerm C} {q : PTerm C}
      (h : p.shift? = some (r', p') := by rfl) (hr : r' ≠ r := by decide) :
      TermTaclet (.find (.select (.delAt s p) r) q) (.find (.select s r) q)
  /-- **`selectOnSaveMemberIn`**: `selectOnSaveMember` in a storage context `K`:
  `find(K[select(save(s, r.p, v), r)], q) ⇝ find(K[save(select(s, r), p, v)], q)`. -/
  | selectOnSaveMemberIn (K : SCtx C) {s : STerm C} {p : PTerm C} {r : Name} {p' : PTerm C}
      {v : SValT C} {q : PTerm C} (h : p.shift? = some (r, p') := by rfl) :
      TermTaclet (.find (K.fill (.select (.save s p v) r)) q)
        (.find (K.fill (.save (.select s r) p' v)) q)
  /-- **`selectOnSaveFrameIn`**: `selectOnSaveFrame` in a storage context. -/
  | selectOnSaveFrameIn (K : SCtx C) {s : STerm C} {p : PTerm C} {r r' : Name} {p' : PTerm C}
      {v : SValT C} {q : PTerm C} (h : p.shift? = some (r', p') := by rfl) (hr : r' ≠ r := by decide) :
      TermTaclet (.find (K.fill (.select (.save s p v) r)) q) (.find (K.fill (.select s r)) q)
  /-- **`selectOnDelAtMemberIn`**: `selectOnDelAtMember` in a storage context. -/
  | selectOnDelAtMemberIn (K : SCtx C) {s : STerm C} {p : PTerm C} {r : Name} {p' : PTerm C}
      {q : PTerm C} (h : p.shift? = some (r, p') := by rfl) :
      TermTaclet (.find (K.fill (.select (.delAt s p) r)) q) (.find (K.fill (.delAt (.select s r) p')) q)
  /-- **`selectOnDelAtFrameIn`**: `selectOnDelAtFrame` in a storage context. -/
  | selectOnDelAtFrameIn (K : SCtx C) {s : STerm C} {p : PTerm C} {r r' : Name} {p' : PTerm C}
      {q : PTerm C} (h : p.shift? = some (r', p') := by rfl) (hr : r' ≠ r := by decide) :
      TermTaclet (.find (K.fill (.select (.delAt s p) r)) q) (.find (K.fill (.select s r)) q)
  /-- **`findOnDelAt`**: where `s` reads the word `w` at `p`, the delete
  leaves its default, `find(delAt(s, p), p) ⇝ default(w)` (`find_delAt_same`,
  `delValueDefault`). -/
  | findOnDelAt {s : STerm C} {p : PTerm C} {w : Value}
      (hw : TermTaclet (.find s p) (.lit w)) (hp : p.hasSeg = true := by rfl) :
      TermTaclet (.find (.delAt s p) p) (.lit (primDefault w))
  /-- **`findOnDelAtBelow`**: below a deleted node that is not a mapping,
  every word reads its default, `find(delAt(s, p), q) ⇝ default(w)`, where `q`
  goes on below `p` and `s` reads the word `w` at `q` off its writes
  (`STerm.findLit?`; `find_delAt_below`, `delValueDefault`).  `hk`, that the
  node is not a mapping (which keeps its members), is the chain's premise. -/
  | findOnDelAtBelow {s : STerm C} {p q : PTerm C} {w : Value} (hk : s.KindFreeAt p)
      (hw : s.findLit? q = some w := by rfl) (hp : p.hasSeg = true := by rfl)
      (hq : q.extends p = true := by rfl) :
      TermTaclet (.find (.delAt s p) q) (.lit (primDefault w))
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

/-- The write at `r.p`, seen from `r`, is the write at `p`: the storages are
one Struct. -/
theorem STerm.selectOnSaveMember_denote {s : STerm C} {p : PTerm C} {r : Name} {p' : PTerm C}
    {v : SValT C} (h : p.shift? = some (r, p')) (σ : State) :
    (STerm.select (.save s p v) r).denote σ = (STerm.save (.select s r) p' v).denote σ := by
  have hne := PTerm.denote_ne_nil (PTerm.shift?_hasSeg p h) σ
  simp only [tm_denote, PTerm.shift?_denote σ p h, copyTo, StValue.selectOnSaveCons, if_true,
    List.isEmpty_iff, hne, if_false, asStruct_st, find_cons _ _ hne]

theorem STerm.selectOnSaveFrame_denote {s : STerm C} {p : PTerm C} {r r' : Name} {p' : PTerm C}
    {v : SValT C} (h : p.shift? = some (r', p')) (hr : r' ≠ r) (σ : State) :
    (STerm.select (.save s p v) r).denote σ = (STerm.select s r).denote σ := by
  simp only [tm_denote, PTerm.shift?_denote σ p h, copyTo, StValue.selectOnSaveCons]
  rw [if_neg (fun e => hr (Seg.field.inj e))]

theorem STerm.selectOnDelAtMember_denote {s : STerm C} {p : PTerm C} {r : Name} {p' : PTerm C}
    (h : p.shift? = some (r, p')) (σ : State) :
    (STerm.select (.delAt s p) r).denote σ = (STerm.delAt (.select s r) p').denote σ := by
  have hne := PTerm.denote_ne_nil (PTerm.shift?_hasSeg p h) σ
  simp only [tm_denote, PTerm.shift?_denote σ p h, Theory.StValue.delAt, StValue.selectOnSaveCons,
    if_true, List.isEmpty_iff, hne, if_false, asStruct_st, find_cons _ _ hne]

theorem STerm.selectOnDelAtFrame_denote {s : STerm C} {p : PTerm C} {r r' : Name} {p' : PTerm C}
    (h : p.shift? = some (r', p')) (hr : r' ≠ r) (σ : State) :
    (STerm.select (.delAt s p) r).denote σ = (STerm.select s r).denote σ := by
  simp only [tm_denote, PTerm.shift?_denote σ p h, Theory.StValue.delAt, StValue.selectOnSaveCons]
  rw [if_neg (fun e => hr (Seg.field.inj e))]

/-- Two storages that denote alike are read alike, in any context. -/
theorem Term.find_fill_theq {s s' : STerm C} (h : ∀ σ, s.denote σ = s'.denote σ) (K : SCtx C)
    (q : PTerm C) : Term.Theq (.find (K.fill s) q) (.find (K.fill s') q) := fun σ => by
  simp only [tm_denote, SCtx.fill_denote h K σ]
  exact Equiv.refl _

/-- The word read off the writes is the word read: `findOnSave` at the write
of `q`, `findOnSaveFrame` past the others. -/
theorem Tm.findLitBy_theq {q : PTerm C} (hq : q.hasSeg = true) :
    (s : STerm C) → {w : Value} → s.findLitBy (· == q) (·.diverges q) = some w →
      Term.Theq (.find s q) (.lit w)
  | .app3 .save s p v, w, h => fun σ => by
    simp only [Tm.findLitBy] at h
    split at h
    · rename_i hpq
      simp only [beq_iff_eq] at hpq
      subst hpq
      obtain rfl := SValT.lit?_eq v h
      simp only [tm_denote, find_copyTo_same _ (PTerm.denote_ne_nil hq σ), copyVal]
      exact Equiv.refl _
    · split at h
      · rename_i hd
        have ih := Tm.findLitBy_theq hq s h σ
        simp only [tm_denote] at ih ⊢
        rw [find_copyTo_frame _ _ _ _ (PTerm.diverges_denote hd σ)]
        exact ih
      · nomatch h
  | .pvS _, _, h | .app0 .storage, _, h | .app1 (.select _) _, _, h | .app2 .delAt _ _, _, h
  | .app2 (.pushSlot _) _ _, _, h | .app2 .pop _ _, _, h | .app2 .shrink _ _, _, h
  | .app2 (.extend _) _ _, _, h | .app3 .push _ _ _, _, h => nomatch h

theorem STerm.findLit?_theq {s : STerm C} {q : PTerm C} {w : Value} (h : s.findLit? q = some w) :
    Term.Theq (.find s q) (.lit w) := by
  unfold STerm.findLit? at h
  split at h
  · exact Tm.findLitBy_theq ‹_› s h
  · nomatch h

/-- **Each term taclet is sound**: its two terms have one Theory value in
every state.  A case is `denote` unfolded and the Theory's lemma. -/
theorem TermTaclet.sound {t t' : Term C} : TermTaclet t t' → Term.Theq t t'
  | .findOnSave hp => fun σ => by
    simp only [tm_denote, find_copyTo_same _ (PTerm.denote_ne_nil hp σ), copyVal]
    exact Equiv.refl _
  | .findOnSaveFrame h => fun σ => by
    simp only [tm_denote, find_copyTo_frame _ _ _ _ (PTerm.diverges_denote h σ)]
    exact Equiv.refl _
  | @findMemberCons _ s p r p' h => fun σ => by
    simp only [tm_denote, PTerm.shift?_denote σ p h,
      find_cons _ _ (PTerm.denote_ne_nil (PTerm.shift?_hasSeg p h) σ)]
    exact Equiv.refl _
  | @selectOnSaveMember _ s p r p' v q h =>
    Term.find_fill_theq (STerm.selectOnSaveMember_denote h) .hole q
  | @selectOnSaveFrame _ s p r r' p' v q h hr =>
    Term.find_fill_theq (STerm.selectOnSaveFrame_denote h hr) .hole q
  | @selectOnDelAtMember _ s p r p' q h =>
    Term.find_fill_theq (STerm.selectOnDelAtMember_denote h) .hole q
  | @selectOnDelAtFrame _ s p r r' p' q h hr =>
    Term.find_fill_theq (STerm.selectOnDelAtFrame_denote h hr) .hole q
  | @selectOnSaveMemberIn _ K s p r p' v q h =>
    Term.find_fill_theq (STerm.selectOnSaveMember_denote h) K q
  | @selectOnSaveFrameIn _ K s p r r' p' v q h hr =>
    Term.find_fill_theq (STerm.selectOnSaveFrame_denote h hr) K q
  | @selectOnDelAtMemberIn _ K s p r p' q h =>
    Term.find_fill_theq (STerm.selectOnDelAtMember_denote h) K q
  | @selectOnDelAtFrameIn _ K s p r r' p' q h hr =>
    Term.find_fill_theq (STerm.selectOnDelAtFrame_denote h hr) K q
  | @findOnDelAt _ s p w hw hp => fun σ => by
    have hr : findSt (s.denote σ) (p.denote σ) = .prim w := Equiv.prim_iff.1 (hw.sound σ)
    simp only [tm_denote, find_delAt_same _ (PTerm.denote_ne_nil hp σ), hr, delValueDefault]
    exact Equiv.refl _
  | @findOnDelAtBelow _ s p q w hk hw hp hq => fun σ => by
    obtain ⟨r, hr, hqr⟩ := PTerm.extends_denote σ q hq
    have hw' := STerm.findLit?_theq hw σ
    simp only [tm_denote] at hw' ⊢
    rw [hqr, find_delAt_below _ (PTerm.denote_ne_nil hp σ) hr (hk σ), ← hqr,
      Equiv.prim_iff.1 hw', delValueDefault]
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
