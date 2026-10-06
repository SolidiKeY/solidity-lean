import Solidity.Calculus.TermRules
import Solidity.Calculus.RuleSyntax

/-!
# Term taclets: the Theory's rules on terms

KeY rewrites the terms a program leaves with the theory's taclets, and a
derivation names the taclet it applies; why the taclet is sound is not part
of the derivation.  `TermTaclet t t'` is that judgement: one constructor per
rule, a schema over the terms of a formula (`find(save(s, p, v), p) ⇝ v`),
under the name the chains write on the arrow, its terms in `tm{ … }`
(`Calculus/RuleSyntax.lean`).  `Proves.rewrite` and
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
the same in every state.  An index check in a storage (`p[i]@S`) is the
index `p[i]`. -/
def Tm.segs? : Tm C s → Option (List Seg)
  | PTerm.root r => some [.field r]
  | PTerm.field p f => p.segs?.map (· ++ [.field f])
  | PTerm.at p i => match Term.litInt? i with
    | some k => p.segs?.map (· ++ [Seg.at k])
    | none => none
  | PTerm.atIn _ p i => match Term.litInt? i with
    | some k => p.segs?.map (· ++ [Seg.at k])
    | none => none
  | _ => none

/-- The shape of a path's segment: a member, or an element at a literal
index (`some k`) or at an index the syntax does not decide (`none`: a
local, a length, the slot past the end). -/
inductive SegT where
  | field (f : Name)
  | at (k : Option Int)
  deriving DecidableEq, Repr

/-- A path's shape, read off its syntax: `none` through an alias. -/
def Tm.shape? : Tm C s → Option (List SegT)
  | PTerm.root r => some [.field r]
  | PTerm.field p f => p.shape?.map (· ++ [.field f])
  | PTerm.next p => p.shape?.map (· ++ [.at none])
  | PTerm.at p i => p.shape?.map (· ++ [.at (Term.litInt? i)])
  | PTerm.nextIn _ p => p.shape?.map (· ++ [.at none])
  | PTerm.atIn _ p i => p.shape?.map (· ++ [.at (Term.litInt? i)])
  | _ => none

/-- The segment has the shape. -/
def SegT.fits : SegT → Seg → Bool
  | .field f, .field g => f == g
  | .at (some k), .at i => k == i
  | .at none, .at _ => true
  | _, _ => false

/-- The path has the shape, segment by segment. -/
def SegT.matches : List SegT → List Seg → Bool
  | [], [] => true
  | x :: a, s :: p => x.fits s && SegT.matches a p
  | _, _ => false

/-- Whether two shapes tell their segments apart: `some true` when the
segments differ in every state (a member against an element, two members
or two literal indices by name or value), `some false` when they are one
segment in every state, `none` when a symbolic index decides nothing. -/
def SegT.apart : SegT → SegT → Option Bool
  | .field f, .field g => some (f != g)
  | .field _, .at _ => some true
  | .at _, .field _ => some true
  | .at (some i), .at (some j) => some (i != j)
  | .at none, .at _ => none
  | .at (some _), .at none => none

/-- The two shapes leave each other: at some position both have a segment
and the segments differ, the ones before being the same — the syntactic
form of the Theory's `diverges`.  A symbolic index decides nothing. -/
def SegT.diverges : List SegT → List SegT → Bool
  | x :: a, y :: b => match x.apart y with
    | some true => true
    | some false => SegT.diverges a b
    | none => false
  | _, _ => false

/-- The two paths leave each other (`SegT.diverges` of their shapes): the
syntactic form of the Theory's `diverges p q`.  A read through an alias is
not decided; a member and an element always diverge, two literal indices by
value, two symbolic indices never. -/
def PTerm.diverges (p q : PTerm C) : Bool :=
  match p.shape?, q.shape? with
  | some a, some b => SegT.diverges a b
  | _, _ => false

/-- `q` leaves `p.length`: the Theory's `diverges q (p ++ [lengthSeg])`. -/
def PTerm.divergesLen (q p : PTerm C) : Bool :=
  match q.shape?, p.shape? with
  | some a, some b => SegT.diverges a (b ++ [.field "length"])
  | _, _ => false

/-- The path its checks aside: `p[i]@S` is `p[i]`, whatever `S`.  A slot
past the end reads its length in a storage, so `p[p.length]@S` stays.
Generic in the sort, as structural recursion over `Tm` asks. -/
def Tm.eraseChecks : Tm C u → Tm C u
  | PTerm.field p f => .app1 (.field f) (Tm.eraseChecks p)
  | PTerm.next p => .app1 .next (Tm.eraseChecks p)
  | PTerm.at p i => .app2 .at (Tm.eraseChecks p) i
  | PTerm.nextIn S p => .app2 .nextIn S (Tm.eraseChecks p)
  | PTerm.atIn _ p i => .app2 .at (Tm.eraseChecks p) i
  | p => p

/-- The two paths have the same segments in every state, their checks
aside (`eraseChecks`). -/
def PTerm.sameSegs (p q : PTerm C) : Bool := Tm.eraseChecks p == Tm.eraseChecks q

theorem PTerm.sameSegs_refl (p : PTerm C) : p.sameSegs p = true := beq_self_eq_true _

/-- `f` of some path on the way down to `t`'s root: `t` itself, the path it
selects from, and so on.  Generic in the sort, as structural recursion over
`Tm` asks. -/
def Tm.extendsAny (f : PTerm C → Bool) : Tm C u → Bool
  | PTerm.field q _ => f q || q.extendsAny f
  | PTerm.at q _ => f q || q.extendsAny f
  | PTerm.atIn _ q _ => f q || q.extendsAny f
  | _ => false

/-- `q` goes on below `p`: `q` is `p` with one or more selectors after it. -/
def PTerm.extends (q p : PTerm C) : Bool := q.extendsAny (· == p)

/-- `q.extends p` gives the Theory's `q = p ++ r`, `r ≠ []`, in every state. -/
theorem PTerm.extends_denote {p : PTerm C} (σ : State) :
    (q : PTerm C) → q.extends p = true → ∃ r, r ≠ [] ∧ q.denote σ = p.denote σ ++ r
  | PTerm.field q f, h => by
    simp only [PTerm.extends, Tm.extendsAny, Bool.or_eq_true, beq_iff_eq] at h
    rcases h with rfl | h
    · exact ⟨[.field f], List.cons_ne_nil _ _, by simp only [tm_denote]⟩
    · obtain ⟨r, hr, hq⟩ := PTerm.extends_denote σ q h
      exact ⟨r ++ [.field f], by simp, by simp only [tm_denote, hq, List.append_assoc]⟩
  | PTerm.at q i, h => by
    simp only [PTerm.extends, Tm.extendsAny, Bool.or_eq_true, beq_iff_eq] at h
    rcases h with rfl | h
    · exact ⟨[.at (asInt (i.denote σ))], List.cons_ne_nil _ _, by simp only [tm_denote]⟩
    · obtain ⟨r, hr, hq⟩ := PTerm.extends_denote σ q h
      exact ⟨r ++ [.at (asInt (i.denote σ))], by simp, by simp only [tm_denote, hq, List.append_assoc]⟩
  | PTerm.atIn _ q i, h => by
    simp only [PTerm.extends, Tm.extendsAny, Bool.or_eq_true, beq_iff_eq] at h
    rcases h with rfl | h
    · exact ⟨[.at (asInt (i.denote σ))], List.cons_ne_nil _ _, by simp only [tm_denote]⟩
    · obtain ⟨r, hr, hq⟩ := PTerm.extends_denote σ q h
      exact ⟨r ++ [.at (asInt (i.denote σ))], by simp, by simp only [tm_denote, hq, List.append_assoc]⟩
  | .pvP _, h | PTerm.root _, h | PTerm.next _, h | PTerm.nextIn _ _, h => nomatch h

/-- The state variable a path is, if it is one alone. -/
def Tm.root? : Tm C u → Option Name
  | PTerm.root r => some r
  | _ => none

theorem PTerm.eq_root_of_root? : (p : PTerm C) → {r : Name} → p.root? = some r → p = .root r
  | PTerm.root _, _, h => by
    simp only [Tm.root?, Option.some.injEq] at h
    subst h
    rfl
  | .pvP _, _, h | .app1 _ _, _, h | .app2 _ _ _, _, h | .app3 _ _ _ _, _, h => nomatch h

/-- A path read from its head, as solkey reads it: the root, and the rest of
the path rooted at its first member — `alice.account.balance` is `alice` and
`account.balance`.  `none` for a root alone or a path through an alias. -/
def Tm.shift? : Tm C u → Option (Name × PTerm C)
  | PTerm.field p f => match p.root? with
    | some r => some (r, .root f)
    | none => (Tm.shift? p).map fun (r, p') => (r, .field p' f)
  | PTerm.at p i => match p.root? with
    | some _ => none
    | none => (Tm.shift? p).map fun (r, p') => (r, .at p' i)
  | PTerm.atIn S p i => match p.root? with
    | some _ => none
    | none => (Tm.shift? p).map fun (r, p') => (r, .atIn S p' i)
  | _ => none

@[inherit_doc Tm.shift?]
def PTerm.shift? (p : PTerm C) : Option (Name × PTerm C) := Tm.shift? p

/-- `shift?` splits the Theory's path at its head, in every state. -/
theorem PTerm.shift?_denote (σ : State) : (p : PTerm C) → {r : Name} → {p' : PTerm C} →
    p.shift? = some (r, p') → p.denote σ = .field r :: p'.denote σ
  | PTerm.field p f, _, _, h => by
    simp only [PTerm.shift?, Tm.shift?] at h
    split at h
    · rename_i r hr
      obtain rfl := PTerm.eq_root_of_root? p hr
      simp only [Option.some.injEq, Prod.mk.injEq] at h
      obtain ⟨rfl, rfl⟩ := h
      simp only [tm_denote, List.singleton_append]
    · simp only [Option.map_eq_some_iff] at h
      obtain ⟨⟨r, p'⟩, hp, h⟩ := h
      simp only [Prod.mk.injEq] at h
      obtain ⟨rfl, rfl⟩ := h
      have ih := PTerm.shift?_denote σ p hp
      simp only [tm_denote] at ih ⊢
      rw [ih]
      rfl
  | PTerm.at p i, _, _, h => by
    simp only [PTerm.shift?, Tm.shift?] at h
    split at h
    · nomatch h
    · simp only [Option.map_eq_some_iff] at h
      obtain ⟨⟨r, p'⟩, hp, h⟩ := h
      simp only [Prod.mk.injEq] at h
      obtain ⟨rfl, rfl⟩ := h
      have ih := PTerm.shift?_denote σ p hp
      simp only [tm_denote] at ih ⊢
      rw [ih]
      rfl
  | PTerm.atIn _ p i, _, _, h => by
    simp only [PTerm.shift?, Tm.shift?] at h
    split at h
    · nomatch h
    · simp only [Option.map_eq_some_iff] at h
      obtain ⟨⟨r, p'⟩, hp, h⟩ := h
      simp only [Prod.mk.injEq] at h
      obtain ⟨rfl, rfl⟩ := h
      have ih := PTerm.shift?_denote σ p hp
      simp only [tm_denote] at ih ⊢
      rw [ih]
      rfl
  | .pvP _, _, _, h | PTerm.root _, _, _, h | PTerm.next _, _, _, h
  | PTerm.nextIn _ _, _, _, h => nomatch h

/-- The rest `shift?` leaves has a segment: it is rooted at the first member. -/
theorem PTerm.shift?_hasSeg : (p : PTerm C) → {r : Name} → {p' : PTerm C} →
    p.shift? = some (r, p') → p'.hasSeg = true
  | PTerm.field p _, _, _, h => by
    simp only [PTerm.shift?, Tm.shift?] at h
    split at h
    · simp only [Option.some.injEq, Prod.mk.injEq] at h
      obtain ⟨rfl, rfl⟩ := h
      rfl
    · simp only [Option.map_eq_some_iff] at h
      obtain ⟨⟨r, p'⟩, -, h⟩ := h
      simp only [Prod.mk.injEq] at h
      obtain ⟨rfl, rfl⟩ := h
      rfl
  | PTerm.at p _, _, _, h | PTerm.atIn _ p _, _, _, h => by
    simp only [PTerm.shift?, Tm.shift?] at h
    split at h
    · nomatch h
    · simp only [Option.map_eq_some_iff] at h
      obtain ⟨⟨r, p'⟩, -, h⟩ := h
      simp only [Prod.mk.injEq] at h
      obtain ⟨rfl, rfl⟩ := h
      rfl
  | .pvP _, _, _, h | PTerm.root _, _, _, h | PTerm.next _, _, _, h
  | PTerm.nextIn _ _, _, _, h => nomatch h

def SValT.lit? : SValT C → Option Value
  | .val (.lit v) => some v
  | _ => none

theorem SValT.lit?_eq : (v : SValT C) → {w : Value} → v.lit? = some w → v = .val (.lit w)
  | .val (.lit _), _, h => by cases h; rfl

/-- The word a storage term reads at a path, read off its writes: through a
`save` at that path of a word, and past a `save` at a path that leaves it.
`eq` and `div` are the path's `(·.sameSegs q)` and `(·.diverges q)`,
functions so that the recursion is structural. -/
def Tm.findLitBy (eq div : PTerm C → Bool) : Tm C u → Option Value
  | STerm.save s p v => if eq p then SValT.lit? v else if div p then s.findLitBy eq div else none
  | _ => none

/-- The word `s` reads at `q`, read off its writes (`Tm.findLitBy`); `none`
where its writes do not decide it. -/
def STerm.findLit? (s : STerm C) (q : PTerm C) : Option Value :=
  if q.hasSeg then s.findLitBy (·.sameSegs q) (·.diverges q) else none

/-- The node at `p` in `s` is not a mapping, in every state (`kindFree`): what
a read below a delete needs, since a delete keeps a mapping's members. -/
def STerm.KindFreeAt (s : STerm C) (p : PTerm C) : Prop :=
  ∀ σ, (findSt (s.denote σ) (p.denote σ)).kindFree = true

/-- `hasSeg` gives the Theory's `p ≠ []` in every state. -/
theorem PTerm.denote_ne_nil {p : PTerm C} (hp : p.hasSeg = true) (σ : State) :
    p.denote σ ≠ [] := by
  match p, hp with
  | .pvP _, hp => nomatch hp
  | PTerm.root _, _ => simp only [tm_denote, ne_eq, List.cons_ne_nil, not_false_eq_true]
  | PTerm.field _ _, _ | PTerm.next _, _ | PTerm.at _ _, _ | PTerm.nextIn _ _, _
  | PTerm.atIn _ _ _, _ =>
    simp only [tm_denote, ne_eq, List.append_eq_nil_iff, List.cons_ne_nil, and_false,
      not_false_eq_true]

/-- A closed path denotes its segments in every state. -/
theorem PTerm.denote_of_segs? (σ : State) : (p : PTerm C) → {l : List Seg} →
    p.segs? = some l → p.denote σ = l
  | .pvP _, _, h | PTerm.next _, _, h | PTerm.nextIn _ _, _, h => nomatch h
  | PTerm.root _, _, h => by
    simp only [Tm.segs?, Option.some.injEq] at h
    simp only [tm_denote, h]
  | PTerm.field p _, _, h => by
    simp only [Tm.segs?, Option.map_eq_some_iff] at h
    obtain ⟨a, ha, rfl⟩ := h
    simp only [tm_denote, PTerm.denote_of_segs? σ p ha]
  | PTerm.at p i, _, h | PTerm.atIn _ p i, _, h => by
    simp only [Tm.segs?] at h
    split at h
    · rename_i k hk
      simp only [Option.map_eq_some_iff] at h
      obtain ⟨a, ha, rfl⟩ := h
      rw [Term.eq_of_litInt? hk]
      simp only [tm_denote, PTerm.denote_of_segs? σ p ha, asInt]
    · cases h

/-- Two paths that have the shapes `a ++ b` have the shape of their halves. -/
theorem SegT.matches_append : (a b : List SegT) → (p q : List Seg) → SegT.matches a p = true →
    SegT.matches b q = true → SegT.matches (a ++ b) (p ++ q) = true
  | [], _, [], _, _, hb => hb
  | x :: a, b, s :: p, q, ha, hb => by
    simp only [SegT.matches, Bool.and_eq_true] at ha
    simp only [List.cons_append, SegT.matches, ha.1, SegT.matches_append a b p q ha.2 hb,
      Bool.and_self]
  | [], _, _ :: _, _, ha, _ | _ :: _, _, [], _, ha, _ => nomatch ha

/-- A path has its shape in every state. -/
theorem PTerm.shape?_matches (σ : State) : (p : PTerm C) → {a : List SegT} →
    p.shape? = some a → SegT.matches a (p.denote σ) = true
  | .pvP _, _, h => nomatch h
  | PTerm.root _, _, h => by
    simp only [Tm.shape?, Option.some.injEq] at h
    subst h
    simp only [tm_denote, SegT.matches, SegT.fits, BEq.rfl, Bool.and_self]
  | PTerm.field p _, _, h => by
    simp only [Tm.shape?, Option.map_eq_some_iff] at h
    obtain ⟨a, ha, rfl⟩ := h
    simp only [tm_denote]
    exact SegT.matches_append _ _ _ _ (PTerm.shape?_matches σ p ha)
      (by simp only [SegT.matches, SegT.fits, BEq.rfl, Bool.and_self])
  | PTerm.next p, _, h | PTerm.nextIn _ p, _, h => by
    simp only [Tm.shape?, Option.map_eq_some_iff] at h
    obtain ⟨a, ha, rfl⟩ := h
    simp only [tm_denote]
    exact SegT.matches_append _ _ _ _ (PTerm.shape?_matches σ p ha) rfl
  | PTerm.at p i, _, h | PTerm.atIn _ p i, _, h => by
    simp only [Tm.shape?, Option.map_eq_some_iff] at h
    obtain ⟨a, ha, rfl⟩ := h
    simp only [tm_denote]
    refine SegT.matches_append _ _ _ _ (PTerm.shape?_matches σ p ha) ?_
    cases hi : Term.litInt? i with
    | none => rfl
    | some k =>
      rw [Term.eq_of_litInt? hi]
      simp only [tm_denote, asInt, SegT.matches, SegT.fits, BEq.rfl, Bool.and_self]

/-- `apart` decides the segments as it says. -/
theorem SegT.apart_sound : {x y : SegT} → {d : Bool} → {s t : Seg} → x.apart y = some d →
    x.fits s = true → y.fits t = true → (d = true → s ≠ t) ∧ (d = false → s = t)
  | .field _, .field _, _, .field _, .field _, h, hs, ht => by
    simp only [SegT.fits, beq_iff_eq] at hs ht
    simp only [SegT.apart, Option.some.injEq] at h
    subst hs ht h
    exact ⟨fun hne e => (bne_iff_ne.1 hne) (Seg.field.inj e),
      fun he => by rw [bne_eq_false_iff_eq.1 he]⟩
  | .at (some _), .at (some _), _, .at _, .at _, h, hs, ht => by
    simp only [SegT.fits, beq_iff_eq] at hs ht
    simp only [SegT.apart, Option.some.injEq] at h
    subst hs ht h
    exact ⟨fun hne e => (bne_iff_ne.1 hne) (Seg.at.inj e),
      fun he => by rw [bne_eq_false_iff_eq.1 he]⟩
  | .field _, .at _, _, .field _, .at _, h, _, _ | .at _, .field _, _, .at _, .field _, h, _, _ => by
    simp only [SegT.apart, Option.some.injEq] at h
    subst h
    exact ⟨fun _ e => Seg.noConfusion e, fun h => nomatch h⟩
  | .at none, .at _, _, _, _, h, _, _ | .at (some _), .at none, _, _, _, h, _, _ => by
    simp only [SegT.apart, reduceCtorEq] at h
  | .field _, _, _, .at _, _, _, hs, _ | .at _, _, _, .field _, _, _, hs, _ => by
    simp only [SegT.fits, Bool.false_eq_true] at hs
  | _, .field _, _, _, .at _, _, _, ht | _, .at _, _, _, .field _, _, _, ht => by
    simp only [SegT.fits, Bool.false_eq_true] at ht

/-- Shapes that diverge have paths that diverge. -/
theorem SegT.diverges_sound : (a b : List SegT) → (p q : List Seg) → SegT.diverges a b = true →
    SegT.matches a p = true → SegT.matches b q = true → Theory.StValue.diverges p q = true
  | x :: a, y :: b, s :: p, t :: q, hd, ha, hb => by
    simp only [SegT.matches, Bool.and_eq_true] at ha hb
    simp only [SegT.diverges] at hd
    simp only [Theory.StValue.diverges]
    cases hx : x.apart y with
    | none => rw [hx] at hd; cases hd
    | some d =>
      rw [hx] at hd
      have hst := SegT.apart_sound hx ha.1 hb.1
      cases d with
      | true => rw [if_neg (hst.1 rfl)]
      | false =>
        rw [if_pos (hst.2 rfl)]
        exact SegT.diverges_sound a b p q hd ha.2 hb.2
  | [], _, _, _, hd, _, _ | _ :: _, [], _, _, hd, _, _ => nomatch hd
  | _ :: _, _ :: _, [], _, _, ha, _ => nomatch ha
  | _ :: _, _ :: _, _ :: _, [], _, _, hb => nomatch hb

/-- `PTerm.diverges` gives the Theory's `diverges` in every state. -/
theorem PTerm.diverges_denote {p q : PTerm C} (h : p.diverges q = true) (σ : State) :
    Theory.StValue.diverges (p.denote σ) (q.denote σ) = true := by
  unfold PTerm.diverges at h
  split at h
  · rename_i a b ha hb
    exact SegT.diverges_sound a b _ _ h (p.shape?_matches σ ha) (q.shape?_matches σ hb)
  · exact absurd h Bool.false_ne_true

/-- `PTerm.divergesLen` gives the Theory's `diverges q (p ++ [lengthSeg])` in
every state. -/
theorem PTerm.divergesLen_denote {q p : PTerm C} (h : q.divergesLen p = true) (σ : State) :
    Theory.StValue.diverges (q.denote σ) (p.denote σ ++ [lengthSeg]) = true := by
  unfold PTerm.divergesLen at h
  split at h
  · rename_i a b ha hb
    exact SegT.diverges_sound _ _ _ _ h (q.shape?_matches σ ha)
      (SegT.matches_append _ _ _ _ (p.shape?_matches σ hb) (by decide))
  · exact absurd h Bool.false_ne_true

/-- A check erased leaves the Theory's path, in every state. -/
theorem PTerm.eraseChecks_denote (σ : State) :
    (p : PTerm C) → (Tm.eraseChecks p).denote σ = p.denote σ
  | .pvP _ | PTerm.root _ => rfl
  | PTerm.field p _ | PTerm.next p | PTerm.at p _ | PTerm.nextIn _ p | PTerm.atIn _ p _ => by
    simp only [Tm.eraseChecks, tm_denote, PTerm.eraseChecks_denote σ p]

/-- A check erased leaves a segment where there was one. -/
theorem PTerm.eraseChecks_hasSeg : (p : PTerm C) → PTerm.hasSeg (Tm.eraseChecks p) = p.hasSeg
  | .pvP _ | PTerm.root _ | PTerm.field _ _ | PTerm.next _ | PTerm.at _ _
  | PTerm.nextIn _ _ | PTerm.atIn _ _ _ => rfl

/-- `sameSegs` gives one Theory path in every state. -/
theorem PTerm.sameSegs_denote (σ : State) (p q : PTerm C) (h : p.sameSegs q = true) :
    p.denote σ = q.denote σ := by
  rw [← PTerm.eraseChecks_denote σ p, ← PTerm.eraseChecks_denote σ q]
  simp only [PTerm.sameSegs, beq_iff_eq] at h
  rw [h]

/-- Paths of the same segments are both bare aliases or neither. -/
theorem PTerm.sameSegs_hasSeg (p q : PTerm C) (h : p.sameSegs q = true) : p.hasSeg = q.hasSeg := by
  rw [← PTerm.eraseChecks_hasSeg p, ← PTerm.eraseChecks_hasSeg q]
  simp only [PTerm.sameSegs, beq_iff_eq] at h
  rw [h]

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
  /-- **`findOnSave`**: `find(save(s, p, v), q) ⇝ v` for a word `v`, `q` the
  path `p` its checks aside (`sameSegs`; `find_copyTo_same`). -/
  | findOnSave {s : STerm C} {p q : PTerm C} {v : Value} (hp : p.hasSeg = true := by rfl)
      (hq : p.sameSegs q = true := by first | rfl | exact PTerm.sameSegs_refl _) :
      TermTaclet tm{ find(save(s, p, lit(v)), q) } tm{ lit(v) }
  /-- **`findOnSaveFrame`**: a read at a path that leaves the written one does
  not see the write, `find(save(s, p, v), q) ⇝ find(s, q)` (`find_copyTo_frame`). -/
  | findOnSaveFrame {s : STerm C} {p q : PTerm C} {v : SValT C}
      (h : p.diverges q = true := by rfl) :
      TermTaclet tm{ find(save(s, p, v), q) } tm{ find(s, q) }
  /-- **`findMemberCons`**: `find(s, r.p) ⇝ find(select(s, r), p)`, the path read
  from its head (`shift?`), as solkey does: the path `consr(consr(nil, r), f)`
  turned into `cons(r, cons(f, nil))` (`consRcons`, `consRnil`), then
  `findDefinitionMemberCons`. -/
  | findMemberCons {s : STerm C} {p : PTerm C} {r : Name} {p' : PTerm C}
      (h : p.shift? = some (r, p') := by rfl) :
      TermTaclet tm{ find(s, p) } tm{ find(select(s, r), p') }
  /-- **`selectOnSaveMember`**: the write at `r.p`, seen from `r`, is a write
  at `p`: `find(select(save(s, r.p, v), r), q) ⇝ find(save(select(s, r), p, v), q)`
  — solkey's `selectOnSaveCons` at `a1 = a2`. -/
  | selectOnSaveMember {s : STerm C} {p : PTerm C} {r : Name} {p' : PTerm C} {v : SValT C}
      {q : PTerm C} (h : p.shift? = some (r, p') := by rfl) :
      TermTaclet tm{ find(select(save(s, p, v), r), q) } tm{ find(save(select(s, r), p', v), q) }
  /-- **`selectOnSaveFrame`**: a write under another root is not seen from `r`:
  `find(select(save(s, r'.p, v), r), q) ⇝ find(select(s, r), q)` — solkey's
  `selectOnSaveCons` at `a1 ≠ a2`. -/
  | selectOnSaveFrame {s : STerm C} {p : PTerm C} {r r' : Name} {p' : PTerm C} {v : SValT C}
      {q : PTerm C} (h : p.shift? = some (r', p') := by rfl) (hr : r' ≠ r := by decide) :
      TermTaclet tm{ find(select(save(s, p, v), r), q) } tm{ find(select(s, r), q) }
  /-- **`selectOnDelAtMember`**: the delete at `r.p`, seen from `r`, is a delete
  at `p`: `find(select(delAt(s, r.p), r), q) ⇝ find(delAt(select(s, r), p), q)`. -/
  | selectOnDelAtMember {s : STerm C} {p : PTerm C} {r : Name} {p' : PTerm C} {q : PTerm C}
      (h : p.shift? = some (r, p') := by rfl) :
      TermTaclet tm{ find(select(delAt(s, p), r), q) } tm{ find(delAt(select(s, r), p'), q) }
  /-- **`selectOnDelAtFrame`**: a delete under another root is not seen from `r`. -/
  | selectOnDelAtFrame {s : STerm C} {p : PTerm C} {r r' : Name} {p' : PTerm C} {q : PTerm C}
      (h : p.shift? = some (r', p') := by rfl) (hr : r' ≠ r := by decide) :
      TermTaclet tm{ find(select(delAt(s, p), r), q) } tm{ find(select(s, r), q) }
  /-- **`selectOnSaveMemberIn`**: `selectOnSaveMember` in a storage context `K`:
  `find(K[select(save(s, r.p, v), r)], q) ⇝ find(K[save(select(s, r), p, v)], q)`. -/
  | selectOnSaveMemberIn (K : SCtx C) {s : STerm C} {p : PTerm C} {r : Name} {p' : PTerm C}
      {v : SValT C} {q : PTerm C} (h : p.shift? = some (r, p') := by rfl) :
      TermTaclet tm{ find(‹K.fill tm{ select(save(s, p, v), r) }›, q) }
        tm{ find(‹K.fill tm{ save(select(s, r), p', v) }›, q) }
  /-- **`selectOnSaveFrameIn`**: `selectOnSaveFrame` in a storage context. -/
  | selectOnSaveFrameIn (K : SCtx C) {s : STerm C} {p : PTerm C} {r r' : Name} {p' : PTerm C}
      {v : SValT C} {q : PTerm C} (h : p.shift? = some (r', p') := by rfl) (hr : r' ≠ r := by decide) :
      TermTaclet tm{ find(‹K.fill tm{ select(save(s, p, v), r) }›, q) }
        tm{ find(‹K.fill tm{ select(s, r) }›, q) }
  /-- **`selectOnDelAtMemberIn`**: `selectOnDelAtMember` in a storage context. -/
  | selectOnDelAtMemberIn (K : SCtx C) {s : STerm C} {p : PTerm C} {r : Name} {p' : PTerm C}
      {q : PTerm C} (h : p.shift? = some (r, p') := by rfl) :
      TermTaclet tm{ find(‹K.fill tm{ select(delAt(s, p), r) }›, q) }
        tm{ find(‹K.fill tm{ delAt(select(s, r), p') }›, q) }
  /-- **`selectOnDelAtFrameIn`**: `selectOnDelAtFrame` in a storage context. -/
  | selectOnDelAtFrameIn (K : SCtx C) {s : STerm C} {p : PTerm C} {r r' : Name} {p' : PTerm C}
      {q : PTerm C} (h : p.shift? = some (r', p') := by rfl) (hr : r' ≠ r := by decide) :
      TermTaclet tm{ find(‹K.fill tm{ select(delAt(s, p), r) }›, q) }
        tm{ find(‹K.fill tm{ select(s, r) }›, q) }
  /-- **`findOnDelAt`**: where `s` reads the word `w` at `p`, the delete
  leaves its default, `find(delAt(s, p), q) ⇝ default(w)`, `q` the path `p`
  its checks aside (`find_delAt_same`, `delValueDefault`). -/
  | findOnDelAt {s : STerm C} {p q : PTerm C} {w : Value}
      (hw : TermTaclet tm{ find(s, p) } tm{ lit(w) }) (hp : p.hasSeg = true := by rfl)
      (hq : p.sameSegs q = true := by first | rfl | exact PTerm.sameSegs_refl _) :
      TermTaclet tm{ find(delAt(s, p), q) } tm{ lit(‹primDefault w›) }
  /-- **`findOnDelAtValue`**: the delete leaves at its path the default of
  what was there, `find(delAt(s, p), q) ⇝ delValue(find(s, q))`, `q` the path
  `p` its checks aside (`find_delAt_same`). -/
  | findOnDelAtValue {s : STerm C} {p q : PTerm C} (hp : p.hasSeg = true := by rfl)
      (hq : p.sameSegs q = true := by first | rfl | exact PTerm.sameSegs_refl _) :
      TermTaclet tm{ find(delAt(s, p), q) } tm{ delValue(find(s, q)) }
  /-- **`delValueLit`**: the default of a word, `delValue(w) ⇝ default(w)`
  (`delValueDefault`). -/
  | delValueLit {w : Value} : TermTaclet tm{ delValue(lit(w)) } tm{ lit(‹primDefault w›) }
  /-- **`findOnDelAtBelow`**: below a deleted node that is not a mapping,
  every word reads its default, `find(delAt(s, p), q) ⇝ default(w)`, where `q`
  goes on below `p` and `s` reads the word `w` at `q` off its writes
  (`STerm.findLit?`; `find_delAt_below`, `delValueDefault`).  `hk`, that the
  node is not a mapping (which keeps its members), is the chain's premise. -/
  | findOnDelAtBelow {s : STerm C} {p q : PTerm C} {w : Value} (hk : s.KindFreeAt p)
      (hw : s.findLit? q = some w := by rfl) (hp : p.hasSeg = true := by rfl)
      (hq : q.extends p = true := by rfl) :
      TermTaclet tm{ find(delAt(s, p), q) } tm{ lit(‹primDefault w›) }
  /-- **`findOnDelAtFrame`**: a read off the deleted path does not see the
  delete (`find_delAt_frame`). -/
  | findOnDelAtFrame {s : STerm C} {p q : PTerm C} (h : p.diverges q = true := by rfl) :
      TermTaclet tm{ find(delAt(s, p), q) } tm{ find(s, q) }
  /-- **`findOnPushFrame`**: a read off the array's path does not see a push
  (`find_pushT_frame`). -/
  | findOnPushFrame {s : STerm C} {p q : PTerm C} {v : SValT C}
      (h : p.diverges q = true := by rfl) :
      TermTaclet tm{ find(save(save(s, p[p.length], v), p.length, p.length + 1), q) } tm{ find(s, q) }
  /-- **`findOnPopFrame`**: a read off the array's path does not see a pop
  (`find_popT_frame`). -/
  | findOnPopFrame {s : STerm C} {p q : PTerm C} (h : p.diverges q = true := by rfl) :
      TermTaclet tm{ find(save(delAt(s, p[p.length - 1]), p.length, p.length - 1), q) } tm{ find(s, q) }
  /-- **`lenOnSaveFrame`**: a length read off the written path does not see
  the write, `len(save(s, q, v), p) ⇝ len(s, p)` where `q` leaves `p.length`
  (`find_copyTo_frame`). -/
  | lenOnSaveFrame {s : STerm C} {q p : PTerm C} {v : SValT C}
      (h : q.divergesLen p = true := by rfl) :
      TermTaclet tm{ find(save(s, q, v), p.length) } tm{ find(s, p.length) }
  /-- **`lenOnDelAtFrame`**: a length read off the deleted path does not see
  the delete (`find_delAt_frame`). -/
  | lenOnDelAtFrame {s : STerm C} {q p : PTerm C} (h : q.divergesLen p = true := by rfl) :
      TermTaclet tm{ find(delAt(s, q), p.length) } tm{ find(s, p.length) }
  /-- Any law of the Theory: `t` and `t'` have one Theory value in every
  state. -/
  | theory {t t' : Term C} (h : Term.Theq t t') : TermTaclet t t'
  /-- A rule read right to left, `rw [← r]`. -/
  | symm {t t' : Term C} (r : TermTaclet t t') : TermTaclet t' t

/-- **`findOnDelAtSave`**: a delete over a written word reads the word's
default, `find(delAt(save(s, p', v), p), q) ⇝ default(v)`, the three paths
one path their checks aside: `findOnDelAt` with `findOnSave` as its premise. -/
theorem TermTaclet.findOnDelAtSave {s : STerm C} {p' p q : PTerm C} {v : Value}
    (hp : p.hasSeg = true := by rfl)
    (hp' : p'.sameSegs p = true := by first | rfl | exact PTerm.sameSegs_refl _)
    (hq : p.sameSegs q = true := by first | rfl | exact PTerm.sameSegs_refl _) :
    TermTaclet tm{ find(delAt(save(s, p', lit(v)), p), q) } tm{ lit(‹primDefault v›) } :=
  .findOnDelAt (.findOnSave ((PTerm.sameSegs_hasSeg p' p hp').trans hp) hp') hp hq

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
    (s : STerm C) → {w : Value} → s.findLitBy (·.sameSegs q) (·.diverges q) = some w →
      Term.Theq (.find s q) (.lit w)
  | STerm.save s p v, w, h => fun σ => by
    simp only [Tm.findLitBy] at h
    split at h
    · rename_i hpq
      obtain rfl := SValT.lit?_eq v h
      have hp : PTerm.hasSeg p = true := (PTerm.sameSegs_hasSeg p q hpq).trans hq
      simp only [tm_denote, ← PTerm.sameSegs_denote σ p q hpq,
        find_copyTo_same _ (PTerm.denote_ne_nil hp σ), copyVal]
      exact Equiv.refl _
    · split at h
      · rename_i hd
        have ih := Tm.findLitBy_theq hq s h σ
        simp only [tm_denote] at ih ⊢
        rw [find_copyTo_frame _ _ _ _ (PTerm.diverges_denote hd σ)]
        exact ih
      · nomatch h
  | .pvS _, _, h | STerm.storage, _, h | STerm.select _ _, _, h | STerm.delAt _ _, _, h
  | STerm.pushSlot _ _ _, _, h | STerm.pop _ _, _, h | STerm.shrink _ _, _, h
  | STerm.extend _ _ _, _, h | STerm.push _ _ _, _, h => nomatch h

theorem STerm.findLit?_theq {s : STerm C} {q : PTerm C} {w : Value} (h : s.findLit? q = some w) :
    Term.Theq (.find s q) (.lit w) := by
  unfold STerm.findLit? at h
  split at h
  · exact Tm.findLitBy_theq ‹_› s h
  · nomatch h

/-- **Each term taclet is sound**: its two terms have one Theory value in
every state.  A case is `denote` unfolded and the Theory's lemma. -/
theorem TermTaclet.sound {t t' : Term C} : TermTaclet t t' → Term.Theq t t'
  | @findOnSave _ s p q v hp hq => fun σ => by
    simp only [tm_denote, ← PTerm.sameSegs_denote σ p q hq,
      find_copyTo_same _ (PTerm.denote_ne_nil hp σ), copyVal]
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
  | @findOnDelAt _ s p q w hw hp hq => fun σ => by
    have hr : findSt (s.denote σ) (p.denote σ) = .prim w := Equiv.prim_iff.1 (hw.sound σ)
    simp only [tm_denote, ← PTerm.sameSegs_denote σ p q hq,
      find_delAt_same _ (PTerm.denote_ne_nil hp σ), hr, delValueDefault]
    exact Equiv.refl _
  | @findOnDelAtValue _ s p q hp hq => fun σ => by
    simp only [tm_denote, ← PTerm.sameSegs_denote σ p q hq,
      find_delAt_same _ (PTerm.denote_ne_nil hp σ)]
    exact Equiv.refl _
  | .delValueLit => fun σ => by
    simp only [tm_denote, delValueDefault]
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
  | .lenOnSaveFrame h => fun σ => by
    simp only [tm_denote, find_copyTo_frame _ _ _ _ (PTerm.divergesLen_denote h σ)]
    exact Equiv.refl _
  | .lenOnDelAtFrame h => fun σ => by
    simp only [tm_denote, find_delAt_frame _ (PTerm.divergesLen_denote h σ)]
    exact Equiv.refl _
  | .theory h => h
  | .symm r => r.sound.symm

end Solidity
