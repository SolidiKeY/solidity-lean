import Solidity.Calculus.Decide

/-!
# Closing a reduction by its terms: `LFml.syn`

KeY closes `select(store(h, o, f, v), o, f) = v` by rewriting and syntactic
equality; it never evaluates the heap.  What `Fml.reduce` leaves is mostly of
that kind: a chain of premises `t ≐ t`, one per term an update computed, each
saying that the term returns, and a conclusion `a ≐ b` whose two sides compute
the same thing under different guards (`seq d a`: `a`, once `d` returns).
`sol_decide`'s general step (`LFml.valid_iff_cons`) evaluates all of it in
every storage shape, which is where its time goes.

`LFml.syn` decides such a formula by its terms alone, as KeY's simplifier
would:

* a term returns when it sits in a strict position (`LTerm.strict`: one its
  term cannot return without) of a premise's side, is a literal, or is built
  from such terms (`LTerm.known`, `LTerm.rets`: a guard and its value, an
  operation on operands that return what a known operation's do, a `kite` on
  integer keys whose branch returns);
* two terms that return return the same value when they are equal once their
  guards are dropped (`LTerm.core`) and `(x - a) + a` is cancelled
  (`LTerm.arith`), or when they are the two sides of a premise `p ≐ q` so;
* a premise `a ≐ b` or `¬(a ≐ b)` on two keys settles every `kite` on them,
  as `select(store(h, k, v), j)` is read under `k = j` or `k ≠ j`
  (`Keys`, `Apart`);
* a quantifier is decided by its body, where no fact known so far mentions
  its local; a read of a snapshot (`\old`, `LTerm.findP`) compares with a
  live read where both return.

`LFml.syn_valid`: a formula `syn` accepts holds in every state.  `syn` is a
`Bool` computation, so the kernel checks it by evaluation, with no `simp`
over the semantics.  It is incomplete — it does not split on keys the
premises leave open, instantiate a quantified premise (a layout premise at a
quantified key), or reason about arithmetic beyond the cancellation —
and `sol_decide` falls back to the full procedure where it says no.
-/

namespace Solidity

namespace Decide

open Semantics SemanticsProperties

/-- `t` returns in `σ`. -/
def Returns (σ : State) (t : LTerm) : Prop := ∃ v, t.eval σ = .ok v

/-! ## Strict positions -/

mutual

/-- The term and the subterms it cannot return without: not the branches of
an `ite`/`kite`, either side of an `orElse`, or the right operand of
`&&`/`||`, which the left may decide alone. -/
def LTerm.strict : LTerm → List LTerm
  | t@(.lit _) | t@(.var _) | t@.err | t@(.env _) => [t]
  | t@(.binop op _ a b) =>
    t :: a.strict ++ (if op = .and ∨ op = .or then [] else b.strict)
  | t@(.unop _ _ a) | t@(.ite a _ _) | t@(.zero a) => t :: a.strict
  | t@(.find s q) | t@(.has s q) | t@(.kmap _ s q) | t@(.len s q) | t@(.findP s q) =>
    t :: s.strict ++ q.strict
  | t@(.sok s) => t :: s.strict
  | t@(.pok q) => t :: q.strict
  | t@(.seq d a) => t :: d.strict ++ a.strict
  | t@(.orElse _ _) => [t]
  | t@(.kite a b _ _) => t :: a.strict ++ b.strict

/-- The terms a path cannot be evaluated without: its keys. -/
def LPath.strict : LPath → List LTerm
  | .root _ => []
  | .field q _ => q.strict
  | .at q k => q.strict ++ k.strict

/-- The terms a storage cannot be evaluated without: what it writes, where. -/
def LStor.strict : LStor → List LTerm
  | .init => []
  | .save s q w => w.strict ++ s.strict ++ q.strict
  | .del s q => s.strict ++ q.strict
  | .arr _ s q w => w.strict ++ s.strict ++ q.strict
  | .copy s q src sq => src.strict ++ sq.strict ++ s.strict ++ q.strict

end

/-- What `evalBinop` returns with the right operand returning `w` it returns
with any right operand returning `w`. -/
theorem evalBinop_right {op : BinOp} {p : PrimTy} {x : Value} {rb : Res Value} {v : Value}
    (h : evalBinop op p x rb = .ok v) (hstrict : ¬(op = .and ∨ op = .or)) :
    ∃ w, rb = .ok w := by
  cases rb with
  | ok w => exact ⟨w, rfl⟩
  | error e =>
    exfalso
    revert h
    unfold evalBinop
    split
    · exact absurd (Or.inl rfl) hstrict
    · exact absurd (Or.inr rfl) hstrict
    · simp [bind, Except.bind]

mutual

/-- A term that returns returns at each of its strict positions. -/
theorem LTerm.strict_returns {σ : State} : (t : LTerm) → Returns σ t →
    ∀ u ∈ t.strict, Returns σ u
  | .lit _, h, u, hu | .var _, h, u, hu | .err, h, u, hu | .env _, h, u, hu => by
    simp only [LTerm.strict, List.mem_singleton] at hu; subst hu; exact h
  | .binop op p a b, ⟨v, h⟩, u, hu => by
    simp only [LTerm.strict, List.mem_cons, List.mem_append] at hu
    simp only [LTerm.eval] at h
    obtain ⟨x, ha, hb⟩ := Res.bind_eq_ok.1 h
    rcases hu with (rfl | hu) | hu
    · exact ⟨v, by simp only [LTerm.eval]; exact h⟩
    · exact LTerm.strict_returns a ⟨x, ha⟩ u hu
    · split at hu
      · simp at hu
      · rename_i hop
        obtain ⟨w, hw⟩ := evalBinop_right hb hop
        exact LTerm.strict_returns b ⟨w, hw⟩ u hu
  | .unop op p a, ⟨v, h⟩, u, hu => by
    simp only [LTerm.strict, List.mem_cons] at hu
    rcases hu with rfl | hu
    · exact ⟨v, h⟩
    · simp only [LTerm.eval] at h
      obtain ⟨x, ha, -⟩ := Res.bind_eq_ok.1 h
      exact LTerm.strict_returns a ⟨x, ha⟩ u hu
  | .ite c a b, ⟨v, h⟩, u, hu => by
    simp only [LTerm.strict, List.mem_cons] at hu
    rcases hu with rfl | hu
    · exact ⟨v, h⟩
    · simp only [LTerm.eval] at h
      obtain ⟨x, hc, -⟩ := Res.bind_eq_ok.1 h
      exact LTerm.strict_returns c ⟨x, hc⟩ u hu
  | .zero a, ⟨v, h⟩, u, hu => by
    simp only [LTerm.strict, List.mem_cons] at hu
    rcases hu with rfl | hu
    · exact ⟨v, h⟩
    · simp only [LTerm.eval] at h
      obtain ⟨x, ha, -⟩ := Res.bind_eq_ok.1 h
      exact LTerm.strict_returns a ⟨x, ha⟩ u hu
  | .find s q, ⟨v, h⟩, u, hu | .has s q, ⟨v, h⟩, u, hu | .kmap _ s q, ⟨v, h⟩, u, hu
  | .len s q, ⟨v, h⟩, u, hu | .findP s q, ⟨v, h⟩, u, hu => by
    simp only [LTerm.strict, List.mem_cons, List.mem_append] at hu
    rcases hu with (rfl | hu) | hu
    · exact ⟨v, h⟩
    · simp only [LTerm.eval] at h
      obtain ⟨x, hs, -⟩ := Res.bind_eq_ok.1 h
      exact LStor.strict_returns s ⟨x, hs⟩ u hu
    · simp only [LTerm.eval] at h
      obtain ⟨x, -, h⟩ := Res.bind_eq_ok.1 h
      obtain ⟨y, hq, -⟩ := Res.bind_eq_ok.1 h
      exact LPath.strict_returns q ⟨y, hq⟩ u hu
  | .sok s, ⟨v, h⟩, u, hu => by
    simp only [LTerm.strict, List.mem_cons] at hu
    rcases hu with rfl | hu
    · exact ⟨v, h⟩
    · simp only [LTerm.eval] at h
      obtain ⟨x, hs, -⟩ := Res.bind_eq_ok.1 h
      exact LStor.strict_returns s ⟨x, hs⟩ u hu
  | .pok q, ⟨v, h⟩, u, hu => by
    simp only [LTerm.strict, List.mem_cons] at hu
    rcases hu with rfl | hu
    · exact ⟨v, h⟩
    · simp only [LTerm.eval] at h
      obtain ⟨x, hq, -⟩ := Res.bind_eq_ok.1 h
      exact LPath.strict_returns q ⟨x, hq⟩ u hu
  | .seq d a, ⟨v, h⟩, u, hu => by
    simp only [LTerm.strict, List.mem_cons, List.mem_append] at hu
    simp only [LTerm.eval] at h
    obtain ⟨x, hd, ha⟩ := Res.bind_eq_ok.1 h
    rcases hu with (rfl | hu) | hu
    · exact ⟨v, by simp only [LTerm.eval]; exact h⟩
    · exact LTerm.strict_returns d ⟨x, hd⟩ u hu
    · exact LTerm.strict_returns a ⟨v, ha⟩ u hu
  | .orElse _ _, h, u, hu => by
    simp only [LTerm.strict, List.mem_singleton] at hu; subst hu; exact h
  | .kite a b t e, ⟨v, h⟩, u, hu => by
    simp only [LTerm.strict, List.mem_cons, List.mem_append] at hu
    simp only [LTerm.eval] at h
    obtain ⟨i, hi, h⟩ := Res.bind_eq_ok.1 h
    obtain ⟨x, ha, -⟩ := Res.bind_eq_ok.1 hi
    obtain ⟨j, hj, -⟩ := Res.bind_eq_ok.1 h
    obtain ⟨y, hb, -⟩ := Res.bind_eq_ok.1 hj
    rcases hu with (rfl | hu) | hu
    · refine ⟨v, ?_⟩
      simp only [LTerm.eval]
      rw [Res.bind_eq_ok]
      exact ⟨i, hi, h⟩
    · exact LTerm.strict_returns a ⟨x, ha⟩ u hu
    · exact LTerm.strict_returns b ⟨y, hb⟩ u hu

/-- A path that evaluates evaluates its keys. -/
theorem LPath.strict_returns {σ : State} : (q : LPath) → (∃ ps, q.eval σ = .ok ps) →
    ∀ u ∈ q.strict, Returns σ u
  | .root _, _, u, hu => by simp [LPath.strict] at hu
  | .field q _, ⟨ps, h⟩, u, hu => by
    simp only [LPath.strict] at hu
    simp only [LPath.eval] at h
    obtain ⟨x, hq, -⟩ := Res.bind_eq_ok.1 h
    exact LPath.strict_returns q ⟨x, hq⟩ u hu
  | .at q k, ⟨ps, h⟩, u, hu => by
    simp only [LPath.strict, List.mem_append] at hu
    simp only [LPath.eval] at h
    obtain ⟨x, hq, h⟩ := Res.bind_eq_ok.1 h
    obtain ⟨i, hk, -⟩ := Res.bind_eq_ok.1 h
    obtain ⟨y, hk, -⟩ := Res.bind_eq_ok.1 hk
    rcases hu with hu | hu
    · exact LPath.strict_returns q ⟨x, hq⟩ u hu
    · exact LTerm.strict_returns k ⟨y, hk⟩ u hu

/-- A storage that evaluates evaluates what it writes and where. -/
theorem LStor.strict_returns {σ : State} : (s : LStor) → (∃ sv, s.eval σ = .ok sv) →
    ∀ u ∈ s.strict, Returns σ u
  | .init, _, u, hu => by simp [LStor.strict] at hu
  | .save s q w, ⟨sv, h⟩, u, hu => by
    simp only [LStor.strict, List.mem_append] at hu
    simp only [LStor.eval] at h
    obtain ⟨x, hw, h⟩ := Res.bind_eq_ok.1 h
    obtain ⟨y, hs, h⟩ := Res.bind_eq_ok.1 h
    obtain ⟨z, hq, -⟩ := Res.bind_eq_ok.1 h
    rcases hu with (hu | hu) | hu
    · exact LTerm.strict_returns w ⟨x, hw⟩ u hu
    · exact LStor.strict_returns s ⟨y, hs⟩ u hu
    · exact LPath.strict_returns q ⟨z, hq⟩ u hu
  | .del s q, ⟨sv, h⟩, u, hu => by
    simp only [LStor.strict, List.mem_append] at hu
    simp only [LStor.eval] at h
    obtain ⟨y, hs, h⟩ := Res.bind_eq_ok.1 h
    obtain ⟨z, hq, -⟩ := Res.bind_eq_ok.1 h
    rcases hu with hu | hu
    · exact LStor.strict_returns s ⟨y, hs⟩ u hu
    · exact LPath.strict_returns q ⟨z, hq⟩ u hu
  | .arr _ s q w, ⟨sv, h⟩, u, hu => by
    simp only [LStor.strict, List.mem_append] at hu
    simp only [LStor.eval] at h
    obtain ⟨x, hw, h⟩ := Res.bind_eq_ok.1 h
    obtain ⟨y, hs, h⟩ := Res.bind_eq_ok.1 h
    obtain ⟨z, hq, -⟩ := Res.bind_eq_ok.1 h
    rcases hu with (hu | hu) | hu
    · exact LTerm.strict_returns w ⟨x, hw⟩ u hu
    · exact LStor.strict_returns s ⟨y, hs⟩ u hu
    · exact LPath.strict_returns q ⟨z, hq⟩ u hu
  | .copy s q src sq, ⟨sv, h⟩, u, hu => by
    simp only [LStor.strict, List.mem_append] at hu
    simp only [LStor.eval] at h
    obtain ⟨a, ha, h⟩ := Res.bind_eq_ok.1 h
    obtain ⟨b, hb, h⟩ := Res.bind_eq_ok.1 h
    obtain ⟨_, _, h⟩ := Res.bind_eq_ok.1 h
    obtain ⟨y, hs, h⟩ := Res.bind_eq_ok.1 h
    obtain ⟨z, hq, -⟩ := Res.bind_eq_ok.1 h
    rcases hu with ((hu | hu) | hu) | hu
    · exact LStor.strict_returns src ⟨a, ha⟩ u hu
    · exact LPath.strict_returns sq ⟨b, hb⟩ u hu
    · exact LStor.strict_returns s ⟨y, hs⟩ u hu
    · exact LPath.strict_returns q ⟨z, hq⟩ u hu

end

/-! ## Dropping the guards -/

/-- What the premises say of pairs of keys: `(true, a, b)` that `a` and `b`
return one value (`a ≐ b`), `(false, a, b)` that they never do
(`¬(a ≐ b)`). -/
abbrev Keys := List (Bool × LTerm × LTerm)

/-- The facts of `ne` hold in `σ`. -/
def Apart (σ : State) (ne : Keys) : Prop :=
  ∀ p ∈ ne, ∀ x y, p.2.1.eval σ = .ok x → p.2.2.eval σ = .ok y → (x = y ↔ p.1 = true)

mutual

/-- The term with its guards dropped: `seq d a` is `a`.  Not inside the
left side of an `orElse`, where a guard that halts picks the right side.  A
read past the live length (`findP`) for a live one, which returns the same
where the live one returns (`SVal.find_of_findLive`): so a read after the
writes compares with a snapshot's (`\old`).  A
`kite` on two keys `ne` says are equal is its `then` branch, on two it keeps
apart its `else` branch, as KeY reads `select(store(h, k, v), j)` under
`k = j` or `k ≠ j`. -/
def LTerm.core (ne : Keys) : LTerm → LTerm
  | .seq _ a => (a.core ne)
  | .lit v => .lit v
  | .var x => .var x
  | .err => .err
  | .env k => .env k
  | .binop op p a b => .binop op p (a.core ne) (b.core ne)
  | .unop op p a => .unop op p (a.core ne)
  | .ite c a b => .ite (c.core ne) (a.core ne) (b.core ne)
  | .zero a => .zero (a.core ne)
  | .find s q => .findP (s.core ne) (q.core ne)
  | .findP s q => .findP (s.core ne) (q.core ne)
  | .has s q => .has (s.core ne) (q.core ne)
  | .kmap sh s q => .kmap sh (s.core ne) (q.core ne)
  | .len s q => .len (s.core ne) (q.core ne)
  | .sok s => .sok (s.core ne)
  | .pok q => .pok (q.core ne)
  | .orElse a b => .orElse a (b.core ne)
  | .kite a b t e =>
    if (true, a, b) ∈ ne ∨ (true, b, a) ∈ ne then t.core ne
    else if (false, a, b) ∈ ne ∨ (false, b, a) ∈ ne then e.core ne
    else .kite (a.core ne) (b.core ne) (t.core ne) (e.core ne)

/-- The path with the guards of its keys dropped. -/
def LPath.core (ne : Keys) : LPath → LPath
  | .root r => .root r
  | .field q f => .field (q.core ne) f
  | .at q k => .at (q.core ne) (k.core ne)

/-- The storage with the guards of its terms dropped. -/
def LStor.core (ne : Keys) : LStor → LStor
  | .init => .init
  | .save s q w => .save (s.core ne) (q.core ne) (w.core ne)
  | .del s q => .del (s.core ne) (q.core ne)
  | .arr op s q w => .arr op (s.core ne) (q.core ne) (w.core ne)
  | .copy s q src sq => .copy (s.core ne) (q.core ne) (src.core ne) (sq.core ne)

end

/-- `evalBinop` with a right operand that returns what the old one did, where
the old one returned. -/
theorem evalBinop_congr {op : BinOp} {p : PrimTy} {x : Value} {rb rb' : Res Value}
    {v : Value} (h : evalBinop op p x rb = .ok v) (hb : ∀ w, rb = .ok w → rb' = .ok w) :
    evalBinop op p x rb' = .ok v := by
  cases rb with
  | ok w => rw [hb w rfl]; exact h
  | error e =>
    revert h
    unfold evalBinop
    split
    · exact id
    · exact id
    · simp [bind, Except.bind]

mutual

/-- **Dropping the guards keeps what a term returns.** -/
theorem LTerm.core_eval {σ : State} {ne : Keys} (hne : Apart σ ne) :
    (t : LTerm) → ∀ {v : Value}, t.eval σ = .ok v →
    (t.core ne).eval σ = .ok v
  | .lit _, _, h | .var _, _, h | .err, _, h | .env _, _, h => h
  | .seq d a, v, h => by
    simp only [LTerm.eval] at h
    obtain ⟨_, -, ha⟩ := Res.bind_eq_ok.1 h
    simp only [LTerm.core]
    exact LTerm.core_eval hne a ha
  | .binop op p a b, v, h => by
    simp only [LTerm.eval] at h
    obtain ⟨x, ha, hb⟩ := Res.bind_eq_ok.1 h
    simp only [LTerm.core, LTerm.eval, LTerm.core_eval hne a ha, Res.ok_bind]
    exact evalBinop_congr hb (fun w hw => LTerm.core_eval hne b hw)
  | .unop op p a, v, h => by
    simp only [LTerm.eval] at h
    obtain ⟨x, ha, h⟩ := Res.bind_eq_ok.1 h
    simp only [LTerm.core, LTerm.eval, LTerm.core_eval hne a ha, Res.ok_bind]
    exact h
  | .ite c a b, v, h => by
    simp only [LTerm.eval] at h
    obtain ⟨x, hc, h⟩ := Res.bind_eq_ok.1 h
    simp only [LTerm.core, LTerm.eval, LTerm.core_eval hne c hc, Res.ok_bind]
    unfold pickBranch at h ⊢
    split at h
    · exact LTerm.core_eval hne a h
    · exact LTerm.core_eval hne b h
    · exact h
  | .zero a, v, h => by
    simp only [LTerm.eval] at h
    obtain ⟨x, ha, h⟩ := Res.bind_eq_ok.1 h
    simp only [LTerm.core, LTerm.eval, LTerm.core_eval hne a ha, Res.ok_bind]
    exact h
  | .find s q, v, h => by
    simp only [LTerm.eval] at h
    obtain ⟨x, hs, h⟩ := Res.bind_eq_ok.1 h
    obtain ⟨y, hq, h⟩ := Res.bind_eq_ok.1 h
    obtain ⟨w, hw, h⟩ := Res.bind_eq_ok.1 h
    simp only [LTerm.core, LTerm.eval, LStor.core_eval hne s hs, LPath.core_eval hne q hq,
      Res.ok_bind, SVal.find_of_findLive hw]
    exact h
  | .has s q, v, h | .kmap _ s q, v, h | .len s q, v, h | .findP s q, v, h => by
    simp only [LTerm.eval] at h
    obtain ⟨x, hs, h⟩ := Res.bind_eq_ok.1 h
    obtain ⟨y, hq, h⟩ := Res.bind_eq_ok.1 h
    simp only [LTerm.core, LTerm.eval, LStor.core_eval hne s hs, LPath.core_eval hne q hq, Res.ok_bind]
    exact h
  | .sok s, v, h => by
    simp only [LTerm.eval] at h
    obtain ⟨x, hs, h⟩ := Res.bind_eq_ok.1 h
    simp only [LTerm.core, LTerm.eval, LStor.core_eval hne s hs, Res.ok_bind]
    exact h
  | .pok q, v, h => by
    simp only [LTerm.eval] at h
    obtain ⟨x, hq, h⟩ := Res.bind_eq_ok.1 h
    simp only [LTerm.core, LTerm.eval, LPath.core_eval hne q hq, Res.ok_bind]
    exact h
  | .orElse a b, v, h => by
    simp only [LTerm.eval] at h
    simp only [LTerm.core, LTerm.eval]
    unfold orElseR at h ⊢
    split at h
    · exact h
    · exact LTerm.core_eval hne b h
  | .kite a b t e, v, h => by
    simp only [LTerm.eval] at h
    obtain ⟨i, hi, h⟩ := Res.bind_eq_ok.1 h
    obtain ⟨x, ha, hi⟩ := Res.bind_eq_ok.1 hi
    obtain ⟨j, hj, h⟩ := Res.bind_eq_ok.1 h
    obtain ⟨y, hb, hj⟩ := Res.bind_eq_ok.1 hj
    have hkey : ∀ c, ((c, a, b) ∈ ne ∨ (c, b, a) ∈ ne) → (i = j ↔ c = true) := by
      intro c hc
      have hxy : x = y ↔ c = true := by
        rcases hc with hc | hc
        · exact hne _ hc x y ha hb
        · exact eq_comm.trans (hne _ hc y x hb ha)
      rw [← hxy]
      cases x <;> cases y <;> simp only [Value.asInt, reduceCtorEq] at hi hj
      cases hi; cases hj
      exact ⟨fun h => h ▸ rfl, fun h => by cases h; rfl⟩
    simp only [LTerm.core]
    split
    · rename_i hc
      rw [if_pos ((hkey true hc).2 rfl)] at h
      exact LTerm.core_eval hne t h
    · split
      · rename_i hc
        have hij : i ≠ j := fun he => by simpa using (hkey false hc).1 he
        rw [if_neg hij] at h
        exact LTerm.core_eval hne e h
      · simp only [LTerm.eval, LTerm.core_eval hne a ha, LTerm.core_eval hne b hb, Res.ok_bind, hi,
          hj]
        by_cases hij : i = j
        · rw [if_pos hij] at h ⊢; exact LTerm.core_eval hne t h
        · rw [if_neg hij] at h ⊢; exact LTerm.core_eval hne e h

/-- Dropping the guards keeps the path a path evaluates to. -/
theorem LPath.core_eval {σ : State} {ne : Keys} (hne : Apart σ ne) :
    (q : LPath) → ∀ {ps : List Seg}, q.eval σ = .ok ps →
    (q.core ne).eval σ = .ok ps
  | .root _, _, h => h
  | .field q f, ps, h => by
    simp only [LPath.eval] at h
    obtain ⟨x, hq, h⟩ := Res.bind_eq_ok.1 h
    simp only [LPath.core, LPath.eval, LPath.core_eval hne q hq, Res.ok_bind]
    exact h
  | .at q k, ps, h => by
    simp only [LPath.eval] at h
    obtain ⟨x, hq, h⟩ := Res.bind_eq_ok.1 h
    obtain ⟨i, hk, h⟩ := Res.bind_eq_ok.1 h
    obtain ⟨y, hk, hi⟩ := Res.bind_eq_ok.1 hk
    simp only [LPath.core, LPath.eval, LPath.core_eval hne q hq, LTerm.core_eval hne k hk, Res.ok_bind,
      hi]
    exact h

/-- Dropping the guards keeps the storage a storage evaluates to. -/
theorem LStor.core_eval {σ : State} {ne : Keys} (hne : Apart σ ne) :
    (s : LStor) → ∀ {sv : SVal}, s.eval σ = .ok sv →
    (s.core ne).eval σ = .ok sv
  | .init, _, h => h
  | .save s q w, sv, h => by
    simp only [LStor.eval] at h
    obtain ⟨x, hw, h⟩ := Res.bind_eq_ok.1 h
    obtain ⟨y, hs, h⟩ := Res.bind_eq_ok.1 h
    obtain ⟨z, hq, h⟩ := Res.bind_eq_ok.1 h
    simp only [LStor.core, LStor.eval, LTerm.core_eval hne w hw, LStor.core_eval hne s hs,
      LPath.core_eval hne q hq, Res.ok_bind]
    exact h
  | .del s q, sv, h => by
    simp only [LStor.eval] at h
    obtain ⟨y, hs, h⟩ := Res.bind_eq_ok.1 h
    obtain ⟨z, hq, h⟩ := Res.bind_eq_ok.1 h
    simp only [LStor.core, LStor.eval, LStor.core_eval hne s hs, LPath.core_eval hne q hq, Res.ok_bind]
    exact h
  | .arr _ s q w, sv, h => by
    simp only [LStor.eval] at h
    obtain ⟨x, hw, h⟩ := Res.bind_eq_ok.1 h
    obtain ⟨y, hs, h⟩ := Res.bind_eq_ok.1 h
    obtain ⟨z, hq, h⟩ := Res.bind_eq_ok.1 h
    simp only [LStor.core, LStor.eval, LTerm.core_eval hne w hw, LStor.core_eval hne s hs,
      LPath.core_eval hne q hq, Res.ok_bind]
    exact h
  | .copy s q src sq, sv, h => by
    simp only [LStor.eval] at h
    obtain ⟨a, ha, h⟩ := Res.bind_eq_ok.1 h
    obtain ⟨b, hb, h⟩ := Res.bind_eq_ok.1 h
    obtain ⟨n, hn, h⟩ := Res.bind_eq_ok.1 h
    obtain ⟨y, hs, h⟩ := Res.bind_eq_ok.1 h
    obtain ⟨z, hq, h⟩ := Res.bind_eq_ok.1 h
    simp only [LStor.core, LStor.eval, LStor.core_eval hne src ha, LPath.core_eval hne sq hb,
      LStor.core_eval hne s hs, LPath.core_eval hne q hq, Res.ok_bind, hn]
    exact h

end

/-! ## Arithmetic

KeY's arithmetic rules, the two this needs: `(x - a) + a` and `(x + a) - a`
are `x` wherever they return, since checked arithmetic computes on the
integers and only refuses a result out of range. -/

/-- `evalBinop` of `+` or `-` that returns: integers in, their sum or
difference out. -/
theorem evalBinop_addsub {op : BinOp} {p : PrimTy} {x y v : Value}
    (hop : op = .add ∨ op = .sub) (h : evalBinop op p x (.ok y) = .ok v) :
    ∃ i j, x = .int i ∧ y = .int j ∧
      v = .int (if op = .add then i + j else i - j) := by
  rcases hop with rfl | rfl
  all_goals
    cases x with
    | bool b => simp [evalBinop, applyBinOp, Value.asInt, bind, Except.bind] at h
    | int i =>
      cases y with
      | bool b => simp [evalBinop, applyBinOp, Value.asInt, bind, Except.bind] at h
      | int j =>
        simp only [evalBinop, applyBinOp, Value.asInt, bind, Except.bind] at h
        exact ⟨i, j, rfl, rfl, by simpa using checkArith_ok_eq h⟩

/-- `a' + b'`, as `x` where `a'` is `x - b'`. -/
def arithAdd (p : PrimTy) (a b : LTerm) : LTerm :=
  match a with
  | .binop .sub _ x c => if c = b then x else .binop .add p a b
  | _ => .binop .add p a b

/-- `a' - b'`, as `x` where `a'` is `x + b'`. -/
def arithSub (p : PrimTy) (a b : LTerm) : LTerm :=
  match a with
  | .binop .add _ x c => if c = b then x else .binop .sub p a b
  | _ => .binop .sub p a b

/-- `(x - a) + a` and `(x + a) - a` as `x`, below every operator. -/
def LTerm.arith : LTerm → LTerm
  | .binop .add p a b => arithAdd p a.arith b.arith
  | .binop .sub p a b => arithSub p a.arith b.arith
  | .binop op p a b => .binop op p a.arith b.arith
  | t => t

/-- The cancellation at one operator: where `a` returns what `a'` does and
`b` what `b'` does, `a' ⊕ b'` cancelled returns what `a ⊕ b` does. -/
theorem arith_step {σ : State} {op : BinOp} (hop : op = .add ∨ op = .sub) {p : PrimTy}
    {a b a' b' : LTerm} {v : Value} (h : (LTerm.binop op p a b).eval σ = .ok v)
    (ha : ∀ w, a.eval σ = .ok w → a'.eval σ = .ok w)
    (hb : ∀ w, b.eval σ = .ok w → b'.eval σ = .ok w) :
    (if op = .add then arithAdd p a' b' else arithSub p a' b').eval σ = .ok v := by
  simp only [LTerm.eval] at h
  obtain ⟨u, hu, hv⟩ := Res.bind_eq_ok.1 h
  have hgen : (LTerm.binop op p a' b').eval σ = .ok v := by
    simp only [LTerm.eval, ha u hu, Res.ok_bind]
    exact evalBinop_congr hv hb
  obtain ⟨w, hw⟩ : ∃ w, b.eval σ = .ok w := by
    cases hbe : b.eval σ with
    | ok w => exact ⟨w, rfl⟩
    | error e =>
      rw [hbe] at hv
      rcases hop with rfl | rfl <;> simp [evalBinop, bind, Except.bind] at hv
  rw [hw] at hv
  obtain ⟨i, j, rfl, rfl, rfl⟩ := evalBinop_addsub hop hv
  have hu' := ha _ hu
  rcases hop with rfl | rfl
  · simp only [if_true]
    unfold arithAdd
    split
    · rename_i q x c
      split
      · rename_i hc
        subst hc
        simp only [LTerm.eval] at hu'
        obtain ⟨X, hX, hsub⟩ := Res.bind_eq_ok.1 hu'
        rw [hb _ hw] at hsub
        obtain ⟨k, l, rfl, hl, hk⟩ := evalBinop_addsub (.inr rfl) hsub
        cases hl
        simp only [reduceCtorEq, if_false, PrimVal.int.injEq] at hk
        rw [hX, hk, Int.sub_add_cancel]
      · exact hgen
    · exact hgen
  · simp only [reduceCtorEq, if_false]
    unfold arithSub
    split
    · rename_i q x c
      split
      · rename_i hc
        subst hc
        simp only [LTerm.eval] at hu'
        obtain ⟨X, hX, hadd⟩ := Res.bind_eq_ok.1 hu'
        rw [hb _ hw] at hadd
        obtain ⟨k, l, rfl, hl, hk⟩ := evalBinop_addsub (.inl rfl) hadd
        cases hl
        simp only [if_true, PrimVal.int.injEq] at hk
        rw [hX, hk, Int.add_sub_cancel]
      · exact hgen
    · exact hgen

/-- Below any operator but `+` and `-`, the cancellation only goes down. -/
theorem LTerm.arith_binop {op : BinOp} {p : PrimTy} {a b : LTerm} (h₁ : op ≠ .add)
    (h₂ : op ≠ .sub) : (LTerm.binop op p a b).arith = .binop op p a.arith b.arith := by
  cases op <;> simp_all [LTerm.arith]

/-- **The cancellation keeps what a term returns.** -/
theorem LTerm.arith_eval {σ : State} : (t : LTerm) → ∀ {v : Value}, t.eval σ = .ok v →
    t.arith.eval σ = .ok v
  | .binop op p a b, v, h => by
    by_cases h₁ : op = .add
    · subst h₁
      have := arith_step (.inl rfl) h (fun _ hw => LTerm.arith_eval a hw)
        (fun _ hw => LTerm.arith_eval b hw)
      simpa only [LTerm.arith, if_true] using this
    by_cases h₂ : op = .sub
    · subst h₂
      have := arith_step (.inr rfl) h (fun _ hw => LTerm.arith_eval a hw)
        (fun _ hw => LTerm.arith_eval b hw)
      simpa only [LTerm.arith, reduceCtorEq, if_false] using this
    simp only [LTerm.eval] at h
    obtain ⟨u, hu, hv⟩ := Res.bind_eq_ok.1 h
    rw [LTerm.arith_binop h₁ h₂]
    simp only [LTerm.eval, LTerm.arith_eval a hu, Res.ok_bind]
    exact evalBinop_congr hv (fun _ hw => LTerm.arith_eval b hw)
  | .lit _, _, h | .var _, _, h | .err, _, h | .env _, _, h | .unop .., _, h | .ite .., _, h
  | .zero _, _, h | .find .., _, h | .has .., _, h | .kmap .., _, h | .len .., _, h | .sok _, _, h | .pok _, _, h
  | .seq .., _, h | .orElse .., _, h | .kite .., _, h | .findP .., _, h => h

/-- Two terms that return, with one value: equal once their guards are
dropped and their arithmetic cancelled. -/
def LTerm.same (ne : Keys) (a b : LTerm) : Bool :=
  (a.core ne).arith == (b.core ne).arith

theorem LTerm.same_eval {σ : State} {ne : Keys} (hne : Apart σ ne)
    {a b : LTerm} {x y : Value} (h : a.same ne b = true) (ha : a.eval σ = .ok x)
    (hb : b.eval σ = .ok y) : x = y := by
  simp only [LTerm.same, beq_iff_eq] at h
  have ha' := LTerm.arith_eval _ (LTerm.core_eval hne a ha)
  have hb' := LTerm.arith_eval _ (LTerm.core_eval hne b hb)
  rw [h, hb'] at ha'
  cases ha'
  rfl

/-! ## The check -/

/-- A term `known` says returns: a literal, one of them, or an operation
on operands that return what the operands of one of them do. -/
def LTerm.known (known : List LTerm) (ne : Keys) (t : LTerm) : Bool :=
  match t with
  | .lit _ => true
  | .binop op p a b => known.contains t || known.any fun
      | .binop op' p' a' b' => op' == op && p' == p && known.contains a && known.contains b &&
          a'.same ne a && b'.same ne b
      | _ => false
  | t => known.contains t

theorem LTerm.known_returns {σ : State} {known : List LTerm} {ne : Keys}
    (hk : ∀ u ∈ known, Returns σ u) (hne : Apart σ ne) (t : LTerm)
    (h : t.known known ne = true) : Returns σ t := by
  have mem : ∀ u, known.contains u = true → Returns σ u :=
    fun u hu => hk u (List.contains_iff_mem.1 hu)
  unfold LTerm.known at h
  split at h
  · exact ⟨_, rfl⟩
  · rename_i op p a b
    simp only [Bool.or_eq_true, List.any_eq_true] at h
    rcases h with h | ⟨K, hK, hc⟩
    · exact mem _ h
    · split at hc
      · rename_i op' p' a' b'
        simp only [Bool.and_eq_true, beq_iff_eq] at hc
        obtain ⟨⟨⟨⟨⟨rfl, rfl⟩, hka⟩, hkb⟩, hsa⟩, hsb⟩ := hc
        obtain ⟨v, hv⟩ := hk _ hK
        simp only [LTerm.eval] at hv
        obtain ⟨u, hu, hv⟩ := Res.bind_eq_ok.1 hv
        obtain ⟨x, hx⟩ := mem a hka
        obtain ⟨y, hy⟩ := mem b hkb
        cases LTerm.same_eval hne hsa hu hx
        refine ⟨v, ?_⟩
        simp only [LTerm.eval, hx, Res.ok_bind]
        exact evalBinop_congr hv (fun w hw => by rw [LTerm.same_eval hne hsb hw hy]; exact hy)
      · simp at hc
  · exact mem _ h

/-- The keys of a path, the last first: `[k, i]` of `people[i].friends[k]`. -/
def LPath.keys : LPath → List LTerm
  | .root _ => []
  | .field q _ => q.keys
  | .at q k => k :: q.keys

/-- A path that evaluates has integer keys. -/
theorem LPath.keys_int {σ : State} : (q : LPath) → (∃ ps, q.eval σ = .ok ps) →
    ∀ k ∈ q.keys, ∃ i, (k.eval σ >>= Value.asInt) = .ok i
  | .root _, _, k, hk => by simp [LPath.keys] at hk
  | .field q _, ⟨ps, h⟩, k, hk => by
    simp only [LPath.eval] at h
    obtain ⟨x, hq, -⟩ := Res.bind_eq_ok.1 h
    exact LPath.keys_int q ⟨x, hq⟩ k hk
  | .at q k', ⟨ps, h⟩, k, hk => by
    simp only [LPath.eval] at h
    obtain ⟨x, hq, h⟩ := Res.bind_eq_ok.1 h
    obtain ⟨i, hi, -⟩ := Res.bind_eq_ok.1 h
    simp only [LPath.keys, List.mem_cons] at hk
    rcases hk with rfl | hk
    · exact ⟨i, hi⟩
    · exact LPath.keys_int q ⟨x, hq⟩ k hk

/-- An integer whatever the state: an integer literal, a value of the
transaction. -/
def LTerm.isIntLit : LTerm → Bool
  | .lit (.int _) | .env _ => true
  | _ => false

theorem LTerm.isIntLit_int {σ : State} : (t : LTerm) → t.isIntLit = true →
    ∃ i, (t.eval σ >>= Value.asInt) = .ok i
  | .lit (.int n), _ => ⟨n, rfl⟩
  | .env _, _ => ⟨_, rfl⟩
  | .lit (.bool _), h | .var _, h | .binop .., h | .unop .., h | .ite .., h | .find .., h
  | .has .., h | .kmap .., h | .len .., h | .sok _, h | .pok _, h | .seq .., h | .orElse .., h
  | .kite .., h | .zero _, h | .err, h | .findP .., h => by simp [LTerm.isIntLit] at h

/-- A term `known` shows is an integer: one whatever the state, or a key of a
path whose `ok(q)` is known to return. -/
def LTerm.isInt (known : List LTerm) (t : LTerm) : Bool :=
  t.isIntLit || known.any fun
    | .pok q => q.keys.contains t
    | _ => false

theorem LTerm.isInt_int {σ : State} {known : List LTerm} (hk : ∀ u ∈ known, Returns σ u)
    {t : LTerm} (h : t.isInt known = true) : ∃ i, (t.eval σ >>= Value.asInt) = .ok i := by
  simp only [LTerm.isInt, Bool.or_eq_true, List.any_eq_true] at h
  rcases h with h | ⟨K, hK, hc⟩
  · exact LTerm.isIntLit_int t h
  · split at hc
    · rename_i q
      obtain ⟨v, hv⟩ := hk _ hK
      simp only [LTerm.eval] at hv
      obtain ⟨ps, hq, -⟩ := Res.bind_eq_ok.1 hv
      exact LPath.keys_int q ⟨ps, hq⟩ t (List.contains_iff_mem.1 hc)
    · cases hc

/-- A term the premises show returns: a known one (`LTerm.known`), a guarded
term whose guard and value do, an operation on operands that return what a
known one's do, a snapshot read where the live read returns, or a `kite` on
integer keys whose branch does — the one the premises pick, or else both. -/
def LTerm.rets (known : List LTerm) (ne : Keys) : LTerm → Bool
  | .seq d a => (LTerm.seq d a).known known ne || (d.rets known ne && a.rets known ne)
  | .kite a b x y => (LTerm.kite a b x y).known known ne ||
      (a.isInt known && b.isInt known &&
        (if (true, a, b) ∈ ne ∨ (true, b, a) ∈ ne then x.rets known ne
         else if (false, a, b) ∈ ne ∨ (false, b, a) ∈ ne then y.rets known ne
         else x.rets known ne && y.rets known ne))
  | .binop op p a b =>
    let ra := a.rets known ne
    let rb := b.rets known ne
    (LTerm.binop op p a b).known known ne || known.any fun
      | .binop op' p' a' b' => op' == op && p' == p && ra && rb && a'.same ne a && b'.same ne b
      | _ => false
  | .findP s q => (LTerm.findP s q).known known ne || (LTerm.find s q).known known ne
  | t@(.lit _) | t@(.var _) | t@(.unop ..) | t@(.ite ..) | t@(.find ..)
  | t@(.has ..) | t@(.kmap ..) | t@(.len ..) | t@(.sok _) | t@(.pok _) | t@(.orElse ..)
  | t@(.zero _) | t@.err | t@(.env _) => t.known known ne

theorem LTerm.rets_returns {σ : State} {known : List LTerm} {ne : Keys}
    (hk : ∀ u ∈ known, Returns σ u) (hne : Apart σ ne) :
    (t : LTerm) → t.rets known ne = true → Returns σ t
  | .seq d a, h => by
    simp only [LTerm.rets, Bool.or_eq_true, Bool.and_eq_true] at h
    rcases h with h | ⟨hd, ha⟩
    · exact LTerm.known_returns hk hne _ h
    · obtain ⟨_, hd⟩ := LTerm.rets_returns hk hne d hd
      obtain ⟨v, ha⟩ := LTerm.rets_returns hk hne a ha
      exact ⟨v, by simp only [LTerm.eval, hd, Res.ok_bind, ha]⟩
  | .kite a b x y, h => by
    simp only [LTerm.rets, Bool.or_eq_true, Bool.and_eq_true] at h
    rcases h with h | ⟨⟨ha, hb⟩, hc⟩
    · exact LTerm.known_returns hk hne _ h
    · obtain ⟨i, hi⟩ := LTerm.isInt_int hk ha
      obtain ⟨j, hj⟩ := LTerm.isInt_int hk hb
      obtain ⟨xa, hxa, hai⟩ := Res.bind_eq_ok.1 hi
      obtain ⟨xb, hxb, hbj⟩ := Res.bind_eq_ok.1 hj
      have hkey : ∀ c, ((c, a, b) ∈ ne ∨ (c, b, a) ∈ ne) → (i = j ↔ c = true) := by
        intro c hc
        have hxy : xa = xb ↔ c = true := by
          rcases hc with hc | hc
          · exact hne _ hc xa xb hxa hxb
          · exact eq_comm.trans (hne _ hc xb xa hxb hxa)
        rw [← hxy]
        cases xa <;> cases xb <;> simp only [Value.asInt, reduceCtorEq] at hai hbj
        cases hai; cases hbj
        exact ⟨fun h => h ▸ rfl, fun h => by cases h; rfl⟩
      have heval : (LTerm.kite a b x y).eval σ = if i = j then x.eval σ else y.eval σ := by
        simp only [LTerm.eval, hi, hj, Res.ok_bind]
      split at hc
      · rename_i hp
        obtain ⟨v, hv⟩ := LTerm.rets_returns hk hne x hc
        exact ⟨v, by rw [heval, if_pos ((hkey true hp).2 rfl), hv]⟩
      · split at hc
        · rename_i _ hp
          have hij : i ≠ j := fun he => by simpa using (hkey false hp).1 he
          obtain ⟨v, hv⟩ := LTerm.rets_returns hk hne y hc
          exact ⟨v, by rw [heval, if_neg hij, hv]⟩
        · simp only [Bool.and_eq_true] at hc
          obtain ⟨v, hv⟩ := LTerm.rets_returns hk hne x hc.1
          obtain ⟨w, hw⟩ := LTerm.rets_returns hk hne y hc.2
          by_cases hij : i = j
          · exact ⟨v, by rw [heval, if_pos hij, hv]⟩
          · exact ⟨w, by rw [heval, if_neg hij, hw]⟩
  | .binop op p a b, h => by
    simp only [LTerm.rets, Bool.or_eq_true, List.any_eq_true] at h
    rcases h with h | ⟨K, hK, hc⟩
    · exact LTerm.known_returns hk hne _ h
    · split at hc
      · rename_i op' p' a' b'
        simp only [Bool.and_eq_true, beq_iff_eq] at hc
        obtain ⟨⟨⟨⟨⟨rfl, rfl⟩, hra⟩, hrb⟩, hsa⟩, hsb⟩ := hc
        obtain ⟨v, hv⟩ := hk _ hK
        simp only [LTerm.eval] at hv
        obtain ⟨u, hu, hv⟩ := Res.bind_eq_ok.1 hv
        obtain ⟨x, hx⟩ := LTerm.rets_returns hk hne a hra
        obtain ⟨y, hy⟩ := LTerm.rets_returns hk hne b hrb
        cases LTerm.same_eval hne hsa hu hx
        refine ⟨v, ?_⟩
        simp only [LTerm.eval, hx, Res.ok_bind]
        exact evalBinop_congr hv (fun w hw => by rw [LTerm.same_eval hne hsb hw hy]; exact hy)
      · simp at hc
  | .findP s q, h => by
    simp only [LTerm.rets, Bool.or_eq_true] at h
    rcases h with h | h
    · exact LTerm.known_returns hk hne _ h
    · obtain ⟨v, hv⟩ := LTerm.known_returns hk hne _ h
      simp only [LTerm.eval] at hv
      obtain ⟨x, hs, hv⟩ := Res.bind_eq_ok.1 hv
      obtain ⟨y, hq, hv⟩ := Res.bind_eq_ok.1 hv
      obtain ⟨w, hw, hv⟩ := Res.bind_eq_ok.1 hv
      exact ⟨v, by simp only [LTerm.eval, hs, hq, Res.ok_bind, SVal.find_of_findLive hw, hv]⟩
  | .lit _, h | .var _, h | .unop .., h | .ite .., h | .find .., h | .has .., h
  | .kmap .., h | .len .., h | .sok _, h | .pok _, h | .orElse .., h | .zero _, h | .err, h
  | .env _, h => LTerm.known_returns hk hne _ h

/-- What a premise tells: the terms it shows return, the pairs it keeps
apart.  A conjunction tells what both conjuncts do. -/
def LFml.prem : LFml → List LTerm × Keys → List LTerm × Keys
  | .eq a b, (k, n) => (a.strict ++ b.strict ++ k, (true, a, b) :: n)
  | .not (.eq a b), (k, n) => (k, (false, a, b) :: n)
  | .not (.and (.eq a a') (.and (.eq b b') (.eq c d))), (k, n) =>
    -- `¬(c = d)` of a program comparison: `¬(defined c ∧ defined d ∧ c ≐ d)`
    if a = c ∧ a' = c ∧ b = d ∧ b' = d then (k, (false, c, d) :: n) else (k, n)
  | .and φ ψ, kn => ψ.prem (φ.prem kn)
  | _, kn => kn

/-- `syn known ne φ`: `φ` holds wherever the terms of `known` return and the
facts of `ne` hold.  A premise adds what it tells (`LFml.prem`); a conclusion
`a ≐ b` needs both sides to return (`LTerm.rets`) and to be the same
(`LTerm.same`), or the same as the sides of a premise `p ≐ q`. -/
def LFml.syn (known : List LTerm) (ne : Keys) : LFml → Bool
  | .tt => true
  | .imp φ ψ => LFml.syn (φ.prem (known, ne)).1 (φ.prem (known, ne)).2 ψ
  | .and φ ψ => LFml.syn known ne φ && LFml.syn known ne ψ
  | .eq a b => a.rets known ne && b.rets known ne &&
      (a.same ne b || ne.any fun (c, p, q) => c && p.rets known ne && q.rets known ne &&
        ((a.same ne p && b.same ne q) || (a.same ne q && b.same ne p)))
  | .not _ => false
  | .all x _ φ => known.all (fun t => !t.vars.contains x) &&
      ne.all (fun q => !q.2.1.vars.contains x && !q.2.2.vars.contains x) && LFml.syn known ne φ

/-- What a premise that holds tells is so. -/
theorem LFml.prem_ok {σ : State} : (φ : LFml) → φ.holds σ →
    ∀ (kn : List LTerm × Keys), (∀ u ∈ kn.1, Returns σ u) → Apart σ kn.2 →
    (∀ u ∈ (φ.prem kn).1, Returns σ u) ∧ Apart σ (φ.prem kn).2
  | .eq a b, h, (k, n), hk, hn => by
    simp only [LFml.holds] at h
    split at h
    · rename_i x y ha hb
      refine ⟨fun u hu => ?_, ?_⟩
      · simp only [LFml.prem, List.mem_append] at hu
        rcases hu with (hu | hu) | hu
        · exact LTerm.strict_returns a ⟨x, ha⟩ u hu
        · exact LTerm.strict_returns b ⟨y, hb⟩ u hu
        · exact hk u hu
      · intro q hq x' y' hx' hy'
        simp only [LFml.prem, List.mem_cons] at hq
        rcases hq with rfl | hq
        · rw [ha] at hx'; rw [hb] at hy'
          cases hx'; cases hy'
          simp only [iff_true]; exact h
        · exact hn q hq x' y' hx' hy'
    · exact h.elim
  | .not (.eq a b), h, (k, n), hk, hn => by
    refine ⟨hk, ?_⟩
    intro q hq x y hx hy
    simp only [LFml.prem, List.mem_cons] at hq
    rcases hq with rfl | hq
    · simp only [Bool.false_eq_true, iff_false]
      intro hxy
      subst hxy
      apply h
      simp only [LFml.holds, hx, hy]
    · exact hn q hq x y hx hy
  | .and φ ψ, h, kn, hk, hn => by
    obtain ⟨hk', hn'⟩ := LFml.prem_ok φ h.1 kn hk hn
    exact LFml.prem_ok ψ h.2 _ hk' hn'
  | .not (.and (.eq a a') (.and (.eq b b') (.eq c d))), h, (k, n), hk, hn => by
    simp only [LFml.prem]
    split
    · rename_i he
      obtain ⟨rfl, rfl, rfl, rfl⟩ := he
      refine ⟨hk, ?_⟩
      intro q hq x y hx hy
      simp only [List.mem_cons] at hq
      rcases hq with rfl | hq
      · simp only [Bool.false_eq_true, iff_false]
        intro hxy
        subst hxy
        apply h
        simp only [LFml.holds, hx, hy, and_self]
      · exact hn q hq x y hx hy
    · exact ⟨hk, hn⟩
  | .tt, _, _, hk, hn | .not .tt, _, _, hk, hn | .not (.not _), _, _, hk, hn
  | .not (.imp _ _), _, _, hk, hn | .imp _ _, _, _, hk, hn => ⟨hk, hn⟩
  | .not (.and .tt _), _, _, hk, hn | .not (.and (.not _) _), _, _, hk, hn
  | .not (.and (.and _ _) _), _, _, hk, hn | .not (.and (.imp _ _) _), _, _, hk, hn
  | .not (.and (.eq _ _) .tt), _, _, hk, hn | .not (.and (.eq _ _) (.not _)), _, _, hk, hn
  | .not (.and (.eq _ _) (.eq _ _)), _, _, hk, hn | .not (.and (.eq _ _) (.imp _ _)), _, _, hk, hn
  | .not (.and (.eq _ _) (.and .tt _)), _, _, hk, hn
  | .not (.and (.eq _ _) (.and (.not _) _)), _, _, hk, hn
  | .not (.and (.eq _ _) (.and (.and _ _) _)), _, _, hk, hn
  | .not (.and (.eq _ _) (.and (.imp _ _) _)), _, _, hk, hn
  | .not (.and (.eq _ _) (.and (.eq _ _) .tt)), _, _, hk, hn
  | .not (.and (.eq _ _) (.and (.eq _ _) (.not _))), _, _, hk, hn
  | .not (.and (.eq _ _) (.and (.eq _ _) (.and _ _))), _, _, hk, hn
  | .not (.and (.eq _ _) (.and (.eq _ _) (.imp _ _))), _, _, hk, hn => ⟨hk, hn⟩
  | .all .., _, _, hk, hn | .not (.all ..), _, _, hk, hn
  | .not (.and (.all ..) _), _, _, hk, hn | .not (.and (.eq _ _) (.all ..)), _, _, hk, hn
  | .not (.and (.eq _ _) (.and (.all ..) _)), _, _, hk, hn
  | .not (.and (.eq _ _) (.and (.eq _ _) (.all ..))), _, _, hk, hn => ⟨hk, hn⟩

theorem LFml.syn_holds : (φ : LFml) → ∀ (σ : State) (known : List LTerm)
    (ne : Keys), (∀ u ∈ known, Returns σ u) → Apart σ ne →
    φ.syn known ne = true → φ.holds σ
  | .tt, _, _, _, _, _, _ => trivial
  | .imp φ ψ, σ, known, ne, hk, hne, h => fun hφ => by
    obtain ⟨hk', hn'⟩ := LFml.prem_ok φ hφ (known, ne) hk hne
    exact LFml.syn_holds ψ σ _ _ hk' hn' h
  | .and φ ψ, σ, known, ne, hk, hne, h => by
    simp only [LFml.syn, Bool.and_eq_true] at h
    exact ⟨LFml.syn_holds φ σ known ne hk hne h.1, LFml.syn_holds ψ σ known ne hk hne h.2⟩
  | .eq a b, σ, known, ne, hk, hne, h => by
    simp only [LFml.syn, Bool.and_eq_true, Bool.or_eq_true, List.any_eq_true] at h
    obtain ⟨⟨ha, hb⟩, hc⟩ := h
    obtain ⟨x, hx⟩ := LTerm.rets_returns hk hne a ha
    obtain ⟨y, hy⟩ := LTerm.rets_returns hk hne b hb
    suffices hxy : x = y by subst hxy; simp only [LFml.holds, hx, hy]
    rcases hc with hc | ⟨⟨c, p, q⟩, hm, hc⟩
    · exact LTerm.same_eval hne hc hx hy
    · obtain ⟨⟨⟨rfl, hp⟩, hq⟩, hs⟩ := hc
      obtain ⟨xp, hxp⟩ := LTerm.rets_returns hk hne p hp
      obtain ⟨yq, hyq⟩ := LTerm.rets_returns hk hne q hq
      have hpq : xp = yq := (hne _ hm xp yq hxp hyq).2 rfl
      rcases hs with ⟨h₁, h₂⟩ | ⟨h₁, h₂⟩
      · rw [LTerm.same_eval hne h₁ hx hxp, LTerm.same_eval hne h₂ hy hyq, hpq]
      · rw [LTerm.same_eval hne h₁ hx hyq, LTerm.same_eval hne h₂ hy hxp, hpq]
  | .not _, _, _, _, _, _, h => by simp [LFml.syn] at h
  | .all x p φ, σ, known, ne, hk, hne, h => by
    simp only [LFml.syn, Bool.and_eq_true, List.all_eq_true] at h
    obtain ⟨⟨hkx, hnx⟩, h⟩ := h
    intro v _
    refine LFml.syn_holds φ _ known ne ?_ ?_ h
    · intro u hu
      obtain ⟨w, hw⟩ := hk u hu
      have hx : x ∉ u.vars := by simpa using hkx u hu
      exact ⟨w, by rw [LTerm.eval_setEnv _ hx]; exact hw⟩
    · intro q hq x' y' hx' hy'
      have hq' := hnx q hq
      simp only [Bool.not_eq_true'] at hq'
      rw [LTerm.eval_setEnv _ (by simpa using hq'.1)] at hx'
      rw [LTerm.eval_setEnv _ (by simpa using hq'.2)] at hy'
      exact hne q hq x' y' hx' hy'

/-- **A formula `syn` accepts holds in every state.** -/
theorem LFml.syn_valid (φ : LFml) (h : φ.syn [] [] = true) : ∀ σ, φ.holds σ :=
  fun σ => LFml.syn_holds φ σ [] [] (fun _ hu => by simp at hu) (fun _ hp => by simp at hp) h

end Decide

end Solidity
