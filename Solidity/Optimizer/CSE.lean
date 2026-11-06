import Solidity.Optimizer.Simplify
import Solidity.Semantics.RunWk

/-!
# O03 common-subexpression elimination over lowering programs

After `x = e;` (recorded when `e` is pure and does not read `x`) or `T x = e;`
(always recorded; an impure `e` is never matched) succeeds, `x` holds `e`'s value; while neither
`x` nor a local `e` reads is assigned, a later occurrence of `e` is replaced
by a read of `x`, as solc's `CommonSubexpressionEliminator` replaces an
expression by a variable known to hold it. A recorded `e` evaluated
successfully (its statement completed), and the state it reads is unchanged
while the entry lives, so the occurrence it replaces evaluates to the same
value: a failing expression is never replaced. An entry survives an
assignment only when `e` is pure (literals, locals, environment reads and
operators over them) and does not read the assigned local (`Val.indep`); the
pure entries also survive the storage statements `assign`, `delete` and `pop`
(`Avail.keep`, via `KeepsLocals`), and an `assign`'s stored value is rewritten.

Only pure expressions are compared: equality is syntactic on the typed IR
(`Val.pbeq`, `false` outside the pure fragment, sound by `Val.pbeq_eq`),
decided without a classical oracle. The invariant is `Avail.Holds A σ`: each
recorded expression evaluates in `σ` to its local's value. Entries are kept
across `x = e`, `T x = e`, `require` and `assert` (and, pure ones only, across
`assign`, `delete`, `pop`), as in propagation; any other statement clears them;
assigning a local drops every entry that reads it or is held by it; a branch,
block or loop exit forgets them, and a loop body starts with none.
Preservation: `Prog.cse_runC` (exact typed run where the entries hold) and
`Prog.cse_empty_runC` (no premise).
-/
namespace Solidity.Optimizer.ConstFold
open Solidity

variable {C : Contract} {Γ : Ctx}

/-! ## Typed syntactic equality on the pure fragment -/

/-- A binary node's operator and operands. -/
def asBin? {q : PrimTy} : Val C Γ q → Option ((p : PrimTy) × BinOp × Val C Γ p × Val C Γ p)
  | .binop (p := p) op _ _ a b => some ⟨p, op, a, b⟩
  | .simple _ | .read _ | .unop .. | .ternary .. | .readMem _ | .len .. | .mlen .. | .modular ..
  | .hash .. => none

/-- A unary node's operator and operand. -/
def asUn? {q : PrimTy} : Val C Γ q → Option ((p : PrimTy) × UnOp × Val C Γ p)
  | .unop (p := p) op _ _ a => some ⟨p, op, a⟩
  | .simple _ | .read _ | .binop .. | .ternary .. | .readMem _ | .len .. | .mlen .. | .modular ..
  | .hash .. => none

/-- A conditional's parts. -/
def asTern? {q : PrimTy} : Val C Γ q → Option (Val C Γ .bool × Val C Γ q × Val C Γ q)
  | .ternary c a b => some (c, a, b)
  | .simple _ | .read _ | .binop .. | .unop .. | .readMem _ | .len .. | .mlen .. | .modular ..
  | .hash .. => none

/-- A modular node's parts. -/
def asMod? {q : PrimTy} : Val C Γ q → Option (ModOp × Val C Γ .uint × Val C Γ .uint × Val C Γ .uint)
  | .modular op a b k => some (op, a, b, k)
  | .simple _ | .read _ | .binop .. | .unop .. | .ternary .. | .readMem _ | .len .. | .mlen ..
  | .hash .. => none

theorem asBin?_eq {q : PrimTy} {v : Val C Γ q} {p : PrimTy} {op : BinOp} {a b : Val C Γ p}
    (h : asBin? v = some ⟨p, op, a, b⟩) :
    ∃ ha hq, v = .binop op ha hq a b := by
  cases v with
  | binop op' ha hq a' b' =>
    simp only [asBin?, Option.some.injEq, Sigma.mk.injEq] at h
    obtain ⟨rfl, h2⟩ := h
    simp only [heq_eq_eq, Prod.mk.injEq] at h2
    obtain ⟨rfl, rfl, rfl⟩ := h2
    exact ⟨ha, hq, rfl⟩
  | simple | read | unop | ternary | readMem | len | mlen | modular | hash =>
    simp only [asBin?, reduceCtorEq] at h

theorem asUn?_eq {q : PrimTy} {v : Val C Γ q} {p : PrimTy} {op : UnOp} {a : Val C Γ p}
    (h : asUn? v = some ⟨p, op, a⟩) : ∃ ha hq, v = .unop op ha hq a := by
  cases v with
  | unop op' ha hq a' =>
    simp only [asUn?, Option.some.injEq, Sigma.mk.injEq] at h
    obtain ⟨rfl, h2⟩ := h
    simp only [heq_eq_eq, Prod.mk.injEq] at h2
    obtain ⟨rfl, rfl⟩ := h2
    exact ⟨ha, hq, rfl⟩
  | simple | read | binop | ternary | readMem | len | mlen | modular | hash =>
    simp only [asUn?, reduceCtorEq] at h

theorem asTern?_eq {q : PrimTy} {v : Val C Γ q} {c : Val C Γ .bool} {a b : Val C Γ q}
    (h : asTern? v = some (c, a, b)) : v = .ternary c a b := by
  cases v with
  | ternary c' a' b' =>
    simp only [asTern?, Option.some.injEq, Prod.mk.injEq] at h
    obtain ⟨rfl, rfl, rfl⟩ := h
    rfl
  | simple | read | binop | unop | readMem | len | mlen | modular | hash =>
    simp only [asTern?, reduceCtorEq] at h

theorem asMod?_eq {q : PrimTy} {v : Val C Γ q} {op : ModOp} {a b k : Val C Γ .uint}
    (h : asMod? v = some (op, a, b, k)) : ∃ e : q = .uint, v = e ▸ .modular op a b k := by
  cases v with
  | modular op' a' b' k' =>
    simp only [asMod?, Option.some.injEq, Prod.mk.injEq] at h
    obtain ⟨rfl, rfl, rfl, rfl⟩ := h
    exact ⟨rfl, rfl⟩
  | simple | read | binop | unop | ternary | readMem | len | mlen | hash =>
    simp only [asMod?, reduceCtorEq] at h

/-- Syntactic equality of pure expressions (`false` outside the fragment). -/
def Val.pbeq : {p : PrimTy} → Val C Γ p → Val C Γ p → Bool
  | _, .simple s, b =>
    match simple? b with
    | some t => Simple.beq s t
    | none => false
  | _, .binop (p := p) op _ _ x y, b =>
    match asBin? b with
    | some ⟨p', op', x', y'⟩ =>
      if h : p' = p then op == op' && Val.pbeq x (h ▸ x') && Val.pbeq y (h ▸ y') else false
    | none => false
  | _, .unop (p := p) op _ _ x, b =>
    match asUn? b with
    | some ⟨p', op', x'⟩ => if h : p' = p then op == op' && Val.pbeq x (h ▸ x') else false
    | none => false
  | _, .ternary c x y, b =>
    match asTern? b with
    | some (c', x', y') => Val.pbeq c c' && Val.pbeq x x' && Val.pbeq y y'
    | none => false
  | _, .modular op x y k, b =>
    match asMod? b with
    | some (op', x', y', k') => op == op' && Val.pbeq x x' && Val.pbeq y y' && Val.pbeq k k'
    | none => false
  | _, .read _, _ | _, .readMem _, _ | _, .len .., _ | _, .mlen .., _ | _, .hash .., _ => false

theorem Val.pbeq_eq : {p : PrimTy} → (a b : Val C Γ p) → Val.pbeq a b = true → a = b
  | _, .simple s, b, h => by
    simp only [Val.pbeq] at h
    cases hb : simple? b with
    | none => simp only [hb, Bool.false_eq_true] at h
    | some t =>
      simp only [hb] at h
      rw [simple?_eq hb, Simple.beq_eq s t h]
  | _, .binop (p := p) op ha hq x y, b, h => by
    simp only [Val.pbeq] at h
    cases hb : asBin? b with
    | none => simp only [hb, Bool.false_eq_true] at h
    | some r =>
      obtain ⟨p', op', x', y'⟩ := r
      simp only [hb] at h
      split at h
      · next e =>
        subst p'
        simp only [Bool.and_eq_true, beq_iff_eq] at h
        obtain ⟨⟨rfl, hx⟩, hy⟩ := h
        obtain ⟨ha', hq', rfl⟩ := asBin?_eq hb
        rw [Val.pbeq_eq x x' hx, Val.pbeq_eq y y' hy]
      · exact absurd h Bool.false_ne_true
  | _, .unop (p := p) op ha hq x, b, h => by
    simp only [Val.pbeq] at h
    cases hb : asUn? b with
    | none => simp only [hb, Bool.false_eq_true] at h
    | some r =>
      obtain ⟨p', op', x'⟩ := r
      simp only [hb] at h
      split at h
      · next e =>
        subst p'
        simp only [Bool.and_eq_true, beq_iff_eq] at h
        obtain ⟨rfl, hx⟩ := h
        obtain ⟨ha', hq', rfl⟩ := asUn?_eq hb
        rw [Val.pbeq_eq x x' hx]
      · exact absurd h Bool.false_ne_true
  | _, .ternary c x y, b, h => by
    simp only [Val.pbeq] at h
    cases hb : asTern? b with
    | none => simp only [hb, Bool.false_eq_true] at h
    | some r =>
      obtain ⟨c', x', y'⟩ := r
      simp only [hb, Bool.and_eq_true] at h
      obtain ⟨⟨hc, hx⟩, hy⟩ := h
      rw [asTern?_eq hb, Val.pbeq_eq c c' hc, Val.pbeq_eq x x' hx, Val.pbeq_eq y y' hy]
  | _, .modular op x y k, b, h => by
    simp only [Val.pbeq] at h
    cases hb : asMod? b with
    | none => simp only [hb, Bool.false_eq_true] at h
    | some r =>
      obtain ⟨op', x', y', k'⟩ := r
      simp only [hb, Bool.and_eq_true, beq_iff_eq] at h
      obtain ⟨⟨⟨rfl, hx⟩, hy⟩, hk⟩ := h
      obtain ⟨e, hbe⟩ := asMod?_eq hb
      cases e
      rw [hbe, Val.pbeq_eq x x' hx, Val.pbeq_eq y y' hy, Val.pbeq_eq k k' hk]
  | _, .read _, _, h | _, .readMem _, _, h | _, .len .., _, h | _, .mlen .., _, h
  | _, .hash .., _, h => by simp only [Val.pbeq, Bool.false_eq_true] at h
  termination_by structural _ a => a

/-! ## Independence of an assigned local -/

/-- `v` is pure and does not read the local at position `n`. -/
def Val.indep (n : Nat) : {p : PrimTy} → Val C Γ p → Bool
  | _, .simple s => !readsAt n s
  | _, .binop _ _ _ a b => Val.indep n a && Val.indep n b
  | _, .unop _ _ _ a => Val.indep n a
  | _, .ternary c a b => Val.indep n c && Val.indep n a && Val.indep n b
  | _, .modular _ a b k => Val.indep n a && Val.indep n b && Val.indep n k
  | _, .read _ | _, .readMem _ | _, .len .. | _, .mlen .. | _, .hash .. => false

theorem Val.evalT_setLocal_indep {q : PrimTy} (σ : State C Γ) (i : Idx Γ (.val q)) (x : q.Denote) :
    {p : PrimTy} → (v : Val C Γ p) → Val.indep i.toNat v = true →
      v.evalT (σ.setLocal i x) = v.evalT σ
  | _, .simple s, h => by
    simp only [Val.indep, Bool.not_eq_eq_eq_not, Bool.not_true] at h
    simp only [Val.evalT, evalT_setLocal_of_not_reads σ i x s h]
  | _, .binop op ha hq a b, h => by
    simp only [Val.indep, Bool.and_eq_true] at h
    simp only [Val.evalT, Val.evalT_setLocal_indep σ i x a h.1,
      Val.evalT_setLocal_indep σ i x b h.2]
  | _, .unop op ha hq a, h => by
    simp only [Val.indep] at h
    simp only [Val.evalT, Val.evalT_setLocal_indep σ i x a h]
  | _, .ternary c a b, h => by
    simp only [Val.indep, Bool.and_eq_true] at h
    simp only [Val.evalT, Val.evalT_setLocal_indep σ i x c h.1.1,
      Val.evalT_setLocal_indep σ i x a h.1.2, Val.evalT_setLocal_indep σ i x b h.2]
  | _, .modular op a b k, h => by
    simp only [Val.indep, Bool.and_eq_true] at h
    simp only [Val.evalT, Val.evalT_setLocal_indep σ i x a h.1.1,
      Val.evalT_setLocal_indep σ i x b h.1.2, Val.evalT_setLocal_indep σ i x k h.2]
  | _, .read _, h | _, .readMem _, h | _, .len .., h | _, .mlen .., h | _, .hash .., h => by
    simp only [Val.indep, Bool.false_eq_true] at h

/-! ## Available expressions -/

/-- Local `j` holds the value of the pure expression `e`. -/
structure Avail (C : Contract) (Γ : Ctx) where
  p : PrimTy
  j : Idx Γ (.val p)
  e : Val C Γ p

/-- Each recorded expression evaluates to its local's value. -/
def Avail.Holds (A : List (Avail C Γ)) (σ : State C Γ) : Prop :=
  ∀ a ∈ A, a.e.evalT σ = .ok (TEnv.get a.j σ.env)

theorem Avail.holds_nil (σ : State C Γ) : Avail.Holds ([] : List (Avail C Γ)) σ :=
  fun _ h => nomatch h

/-- The local holding `v`, if one is recorded. -/
def Avail.find? {p : PrimTy} (v : Val C Γ p) : List (Avail C Γ) → Option (Idx Γ (.val p))
  | [] => none
  | a :: A =>
    if h : a.p = p then
      if Val.pbeq (h ▸ a.e) v then some (h ▸ a.j) else Avail.find? v A
    else Avail.find? v A

theorem Avail.find?_evalT {A : List (Avail C Γ)} {σ : State C Γ} (hA : Avail.Holds A σ)
    {p : PrimTy} (v : Val C Γ p) {j : Idx Γ (.val p)} (hf : Avail.find? v A = some j) :
    v.evalT σ = .ok (TEnv.get j σ.env) := by
  induction A with
  | nil => simp only [Avail.find?, reduceCtorEq] at hf
  | cons a A ih =>
    have ha := hA a List.mem_cons_self
    have hA' : Avail.Holds A σ := fun b hb => hA b (List.mem_cons_of_mem a hb)
    obtain ⟨q, k, e⟩ := a
    simp only [Avail.find?] at hf
    split at hf
    · next hq =>
      subst hq
      split at hf
      · next hb =>
        simp only [Option.some.injEq] at hf
        subst hf
        rw [← Val.pbeq_eq e v hb]
        exact ha
      · exact ih hA' hf
    · exact ih hA' hf

/-- Replace each recorded subexpression by a read of the local holding it. -/
def _root_.Solidity.Val.cse (A : List (Avail C Γ)) : {p : PrimTy} → Val C Γ p → Val C Γ p
  | _, v@(.simple _) => v
  | _, v@(.binop op h hq a b) =>
    match Avail.find? v A with
    | some j => .simple (.local j)
    | none => .binop op h hq (a.cse A) (b.cse A)
  | _, v@(.unop op h hq a) =>
    match Avail.find? v A with
    | some j => .simple (.local j)
    | none => .unop op h hq (a.cse A)
  | _, v@(.ternary c a b) =>
    match Avail.find? v A with
    | some j => .simple (.local j)
    | none => .ternary (c.cse A) (a.cse A) (b.cse A)
  | _, v@(.modular op a b k) =>
    match Avail.find? v A with
    | some j => .simple (.local j)
    | none => .modular op (a.cse A) (b.cse A) (k.cse A)
  | _, v@(.read _) | _, v@(.readMem _) | _, v@(.len ..) | _, v@(.mlen ..) | _, v@(.hash ..) => v

theorem _root_.Solidity.Val.cse_evalT {A : List (Avail C Γ)} {σ : State C Γ}
    (hA : Avail.Holds A σ) : {p : PrimTy} → (v : Val C Γ p) → (v.cse A).evalT σ = v.evalT σ
  | _, .simple _ => by simp only [Val.cse]
  | _, .binop op h hq a b => by
    simp only [Val.cse]
    split
    · next j hj => exact (Avail.find?_evalT hA _ hj).symm
    · simp only [Val.evalT, Val.cse_evalT hA a, Val.cse_evalT hA b]
  | _, .unop op h hq a => by
    simp only [Val.cse]
    split
    · next j hj => exact (Avail.find?_evalT hA _ hj).symm
    · simp only [Val.evalT, Val.cse_evalT hA a]
  | _, .ternary c a b => by
    simp only [Val.cse]
    split
    · next j hj => exact (Avail.find?_evalT hA _ hj).symm
    · simp only [Val.evalT, Val.cse_evalT hA c, Val.cse_evalT hA a, Val.cse_evalT hA b]
  | _, .modular op a b k => by
    simp only [Val.cse]
    split
    · next j hj => exact (Avail.find?_evalT hA _ hj).symm
    · simp only [Val.evalT, Val.cse_evalT hA a, Val.cse_evalT hA b, Val.cse_evalT hA k]
  | _, .read _ | _, .readMem _ | _, .len .. | _, .mlen .. | _, .hash .. => by simp only [Val.cse]

/-- Entries after `i = r;` (`r` the original right side). -/
def Avail.set {p : PrimTy} (A : List (Avail C Γ)) (i : Idx Γ (.val p)) (r : Val C Γ p) :
    List (Avail C Γ) :=
  let kept := A.filter fun a => a.j.toNat != i.toNat && Val.indep i.toNat a.e
  if Val.indep i.toNat r then ⟨p, i, r⟩ :: kept else kept

/-- Entries read one local deeper. -/
def Avail.push {t : LTy} (A : List (Avail C Γ)) : List (Avail C (t :: Γ)) :=
  A.map fun a => ⟨a.p, a.j.there, a.e.wk (.drop .refl)⟩

/-- Entries after `T x = e;`. -/
def Avail.decl {p : PrimTy} (A : List (Avail C Γ)) :
    Option (Val C Γ p) → List (Avail C (.val p :: Γ))
  | none => Avail.push A
  | some e => ⟨p, .here, e.wk (.drop .refl)⟩ :: Avail.push A

private theorem get_set_ne' {H : HTy} {Γ : Ctx} {t u : LTy} : (i : Idx Γ t) → (j : Idx Γ u) →
    (v : t.TDenote C H) → (e : TEnv C H Γ) → i.toNat ≠ j.toNat →
      TEnv.get j (TEnv.set i v e) = TEnv.get j e
  | .here, .here, _, _, h => absurd rfl h
  | .here, .there _, _, _, _ => rfl
  | .there _, .here, _, _, _ => rfl
  | .there i, .there j, v, e, h => get_set_ne' i j v e.2 fun h' => h (congrArg (· + 1) h')

private theorem get_set' {H : HTy} {Γ : Ctx} {t : LTy} : (i : Idx Γ t) → (v : t.TDenote C H) →
    (e : TEnv C H Γ) → TEnv.get i (TEnv.set i v e) = v
  | .here, _, _ => rfl
  | .there i, v, e => get_set' i v e.2

theorem Avail.holds_set {A : List (Avail C Γ)} {σ : State C Γ} (hA : Avail.Holds A σ)
    {p : PrimTy} (i : Idx Γ (.val p)) (r : Val C Γ p) (v : p.Denote) (hv : r.evalT σ = .ok v) :
    Avail.Holds (Avail.set A i r) (σ.setLocal i v) := by
  have hkept : Avail.Holds (A.filter fun a => a.j.toNat != i.toNat && Val.indep i.toNat a.e)
      (σ.setLocal i v) := by
    intro a ha
    obtain ⟨hmem, hk⟩ := List.mem_filter.mp ha
    simp only [Bool.and_eq_true, bne_iff_ne] at hk
    rw [Val.evalT_setLocal_indep σ i v a.e hk.2, hA a hmem]
    show Except.ok (TEnv.get a.j σ.env) = Except.ok (TEnv.get a.j (TEnv.set i v σ.env))
    rw [get_set_ne' i a.j v σ.env (Ne.symm hk.1)]
  unfold Avail.set
  split
  · next hr =>
    intro a ha
    rcases List.mem_cons.mp ha with rfl | ha
    · show r.evalT (σ.setLocal i v) = .ok (TEnv.get i (TEnv.set i v σ.env))
      rw [Val.evalT_setLocal_indep σ i v r hr, hv, get_set']
    · exact hkept a ha
  · exact hkept

theorem Avail.holds_push {A : List (Avail C Γ)} {σ : State C Γ} (hA : Avail.Holds A σ)
    {t : LTy} (v : t.TDenote C σ.H) : Avail.Holds (Avail.push (t := t) A) (σ.push v) := by
  intro a ha
  obtain ⟨b, hb, rfl⟩ := List.mem_map.mp ha
  show (b.e.wk (.drop .refl)).evalT (σ.lift (.drop .refl) (v, σ.env)) = _
  rw [Val.evalT_wk]
  exact hA b hb

theorem Avail.holds_decl {A : List (Avail C Γ)} {σ : State C Γ} (hA : Avail.Holds A σ)
    {p : PrimTy} (init : Option (Val C Γ p)) (v : p.Denote)
    (hv : ∀ e, init = some e → e.evalT σ = .ok v) :
    Avail.Holds (Avail.decl A init) (σ.push (t := .val p) v) := by
  cases init with
  | none => exact Avail.holds_push (t := .val p) hA v
  | some e =>
    intro a ha
    rcases List.mem_cons.mp ha with rfl | ha
    · show (e.wk (.drop .refl)).evalT
        (σ.lift (.drop .refl) ((v, σ.env) : TEnv C σ.H (.val p :: Γ))) = _
      rw [Val.evalT_wk]
      exact hv e rfl
    · exact Avail.holds_push (t := .val p) hA v a ha

/-! ## Across statements that keep the locals -/

/-- The pure fragment: literals, locals, environment reads and operators. -/
def Val.isPure : {p : PrimTy} → Val C Γ p → Bool
  | _, .simple _ => true
  | _, .binop _ _ _ a b => Val.isPure a && Val.isPure b
  | _, .unop _ _ _ a => Val.isPure a
  | _, .ternary c a b => Val.isPure c && Val.isPure a && Val.isPure b
  | _, .modular _ a b k => Val.isPure a && Val.isPure b && Val.isPure k
  | _, .read _ | _, .readMem _ | _, .len .. | _, .mlen .. | _, .hash .. => false

theorem Val.evalT_keep {σ τ : State C Γ}
    (hl : ∀ (q : PrimTy) (k : Idx Γ (.val q)), TEnv.get k τ.env = TEnv.get k σ.env)
    (he : ∀ key, τ.envVal key = σ.envVal key) :
    {p : PrimTy} → (v : Val C Γ p) → Val.isPure v = true → v.evalT τ = v.evalT σ
  | _, .simple s, _ => by
    cases s with
    | lit => rfl
    | bool => rfl
    | «local» k => exact congrArg Except.ok (hl _ k)
    | env key hp => cases hp; exact congrArg Except.ok (he key)
  | _, .binop op ha hq a b, h => by
    simp only [Val.isPure, Bool.and_eq_true] at h
    simp only [Val.evalT, Val.evalT_keep hl he a h.1, Val.evalT_keep hl he b h.2]
  | _, .unop op ha hq a, h => by
    simp only [Val.isPure] at h
    simp only [Val.evalT, Val.evalT_keep hl he a h]
  | _, .ternary c a b, h => by
    simp only [Val.isPure, Bool.and_eq_true] at h
    simp only [Val.evalT, Val.evalT_keep hl he c h.1.1, Val.evalT_keep hl he a h.1.2,
      Val.evalT_keep hl he b h.2]
  | _, .modular op a b k, h => by
    simp only [Val.isPure, Bool.and_eq_true] at h
    simp only [Val.evalT, Val.evalT_keep hl he a h.1.1, Val.evalT_keep hl he b h.1.2,
      Val.evalT_keep hl he k h.2]
  | _, .read _, h | _, .readMem _, h | _, .len .., h | _, .mlen .., h | _, .hash .., h => by
    simp only [Val.isPure, Bool.false_eq_true] at h

/-- The pure entries, which survive a step that keeps the locals. -/
def Avail.keep (A : List (Avail C Γ)) : List (Avail C Γ) := A.filter fun a => Val.isPure a.e

theorem Avail.holds_keep {A : List (Avail C Γ)} {f : TStep C Γ Γ} (hk : KeepsLocals f)
    {σ : State C Γ} (hA : Avail.Holds A σ) {o : Out C σ.H Γ} (ho : f σ = .ok o) :
    Avail.Holds (Avail.keep A) o.st := by
  obtain ⟨hl, he⟩ := hk σ o ho
  intro a ha
  obtain ⟨hmem, hp⟩ := List.mem_filter.mp ha
  rw [Val.evalT_keep hl he a.e hp, hA a hmem, hl]

/-- CSE inside a storage source's value. -/
def _root_.Solidity.Src.cse (A : List (Avail C Γ)) : {T : Ty} → Src C Γ T → Src C Γ T
  | _, .val v => .val (v.cse A)
  | _, s@(.copy ..) | _, s@(.fixedCopy ..) | _, s@(.copyMem ..) | _, s@(.fixedCopyMem ..) => s

theorem _root_.Solidity.Src.cse_valueT {A : List (Avail C Γ)} {σ : State C Γ}
    (hA : Avail.Holds A σ) : {T : Ty} → (r : Src C Γ T) → (r.cse A).valueT σ = r.valueT σ
  | _, .val v => by simp only [Src.cse, Src.valueT, Val.cse_evalT hA]
  | _, .copy .. | _, .fixedCopy .. | _, .copyMem .. | _, .fixedCopyMem .. => rfl

/-! ## The pass -/

mutual
/-- CSE through one statement: the rewritten statement and the entries after it. -/
def Stmt.cse : {Γ Γ' : Ctx} → List (Avail C Γ) → Stmt C Γ Γ' → Stmt C Γ Γ' × List (Avail C Γ')
  | _, _, F, .assignLocal i r => (.assignLocal i (r.cse F), Avail.set F i r)
  | _, _, F, .declLocal p x init =>
    (.declLocal p x (init.map (Val.cse F)), Avail.decl F init)
  | _, _, F, .require c => (.require (c.cse F), F)
  | _, _, F, .assert c => (.assert (c.cse F), F)
  | _, _, F, .ite c thn els =>
    (.ite (c.cse F) (Prog.cse F thn) (Prog.cse F els), [])
  | _, _, F, .block body => (.block (Prog.cse F body), [])
  | _, _, _, .loop a c body => (.loop a c (Prog.cse [] body), [])
  | _, _, F, .assign l r => (.assign l (r.cse F), Avail.keep F)
  | _, _, F, .delete l => (.delete l, Avail.keep F)
  | _, _, F, .pop b => (.pop b, Avail.keep F)
  | _, _, _, s@(.rebind ..) | _, _, _, s@(.declStorage ..)
  | _, _, _, s@(.opAssign ..) | _, _, _, s@(.incDec ..) | _, _, _, s@(.assignIncDec ..)
  | _, _, _, s@(.assignLocalPush ..) | _, _, _, s@(.push ..)
  | _, _, _, s@(.transfer ..) | _, _, _, s@(.send ..) | _, _, _, s@(.declMem ..)
  | _, _, _, s@(.rebindMem ..) | _, _, _, s@(.assignFromMem ..) | _, _, _, s@(.assignMem ..)
  | _, _, _, s@(.deleteMem ..) | _, _, _, s@(.assignNew ..)
  | _, _, _, s@.revert | _, _, _, s@.assumeFalse | _, _, _, s@(.call ..)
  | _, _, _, s@(.tryCall ..) | _, _, _, s@(.pushOpAssign ..) | _, _, _, s@(.pushIncDec ..)
  | _, _, _, s@(.callReceiver ..) | _, _, _, s@(.callReceiverPush ..)
  | _, _, _, s@(.callRec ..) | _, _, _, s@(.revertData ..) | _, _, _, s@(.catchData ..) =>
    (s, [])

/-- CSE through a sequence. -/
def Prog.cse : {Γ Γ' : Ctx} → List (Avail C Γ) → Prog C Γ Γ' → Prog C Γ Γ'
  | _, _, _, .nil => .nil
  | _, _, F, .cons s P =>
    let r := Stmt.cse F s
    .cons r.1 (Prog.cse r.2 P)
end

/-! ## Preservation -/

mutual
/-- A statement's rewrite runs as it does where the entry facts hold, and
the exit facts hold in each state it leaves. -/
theorem Stmt.cse_runC : {Γ Γ' : Ctx} → (F : List (Avail C Γ)) → (s : Stmt C Γ Γ') →
    (σ : State C Γ) → Avail.Holds F σ →
      Stmt.runC (Stmt.cse F s).1 σ = Stmt.runC s σ ∧
      ∀ o, Stmt.runC s σ = .ok o → Avail.Holds (Stmt.cse F s).2 o.st
  | _, _, F, .assignLocal i r, σ, hF => by
    refine ⟨?_, ?_⟩
    · simp only [Stmt.cse, Stmt.runC, TRun.assignLocal, Val.cse_evalT hF]
    · intro o ho
      simp only [Stmt.runC, TRun.assignLocal, bind, Except.bind] at ho
      cases hr : r.evalT σ with
      | error e => simp only [hr, reduceCtorEq] at ho
      | ok v =>
        simp only [hr, pure, Except.pure, Except.ok.injEq] at ho
        subst ho
        exact Avail.holds_set hF i r v hr
  | _, _, F, .declLocal p x init, σ, hF => by
    have hinit : ∀ σ' : State C _, Avail.Holds F σ' →
        TRun.declLocal p (init.map (Val.cse F)) σ' = TRun.declLocal p init σ' := by
      intro σ' hF'
      cases init <;> simp only [TRun.declLocal, Option.map, Val.cse_evalT hF']
    refine ⟨hinit σ hF, ?_⟩
    intro o ho
    simp only [Stmt.cse]
    cases init with
    | none =>
      simp only [Stmt.runC, TRun.declLocal, pure, Except.pure, bind, Except.bind,
        Except.ok.injEq] at ho
      subst ho
      exact Avail.holds_decl hF none _ (fun _ h => nomatch h)
    | some e =>
      simp only [Stmt.runC, TRun.declLocal, bind, Except.bind] at ho
      cases he : e.evalT σ with
      | error err => simp only [he, reduceCtorEq] at ho
      | ok v =>
        simp only [he, pure, Except.pure, Except.ok.injEq] at ho
        subst ho
        exact Avail.holds_decl hF (some e) v fun e' h => by
          simp only [Option.some.injEq] at h
          subst h
          exact he
  | _, _, F, .require c, σ, hF => by
    refine ⟨?_, ?_⟩
    · simp only [Stmt.cse, Stmt.runC, TRun.require, Val.cse_evalT hF]
    · intro o ho
      simp only [Stmt.runC, TRun.require, bind, Except.bind] at ho
      cases hc : c.evalT σ with
      | error e => simp only [hc, reduceCtorEq] at ho
      | ok v =>
        cases hb : boolT v
        · simp only [hc, hb, Bool.false_eq_true, ite_false, reduceCtorEq] at ho
        · simp only [hc, hb, ite_true, pure, Except.pure, Except.ok.injEq] at ho
          subst ho
          exact hF
  | _, _, F, .assert c, σ, hF => by
    refine ⟨?_, ?_⟩
    · simp only [Stmt.cse, Stmt.runC, TRun.assert, Val.cse_evalT hF]
    · intro o ho
      simp only [Stmt.runC, TRun.assert, bind, Except.bind] at ho
      cases hc : c.evalT σ with
      | error e => simp only [hc, reduceCtorEq] at ho
      | ok v =>
        cases hb : boolT v
        · simp only [hc, hb, Bool.false_eq_true, ite_false, reduceCtorEq] at ho
        · simp only [hc, hb, ite_true, pure, Except.pure, Except.ok.injEq] at ho
          subst ho
          exact hF
  | _, _, F, .ite c thn els, σ, hF => by
    refine ⟨?_, fun _ _ => Avail.holds_nil _⟩
    simp only [Stmt.cse, Stmt.runC, TRun.ite, Val.cse_evalT hF,
      (Prog.cse_runC F thn σ hF), (Prog.cse_runC F els σ hF)]
    rw [Subsingleton.elim (Prog.cse F thn).ext thn.ext,
      Subsingleton.elim (Prog.cse F els).ext els.ext]
  | _, _, F, .block body, σ, hF => by
    refine ⟨?_, fun _ _ => Avail.holds_nil _⟩
    simp only [Stmt.cse, Stmt.runC, TRun.block, (Prog.cse_runC F body σ hF)]
    rw [Subsingleton.elim (Prog.cse F body).ext body.ext]
  | _, _, _, .loop a c body, σ, _ => by
    refine ⟨?_, fun _ _ => Avail.holds_nil _⟩
    have hb : Prog.runC (Prog.cse [] body) = Prog.runC body :=
      funext fun τ => Prog.cse_runC [] body τ (Avail.holds_nil τ)
    simp only [Stmt.cse, Stmt.runC]
    rw [hb, Subsingleton.elim (Prog.cse [] body).ext body.ext]
  | _, _, F, .assign l r, σ, hF =>
    ⟨by simp only [Stmt.cse, Stmt.runC, TRun.assign, Src.cse_valueT hF],
      fun _ ho => Avail.holds_keep (keeps_assign l r) hF ho⟩
  | _, _, F, .delete l, σ, hF => ⟨rfl, fun _ ho => Avail.holds_keep (keeps_delete l) hF ho⟩
  | _, _, F, .pop b, σ, hF => ⟨rfl, fun _ ho => Avail.holds_keep (keeps_pop b) hF ho⟩
  | _, _, _, .rebind .., _, _ | _, _, _, .declStorage .., _, _
  | _, _, _, .opAssign .., _, _ | _, _, _, .incDec .., _, _ | _, _, _, .assignIncDec .., _, _
  | _, _, _, .assignLocalPush .., _, _ | _, _, _, .push .., _, _
  | _, _, _, .transfer .., _, _ | _, _, _, .send .., _, _ | _, _, _, .declMem .., _, _
  | _, _, _, .rebindMem .., _, _ | _, _, _, .assignFromMem .., _, _
  | _, _, _, .assignMem .., _, _ | _, _, _, .deleteMem .., _, _
  | _, _, _, .assignNew .., _, _ | _, _, _, .revert, _, _ | _, _, _, .assumeFalse, _, _
  | _, _, _, .call .., _, _ | _, _, _, .tryCall .., _, _ | _, _, _, .pushOpAssign .., _, _
  | _, _, _, .pushIncDec .., _, _ | _, _, _, .callReceiver .., _, _
  | _, _, _, .callReceiverPush .., _, _ | _, _, _, .callRec .., _, _
  | _, _, _, .revertData .., _, _ | _, _, _, .catchData .., _, _ =>
    ⟨rfl, fun _ _ => Avail.holds_nil _⟩

/-- A sequence's rewrite runs as it does where the entry facts hold. -/
theorem Prog.cse_runC : {Γ Γ' : Ctx} → (F : List (Avail C Γ)) → (P : Prog C Γ Γ') →
    (σ : State C Γ) → Avail.Holds F σ → Prog.runC (Prog.cse F P) σ = Prog.runC P σ
  | _, _, _, .nil, _, _ => rfl
  | _, _, F, .cons s P, σ, hF => by
    obtain ⟨hrun, hout⟩ := Stmt.cse_runC F s σ hF
    simp only [Prog.cse, Prog.runC, TRun.seq, hrun]
    cases ho : Stmt.runC s σ with
    | error e => rfl
    | ok o =>
      dsimp only
      rw [Prog.cse_runC _ P o.st (hout o ho)]
end

/-- **CSE with no entry facts preserves the typed run.** -/
theorem Prog.cse_empty_runC {Γ Γ' : Ctx} (P : Prog C Γ Γ') :
    Prog.runC (Prog.cse [] P) = Prog.runC P :=
  funext fun σ => Prog.cse_runC [] P σ (Avail.holds_nil σ)

theorem cse_preserves (Γ Γ' : Ctx) :
    Preserves (SameRun (C := C) (Γ := Γ) (Γ' := Γ'))
      (Prog.cse [] : Lowering.Pass C Γ Γ') :=
  fun P => (Prog.cse_empty_runC P).symm

end Solidity.Optimizer.ConstFold
