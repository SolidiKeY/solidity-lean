import Solidity.Optimizer.StmtFold

/-!
# O02 constant and copy propagation over lowering programs

A forward pass over `Prog C Γ Δ` that tracks, for value locals, a simple
value known to equal them: a literal (constant propagation) or another local
(copy propagation). A read of such a local is replaced by that value, then the
expression is folded (`Val.cfold`), so a propagated constant feeds folding.

Facts are created only by `x = e;` and `T x = e;` whose folded right-hand
side is a literal or a local. They survive local assignments (minus the ones
an assignment kills: the fact for the assigned local and every fact reading
it), declarations, `require`, `assert`, and the storage statements `assign`,
`delete` and `pop`, which leave every local and environment value as it was
(`KeepsLocals`); the value an `assign` stores is propagated into. Any other statement, and the exit
of a branch, block or loop, forgets every fact; a loop body and its condition
are processed with no facts, since they run in states the entry facts need not
describe. `transfer`/`send` operands are not rewritten here (they are folded
by `Prog.cfold`).
Environment values (`msg.sender`, …) are never recorded.

The invariant is `Facts.Holds F σ`: each recorded local holds its value in
`σ`. Preservation (`Prog.cprop_runC`) is equality of the typed run in every
state where the entry facts hold, so with no entry facts the whole run is
unchanged (`cprop_preserves`).
-/
namespace Solidity.Optimizer.ConstFold
open Solidity

variable {C : Contract}

/-! ## Simple values under local changes -/

/-- Does this simple value read the local at position `n`? -/
def readsAt {Γ : Ctx} {p : PrimTy} (n : Nat) : Simple C Γ p → Bool
  | .local k => k.toNat == n
  | .lit .. | .bool _ | .env .. => false

/-- A simple value read one local deeper. -/
def shiftS {Γ : Ctx} {t : LTy} : {p : PrimTy} → Simple C Γ p → Simple C (t :: Γ) p
  | _, .lit n h => .lit n h
  | _, .bool b => .bool b
  | _, .local k => .local k.there
  | _, .env k hp => .env k hp

theorem shiftS_evalT {Γ : Ctx} {t : LTy} (σ : State C Γ) (v : t.TDenote C σ.H) :
    {p : PrimTy} → (s : Simple C Γ p) → (shiftS s).evalT (σ.push v) = s.evalT σ
  | _, .lit .. => rfl
  | _, .bool _ => rfl
  | _, .local _ => rfl
  | _, .env _ hp => by cases hp; rfl

/-- Two indices at one position are one index. -/
theorem Idx.eq_of_toNat : {Γ : Ctx} → {p q : PrimTy} → (i : Idx Γ (.val p)) →
    (j : Idx Γ (.val q)) → j.toNat = i.toNat → ∃ e : p = q, j = e ▸ i
  | _, _, _, .here, .here, _ => ⟨rfl, rfl⟩
  | _, _, _, .here, .there _, h => by simp only [Idx.toNat] at h; omega
  | _, _, _, .there _, .here, h => by simp only [Idx.toNat] at h; omega
  | _, _, _, .there i, .there j, h => by
    simp only [Idx.toNat, Nat.add_right_cancel_iff] at h
    obtain ⟨e, he⟩ := Idx.eq_of_toNat i j h
    subst e
    subst he
    exact ⟨rfl, rfl⟩

private theorem get_set_ne {H : HTy} {Γ : Ctx} {t u : LTy} : (i : Idx Γ t) → (j : Idx Γ u) →
    (v : t.TDenote C H) → (e : TEnv C H Γ) → i.toNat ≠ j.toNat →
      TEnv.get j (TEnv.set i v e) = TEnv.get j e
  | .here, .here, _, _, h => absurd rfl h
  | .here, .there _, _, _, _ => rfl
  | .there _, .here, _, _, _ => rfl
  | .there i, .there j, v, e, h => get_set_ne i j v e.2 fun h' => h (congrArg (· + 1) h')

private theorem get_set {H : HTy} {Γ : Ctx} {t : LTy} : (i : Idx Γ t) → (v : t.TDenote C H) →
    (e : TEnv C H Γ) → TEnv.get i (TEnv.set i v e) = v
  | .here, _, _ => rfl
  | .there i, v, e => get_set i v e.2

theorem evalT_setLocal_of_not_reads {Γ : Ctx} {p q : PrimTy} (σ : State C Γ)
    (i : Idx Γ (.val q)) (v : q.Denote) (s : Simple C Γ p)
    (hs : readsAt i.toNat s = false) : s.evalT (σ.setLocal i v) = s.evalT σ := by
  cases s with
  | lit => rfl
  | bool => rfl
  | env k hp => cases hp; rfl
  | «local» k =>
    simp only [readsAt, beq_eq_false_iff_ne] at hs
    exact get_set_ne i k v σ.env (Ne.symm hs)

/-! ## Facts -/

/-- For each value local, a simple value known to equal it. -/
structure Facts (C : Contract) (Γ : Ctx) where
  get : (p : PrimTy) → Idx Γ (.val p) → Option (Simple C Γ p)

def Facts.empty {Γ : Ctx} : Facts C Γ := ⟨fun _ _ => none⟩

/-- Every recorded fact holds in `σ`. -/
def Facts.Holds {Γ : Ctx} (F : Facts C Γ) (σ : State C Γ) : Prop :=
  ∀ (p : PrimTy) (j : Idx Γ (.val p)) (s : Simple C Γ p), F.get p j = some s →
    TEnv.get j σ.env = s.evalT σ

theorem Facts.holds_empty {Γ : Ctx} (σ : State C Γ) : (Facts.empty : Facts C Γ).Holds σ :=
  fun _ _ _ h => nomatch h

/-- Facts after `i = e;`, where `s?` is the simple value of `e`, if any. -/
def Facts.set {Γ : Ctx} {p : PrimTy} (F : Facts C Γ) (i : Idx Γ (.val p))
    (s? : Option (Simple C Γ p)) : Facts C Γ := ⟨fun q j =>
  if j.toNat = i.toNat then
    match s? with
    | some s => if h : p = q then some (h ▸ s) else none
    | none => none
  else
    match F.get q j with
    | some t => if readsAt i.toNat t then none else some t
    | none => none⟩

/-- Facts after a declaration with simple initial value `s?`. -/
def Facts.push {Γ : Ctx} {p : PrimTy} (F : Facts C Γ) (s? : Option (Simple C Γ p)) :
    Facts C (.val p :: Γ) := ⟨fun _ j =>
  match j with
  | .here => s?.map shiftS
  | .there j => (F.get _ j).map shiftS⟩

/-- A simple value that is a literal or a local (not an environment read). -/
def Simple.asPure? {Γ : Ctx} : {p : PrimTy} → Simple C Γ p → Option (Simple C Γ p)
  | _, .lit n h => some (.lit n h)
  | _, .bool b => some (.bool b)
  | _, .local k => some (.local k)
  | _, .env .. => none

/-- The simple value an expression is, if it is a literal or a local. -/
def _root_.Solidity.Val.asSimple? {Γ : Ctx} {p : PrimTy} : Val C Γ p → Option (Simple C Γ p)
  | .simple s => Simple.asPure? s
  | .read _ | .binop .. | .unop .. | .ternary .. | .readMem _ | .len ..
  | .mlen .. | .modular .. | .hash .. => none

theorem _root_.Solidity.Val.asSimple?_evalT {Γ : Ctx} {p : PrimTy} {v : Val C Γ p}
    {s : Simple C Γ p} (h : v.asSimple? = some s) (σ : State C Γ) :
    v.evalT σ = .ok (s.evalT σ) ∧
      ∀ n, readsAt n s = true → ∃ k : Idx Γ (.val p), s = .local k ∧ k.toNat = n := by
  cases v with
  | simple t =>
    cases t with
    | lit =>
      simp only [Val.asSimple?, Simple.asPure?, Option.some.injEq] at h
      subst h
      exact ⟨rfl, fun _ hr => nomatch hr⟩
    | bool =>
      simp only [Val.asSimple?, Simple.asPure?, Option.some.injEq] at h
      subst h
      exact ⟨rfl, fun _ hr => nomatch hr⟩
    | «local» k =>
      simp only [Val.asSimple?, Simple.asPure?, Option.some.injEq] at h
      subst h
      exact ⟨rfl, fun n hr => ⟨k, rfl, by simpa only [readsAt, beq_iff_eq] using hr⟩⟩
    | env => simp only [Val.asSimple?, Simple.asPure?, reduceCtorEq] at h
  | read | binop | unop | ternary | readMem | len | mlen | modular | hash =>
    simp only [Val.asSimple?, reduceCtorEq] at h

theorem Facts.holds_set {Γ : Ctx} {p : PrimTy} {F : Facts C Γ} {σ : State C Γ}
    (hF : F.Holds σ) (i : Idx Γ (.val p)) (r : Val C Γ p) (v : p.Denote)
    (hv : r.evalT σ = .ok v) :
    (F.set i r.asSimple?).Holds (σ.setLocal i v) := by
  intro q j s hs
  simp only [Facts.set] at hs
  by_cases hji : j.toNat = i.toNat
  · obtain ⟨e, hje⟩ := Idx.eq_of_toNat i j hji
    subst e
    subst j
    simp only [ite_true] at hs
    cases hr : r.asSimple? with
    | none => simp only [hr, reduceCtorEq] at hs
    | some t =>
      simp only [hr, dite_true, Option.some.injEq] at hs
      subst hs
      obtain ⟨ev, hloc⟩ := Val.asSimple?_evalT hr σ
      have htv : t.evalT σ = v := by rw [hv] at ev; exact (Except.ok.inj ev).symm
      show TEnv.get i (TEnv.set i v σ.env) = t.evalT (σ.setLocal i v)
      rw [get_set]
      cases hrd : readsAt i.toNat t with
      | false => rw [evalT_setLocal_of_not_reads σ i v t hrd, htv]
      | true =>
        obtain ⟨k, rfl, hk⟩ := hloc _ hrd
        obtain ⟨e, hke⟩ := Idx.eq_of_toNat i k hk
        cases e
        subst k
        show v = TEnv.get i (TEnv.set i v σ.env)
        rw [get_set]
  · simp only [hji, ite_false] at hs
    cases hFj : F.get q j with
    | none => simp only [hFj, reduceCtorEq] at hs
    | some t =>
      simp only [hFj] at hs
      cases hrd : readsAt i.toNat t with
      | true => simp only [hrd, ite_true, reduceCtorEq] at hs
      | false =>
        simp only [hrd, Bool.false_eq_true, ite_false, Option.some.injEq] at hs
        subst hs
        show TEnv.get j (TEnv.set i v σ.env) = t.evalT (σ.setLocal i v)
        rw [get_set_ne i j v σ.env (Ne.symm hji), evalT_setLocal_of_not_reads σ i v t hrd]
        exact hF q j t hFj

theorem Facts.holds_push {Γ : Ctx} {p : PrimTy} {F : Facts C Γ} {σ : State C Γ}
    (hF : F.Holds σ) (s? : Option (Simple C Γ p)) (v : p.Denote)
    (hv : ∀ s, s? = some s → v = s.evalT σ) :
    (F.push s?).Holds (σ.push (t := .val p) v) := by
  intro q j s hs
  cases j with
  | here =>
    cases hs' : s? with
    | none => simp only [Facts.push, hs', Option.map, reduceCtorEq] at hs
    | some t =>
      simp only [Facts.push, hs', Option.map, Option.some.injEq] at hs
      subst hs
      rw [shiftS_evalT]
      exact hv t hs'
  | there j =>
    cases hFj : F.get q j with
    | none => simp only [Facts.push, hFj, Option.map, reduceCtorEq] at hs
    | some t =>
      simp only [Facts.push, hFj, Option.map, Option.some.injEq] at hs
      subst hs
      rw [shiftS_evalT]
      exact hF q j t hFj

/-! ## Substitution -/

/-- Replace each read of a local with a recorded fact by that fact. Reads
inside storage and memory paths are left as written. -/
def _root_.Solidity.Val.subst {Γ : Ctx} (F : Facts C Γ) : {p : PrimTy} → Val C Γ p → Val C Γ p
  | _, .simple (.local k) =>
    match F.get _ k with
    | some s => .simple s
    | none => .simple (.local k)
  | _, .simple s@(.lit ..) | _, .simple s@(.bool _) | _, .simple s@(.env ..) => .simple s
  | _, .binop op h hq a b => .binop op h hq (a.subst F) (b.subst F)
  | _, .unop op h hq a => .unop op h hq (a.subst F)
  | _, .ternary c a b => .ternary (c.subst F) (a.subst F) (b.subst F)
  | _, .modular op a b k => .modular op (a.subst F) (b.subst F) (k.subst F)
  | _, v@(.read _) | _, v@(.readMem _) | _, v@(.len ..) | _, v@(.mlen ..)
  | _, v@(.hash ..) => v

theorem _root_.Solidity.Val.subst_evalT {Γ : Ctx} {F : Facts C Γ} {σ : State C Γ} (hF : F.Holds σ) :
    {p : PrimTy} → (v : Val C Γ p) → (v.subst F).evalT σ = v.evalT σ
  | _, .simple (.local k) => by
    simp only [Val.subst]
    cases hk : F.get _ k with
    | none => rfl
    | some s => exact congrArg Except.ok (hF _ k s hk).symm
  | _, .simple (.lit ..) | _, .simple (.bool _) | _, .simple (.env ..) => by
    simp only [Val.subst]
  | _, .binop op h hq a b => by
    simp only [Val.subst, Val.evalT, Val.subst_evalT hF a, Val.subst_evalT hF b]
  | _, .unop op h hq a => by
    simp only [Val.subst, Val.evalT, Val.subst_evalT hF a]
  | _, .ternary c a b => by
    simp only [Val.subst, Val.evalT, Val.subst_evalT hF c, Val.subst_evalT hF a,
      Val.subst_evalT hF b]
  | _, .modular op a b k => by
    simp only [Val.subst, Val.evalT, Val.subst_evalT hF a, Val.subst_evalT hF b,
      Val.subst_evalT hF k]
  | _, .read _ | _, .readMem _ | _, .len .. | _, .mlen .. | _, .hash .. => rfl

/-- Propagate, then fold. -/
def _root_.Solidity.Val.opt {Γ : Ctx} {p : PrimTy} (F : Facts C Γ) (v : Val C Γ p) : Val C Γ p :=
  (v.subst F).cfold

theorem _root_.Solidity.Val.opt_evalT {Γ : Ctx} {F : Facts C Γ} {σ : State C Γ} (hF : F.Holds σ)
    {p : PrimTy} (v : Val C Γ p) : (v.opt F).evalT σ = v.evalT σ := by
  rw [Val.opt, Val.cfold_evalT, Val.subst_evalT hF]

/-! ## Statements that keep the locals -/

/-- A step that leaves every value-typed local and every environment value as it was. -/
def KeepsLocals {Γ : Ctx} (f : TStep C Γ Γ) : Prop :=
  ∀ σ o, f σ = .ok o →
    (∀ (q : PrimTy) (k : Idx Γ (.val q)), TEnv.get k o.st.env = TEnv.get k σ.env) ∧
      ∀ key, o.st.envVal key = σ.envVal key

theorem Facts.holds_keep {Γ : Ctx} {F : Facts C Γ} {f : TStep C Γ Γ} (hk : KeepsLocals f)
    {σ : State C Γ} (hF : F.Holds σ) {o : Out C σ.H Γ} (ho : f σ = .ok o) : F.Holds o.st := by
  obtain ⟨hl, he⟩ := hk σ o ho
  intro q j s hs
  rw [hl q j, hF q j s hs]
  cases s with
  | lit => rfl
  | bool => rfl
  | «local» k => exact (hl _ k).symm
  | env key hp => cases hp; exact (he key).symm

theorem keeps_assign {Γ : Ctx} {T : Ty} (l : Loc C Γ T) (r : Src C Γ T) :
    KeepsLocals (TRun.assign l r) := by
  intro σ o ho
  simp only [TRun.assign, bind, Except.bind, pure, Except.pure] at ho
  repeat' split at ho
  all_goals first
    | exact absurd ho (by simp only [reduceCtorEq, not_false_eq_true])
    | (cases ho; exact ⟨fun _ _ => rfl, fun _ => rfl⟩)

theorem keeps_delete {Γ : Ctx} {T : Ty} (l : Loc C Γ T) : KeepsLocals (TRun.delete l) := by
  intro σ o ho
  simp only [TRun.delete, bind, Except.bind, pure, Except.pure] at ho
  repeat' split at ho
  all_goals first
    | exact absurd ho (by simp only [reduceCtorEq, not_false_eq_true])
    | (cases ho; exact ⟨fun _ _ => rfl, fun _ => rfl⟩)

theorem keeps_pop {Γ : Ctx} {E : Ty} (b : SPath C Γ (.array E)) : KeepsLocals (TRun.pop b) := by
  intro σ o ho
  simp only [TRun.pop, bind, Except.bind, pure, Except.pure] at ho
  repeat' split at ho
  all_goals first
    | exact absurd ho (by simp only [reduceCtorEq, not_false_eq_true])
    | (cases ho; exact ⟨fun _ _ => rfl, fun _ => rfl⟩)

/-- Propagate into a storage source's value. -/
def _root_.Solidity.Src.opt {Γ : Ctx} (F : Facts C Γ) : {T : Ty} → Src C Γ T → Src C Γ T
  | _, .val v => .val (v.opt F)
  | _, s@(.copy ..) | _, s@(.fixedCopy ..) | _, s@(.copyMem ..) | _, s@(.fixedCopyMem ..) => s

theorem _root_.Solidity.Src.opt_valueT {Γ : Ctx} {F : Facts C Γ} {σ : State C Γ}
    (hF : F.Holds σ) : {T : Ty} → (r : Src C Γ T) → (r.opt F).valueT σ = r.valueT σ
  | _, .val v => by simp only [Src.opt, Src.valueT, Val.opt_evalT hF]
  | _, .copy .. | _, .fixedCopy .. | _, .copyMem .. | _, .fixedCopyMem .. => rfl

/-! ## The pass -/

mutual
/-- Propagate through one statement: the rewritten statement and the facts
after it. -/
def Stmt.cprop : {Γ Γ' : Ctx} → Facts C Γ → Stmt C Γ Γ' → Stmt C Γ Γ' × Facts C Γ'
  | _, _, F, .assignLocal i r =>
    let r' := r.opt F
    (.assignLocal i r', F.set i r'.asSimple?)
  | _, _, F, .declLocal p x init =>
    let init' := init.map (Val.opt F)
    (.declLocal p x init', F.push (init'.bind Val.asSimple?))
  | _, _, F, .require c => (.require (c.opt F), F)
  | _, _, F, .assert c => (.assert (c.opt F), F)
  | _, _, F, .ite c thn els =>
    (.ite (c.opt F) (Prog.cprop F thn) (Prog.cprop F els), Facts.empty)
  | _, _, F, .block body => (.block (Prog.cprop F body), Facts.empty)
  | _, _, _, .loop a c body => (.loop a c.cfold (Prog.cprop Facts.empty body), Facts.empty)
  | _, _, F, .assign l r => (.assign l (r.opt F), F)
  | _, _, F, .delete l => (.delete l, F)
  | _, _, F, .pop b => (.pop b, F)
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
    (s, Facts.empty)

/-- Propagate through a sequence. -/
def Prog.cprop : {Γ Γ' : Ctx} → Facts C Γ → Prog C Γ Γ' → Prog C Γ Γ'
  | _, _, _, .nil => .nil
  | _, _, F, .cons s P =>
    let r := Stmt.cprop F s
    .cons r.1 (Prog.cprop r.2 P)
end

/-! ## Preservation -/

mutual
/-- A statement's rewrite runs as it does where the entry facts hold, and
the exit facts hold in each state it leaves. -/
theorem Stmt.cprop_runC : {Γ Γ' : Ctx} → (F : Facts C Γ) → (s : Stmt C Γ Γ') →
    (σ : State C Γ) → F.Holds σ →
      Stmt.runC (Stmt.cprop F s).1 σ = Stmt.runC s σ ∧
      ∀ o, Stmt.runC s σ = .ok o → (Stmt.cprop F s).2.Holds o.st
  | _, _, F, .assignLocal i r, σ, hF => by
    refine ⟨?_, ?_⟩
    · simp only [Stmt.cprop, Stmt.runC, TRun.assignLocal, Val.opt_evalT hF]
    · intro o ho
      simp only [Stmt.runC, TRun.assignLocal, bind, Except.bind] at ho
      cases hr : r.evalT σ with
      | error e => simp only [hr, reduceCtorEq] at ho
      | ok v =>
        simp only [hr, pure, Except.pure, Except.ok.injEq] at ho
        subst ho
        exact Facts.holds_set hF i (r.opt F) v (by rw [Val.opt_evalT hF, hr])
  | _, _, F, .declLocal p x init, σ, hF => by
    have hinit : ∀ σ' : State C _, F.Holds σ' →
        TRun.declLocal p (init.map (Val.opt F)) σ' = TRun.declLocal p init σ' := by
      intro σ' hF'
      cases init <;> simp only [TRun.declLocal, Option.map, Val.opt_evalT hF']
    refine ⟨hinit σ hF, ?_⟩
    intro o ho
    simp only [Stmt.cprop]
    cases init with
    | none =>
      simp only [Stmt.runC, TRun.declLocal, pure, Except.pure, bind, Except.bind,
        Except.ok.injEq] at ho
      subst ho
      exact Facts.holds_push hF _ _ (fun _ h => nomatch h)
    | some e =>
      simp only [Stmt.runC, TRun.declLocal, bind, Except.bind] at ho
      cases he : e.evalT σ with
      | error err => simp only [he, reduceCtorEq] at ho
      | ok v =>
        simp only [he, pure, Except.pure, Except.ok.injEq] at ho
        subst ho
        refine Facts.holds_push hF _ v fun s hs => ?_
        simp only [Option.map, Option.bind] at hs
        have ev := (Val.asSimple?_evalT hs σ).1
        rw [Val.opt_evalT hF, he] at ev
        exact Except.ok.inj ev
  | _, _, F, .require c, σ, hF => by
    refine ⟨?_, ?_⟩
    · simp only [Stmt.cprop, Stmt.runC, TRun.require, Val.opt_evalT hF]
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
    · simp only [Stmt.cprop, Stmt.runC, TRun.assert, Val.opt_evalT hF]
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
    refine ⟨?_, fun _ _ => Facts.holds_empty _⟩
    simp only [Stmt.cprop, Stmt.runC, TRun.ite, Val.opt_evalT hF,
      (Prog.cprop_runC F thn σ hF), (Prog.cprop_runC F els σ hF)]
    rw [Subsingleton.elim (Prog.cprop F thn).ext thn.ext,
      Subsingleton.elim (Prog.cprop F els).ext els.ext]
  | _, _, F, .block body, σ, hF => by
    refine ⟨?_, fun _ _ => Facts.holds_empty _⟩
    simp only [Stmt.cprop, Stmt.runC, TRun.block, (Prog.cprop_runC F body σ hF)]
    rw [Subsingleton.elim (Prog.cprop F body).ext body.ext]
  | _, _, _, .loop a c body, σ, _ => by
    refine ⟨?_, fun _ _ => Facts.holds_empty _⟩
    have hb : Prog.runC (Prog.cprop Facts.empty body) = Prog.runC body :=
      funext fun τ => Prog.cprop_runC Facts.empty body τ (Facts.holds_empty τ)
    simp only [Stmt.cprop, Stmt.runC]
    rw [hb, TRun.loop_congr (Val.cfold_evalT · c) body.ext]
  | _, _, F, .assign l r, σ, hF =>
    ⟨by simp only [Stmt.cprop, Stmt.runC, TRun.assign, Src.opt_valueT hF],
      fun _ ho => Facts.holds_keep (keeps_assign l r) hF ho⟩
  | _, _, F, .delete l, σ, hF => ⟨rfl, fun _ ho => Facts.holds_keep (keeps_delete l) hF ho⟩
  | _, _, F, .pop b, σ, hF => ⟨rfl, fun _ ho => Facts.holds_keep (keeps_pop b) hF ho⟩
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
    ⟨rfl, fun _ _ => Facts.holds_empty _⟩

/-- A sequence's rewrite runs as it does where the entry facts hold. -/
theorem Prog.cprop_runC : {Γ Γ' : Ctx} → (F : Facts C Γ) → (P : Prog C Γ Γ') →
    (σ : State C Γ) → F.Holds σ → Prog.runC (Prog.cprop F P) σ = Prog.runC P σ
  | _, _, _, .nil, _, _ => rfl
  | _, _, F, .cons s P, σ, hF => by
    obtain ⟨hrun, hout⟩ := Stmt.cprop_runC F s σ hF
    simp only [Prog.cprop, Prog.runC, TRun.seq, hrun]
    cases ho : Stmt.runC s σ with
    | error e => rfl
    | ok o =>
      dsimp only
      rw [Prog.cprop_runC _ P o.st (hout o ho)]
end

/-- **Propagation with no entry facts preserves the typed run.** -/
theorem Prog.cprop_empty_runC {Γ Γ' : Ctx} (P : Prog C Γ Γ') :
    Prog.runC (Prog.cprop Facts.empty P) = Prog.runC P :=
  funext fun σ => Prog.cprop_runC Facts.empty P σ (Facts.holds_empty σ)

theorem cprop_preserves (Γ Γ' : Ctx) :
    Preserves (SameRun (C := C) (Γ := Γ) (Γ' := Γ'))
      (Prog.cprop Facts.empty : Lowering.Pass C Γ Γ') :=
  fun P => (Prog.cprop_empty_runC P).symm

end Solidity.Optimizer.ConstFold
