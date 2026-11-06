import Solidity.Optimizer.StmtFold
import Solidity.Semantics.RunWk

/-!
# O02 unused-variable elimination over lowering programs

`T x = e; P` at the head of a block, where `P` never reads `x` and `e` cannot
fail, is the block `P` without the declaration. "Never reads `x`" is decided
by strengthening: `Prog.str? (.drop .refl) P` returns a program `P'` over the
context without `x` whose weakening is exactly `P` (`Prog.str?_wk`). The run
of the declaration-and-`P` is then the run of `P'` with one more local kept
alongside (`Prog.run_wk`, the existing weakening lemma of the typed run), and
the block's end pops it, so both blocks run alike (`blockDecl_runC`).

The initialiser must not fail (none, or a simple value: literal, local or
environment read), since dropping a failing initialiser would hide its halt.
Strengthening covers local assignments and declarations, `require`, `assert`,
`revert`, `assume(false)`, `transfer`, conditionals and blocks over value
expressions without storage or memory paths; a body using any other form is
left as written. Only an explicit `{ … }` block's first statement is a
candidate (not `if` branches, loop bodies, call bodies or the top level); one
declaration is removed per block per run of the pass.
-/
namespace Solidity.Optimizer.ConstFold
open Solidity

variable {C : Contract}

/-! ## Strengthening -/

/-- The index a weakening sent to `j`, if `j` is one it keeps. -/
def Idx.str? : {Γ Δ : Ctx} → {t : LTy} → Thin Γ Δ → Idx Δ t → Option (Idx Γ t)
  | _, _, _, .refl, j => some j
  | _, _, _, .keep _, .here => some .here
  | _, _, _, .keep h, .there j => (Idx.str? h j).map .there
  | _, _, _, .drop _, .here => none
  | _, _, _, .drop h, .there j => Idx.str? h j

theorem Idx.str?_wk : {Γ Δ : Ctx} → {t : LTy} → (h : Thin Γ Δ) → (j : Idx Δ t) →
    (i : Idx Γ t) → Idx.str? h j = some i → i.wk h = j
  | _, _, _, .refl, j, i, e => by
    simp only [Idx.str?, Option.some.injEq] at e
    subst e
    exact Idx.wk_refl _
  | _, _, _, .keep _, .here, i, e => by
    simp only [Idx.str?, Option.some.injEq] at e
    subst e
    rfl
  | _, _, _, .keep h, .there j, i, e => by
    simp only [Idx.str?] at e
    cases hj : Idx.str? h j with
    | none => simp only [hj, Option.map_none, reduceCtorEq] at e
    | some i' =>
      simp only [hj, Option.map_some, Option.some.injEq] at e
      subst e
      exact congrArg Idx.there (Idx.str?_wk h j i' hj)
  | _, _, _, .drop _, .here, _, e => by simp only [Idx.str?, reduceCtorEq] at e
  | _, _, _, .drop h, .there j, i, e => congrArg Idx.there (Idx.str?_wk h j i e)

def Simple.str? {Γ Δ : Ctx} (h : Thin Γ Δ) : {p : PrimTy} → Simple C Δ p → Option (Simple C Γ p)
  | _, .lit n hn => some (.lit n hn)
  | _, .bool b => some (.bool b)
  | _, .local i => (Idx.str? h i).map .local
  | _, .env k hp => some (.env k hp)

theorem Simple.str?_wk {Γ Δ : Ctx} (h : Thin Γ Δ) : {p : PrimTy} → (s : Simple C Δ p) →
    (t : Simple C Γ p) → Simple.str? h s = some t → t.wk h = s
  | _, .lit .., t, e | _, .bool _, t, e | _, .env .., t, e => by
    simp only [Simple.str?, Option.some.injEq] at e
    subst e
    rfl
  | _, .local i, t, e => by
    simp only [Simple.str?] at e
    cases hi : Idx.str? h i with
    | none => simp only [hi, Option.map_none, reduceCtorEq] at e
    | some i' =>
      simp only [hi, Option.map_some, Option.some.injEq] at e
      subst e
      exact congrArg Simple.local (Idx.str?_wk h i i' hi)

/-- Strengthen a value expression without storage or memory paths. -/
def Val.str? {Γ Δ : Ctx} (h : Thin Γ Δ) : {p : PrimTy} → Val C Δ p → Option (Val C Γ p)
  | _, .simple s => (Simple.str? h s).map .simple
  | _, .binop op ha hq a b =>
    match Val.str? h a, Val.str? h b with
    | some a', some b' => some (.binop op ha hq a' b')
    | _, _ => none
  | _, .unop op ha hq a => (Val.str? h a).map (.unop op ha hq)
  | _, .ternary c a b =>
    match Val.str? h c, Val.str? h a, Val.str? h b with
    | some c', some a', some b' => some (.ternary c' a' b')
    | _, _, _ => none
  | _, .modular op a b k =>
    match Val.str? h a, Val.str? h b, Val.str? h k with
    | some a', some b', some k' => some (.modular op a' b' k')
    | _, _, _ => none
  | _, .read _ | _, .readMem _ | _, .len .. | _, .mlen .. | _, .hash .. => none

theorem Val.str?_wk {Γ Δ : Ctx} (h : Thin Γ Δ) : {p : PrimTy} → (v : Val C Δ p) →
    (w : Val C Γ p) → Val.str? h v = some w → w.wk h = v
  | _, .simple s, w, e => by
    simp only [Val.str?] at e
    cases hs : Simple.str? h s with
    | none => simp only [hs, Option.map_none, reduceCtorEq] at e
    | some t =>
      simp only [hs, Option.map_some, Option.some.injEq] at e
      subst e
      exact congrArg Val.simple (Simple.str?_wk h s t hs)
  | _, .binop op ha hq a b, w, e => by
    simp only [Val.str?] at e
    cases h1 : Val.str? h a <;> cases h2 : Val.str? h b <;>
      simp only [h1, h2, reduceCtorEq, Option.some.injEq] at e
    subst e
    simp only [Val.wk, Val.str?_wk h a _ h1, Val.str?_wk h b _ h2]
  | _, .unop op ha hq a, w, e => by
    simp only [Val.str?] at e
    cases h1 : Val.str? h a with
    | none => simp only [h1, Option.map_none, reduceCtorEq] at e
    | some a' =>
      simp only [h1, Option.map_some, Option.some.injEq] at e
      subst e
      simp only [Val.wk, Val.str?_wk h a _ h1]
  | _, .ternary c a b, w, e => by
    simp only [Val.str?] at e
    cases h0 : Val.str? h c <;> cases h1 : Val.str? h a <;> cases h2 : Val.str? h b <;>
      simp only [h0, h1, h2, reduceCtorEq, Option.some.injEq] at e
    subst e
    simp only [Val.wk, Val.str?_wk h c _ h0, Val.str?_wk h a _ h1, Val.str?_wk h b _ h2]
  | _, .modular op a b k, w, e => by
    simp only [Val.str?] at e
    cases h0 : Val.str? h a <;> cases h1 : Val.str? h b <;> cases h2 : Val.str? h k <;>
      simp only [h0, h1, h2, reduceCtorEq, Option.some.injEq] at e
    subst e
    simp only [Val.wk, Val.str?_wk h a _ h0, Val.str?_wk h b _ h1, Val.str?_wk h k _ h2]
  | _, .read _, _, e | _, .readMem _, _, e | _, .len .., _, e | _, .mlen .., _, e
  | _, .hash .., _, e => by simp only [Val.str?, reduceCtorEq] at e

/-- A strengthened program: its context, the thinning to the original's, and it. -/
abbrev Str (C : Contract) (Γ Δ' : Ctx) := (Γ' : Ctx) × Thin Γ' Δ' × Prog C Γ Γ'

mutual
/-- Strengthen a statement of the covered fragment. -/
def Stmt.str? {Γ Δ : Ctx} (h : Thin Γ Δ) : {Δ' : Ctx} → Stmt C Δ Δ' →
    Option ((Γ' : Ctx) × Thin Γ' Δ' × Stmt C Γ Γ')
  | _, .assignLocal i r =>
    match Idx.str? h i, Val.str? h r with
    | some i', some r' => some ⟨_, h, .assignLocal i' r'⟩
    | _, _ => none
  | _, .declLocal p x none => some ⟨_, .keep h, .declLocal p x none⟩
  | _, .declLocal p x (some e) =>
    (Val.str? h e).map fun e' => ⟨_, .keep h, .declLocal p x (some e')⟩
  | _, .require c => (Val.str? h c).map fun c' => ⟨_, h, .require c'⟩
  | _, .assert c => (Val.str? h c).map fun c' => ⟨_, h, .assert c'⟩
  | _, .revert => some ⟨_, h, .revert⟩
  | _, .assumeFalse => some ⟨_, h, .assumeFalse⟩
  | _, .transfer r a =>
    match Val.str? h r, Val.str? h a with
    | some r', some a' => some ⟨_, h, .transfer r' a'⟩
    | _, _ => none
  | _, .ite c thn els =>
    match Val.str? h c, Prog.str? h thn, Prog.str? h els with
    | some c', some ⟨_, _, thn'⟩, some ⟨_, _, els'⟩ => some ⟨_, h, .ite c' thn' els'⟩
    | _, _, _ => none
  | _, .block body =>
    match Prog.str? h body with
    | some ⟨_, _, body'⟩ => some ⟨_, h, .block body'⟩
    | none => none
  | _, .assign .. | _, .rebind .. | _, .declStorage .. | _, .opAssign .. | _, .incDec ..
  | _, .assignIncDec .. | _, .assignLocalPush .. | _, .push .. | _, .pop .. | _, .send ..
  | _, .declMem .. | _, .rebindMem .. | _, .assignFromMem .. | _, .assignMem .. | _, .delete ..
  | _, .deleteMem .. | _, .assignNew .. | _, .call .. | _, .tryCall .. | _, .loop ..
  | _, .pushOpAssign .. | _, .pushIncDec .. | _, .callReceiver .. | _, .callReceiverPush ..
  | _, .callRec .. | _, .revertData .. | _, .catchData .. => none

/-- Strengthen a sequence of the covered fragment. -/
def Prog.str? {Γ Δ : Ctx} (h : Thin Γ Δ) : {Δ' : Ctx} → Prog C Δ Δ' → Option (Str C Γ Δ')
  | _, .nil => some ⟨_, h, .nil⟩
  | _, .cons s P =>
    match Stmt.str? h s with
    | some ⟨_, h₁, s'⟩ =>
      match Prog.str? h₁ P with
      | some ⟨_, h₂, P'⟩ => some ⟨_, h₂, .cons s' P'⟩
      | none => none
    | none => none
end

mutual
theorem Stmt.str?_wk {Γ Δ : Ctx} (h : Thin Γ Δ) : {Δ' : Ctx} → (s : Stmt C Δ Δ') →
    (r : (Γ' : Ctx) × Thin Γ' Δ' × Stmt C Γ Γ') → Stmt.str? h s = some r →
      r.2.2.wk h = ⟨Δ', r.2.1, s⟩
  | _, .assignLocal i r, w, e => by
    simp only [Stmt.str?] at e
    cases h1 : Idx.str? h i <;> cases h2 : Val.str? h r <;>
      simp only [h1, h2, reduceCtorEq, Option.some.injEq] at e
    subst e
    simp only [Stmt.wk, Idx.str?_wk h i _ h1, Val.str?_wk h r _ h2]
  | _, .declLocal p x none, w, e => by
    simp only [Stmt.str?, Option.some.injEq] at e
    subst e
    rfl
  | _, .declLocal p x (some v), w, e => by
    simp only [Stmt.str?] at e
    cases h1 : Val.str? h v with
    | none => simp only [h1, Option.map_none, reduceCtorEq] at e
    | some v' =>
      simp only [h1, Option.map_some, Option.some.injEq] at e
      subst e
      simp only [Stmt.wk, Option.map, Val.str?_wk h v _ h1]
  | _, .require c, w, e => by
    simp only [Stmt.str?] at e
    cases h1 : Val.str? h c with
    | none => simp only [h1, Option.map_none, reduceCtorEq] at e
    | some c' =>
      simp only [h1, Option.map_some, Option.some.injEq] at e
      subst e
      simp only [Stmt.wk, Val.str?_wk h c _ h1]
  | _, .assert c, w, e => by
    simp only [Stmt.str?] at e
    cases h1 : Val.str? h c with
    | none => simp only [h1, Option.map_none, reduceCtorEq] at e
    | some c' =>
      simp only [h1, Option.map_some, Option.some.injEq] at e
      subst e
      simp only [Stmt.wk, Val.str?_wk h c _ h1]
  | _, .revert, w, e | _, .assumeFalse, w, e => by
    simp only [Stmt.str?, Option.some.injEq] at e
    subst e
    rfl
  | _, .transfer r a, w, e => by
    simp only [Stmt.str?] at e
    cases h1 : Val.str? h r <;> cases h2 : Val.str? h a <;>
      simp only [h1, h2, reduceCtorEq, Option.some.injEq] at e
    subst e
    simp only [Stmt.wk, Val.str?_wk h r _ h1, Val.str?_wk h a _ h2]
  | _, .ite c thn els, w, e => by
    simp only [Stmt.str?] at e
    cases h0 : Val.str? h c with
    | none => simp only [h0, reduceCtorEq] at e
    | some c' =>
      cases h1 : Prog.str? h thn with
      | none => simp only [h0, h1, reduceCtorEq] at e
      | some t =>
        cases h2 : Prog.str? h els with
        | none => simp only [h0, h1, h2, reduceCtorEq] at e
        | some f =>
          obtain ⟨_, _, thn'⟩ := t
          obtain ⟨_, _, els'⟩ := f
          simp only [h0, h1, h2, Option.some.injEq] at e
          subst e
          have e1 := Prog.str?_wk h thn _ h1
          have e2 := Prog.str?_wk h els _ h2
          simp only at e1 e2
          simp only [Stmt.wk, Val.str?_wk h c _ h0]
          rw [e1, e2]
  | _, .block body, w, e => by
    simp only [Stmt.str?] at e
    cases h1 : Prog.str? h body with
    | none => simp only [h1, reduceCtorEq] at e
    | some t =>
      obtain ⟨_, _, body'⟩ := t
      simp only [h1, Option.some.injEq] at e
      subst e
      have e1 := Prog.str?_wk h body _ h1
      simp only at e1
      simp only [Stmt.wk]
      rw [e1]
  | _, .assign .., _, e | _, .rebind .., _, e | _, .declStorage .., _, e
  | _, .opAssign .., _, e | _, .incDec .., _, e | _, .assignIncDec .., _, e
  | _, .assignLocalPush .., _, e | _, .push .., _, e | _, .pop .., _, e | _, .send .., _, e
  | _, .declMem .., _, e | _, .rebindMem .., _, e | _, .assignFromMem .., _, e
  | _, .assignMem .., _, e | _, .delete .., _, e | _, .deleteMem .., _, e
  | _, .assignNew .., _, e | _, .call .., _, e | _, .tryCall .., _, e | _, .loop .., _, e
  | _, .pushOpAssign .., _, e | _, .pushIncDec .., _, e | _, .callReceiver .., _, e
  | _, .callReceiverPush .., _, e | _, .callRec .., _, e | _, .revertData .., _, e
  | _, .catchData .., _, e => by simp only [Stmt.str?, reduceCtorEq] at e

theorem Prog.str?_wk {Γ Δ : Ctx} (h : Thin Γ Δ) : {Δ' : Ctx} → (P : Prog C Δ Δ') →
    (r : Str C Γ Δ') → Prog.str? h P = some r → r.2.2.wk h = ⟨Δ', r.2.1, P⟩
  | _, .nil, w, e => by
    simp only [Prog.str?, Option.some.injEq] at e
    subst e
    rfl
  | _, .cons s P, w, e => by
    simp only [Prog.str?] at e
    cases h1 : Stmt.str? h s with
    | none => simp only [h1, reduceCtorEq] at e
    | some t =>
      obtain ⟨_, h₁, s'⟩ := t
      cases h2 : Prog.str? h₁ P with
      | none => simp only [h1, h2, reduceCtorEq] at e
      | some u =>
        obtain ⟨_, h₂, P'⟩ := u
        simp only [h1, h2, Option.some.injEq] at e
        subst e
        have hs := Stmt.str?_wk h s _ h1
        have hP := Prog.str?_wk h₁ P _ h2
        simp only at hs hP
        simp only [Prog.wk]
        rw [hs]
        simp only
        rw [hP]
end

/-! ## Dropping an unused declaration -/

section Drop
variable {Γ : Ctx}

/-- An expression whose evaluation cannot fail. -/
def Val.isSimple {p : PrimTy} : Val C Γ p → Bool
  | .simple _ => true
  | .read _ | .binop .. | .unop .. | .ternary .. | .readMem _ | .len .. | .mlen .. | .modular ..
  | .hash .. => false

/-- A declaration's initialiser that cannot fail. -/
def initSafe {p : PrimTy} : Option (Val C Γ p) → Bool
  | none => true
  | some v => Val.isSimple v

theorem declLocal_ok {p : PrimTy} (init : Option (Val C Γ p)) (hi : initSafe init = true)
    (σ : State C Γ) : ∃ v, TRun.declLocal p init σ = .ok ⟨σ.push v, List.prefix_refl _⟩ := by
  cases init with
  | none => exact ⟨_, rfl⟩
  | some e =>
    cases e with
    | simple s => exact ⟨_, rfl⟩
    | read | binop | unop | ternary | readMem | len | mlen | modular | hash =>
      simp only [initSafe, Val.isSimple, Bool.false_eq_true] at hi

private theorem drop_trans {H : HTy} {Γ Δ : Ctx} (a : Ext Γ Δ) : {Ε : Ctx} → (b : Ext Δ Ε) →
    (e : TEnv C H Ε) → TEnv.drop (a.trans b) e = TEnv.drop a (TEnv.drop b e)
  | _, .refl, _ => rfl
  | _, .push b, e => drop_trans a b e.2

/-- A weakening by one dropped local, its scope ended, is the original outcome. -/
theorem TWkRel.pop {H : HTy} {t : LTy} {o : List ((u : LTy) × u.TDenote C H)}
    {Y : TRes (Out C H Γ)} {Z : TRes (Out C H (t :: Γ))}
    (hr : TWkRel (.drop .refl) o Y Z) : Z.map (Out.drop (.push .refl)) = Y := by
  cases Y with
  | error e => cases Z with
    | error e' =>
      have : e = e' := hr
      subst this
      rfl
    | ok => exact False.elim hr
  | ok a => cases Z with
    | error => exact False.elim hr
    | ok b =>
      obtain ⟨d, _, rfl⟩ := hr
      rfl

/-- **A block whose first declaration is unused runs as the block without it.** -/
theorem blockDecl_runC {Γ₁ Γ' : Ctx} {p : PrimTy} (x : Var) (init : Option (Val C Γ p))
    (hi : initSafe init = true) (P : Prog C (.val p :: Γ) Γ₁) (P' : Prog C Γ Γ')
    (h' : Thin Γ' Γ₁) (hw : P'.wk (.drop .refl) = ⟨Γ₁, h', P⟩) :
    Stmt.runC (.block P') = Stmt.runC (.block (.cons (.declLocal p x init) P)) := by
  funext σ
  obtain ⟨v, hv⟩ := declLocal_ok init hi σ
  have hd := TWkRel.drop (Prog.wk_over P' (.drop .refl))
    (Prog.run_wk P' (.drop .refl) σ ((v, σ.env) : TEnv C σ.H (.val p :: Γ)))
  rw [hw] at hd
  have hpop := TWkRel.pop hd
  simp only [Prog.run, Prog.runR_eq] at hpop
  change Except.map (Out.drop (.push .refl)) (Except.map (Out.drop P.ext) (P.runC (σ.push v))) =
    Except.map (Out.drop P'.ext) (P'.runC σ) at hpop
  change Except.map (Out.drop P'.ext) (P'.runC σ) = _
  rw [← hpop]
  simp only [Stmt.runC, TRun.block, Prog.runC, TRun.seq, hv]
  cases Prog.runC P (σ.push v) with
  | error e => rfl
  | ok o =>
    show Except.ok _ = Except.ok _
    congr 1
    show (⟨(o.st.drop P.ext).drop (.push .refl), o.ext⟩ : Out C σ.H Γ) =
      ⟨o.st.drop ((Stmt.declLocal p x init).ext.trans P.ext), _⟩
    rw [Subsingleton.elim ((Stmt.declLocal p x init).ext.trans P.ext)
      ((Ext.push .refl).trans P.ext)]
    simp only [State.drop, drop_trans]

end Drop

/-! ## The pass -/

/-- A block of `s; P`, without `s` when it is an unused safe declaration. -/
def blockCons : {Γ Γ₁ Γ₂ : Ctx} → Stmt C Γ Γ₁ → Prog C Γ₁ Γ₂ → Stmt C Γ Γ
  | _, _, _, .declLocal p x init, P =>
    if initSafe init then
      match Prog.str? (.drop .refl) P with
      | some ⟨_, _, P'⟩ => .block P'
      | none => .block (.cons (.declLocal p x init) P)
    else .block (.cons (.declLocal p x init) P)
  | _, _, _, s@(.assign ..), P => .block (.cons s P)
  | _, _, _, s@(.rebind ..), P => .block (.cons s P)
  | _, _, _, s@(.assignLocal ..), P => .block (.cons s P)
  | _, _, _, s@(.declStorage ..), P => .block (.cons s P)
  | _, _, _, s@(.opAssign ..), P => .block (.cons s P)
  | _, _, _, s@(.incDec ..), P => .block (.cons s P)
  | _, _, _, s@(.assignIncDec ..), P => .block (.cons s P)
  | _, _, _, s@(.assignLocalPush ..), P => .block (.cons s P)
  | _, _, _, s@(.push ..), P => .block (.cons s P)
  | _, _, _, s@(.pop ..), P => .block (.cons s P)
  | _, _, _, s@(.transfer ..), P => .block (.cons s P)
  | _, _, _, s@(.send ..), P => .block (.cons s P)
  | _, _, _, s@(.declMem ..), P => .block (.cons s P)
  | _, _, _, s@(.rebindMem ..), P => .block (.cons s P)
  | _, _, _, s@(.assignFromMem ..), P => .block (.cons s P)
  | _, _, _, s@(.assignMem ..), P => .block (.cons s P)
  | _, _, _, s@(.delete ..), P => .block (.cons s P)
  | _, _, _, s@(.deleteMem ..), P => .block (.cons s P)
  | _, _, _, s@(.assignNew ..), P => .block (.cons s P)
  | _, _, _, s@(.ite ..), P => .block (.cons s P)
  | _, _, _, s@(.require ..), P => .block (.cons s P)
  | _, _, _, s@(.assert ..), P => .block (.cons s P)
  | _, _, _, s@(.revert), P => .block (.cons s P)
  | _, _, _, s@(.assumeFalse), P => .block (.cons s P)
  | _, _, _, s@(.call ..), P => .block (.cons s P)
  | _, _, _, s@(.tryCall ..), P => .block (.cons s P)
  | _, _, _, s@(.loop ..), P => .block (.cons s P)
  | _, _, _, s@(.block ..), P => .block (.cons s P)
  | _, _, _, s@(.pushOpAssign ..), P => .block (.cons s P)
  | _, _, _, s@(.pushIncDec ..), P => .block (.cons s P)
  | _, _, _, s@(.callReceiver ..), P => .block (.cons s P)
  | _, _, _, s@(.callReceiverPush ..), P => .block (.cons s P)
  | _, _, _, s@(.callRec ..), P => .block (.cons s P)
  | _, _, _, s@(.revertData ..), P => .block (.cons s P)
  | _, _, _, s@(.catchData ..), P => .block (.cons s P)

/-- A block, its first declaration dropped when unused. -/
def blockUve {Γ Γ₁ : Ctx} : Prog C Γ Γ₁ → Stmt C Γ Γ
  | .nil => .block .nil
  | .cons s P => blockCons s P

theorem blockCons_runC : {Γ Γ₁ Γ₂ : Ctx} → (s : Stmt C Γ Γ₁) → (P : Prog C Γ₁ Γ₂) →
    Stmt.runC (blockCons s P) = Stmt.runC (.block (.cons s P))
  | _, _, _, .declLocal p x init, P => by
    simp only [blockCons]
    split
    · next hi =>
      split
      · next Γ' h' P' hs => exact blockDecl_runC x init hi P P' h' (Prog.str?_wk _ P _ hs)
      · rfl
    · rfl
  | _, _, _, .assign .., _
  | _, _, _, .rebind .., _
  | _, _, _, .assignLocal .., _
  | _, _, _, .declStorage .., _
  | _, _, _, .opAssign .., _
  | _, _, _, .incDec .., _
  | _, _, _, .assignIncDec .., _
  | _, _, _, .assignLocalPush .., _
  | _, _, _, .push .., _
  | _, _, _, .pop .., _
  | _, _, _, .transfer .., _
  | _, _, _, .send .., _
  | _, _, _, .declMem .., _
  | _, _, _, .rebindMem .., _
  | _, _, _, .assignFromMem .., _
  | _, _, _, .assignMem .., _
  | _, _, _, .delete .., _
  | _, _, _, .deleteMem .., _
  | _, _, _, .assignNew .., _
  | _, _, _, .ite .., _
  | _, _, _, .require .., _
  | _, _, _, .assert .., _
  | _, _, _, .revert, _
  | _, _, _, .assumeFalse, _
  | _, _, _, .call .., _
  | _, _, _, .tryCall .., _
  | _, _, _, .loop .., _
  | _, _, _, .block .., _
  | _, _, _, .pushOpAssign .., _
  | _, _, _, .pushIncDec .., _
  | _, _, _, .callReceiver .., _
  | _, _, _, .callReceiverPush .., _
  | _, _, _, .callRec .., _
  | _, _, _, .revertData .., _
  | _, _, _, .catchData .., _ => rfl

theorem blockUve_runC {Γ Γ₁ : Ctx} (P : Prog C Γ Γ₁) :
    Stmt.runC (blockUve P) = Stmt.runC (.block P) := by
  cases P with
  | nil => rfl
  | cons s P => exact blockCons_runC s P

mutual
/-- Unused-variable elimination at the head of every explicit `{ … }` block of a
statement (not `if` branches, loop bodies or call bodies). -/
def Stmt.uve : {Γ Γ' : Ctx} → Stmt C Γ Γ' → Stmt C Γ Γ'
  | _, _, .ite c thn els => .ite c (Prog.uve thn) (Prog.uve els)
  | _, _, .block body => blockUve (Prog.uve body)
  | _, _, .loop a c body => .loop a c (Prog.uve body)
  | _, _, s@(.assign ..) => s
  | _, _, s@(.rebind ..) => s
  | _, _, s@(.assignLocal ..) => s
  | _, _, s@(.declLocal ..) => s
  | _, _, s@(.declStorage ..) => s
  | _, _, s@(.opAssign ..) => s
  | _, _, s@(.incDec ..) => s
  | _, _, s@(.assignIncDec ..) => s
  | _, _, s@(.assignLocalPush ..) => s
  | _, _, s@(.push ..) => s
  | _, _, s@(.pop ..) => s
  | _, _, s@(.transfer ..) => s
  | _, _, s@(.send ..) => s
  | _, _, s@(.declMem ..) => s
  | _, _, s@(.rebindMem ..) => s
  | _, _, s@(.assignFromMem ..) => s
  | _, _, s@(.assignMem ..) => s
  | _, _, s@(.delete ..) => s
  | _, _, s@(.deleteMem ..) => s
  | _, _, s@(.assignNew ..) => s
  | _, _, s@(.require ..) => s
  | _, _, s@(.assert ..) => s
  | _, _, s@(.revert) => s
  | _, _, s@(.assumeFalse) => s
  | _, _, s@(.call ..) => s
  | _, _, s@(.tryCall ..) => s
  | _, _, s@(.pushOpAssign ..) => s
  | _, _, s@(.pushIncDec ..) => s
  | _, _, s@(.callReceiver ..) => s
  | _, _, s@(.callReceiverPush ..) => s
  | _, _, s@(.callRec ..) => s
  | _, _, s@(.revertData ..) => s
  | _, _, s@(.catchData ..) => s

/-- Unused-variable elimination at the head of every explicit block of a sequence. -/
def Prog.uve : {Γ Γ' : Ctx} → Prog C Γ Γ' → Prog C Γ Γ'
  | _, _, .nil => .nil
  | _, _, .cons s P => .cons (Stmt.uve s) (Prog.uve P)
end

mutual
theorem Stmt.uve_runC : {Γ Γ' : Ctx} → (s : Stmt C Γ Γ') → Stmt.runC (Stmt.uve s) = Stmt.runC s
  | _, _, .ite c thn els => by
    simp only [Stmt.uve, Stmt.runC]
    rw [Prog.uve_runC thn, Prog.uve_runC els]
    exact TRun.ite_congr (fun _ => rfl) _ _ _ _ _ _
  | _, _, .block body => by
    simp only [Stmt.uve]
    rw [blockUve_runC]
    simp only [Stmt.runC]
    rw [Prog.uve_runC body]
    exact TRun.block_congr _ _ _
  | _, _, .loop a c body => by
    simp only [Stmt.uve, Stmt.runC]
    rw [Prog.uve_runC body]
    exact TRun.loop_congr (fun _ => rfl) _ _ _
  | _, _, .assign ..
  | _, _, .rebind ..
  | _, _, .assignLocal ..
  | _, _, .declLocal ..
  | _, _, .declStorage ..
  | _, _, .opAssign ..
  | _, _, .incDec ..
  | _, _, .assignIncDec ..
  | _, _, .assignLocalPush ..
  | _, _, .push ..
  | _, _, .pop ..
  | _, _, .transfer ..
  | _, _, .send ..
  | _, _, .declMem ..
  | _, _, .rebindMem ..
  | _, _, .assignFromMem ..
  | _, _, .assignMem ..
  | _, _, .delete ..
  | _, _, .deleteMem ..
  | _, _, .assignNew ..
  | _, _, .require ..
  | _, _, .assert ..
  | _, _, .revert
  | _, _, .assumeFalse
  | _, _, .call ..
  | _, _, .tryCall ..
  | _, _, .pushOpAssign ..
  | _, _, .pushIncDec ..
  | _, _, .callReceiver ..
  | _, _, .callReceiverPush ..
  | _, _, .callRec ..
  | _, _, .revertData ..
  | _, _, .catchData .. => rfl

theorem Prog.uve_runC : {Γ Γ' : Ctx} → (P : Prog C Γ Γ') → Prog.runC (Prog.uve P) = Prog.runC P
  | _, _, .nil => rfl
  | _, _, .cons s P => by
    simp only [Prog.uve, Prog.runC]
    rw [Stmt.uve_runC s, Prog.uve_runC P]
end

theorem uve_preserves (Γ Γ' : Ctx) :
    Preserves (SameRun (C := C) (Γ := Γ) (Γ' := Γ')) (Prog.uve : Lowering.Pass C Γ Γ') :=
  fun P => (Prog.uve_runC P).symm

end Solidity.Optimizer.ConstFold
