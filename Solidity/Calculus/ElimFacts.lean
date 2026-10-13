import Solidity.Calculus.Closer
import Solidity.Calculus.DecideEval

/-!
# The elimination under its premises

`LFml.elim` reads every storage term through the writes below it, the
readers of each write nesting the ones below (`Calculus/Decide.lean`).  A
leaf's premises often settle what those readers compare — a `require` on
an array's length makes the length a literal — and a reader that compares
two literals takes one branch (`keyCmp`).  `LFml.elimF` eliminates under
the premises it has passed: the equations an eliminated premise states
(`LFml.factsOf`: a side a literal, or `x == v` read `true`) rewrite every
word and every storage reading the elimination builds after it
(`ElimM.rwF`, by `Facts.rw`), so that the readers below compare what the
premises say.  A premise holds where what follows it is read, so the
rewrite keeps what the formula says (`LFml.elimF_holds`).
-/

namespace Solidity

namespace Decide

open Semantics

variable {C : Contract}

/-! ## Rewriting what the elimination builds -/

section Rw

/-- What the premises rewrite, at a sort: a word, and each reading of a
storage. -/
def ElimM.rwF (F : Facts C) : (s : Srt) → ElimM C s → ElimM C s
  | .val _, e => F.rw (e : LTm C (.val _))
  | .st, S => (⟨(S : SFun C).ok, fun c P => F.rw ((S : SFun C).rd c P), (S : SFun C).orig⟩ :
      SFun C)
  | _, e => e

/-- `LTm.elimF`'s compiled twin. -/
def LTm.elimFM (F : Facts C) : {s : Srt} → LTm C s → ElimM C s
  | _, .var k => ElimM.rwF F _ (.var k : LTm C (.val _))
  | s, .app0 o => ElimM.rwF F s o.elim
  | s, .app1 o x => ElimM.rwF F s (o.elim x (x.elimFM F))
  | s, .app2 o x y => ElimM.rwF F s (o.elim x y (x.elimFM F) (y.elimFM F))
  | s, .app3 o x y z => ElimM.rwF F s (o.elim x y z (x.elimFM F) (y.elimFM F) (z.elimFM F))
  | _, .index it q i => pathIdx it (q.elimFM F) (i.elimFM F)
  | _, .obsW q => ElimM.ofOrig _ (.obsW q)
  | _, .obsL q => ElimM.ofOrig _ (.obsL q)
  | _, .obsH q => ElimM.ofOrig _ (.obsH q)
  | s, .seq (s' := s') d a =>
    ElimM.guarded s (ElimM.guard s' (d.elimFM F) d) (a.elimFM F) (.seq d a)
  | s, .orElse a b => ElimM.orElse s (a.elimFM F) (b.elimFM F) (.orElse a b)
  | s, .kite a b t e =>
    ElimM.kite (a.elimFM F) (b.elimFM F) s (t.elimFM F) (e.elimFM F) (.kite a b t e)
  | s, .err => ElimM.ofOrig s .err

/-- **The elimination, its words and storage readings rewritten by the
premises `F`.**  By the recursor. -/
@[implemented_by LTm.elimFM]
def LTm.elimF (F : Facts C) {s : Srt} (t : LTm C s) : ElimM C s :=
  @LTm.rec C (fun s _ => ElimM C s)
    (fun {_} k => ElimM.rwF F _ (.var k : LTm C (.val _)))
    (fun {s} o => ElimM.rwF F s o.elim)
    (fun {_} {s} o x ex => ElimM.rwF F s (o.elim x ex))
    (fun {_} {_} {s} o x y ex ey => ElimM.rwF F s (o.elim x y ex ey))
    (fun {_} {_} {_} {s} o x y z ex ey ez => ElimM.rwF F s (o.elim x y z ex ey ez))
    (fun it _ _ eq ei => pathIdx it eq ei)
    (fun q _ => ElimM.ofOrig _ (.obsW q))
    (fun q _ => ElimM.ofOrig _ (.obsL q))
    (fun q _ => ElimM.ofOrig _ (.obsH q))
    (fun {s'} {s} d a ed ea => ElimM.guarded s (ElimM.guard s' ed d) ea (.seq d a))
    (fun {s} a b ea eb => ElimM.orElse s ea eb (.orElse a b))
    (fun {_} {s} a b t e ea eb et ee => ElimM.kite ea eb s et ee (.kite a b t e))
    (fun {s} => ElimM.ofOrig s .err)
    s t

variable (g : State C []) (ν : AEnv)

theorem ElimM.rwF_rep {F : Facts C} (hF : F.Ok g ν) :
    (s : Srt) → (e : ElimM C s) → (t : LTm C s) → ElimM.Rep g ν s e t →
      ElimM.Rep g ν s (ElimM.rwF F s e) t
  | .val _, e, t, h => (F.rw_eval hF (e : LTm C (.val _))).trans h
  | .st, S, t, h =>
    ⟨h.orig, h.ok, fun st hst V c Q r hQ => (F.rw_eval hF _).trans (h.rd st hst V c Q r hQ)⟩
  | .path _, _, _, h | .sv _, _, _, h | .ident _, _, _, h | .addr _, _, _, h | .mem, _, _, h
  | .mv _, _, _, h | .sts _, _, _, h | .spath _ _, _, _, h | .kint, _, _, h => h

/-- **The elimination under premises that hold keeps what a term reads.** -/
theorem LTm.elimF_rep {F : Facts C} (hF : F.Ok g ν) :
    {s : Srt} → (t : LTm C s) → ElimM.Rep g ν s (t.elimF F) t
  | _, .var k => ElimM.rwF_rep g ν hF _ _ _ rfl
  | _, .app0 o => ElimM.rwF_rep g ν hF _ _ _ (Op0.elim_rep g ν o)
  | _, .app1 o x => ElimM.rwF_rep g ν hF _ _ _ (Op1.elim_rep g ν o x _ (LTm.elimF_rep hF x))
  | _, .app2 o x y => ElimM.rwF_rep g ν hF _ _ _
      (Op2.elim_rep g ν o x y _ _ (LTm.elimF_rep hF x) (LTm.elimF_rep hF y))
  | _, .app3 o x y z => ElimM.rwF_rep g ν hF _ _ _
      (Op3.elim_rep g ν o x y z _ _ _ (LTm.elimF_rep hF x) (LTm.elimF_rep hF y)
        (LTm.elimF_rep hF z))
  | _, .index it q i => pathIdx_rep g ν it (LTm.elimF_rep hF q) (LTm.elimF_rep hF i)
  | _, .obsW q => ElimM.ofOrig_rep g ν _ _
  | _, .obsL q => ElimM.ofOrig_rep g ν _ _
  | _, .obsH q => ElimM.ofOrig_rep g ν _ _
  | s, .seq (s' := s') d a =>
    ElimM.guarded_rep g ν d _ (ElimM.guard_eval g ν s' _ d (LTm.elimF_rep hF d)) s _ a
      (LTm.elimF_rep hF a)
  | s, .orElse a b => ElimM.orElse_rep g ν s _ _ a b (LTm.elimF_rep hF a) (LTm.elimF_rep hF b)
  | s, .kite a b t e =>
    ElimM.kite_rep g ν (LTm.elimF_rep hF a) (LTm.elimF_rep hF b) s _ _ t e (LTm.elimF_rep hF t)
      (LTm.elimF_rep hF e)
  | s, .err => ElimM.ofOrig_rep g ν s _

theorem LTm.elimF_eval {F : Facts C} (hF : F.Ok g ν) {p : PrimTy} (t : LTm C (.val p)) :
    ((t.elimF F : LTm C (.val p)).eval g ν : Option p.Denote) = t.eval g ν :=
  LTm.elimF_rep g ν hF t

end Rw

/-! ## What a premise states -/

section Facts

/-- `x == v` read `true` states `x ≐ v`. -/
def _root_.Solidity.Op2.eqBFact {a b s : Srt} (o : Op2 C a b s) (x : LTm C a) (y : LTm C b) :
    Option (EqF C) :=
  match o, x, y with
  | .binop op _, x, y =>
    match op with
    | .eqB => some ⟨_, x, y⟩
    | _ => none
  | _, _, _ => none

/-- The equation a word `x == y` states, where it is one. -/
def LTm.eqBFact? (t : LTm C (.val .bool)) : Option (EqF C) :=
  match t with
  | .app2 o x y => o.eqBFact x y
  | _ => none

/-- The equations `a ≐ b` states that the elimination rewrites by: toward
a literal side; `x == v` read `true`, `x ≐ v`. -/
def eqFacts {p : PrimTy} (a b : LTm C (.val p)) : List (EqF C) :=
  (match b.litV?, a.litV? with
    | some _, _ => [⟨p, a, b⟩]
    | none, some _ => [⟨p, b, a⟩]
    | none, none => []) ++
  (match p, a, b with
    | .bool, a, b => if b.isTT then (a.eqBFact?).toList else []
    | _, _, _ => [])

/-- `LFml.factsOf`'s compiled twin. -/
def LFml.factsOfM : LFml C → List (EqF C)
  | .eq a b => eqFacts a b
  | .and φ ψ => φ.factsOfM ++ ψ.factsOfM
  | _ => []

/-- **The equations a formula states**: its equations and those of its
conjuncts.  By the recursor. -/
@[implemented_by LFml.factsOfM]
def LFml.factsOf (φ : LFml C) : List (EqF C) :=
  @LFml.rec C (fun _ => List (EqF C)) [] (@fun _ a b => eqFacts a b) (fun _ _ => [])
    (fun _ _ ih₁ ih₂ => ih₁ ++ ih₂) (fun _ _ _ _ => []) (fun _ _ _ _ => []) φ

variable {g : State C []} {ν : AEnv}

theorem Op2.eqBFact_sound {a b s : Srt} (o : Op2 C a b s) (x : LTm C a) (y : LTm C b)
    {e : EqF C} (he : o.eqBFact x y = some e) (hs : s = .val .bool)
    (ht : (LTm.app2 o x y).eval g ν = hs ▸ (some true : Option ((Srt.val .bool).Den C g.H))) :
    ∃ x, (e.l.eval g ν : Option e.p.Denote) = some x ∧ e.r.eval g ν = some x := by
  cases o <;> simp only [Op2.eqBFact, reduceCtorEq] at he
  rename_i op p hop
  cases op <;> simp only [reduceCtorEq, Option.some.injEq] at he
  subst he
  cases hs
  have ht' : ((LTm.app2 (.binop .eqB hop) x y).eval g ν : Option Bool) = some true := ht
  rw [LTm.eval_app2, Op2.eval_eq_evalM] at ht'
  cases hx : (x.eval g ν : Option p.Denote) with
  | none => rw [hx] at ht'; cases ht'
  | some u =>
    rw [hx] at ht'
    obtain ⟨w, hw, hv⟩ := binopT_eqB ht'
    have e : u = w := of_decide_eq_true hv.symm
    subst e
    exact ⟨u, rfl, hw⟩

theorem LTm.eqBFact?_sound {t : LTm C (.val .bool)} {e : EqF C} (h : t.eqBFact? = some e)
    (ht : (t.eval g ν : Option Bool) = some true) :
    ∃ x, (e.l.eval g ν : Option e.p.Denote) = some x ∧ e.r.eval g ν = some x := by
  cases t with
  | app2 o x y => exact Op2.eqBFact_sound o x y h rfl ht
  | _ => simp only [LTm.eqBFact?, reduceCtorEq] at h

theorem eqFacts_sound {p : PrimTy} {a b : LTm C (.val p)} (h : (LFml.eq a b).holds g ν) :
    ∀ e ∈ eqFacts a b, ∃ x, (e.l.eval g ν : Option e.p.Denote) = some x ∧ e.r.eval g ν = some x := by
  obtain ⟨x, ha, hb⟩ := (LFml.holds_eq_iff g ν a b).1 h
  intro e he
  unfold eqFacts at he
  rcases List.mem_append.1 he with he | he
  · split at he
    · rw [List.mem_singleton] at he; subst he; exact ⟨x, ha, hb⟩
    · rw [List.mem_singleton] at he; subst he; exact ⟨x, hb, ha⟩
    · cases he
  · cases p with
    | bool =>
      simp only at he
      split at he
      · rename_i htt
        cases hq : a.eqBFact? with
        | none => rw [hq] at he; cases he
        | some e' =>
          rw [hq, Option.toList_some, List.mem_singleton] at he
          subst he
          rw [LTm.isTT_eval htt] at hb
          cases hb
          exact LTm.eqBFact?_sound hq ha
      · cases he
    | uint | int => cases he

theorem LFml.factsOf_sound {φ : LFml C} (h : φ.holds g ν) :
    ∀ e ∈ φ.factsOf, ∃ x, (e.l.eval g ν : Option e.p.Denote) = some x ∧ e.r.eval g ν = some x := by
  induction φ with
  | eq a b => exact eqFacts_sound h
  | and φ ψ ihφ ihψ =>
    intro e he
    rcases List.mem_append.1 he with he | he
    · exact ihφ h.1 e he
    · exact ihψ h.2 e he
  | _ => intro e he; cases he

end Facts

/-! ## A formula, eliminated under its premises -/

section Fml

/-- The premises `F` with the equations `es` added. -/
def Facts.addEqs (F : Facts C) (es : List (EqF C)) : Facts C := { F with eqs := es ++ F.eqs }

theorem Facts.addEqs_ok {g : State C []} {ν : AEnv} {F : Facts C} (hF : F.Ok g ν)
    {es : List (EqF C)}
    (h : ∀ e ∈ es, ∃ x, (e.l.eval g ν : Option e.p.Denote) = some x ∧ e.r.eval g ν = some x) :
    (F.addEqs es).Ok g ν :=
  ⟨fun e he => (List.mem_append.1 he).elim (h e) (hF.eqs e), hF.nes, hF.rets, hF.bnds⟩

/-- `LFml.elimF`'s compiled twin. -/
def LFml.elimFM : LFml C → Facts C → LFml C
  | .tt, _ => .tt
  | .eq a b, F => .eq (a.elimF F : LTm C (.val _)) (b.elimF F : LTm C (.val _))
  | .not φ, F => .not (φ.elimFM F)
  | .and φ ψ, F => .and (φ.elimFM F) (ψ.elimFM F)
  | .imp φ ψ, F =>
    let φ' := φ.elimFM F
    .imp φ' (ψ.elimFM (F.addEqs φ'.factsOf))
  | .all k p φ, F => .all k p (φ.elimFM (F.drop k))

/-- **A formula eliminated under its premises**: below an implication, what
its eliminated premise states (`LFml.factsOf`) rewrites the elimination of
its conclusion; below a quantifier, the premises that do not mention its
atom.  By the recursor. -/
@[implemented_by LFml.elimFM]
def LFml.elimF (φ : LFml C) (F : Facts C) : LFml C :=
  @LFml.rec C (fun _ => Facts C → LFml C) (fun _ => .tt)
    (@fun _ a b F => .eq (a.elimF F : LTm C (.val _)) (b.elimF F : LTm C (.val _)))
    (fun _ ih F => .not (ih F)) (fun _ _ ih₁ ih₂ F => .and (ih₁ F) (ih₂ F))
    (fun _ _ ih₁ ih₂ F =>
      let φ' := ih₁ F
      .imp φ' (ih₂ (F.addEqs φ'.factsOf)))
    (fun k p _ ih F => .all k p (ih (F.drop k))) φ F

/-- **The elimination under premises keeps what a formula says.** -/
theorem LFml.elimF_holds (g : State C []) : (φ : LFml C) → ∀ (F : Facts C) (ν : AEnv),
    F.Ok g ν → ((φ.elimF F).holds g ν ↔ φ.holds g ν)
  | .tt, _, _, _ => Iff.rfl
  | .eq a b, F, ν, hF => by
    show (LFml.eq (a.elimF F : LTm C (.val _)) (b.elimF F : LTm C (.val _))).holds g ν ↔ _
    rw [LFml.holds_eq_iff, LFml.holds_eq_iff, LTm.elimF_eval g ν hF, LTm.elimF_eval g ν hF]
  | .not φ, F, ν, hF => not_congr (LFml.elimF_holds g φ F ν hF)
  | .and φ ψ, F, ν, hF => and_congr (LFml.elimF_holds g φ F ν hF) (LFml.elimF_holds g ψ F ν hF)
  | .imp φ ψ, F, ν, hF => by
    show ((φ.elimF F).holds g ν → (ψ.elimF (F.addEqs (φ.elimF F).factsOf)).holds g ν) ↔ _
    have h₁ := LFml.elimF_holds g φ F ν hF
    constructor
    · intro h hφ
      have hφ' := h₁.2 hφ
      exact (LFml.elimF_holds g ψ _ ν (Facts.addEqs_ok hF (LFml.factsOf_sound hφ'))).1 (h hφ')
    · intro h hφ'
      exact (LFml.elimF_holds g ψ _ ν (Facts.addEqs_ok hF (LFml.factsOf_sound hφ'))).2
        (h (h₁.1 hφ'))
  | .all k p φ, F, ν, hF => forall_congr' fun v =>
      LFml.elimF_holds g φ (F.drop k) _ (Facts.drop_ok hF k p v)

end Fml

end Decide

end Solidity
