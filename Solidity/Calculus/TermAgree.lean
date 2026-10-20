import Solidity.Calculus.DeclarationFacts
import Solidity.Calculus.SoundArms

/-!
# Terms the Theory reads as the interpreter does

An equation is read in the Theory (`Tm.denote`), where a read off the end
of what is there reads the default; the decision procedure reads the typed
evaluation (`Tm.eval`), where it reverts.  On the terms below the two
readings agree (`Tm.agreeB_denote`), so an equation of two of them is the
equation of their typed readings, `none` included: the decision procedure
reads it exactly, at either polarity (`Calculus/DecideScoped.lean`).

* `Tm.totB`: a value that returns in every typed state (`Tm.Total`,
  `Calculus/DeclarationFacts.lean`): a local, a literal, a value of the
  transaction, a read of `storage` at a declared place (`Tm.declB`: a root,
  a member, a mapping entry at a key that returns).  An array element is
  not one: its index is checked.
* `Tm.agreeB`: such a value, or an operator or a conditional over values
  that agree, which the Theory reads as the interpreter does.
-/

namespace Solidity

variable {C : Contract} {Γ : Ctx}

/-- A symbol that is a mapping's entry. -/
def Op2.isAtMap {a b s : Srt} : Op2 C a b s → Bool
  | .at .map => true
  | _ => false

/-- `find`, or a dynamic array's `len`: a read at a place. -/
def Op2.isFind {a b s : Srt} : Op2 C a b s → Bool
  | .find | .len => true
  | _ => false

/-- `storage`, or a snapshot of it (`old`). -/
def Tm.isStorageB {s : Srt} : Tm C Γ s → Bool
  | .app0 .storage => true
  | .pvS _ => true
  | _ => false

mutual

/-- A path through declarations: a root, a member, a mapping entry at a key
that returns. -/
def Tm.declB : {s : Srt} → Tm C Γ s → Bool
  | _, .app0 (.root _ _) => true
  | _, .app1 (.field _) q => q.declB
  | _, .app2 o q k => o.isAtMap && q.declB && k.totB
  | _, _ => false

/-- A value that returns in every typed state. -/
def Tm.totB : {s : Srt} → Tm C Γ s → Bool
  | _, .pvV _ => true
  | _, .app0 (.lit _) => true
  | _, .app0 (.env _) => true
  | _, .app2 o s q => o.isFind && s.isStorageB && q.declB
  | _, _ => false

end

/-- A dynamic array's length at a declared place returns: the array is there,
and its length is below `2^256` (`Storage.len`). -/
theorem Tm.total_len {E : Ty} {s : Tm C Γ .st} {q : Tm C Γ (.path (.ref (.array E)))}
    (hs : s.Total) (hq : q.Declared) : Tm.Total (.app2 .len s q) := by
  intro σ
  obtain ⟨st, hst⟩ := hs σ
  obtain ⟨r, hr, hd⟩ := hq σ
  obtain ⟨w, hw⟩ := SRef.Declared.find hd st
  refine ⟨lenU (SVal.view w : ArrView E).n (SVal.view w : ArrView E).hn, ?_⟩
  show (do (← s.eval σ).len (← q.eval σ)) = _
  rw [hst, hr]
  show (do let w : ArrView E := SVal.view (← st.find r); some (lenU w.n w.hn)) = _
  rw [hw]
  rfl

/-- What `Tm.declB` and `Tm.totB` give, by sort. -/
def Tm.GoodS : (s : Srt) → Tm C Γ s → Prop
  | .val _, t => t.Total
  | .path _, t => t.Declared
  | _, _ => True

theorem Tm.declB_totB_sound {s : Srt} (t : Tm C Γ s) :
    (t.declB = true → Tm.GoodS s t) ∧ (t.totB = true → Tm.GoodS s t) := by
  induction t with
  | pvV i => exact ⟨nofun, fun _ => Tm.total_local i⟩
  | app0 o =>
    cases o with
    | lit v => exact ⟨nofun, fun _ => Tm.total_lit v⟩
    | env k => exact ⟨nofun, fun _ => Tm.total_env k⟩
    | root r h => exact ⟨fun _ => Tm.declared_root r h, nofun⟩
    | _ => exact ⟨nofun, nofun⟩
  | app1 o x ih =>
    cases o with
    | field h => exact ⟨fun hd => Tm.declared_field h (ih.1 hd), nofun⟩
    | _ => exact ⟨nofun, nofun⟩
  | app2 o x y ihx ihy =>
    cases o with
    | «at» it =>
      cases it with
      | map =>
        refine ⟨fun hd => ?_, nofun⟩
        simp only [Tm.declB, Op2.isAtMap, Bool.true_and, Bool.and_eq_true] at hd
        exact Tm.declared_key (ihx.1 hd.1) (ihy.2 hd.2)
      | arr _ =>
        refine ⟨fun hd => ?_, nofun⟩
        simp only [Tm.declB, Op2.isAtMap, Bool.false_and, Bool.false_eq_true] at hd
    | find =>
      refine ⟨nofun, fun ht => ?_⟩
      simp only [Tm.totB, Op2.isFind, Bool.true_and, Bool.and_eq_true] at ht
      obtain ⟨hs, hq⟩ := ht
      cases x with
      | app0 o =>
        cases o with
        | storage => exact Tm.total_find Tm.total_storage (ihy.1 hq)
        | _ => simp only [Tm.isStorageB, Bool.false_eq_true] at hs
      | pvS i => exact Tm.total_find (Tm.total_old i) (ihy.1 hq)
      | _ => simp only [Tm.isStorageB, Bool.false_eq_true] at hs
    | len =>
      refine ⟨nofun, fun ht => ?_⟩
      simp only [Tm.totB, Op2.isFind, Bool.true_and, Bool.and_eq_true] at ht
      obtain ⟨hs, hq⟩ := ht
      have hst : x.Total := by
        cases x with
        | app0 o =>
          cases o with
          | storage => exact Tm.total_storage
          | _ => simp only [Tm.isStorageB, Bool.false_eq_true] at hs
        | pvS i => exact Tm.total_old i
        | _ => simp only [Tm.isStorageB, Bool.false_eq_true] at hs
      exact Tm.total_len hst (ihy.1 hq)
    | _ => exact ⟨nofun, nofun⟩
  | pvP _ | pvS _ | pvI _ | netOf _ _ _ | app3 _ _ _ _ _ _ _ | pvZ _ => exact ⟨nofun, nofun⟩

/-- A value that returns in every typed state returns. -/
theorem Tm.totB_total {p : PrimTy} {t : Tm C Γ (.val p)} (h : t.totB = true) : t.Total :=
  (Tm.declB_totB_sound t).2 h

/-- A constant the Theory reads as the interpreter does. -/
def Op0.agreesB {s : Srt} : Op0 C s → Bool
  | .lit _ | .env _ | .zlit _ => true
  | _ => false

/-- A unary symbol the Theory reads as the interpreter does, on an operand
it so reads: an operator, the ledger's entry, a widening to KeY's `int`. -/
def Op1.agreesB {a s : Srt} : Op1 C a s → Bool
  | .unop .. | .net | .toInt | .delValue => true
  | _ => false

/-- A binary symbol the Theory reads as the interpreter does: an operator,
KeY's `int` arithmetic and comparisons. -/
def Op2.agreesB {a b s : Srt} : Op2 C a b s → Bool
  | .binop .. | .zbin .. | .zcmp .. => true
  | _ => false

/-- A memory read, which the Theory reads by the interpreter whatever its
operands (`Op2.denote`). -/
def Op2.memReadB {a b s : Srt} : Op2 C a b s → Bool
  | .read | .mlen | .keccak => true
  | _ => false

/-- The conditional. -/
def Op3.isIteB {a b c s : Srt} : Op3 C a b c s → Bool
  | .ite => true
  | _ => false

/-- A value the Theory reads as the interpreter does: one that returns, or a
symbol the Theory reads alike over such values. -/
def Tm.agreeB : {s : Srt} → Tm C Γ s → Bool
  | _, .pvV _ => true
  | _, .pvP _ => false
  | _, .pvS _ => false
  | _, .pvI _ => false
  | _, .netOf _ a => a.agreeB
  | _, .app0 o => o.agreesB
  | _, .app1 o x => o.agreesB && x.agreeB
  | _, .app2 o x y =>
    (o.agreesB && x.agreeB && y.agreeB) || o.memReadB || Tm.totB (.app2 o x y)
  | _, .app3 o c x y => o.isIteB && c.agreeB && x.agreeB && y.agreeB
  | _, .pvZ _ => true

/-- What `Tm.agreeB` gives, by sort. -/
def Tm.AgreeS : (s : Srt) → Tm C Γ s → Prop
  | .val _, t => ∀ σ : State C Γ, t.denote σ = t.eval σ
  | .kint, t => ∀ σ : State C Γ, t.denote σ = t.eval σ
  | _, _ => True

/-- A value that returns reads in the Theory as it evaluates. -/
theorem Tm.denote_of_total {p : PrimTy} {t : Tm C Γ (.val p)} (h : t.Total) (σ : State C Γ) :
    t.denote σ = t.eval σ := by
  obtain ⟨v, hv⟩ := h σ
  rw [hv, Tm.denote_eval σ t v hv]

theorem Tm.agreeB_sound {s : Srt} (t : Tm C Γ s) : t.agreeB = true → Tm.AgreeS s t := by
  induction t with
  | pvV i => exact fun _ => Tm.denote_of_total (Tm.total_local i)
  | pvZ i => exact fun _ _ => rfl
  | netOf i a ih =>
    intro h σ
    have ih' := ih h σ
    show (a.denote σ).map _ = (a.eval σ).bind (Tm.netOfT _)
    rw [ih']
    cases a.eval σ <;> rfl
  | app0 o =>
    intro h
    cases o with
    | lit v => exact Tm.denote_of_total (Tm.total_lit v)
    | env k => exact Tm.denote_of_total (Tm.total_env k)
    | zlit n => exact fun _ => rfl
    | _ => first | trivial | simp only [Tm.agreeB, Op0.agreesB, Bool.false_eq_true] at h
  | app1 o x ih =>
    intro h
    cases o with
    | unop op hop =>
      simp only [Tm.agreeB, Op1.agreesB, Bool.true_and] at h
      intro σ
      show (x.denote σ).bind (op.evalT hop) = (x.eval σ).bind (op.evalT hop)
      rw [ih h σ]
    | net =>
      simp only [Tm.agreeB, Op1.agreesB, Bool.true_and] at h
      intro σ
      show (x.denote σ).map _ = (x.eval σ).map _
      rw [ih h σ]
    | toInt =>
      simp only [Tm.agreeB, Op1.agreesB, Bool.true_and] at h
      intro σ
      show (x.denote σ).map _ = (x.eval σ).map _
      rw [ih h σ]
    | delValue =>
      simp only [Tm.agreeB, Op1.agreesB, Bool.true_and] at h
      intro σ
      show (x.denote σ).map _ = (x.eval σ).map _
      rw [ih h σ]
    | _ => first | trivial | simp only [Tm.agreeB, Op1.agreesB, Bool.false_and,
        Bool.false_eq_true] at h
  | app2 o x y ihx ihy =>
    intro h
    cases o with
    | binop op hop =>
      simp only [Tm.agreeB, Op2.agreesB, Op2.memReadB, Bool.true_and, Tm.totB, Op2.isFind,
        Bool.false_and, Bool.or_false, Bool.and_eq_true] at h
      intro σ
      rw [Tm.eval_binop]
      show (x.denote σ).bind (fun v => binopT op hop v (y.denote σ)) = _
      rw [ihx h.1 σ, ihy h.2 σ]
    | zbin op hop =>
      simp only [Tm.agreeB, Op2.agreesB, Op2.memReadB, Bool.true_and, Tm.totB, Op2.isFind,
        Bool.false_and, Bool.or_false, Bool.and_eq_true] at h
      intro σ
      show (do some (op.evalZ (← x.denote σ) (← y.denote σ))) =
        (do some (op.evalZ (← x.eval σ) (← y.eval σ)))
      rw [ihx h.1 σ, ihy h.2 σ]
    | zcmp op hop =>
      simp only [Tm.agreeB, Op2.agreesB, Op2.memReadB, Bool.true_and, Tm.totB, Op2.isFind,
        Bool.false_and, Bool.or_false, Bool.and_eq_true] at h
      intro σ
      show (do some (op.cmpZ (← x.denote σ) (← y.denote σ))) =
        (do some (op.cmpZ (← x.eval σ) (← y.eval σ)))
      rw [ihx h.1 σ, ihy h.2 σ]
    | find =>
      simp only [Tm.agreeB, Op2.agreesB, Op2.memReadB, Bool.false_and, Bool.false_or] at h
      exact Tm.denote_of_total (Tm.totB_total h)
    | len =>
      simp only [Tm.agreeB, Op2.agreesB, Op2.memReadB, Bool.false_and, Bool.false_or] at h
      exact Tm.denote_of_total (Tm.totB_total h)
    | read => exact fun _ => rfl
    | mlen => exact fun _ => rfl
    | keccak => exact fun _ => rfl
    | _ => first | trivial | simp only [Tm.agreeB, Op2.agreesB, Op2.memReadB, Tm.totB,
        Op2.isFind, Bool.false_and, Bool.false_or, Bool.false_eq_true] at h
  | app3 o c x y ihc ihx ihy =>
    intro h
    cases o with
    | ite =>
      simp only [Tm.agreeB, Op3.isIteB, Bool.true_and, Bool.and_eq_true] at h
      intro σ
      show (c.denote σ).bind (fun v => cond v (x.denote σ) (y.denote σ)) =
        (c.eval σ).bind (fun v => cond v (x.eval σ) (y.eval σ))
      rw [ihc h.1.1 σ, ihx h.1.2 σ, ihy h.2 σ]
    | _ => first | trivial | simp only [Tm.agreeB, Op3.isIteB, Bool.false_and,
        Bool.false_eq_true] at h
  | pvP _ | pvS _ | pvI _ => exact fun h => by simp only [Tm.agreeB, Bool.false_eq_true] at h

/-- **A value that agrees reads in the Theory as it evaluates.** -/
theorem Tm.agreeB_denote {p : PrimTy} {t : Tm C Γ (.val p)} (h : t.agreeB = true)
    (σ : State C Γ) : t.denote σ = t.eval σ :=
  Tm.agreeB_sound t h σ

/-- An equation of two values that agree holds where their typed readings
are one, a halt included. -/
theorem holds_eq_of_agree {p : PrimTy} {a b : Tm C Γ (.val p)} (ha : a.agreeB = true)
    (hb : b.agreeB = true) (σ : State C Γ) : holds σ (.eq a b) ↔ a.eval σ = b.eval σ := by
  rw [holds_eq, Tm.agreeB_denote ha σ, Tm.agreeB_denote hb σ]

end Solidity
