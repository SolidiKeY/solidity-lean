import Solidity.Calculus.ExactReduction

/-!
# Array elements read as the Theory reads them (M7, step 6)

A formula reads an array element `a[i]` in the Theory (`Tm.denote`): the
word at the location, the live elements and the slots past them alike, the
default past every slot.  The interpreter's read (`Tm.eval`) halts past the
live length.  So an equation over such a read is not one `Tm.agreeB` admits,
and update pushing read it one way at each polarity (`Fml.eqAt`).

`Tm.toLT` pushes the updates into such a term exactly: the read becomes
`orElse(find(S, q[i]), 0)`, the unchecked location in the storage `S` the
updates left, the default where nothing is there; an operator over such
terms is pushed in as it is.  `Tm.toLT_sound` proves that the pushed-in term
reads what the Theory reads.  `ExactAt.ofFormula?` takes the equation so
when it is not one `Tm.agreeB` admits (`ExactAt.eqT?`,
`Calculus/ExactUpdates.lean`).
-/

namespace Solidity.Decide

variable {C : Contract} {Γ : Ctx}

/-- The default of a primitive type, as a literal. -/
abbrev LTm.dfltLit (p : PrimTy) : LTm C (.val p) := .app0 (.lit (PrimTy.dflt p))

/-- The index step of an element read in the Theory, pushed in unchecked. -/
def thIdx? (ρ : SymS C Γ) {R : RefTy} {k : PrimTy} {p : PrimTy} (x : Tm C Γ .st)
    (it : IndexTy R k (.prim p)) (q : Tm C Γ (.path (.ref R))) (i : Tm C Γ (.val k)) :
    Option (LTm C (.val p)) :=
  if x.isStorageB && q.declB && i.agreeB then
    (x.toL ρ).bind fun S => (q.toL ρ).bind fun q' => (i.toL ρ).bind fun i' =>
      some (.orElse (.app2 .find S (.index it q'
        (if i.totB then i' else .orElse i' (LTm.dfltLit k)))) (LTm.dfltLit p))
  else none

/-- The path of an element read in the Theory: an index step. -/
def thAt? (ρ : SymS C Γ) {a b : Srt} {p : PrimTy} (x : Tm C Γ .st)
    (o : Op2 C a b (.path (.prim p))) (q : Tm C Γ a) (i : Tm C Γ b) : Option (LTm C (.val p)) :=
  match a, b, o, q, i with
  | _, _, .at it, q, i => thIdx? ρ x it q i
  | _, _, _, _, _ => none

/-- **An array element read in the Theory**, pushed in: `find(s, q[i])`, `s`
a storage that returns, `q` a declared path, `i` an index the Theory reads
as the interpreter does.  The read is unchecked, the default where nothing
is there; a halting index reads as the Theory reads it, the slot `0`. -/
def thFind? (ρ : SymS C Γ) {p : PrimTy} (x : Tm C Γ .st) (y : Tm C Γ (.path (.prim p))) :
    Option (LTm C (.val p)) :=
  match y with
  | .app2 o q i => thAt? ρ x o q i
  | _ => none

/-- A binary node of the Theory pushed in: an array element read, or an
operator over terms pushed in. -/
def thApp2? (ρ : SymS C Γ) {a b s : Srt} (o : Op2 C a b s) (x : Tm C Γ a) (y : Tm C Γ b)
    (rx : Option (LTm C a)) (ry : Option (LTm C b)) : Option (LTm C s) :=
  match a, b, s, o, x, y, rx, ry with
  | _, _, _, .find, x, y, _, _ => thFind? ρ x y
  | _, _, _, .binop op h, _, _, rx, ry =>
    rx.bind fun x' => ry.bind fun y' => some (.app2 (.binop op h) x' y')
  | _, _, _, _, _, _, _, _ => none

/-- **A term pushed in as the Theory reads it**: a term the Theory reads as
the interpreter does (`Tm.agreeB`) as `Tm.toL` pushes it, an array element
read by `thFind?`, an operator over such terms; `none` elsewhere. -/
def _root_.Solidity.Tm.toLT (ρ : SymS C Γ) : {s : Srt} → Tm C Γ s → Option (LTm C s)
  | _, t@(.app2 o x y) =>
    if t.agreeB then t.toL ρ else thApp2? ρ o x y (Tm.toLT ρ x) (Tm.toLT ρ y)
  | _, t => if t.agreeB then t.toL ρ else none

/-- A term that falls back on one that always returns. -/
def LTm.orRets : {s : Srt} → LTm C s → Bool
  | _, .orElse _ b => b.retsS
  | _, _ => false

theorem LTm.orRets_eval (g : State C []) (ν : AEnv) {s : Srt} {t : LTm C s} (h : t.orRets = true) :
    ∃ v, t.eval g ν = some v := by
  cases t with
  | orElse a b =>
    obtain ⟨v, hv⟩ := LTm.retsS_eval (g := g) (ν := ν) (t := b) h
    rw [LTm.eval_orElse, hv]
    cases a.eval g ν with
    | none => exact ⟨v, rfl⟩
    | some w => exact ⟨w, rfl⟩
  | _ => simp only [LTm.orRets, Bool.false_eq_true] at h

/-- What a pushed-in term reads, by sort: at a value, what the Theory
reads. -/
def ThRel (g₀ : State C []) (τ : State C Γ) : (s : Srt) → Option (s.Den C g₀.H) → Tm C Γ s → Prop
  | .val p, x, t => (x : Option p.Denote) = t.denote τ
  | _, _, _ => True

section Sound

variable {g₀ : State C []} {ν : AEnv} {ρ : SymS C Γ} {τ : State C Γ}

/-- The word a storage shows at a location, by `find`. -/
theorem obs_word_ref_find (st : Storage C) {P : PrimTy} (r : SRef C (.prim P)) :
    st.obs.word (.ref r) = SVal.wordOf (st.find r) := by
  rw [Storage.obs_word_ref, SVal.obs_word, Storage.find, SVal.find_eq_findM]

theorem wordOf_eq_getD {P : PrimTy} (x : Option (SVal (.prim P))) :
    SVal.wordOf x = (x.bind fun v => some (SVal.view v : P.Denote)).getD (PrimTy.dflt P) := by
  cases x <;> rfl

/-- A storage term that `Tm.isStorageB` admits returns. -/
theorem _root_.Solidity.Tm.isStorageB_total {x : Tm C Γ .st} (h : x.isStorageB = true) : x.Total := by
  cases x with
  | app0 o =>
    cases o with
    | storage => exact Tm.total_storage
    | _ => simp only [Tm.isStorageB, Bool.false_eq_true] at h
  | pvS i => exact Tm.total_old i
  | _ => simp only [Tm.isStorageB, Bool.false_eq_true] at h

theorem thIdx?_sound (hA : Agrees g₀ ν ρ τ) {R : RefTy} {k p : PrimTy} (x : Tm C Γ .st)
    (it : IndexTy R k (.prim p)) (q : Tm C Γ (.path (.ref R))) (i : Tm C Γ (.val k))
    {t' : LTm C (.val p)} (h : thIdx? ρ x it q i = some t') :
    (t'.eval g₀ ν : Option p.Denote) = (Tm.app2 .find x (.app2 (.at it) q i)).denote τ := by
  unfold thIdx? at h
  split at h
  · rename_i hc
    simp only [Bool.and_eq_true] at hc
    obtain ⟨⟨hx, hq⟩, hi⟩ := hc
    simp only [Option.bind_eq_some_iff, Option.some.injEq] at h
    obtain ⟨S, hS, q', hq', i', hi', rfl⟩ := h
    obtain ⟨st, hst⟩ := Tm.isStorageB_total hx τ
    obtain ⟨r, hr, -⟩ := (Tm.declB_totB_sound q).1 hq τ
    have eS : (S.eval g₀ ν : Option (Storage C)) = some st := (Tm.toL_drel hA x S hS).trans hst
    have eq' : (q'.eval g₀ ν : Option (SRef C (.ref R))) = some r := (Tm.toL_drel hA q q' hq').trans hr
    have ei' : (i'.eval g₀ ν : Option k.Denote) = i.eval τ := Tm.toL_drel hA i i' hi'
    have dx : x.denote τ = st.obs := Tm.denote_eval τ x st hst
    have dq : q.denote τ = .ref r := Tm.denote_eval τ q r hr
    have di : i.denote τ = i.eval τ := Tm.agreeB_denote hi τ
    have ek : ((if i.totB = true then i' else i'.orElse (LTm.dfltLit k)).eval g₀ ν : Option k.Denote) =
        some ((i.eval τ).getD (PrimTy.dflt k)) := by
      split
      · rename_i ht
        obtain ⟨v, hv⟩ := Tm.totB_total ht τ
        rw [ei', hv]; rfl
      · rw [LTm.eval_orElse, ei']
        cases i.eval τ <;> rfl
    rw [LTm.eval_orElse, LTm.eval_app2, Close.Op2.eval_find, eS, LTm.eval_index, eq', ek]
    simp only [Option.bind_some, Tm.denote, Op2.denote, dx, dq, di, SLoc.app_ref]
    rw [obs_word_ref_find]
    change _ = some (SVal.wordOf (Storage.find st (SRef.index r it ((i.eval τ).getD (PrimTy.dflt k)))))
    cases Storage.find st (SRef.index r it ((i.eval τ).getD (PrimTy.dflt k))) <;> rfl
  · cases h

theorem thFind?_sound (hA : Agrees g₀ ν ρ τ) {p : PrimTy} (x : Tm C Γ .st)
    (y : Tm C Γ (.path (.prim p))) {t' : LTm C (.val p)} (h : thFind? ρ x y = some t') :
    (t'.eval g₀ ν : Option p.Denote) = (Tm.app2 .find x y).denote τ := by
  cases y with
  | app2 o q i =>
    cases o with
    | «at» it => exact thIdx?_sound hA x it q i h
    | _ => cases h
  | _ => cases h

/-- A term pushed in by `Tm.toL` that the Theory reads as the interpreter
does reads what the Theory reads. -/
theorem toL_thRel (hA : Agrees g₀ ν ρ τ) {s : Srt} (t : Tm C Γ s) {t' : LTm C s}
    (ha : t.agreeB = true) (h : t.toL ρ = some t') : ThRel g₀ τ s (t'.eval g₀ ν) t := by
  cases s with
  | val p => exact (Tm.toL_drel hA t t' h).trans (Tm.agreeB_denote ha τ).symm
  | _ => trivial

/-- **A term pushed in as the Theory reads it reads what the Theory reads.** -/
theorem _root_.Solidity.Tm.toLT_sound (hA : Agrees g₀ ν ρ τ) {s : Srt} (t : Tm C Γ s) {t' : LTm C s}
    (h : t.toLT ρ = some t') : ThRel g₀ τ s (t'.eval g₀ ν) t := by
  induction t with
  | app2 o x y ihx ihy =>
    unfold Tm.toLT at h
    split at h
    · exact toL_thRel hA _ (by assumption) h
    · cases o with
      | find => exact thFind?_sound hA x y h
      | binop op hop =>
        simp only [thApp2?, Option.bind_eq_some_iff, Option.some.injEq] at h
        obtain ⟨x', hx', y', hy', rfl⟩ := h
        have ex : (x'.eval g₀ ν : Option _) = x.denote τ := ihx hx'
        have ey : (y'.eval g₀ ν : Option _) = y.denote τ := ihy hy'
        show (LTm.app2 (.binop op hop) x' y').eval g₀ ν = Tm.denote τ (Tm.app2 (.binop op hop) x y)
        rw [LTm.eval_app2, Close.Op2.eval_binop, ex, ey]
        rfl
      | _ => cases h
  | _ =>
    unfold Tm.toLT at h
    split at h
    · exact toL_thRel hA _ (by assumption) h
    · cases h

end Sound

end Solidity.Decide
