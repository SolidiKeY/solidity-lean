import Solidity.Calculus.ArrayCut

/-!
# Slot tests a length check settles (M7, step 6)

The elimination reads a checked element `a[i]` behind two guards: `i` below
the live length (`if(i < a.length) then true else err`) and the slot there
(`if(has(a[i])) then … else err`).  Past the first the second always holds:
below the live length every slot is there.  `LTm.hasFold` replaces the slot
test by `true` wherever a length check of the same index guards it
(`LTm.eval_hasFold`), once the guards are chained to the right
(`LTm.reassoc`).  The array cut then makes no atom for it: every atom a
leaf keeps is a variable of the arithmetic, whose search grows with their
number.
-/

namespace Solidity.Decide

variable {C : Contract}

/-! ## Guards chained to the right -/

/-- `seq d a`, the guards of `d` chained in front of `a`. -/
def LTm.mkSeqR : {s' s : Srt} → LTm C s' → LTm C s → LTm C s
  | _, _, .seq d₁ d₂, a => LTm.mkSeqR d₁ (LTm.mkSeqR d₂ a)
  | _, _, d, a => .seq d a

theorem LTm.eval_mkSeqR (g : State C []) (ν : AEnv) : ∀ {s' s : Srt} (d : LTm C s') (a : LTm C s),
    (LTm.mkSeqR d a).eval g ν = (LTm.seq d a).eval g ν := by
  intro s' s d a
  induction d generalizing s a with
  | seq d₁ d₂ ih₁ ih₂ =>
    rw [LTm.mkSeqR, ih₁, LTm.eval_seq, LTm.eval_seq, ih₂, LTm.eval_seq, LTm.eval_seq]
    cases (d₁.eval g ν) <;> rfl
  | _ => rfl

/-- **Guards chained to the right**, everywhere. -/
def LTm.reassoc : {s : Srt} → LTm C s → LTm C s
  | _, .var k => .var k
  | _, .app0 o => .app0 o
  | _, .err => .err
  | _, .app1 o a => .app1 o a.reassoc
  | _, .app2 o a b => .app2 o a.reassoc b.reassoc
  | _, .app3 o a b c => .app3 o a.reassoc b.reassoc c.reassoc
  | _, .index it a b => .index it a.reassoc b.reassoc
  | _, .obsW a => .obsW a.reassoc
  | _, .obsL a => .obsL a.reassoc
  | _, .obsH a => .obsH a.reassoc
  | _, .seq a b => LTm.mkSeqR a.reassoc b.reassoc
  | _, .orElse a b => .orElse a.reassoc b.reassoc
  | _, .kite a b t e => .kite a.reassoc b.reassoc t.reassoc e.reassoc

theorem LTm.eval_reassoc (g : State C []) (ν : AEnv) {s : Srt} (t : LTm C s) :
    t.reassoc.eval g ν = t.eval g ν := by
  induction t with
  | var | app0 | err => rfl
  | app1 o a ih => rw [LTm.reassoc, LTm.eval_app1, LTm.eval_app1, ih]
  | app2 o a b iha ihb => rw [LTm.reassoc, LTm.eval_app2, LTm.eval_app2, iha, ihb]
  | app3 o a b c iha ihb ihc => rw [LTm.reassoc, LTm.eval_app3, LTm.eval_app3, iha, ihb, ihc]
  | index it a b iha ihb => rw [LTm.reassoc, LTm.eval_index, LTm.eval_index, iha, ihb]
  | obsW a ih => rw [LTm.reassoc, LTm.eval_obsW, LTm.eval_obsW, ih]
  | obsL a ih => rw [LTm.reassoc, LTm.eval_obsL, LTm.eval_obsL, ih]
  | obsH a ih => rw [LTm.reassoc, LTm.eval_obsH, LTm.eval_obsH, ih]
  | seq a b iha ihb => rw [LTm.reassoc, LTm.eval_mkSeqR, LTm.eval_seq, LTm.eval_seq, iha, ihb]
  | orElse a b iha ihb => rw [LTm.reassoc, LTm.eval_orElse, LTm.eval_orElse, iha, ihb]
  | kite a b t e iha ihb iht ihe =>
    rw [LTm.reassoc, LTm.eval_kite, LTm.eval_kite, iha, ihb, iht, ihe]

/-! ## Slot tests a length check settles -/

/-- Below the live length of an actual array of primitives, a slot is
there. -/
theorem has_of_lt_len (st : Storage C) {a : Name} {e : PrimTy}
    (h : C.rootType a = some (.ref (.array (.prim e)))) (k : PrimTy.uint.Denote)
    (hk : k.1 < (uintOfNat (st.obs.len (.ref (SRef.ofRoot a h)))).1) :
    st.obs.has (.ref ((SRef.ofRoot a h).index (.arr .dyn) k)) = true := by
  have hp : ((SRef.ofRoot a h).index (.arr .dyn) k).path = .at k .nil := by
    simp only [SRef.index, SRef.append, SRef.ofRoot, Path.index_dyn, Path.append_nil]
  simp only [Storage.obs_has_ref, Storage.obs_len_ref, hp] at hk ⊢
  obtain ⟨B, hB, -, hL⟩ := dyn_shape_val (st.get h)
  have hl : (SRef.ofRoot a h).path = .nil := rfl
  rw [hl] at hk
  rw [hB]
  have h0 := uint_nonneg k
  have h1 := uint_nonneg (uintOfNat ((st.get h).obs.len .nil))
  simp only [decide_eq_true_eq]
  omega

/-- The length check of an element read of a dynamic array root:
`if(i < a.length) then true else err`; a fixed array has none. -/
def lenGuardOf {R : RefTy} {E : Ty} (a : Name) (h : C.rootType a = some (.ref R))
    (ar : ArrTy R E) (i : LTm C (.val .uint)) : Option (LTm C (.val .bool)) :=
  match R, h, ar with
  | _, h, .dyn => some (.app3 .ite (LTm.ltU i (.obsL (.app0 (.root a h)))) LTm.tt .err)
  | _, _, .fixed => none

/-- **Where the length check returns, the slot is there.** -/
theorem lenGuardOf_sound (g : State C []) (ν : AEnv) {R : RefTy} {e : PrimTy} (a : Name)
    (h : C.rootType a = some (.ref R)) (ar : ArrTy R (.prim e)) (i : LTm C (.val .uint))
    {G : LTm C (.val .bool)} (hG : lenGuardOf a h ar i = some G) (hr : ∃ v, G.eval g ν = some v) :
    ((LTm.obsH (.index (.arr ar) (.app0 (.root a h)) i)).eval g ν : Option Bool) = some true := by
  cases ar with
  | fixed => cases hG
  | dyn =>
    simp only [lenGuardOf, Option.some.injEq] at hG
    subst hG
    obtain ⟨v, hv⟩ := hr
    change ((LTm.ltU i (.obsL (.app0 (.root a h)))).eval g ν : Option Bool).bind
      (fun b => cond b (some true) none) = some v at hv
    rw [LTm.eval_obsH, LTm.eval_index, LTm.eval_app0]
    cases hx : (i.eval g ν : Option PrimTy.uint.Denote) with
    | none =>
      rw [LTm.eval_app2, hx] at hv; cases hv
    | some k =>
      rw [LTm.eval_app2, hx, LTm.eval_obsL, LTm.eval_app0] at hv
      change ((some (decide (k.1 < (uintOfNat (g.storage.obs.len (.ref (SRef.ofRoot a h)))).1)) :
        Option Bool).bind fun b => cond b (some true) none) = some v at hv
      by_cases hk : k.1 < (uintOfNat (g.storage.obs.len (.ref (SRef.ofRoot a h)))).1
      · exact congrArg some (has_of_lt_len g.storage h k hk)
      · simp only [hk, decide_false, Option.bind_some, cond_false, reduceCtorEq] at hv

/-- A slot test the guard `d` settles: an element of a dynamic array root
whose length check is `d`. -/
def settles {s' : Srt} (d : LTm C s') {T : Ty} (q : LTm C (.path T)) : Bool :=
  match q.elemPath? with
  | some ep =>
    match lenGuardOf ep.root ep.h ep.ar ep.i with
    | some G => d.beqR G
    | none => false
  | none => false

theorem settles_sound (g : State C []) (ν : AEnv) {s' : Srt} {d : LTm C s'} {T : Ty}
    {q : LTm C (.path T)} (h : settles d q = true) (hd : ∃ v, d.eval g ν = some v) :
    ((LTm.obsH q).eval g ν : Option Bool) = some true := by
  unfold settles at h
  split at h
  · rename_i ep _
    split at h
    · rename_i G hG
      have e := LTm.sigma_eq_of_beqR h
      rcases ep with ⟨a, R, hR, _, ar, e', he, i, rfl⟩
      subst he
      simp only [Sigma.mk.injEq] at e
      obtain ⟨rfl, e⟩ := e
      cases eq_of_heq e
      exact lenGuardOf_sound g ν a hR ar i hG hd
    · cases h
  · cases h

/-- The slot tests the guard `d` settles replaced by `true`, outside paths and
observations (a test there is kept). -/
def LTm.foldUnder {s' : Srt} (d : LTm C s') : {s : Srt} → LTm C s → LTm C s
  | _, .var k => .var k
  | _, .app0 o => .app0 o
  | _, .err => .err
  | _, .app1 o a => .app1 o (LTm.foldUnder d a)
  | _, .app2 o a b => .app2 o (LTm.foldUnder d a) (LTm.foldUnder d b)
  | _, .app3 o a b c => .app3 o (LTm.foldUnder d a) (LTm.foldUnder d b) (LTm.foldUnder d c)
  | _, .index it a b => .index it a b
  | _, .obsW a => .obsW a
  | _, .obsL a => .obsL a
  | _, .obsH a => if settles d a then LTm.tt else .obsH a
  | _, .seq a b => .seq (LTm.foldUnder d a) (LTm.foldUnder d b)
  | _, .orElse a b => .orElse (LTm.foldUnder d a) (LTm.foldUnder d b)
  | _, .kite a b t e =>
    .kite (LTm.foldUnder d a) (LTm.foldUnder d b) (LTm.foldUnder d t) (LTm.foldUnder d e)

/-- Where `d` returns, folding under it keeps every value. -/
theorem LTm.eval_foldUnder (g : State C []) (ν : AEnv) {s' : Srt} (d : LTm C s')
    (hd : ∃ v, d.eval g ν = some v) {s : Srt} (t : LTm C s) :
    (LTm.foldUnder d t).eval g ν = t.eval g ν := by
  induction t with
  | var | app0 | err | index | obsW | obsL => rfl
  | app1 o a ih => rw [LTm.foldUnder, LTm.eval_app1, LTm.eval_app1, ih]
  | app2 o a b iha ihb => rw [LTm.foldUnder, LTm.eval_app2, LTm.eval_app2, iha, ihb]
  | app3 o a b c iha ihb ihc => rw [LTm.foldUnder, LTm.eval_app3, LTm.eval_app3, iha, ihb, ihc]
  | obsH a _ =>
    rw [LTm.foldUnder]
    split
    · rename_i h
      exact (settles_sound g ν h hd).symm
    · rfl
  | seq a b iha ihb => rw [LTm.foldUnder, LTm.eval_seq, LTm.eval_seq, iha, ihb]
  | orElse a b iha ihb => rw [LTm.foldUnder, LTm.eval_orElse, LTm.eval_orElse, iha, ihb]
  | kite a b t e iha ihb iht ihe =>
    rw [LTm.foldUnder, LTm.eval_kite, LTm.eval_kite, iha, ihb, iht, ihe]

/-! ## The fold -/

/-- `seq d a`, the slot tests `d` settles replaced in `a`. -/
def LTm.seqFold {s' s : Srt} (d : LTm C s') (a : LTm C s) : LTm C s := .seq d (LTm.foldUnder d a)

theorem LTm.eval_seqFold (g : State C []) (ν : AEnv) {s' s : Srt} (d : LTm C s') (a : LTm C s) :
    (LTm.seqFold d a).eval g ν = (LTm.seq d a).eval g ν := by
  unfold LTm.seqFold
  rw [LTm.eval_seq, LTm.eval_seq]
  cases hd : d.eval g ν with
  | none => rfl
  | some v => exact LTm.eval_foldUnder g ν d ⟨v, hd⟩ a

/-- **Slot tests that a length check settles replaced by `true`**, bottom
up. -/
def LTm.hasFold : {s : Srt} → LTm C s → LTm C s
  | _, .var k => .var k
  | _, .app0 o => .app0 o
  | _, .err => .err
  | _, .app1 o a => .app1 o a.hasFold
  | _, .app2 o a b => .app2 o a.hasFold b.hasFold
  | _, .app3 o a b c => .app3 o a.hasFold b.hasFold c.hasFold
  | _, .index it a b => .index it a.hasFold b.hasFold
  | _, .obsW a => .obsW a.hasFold
  | _, .obsL a => .obsL a.hasFold
  | _, .obsH a => .obsH a.hasFold
  | _, .seq a b => LTm.seqFold a.hasFold b.hasFold
  | _, .orElse a b => .orElse a.hasFold b.hasFold
  | _, .kite a b t e => .kite a.hasFold b.hasFold t.hasFold e.hasFold

theorem LTm.eval_hasFold (g : State C []) (ν : AEnv) {s : Srt} (t : LTm C s) :
    t.hasFold.eval g ν = t.eval g ν := by
  induction t with
  | var | app0 | err => rfl
  | app1 o a ih => rw [LTm.hasFold, LTm.eval_app1, LTm.eval_app1, ih]
  | app2 o a b iha ihb => rw [LTm.hasFold, LTm.eval_app2, LTm.eval_app2, iha, ihb]
  | app3 o a b c iha ihb ihc => rw [LTm.hasFold, LTm.eval_app3, LTm.eval_app3, iha, ihb, ihc]
  | index it a b iha ihb => rw [LTm.hasFold, LTm.eval_index, LTm.eval_index, iha, ihb]
  | obsW a ih => rw [LTm.hasFold, LTm.eval_obsW, LTm.eval_obsW, ih]
  | obsL a ih => rw [LTm.hasFold, LTm.eval_obsL, LTm.eval_obsL, ih]
  | obsH a ih => rw [LTm.hasFold, LTm.eval_obsH, LTm.eval_obsH, ih]
  | seq a b iha ihb => rw [LTm.hasFold, LTm.eval_seqFold, LTm.eval_seq, LTm.eval_seq, iha, ihb]
  | orElse a b iha ihb => rw [LTm.hasFold, LTm.eval_orElse, LTm.eval_orElse, iha, ihb]
  | kite a b t e iha ihb iht ihe =>
    rw [LTm.hasFold, LTm.eval_kite, LTm.eval_kite, iha, ihb, iht, ihe]

/-- **The fold of a formula**: guards chained, settled slot tests replaced,
in every equation. -/
def LFml.hasFold (φ : LFml C) : LFml C :=
  φ.mapEq fun a b => .eq a.reassoc.hasFold b.reassoc.hasFold

theorem LFml.hasFold_holds (g : State C []) (φ : LFml C) (ν : AEnv) :
    φ.hasFold.holds g ν ↔ φ.holds g ν := by
  apply LFml.mapEq_holds g _ _ φ ν
  intro ν p a b
  simp only [LFml.holds, LTm.eval_hasFold, LTm.eval_reassoc]

/-- info: 'Solidity.Decide.LFml.hasFold_holds' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms LFml.hasFold_holds

end Solidity.Decide
