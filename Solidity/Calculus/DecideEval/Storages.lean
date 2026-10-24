import Solidity.Calculus.DecideEval.Readers

/-!
# The reduction's evaluation: storages

Storages, and what the eliminated terms stand for: the storage operations'
guards, the operations eliminated, paths and stored values eliminated.

A piece of `Calculus/DecideEval.lean`, whose docstring describes the whole.
-/

namespace Solidity

namespace Decide

open Semantics

variable {C : Contract} (g : State C []) (ν : AEnv)

/-! ## Storages -/

/-- What `c` observes of a storage at a reference. -/
def CK.obsS {V : Ty} (c : CK V) (o : TSto C) (r : SRef C V) : c.out.Denote :=
  match V, c with
  | _, .word _ => o.word (.ref r)
  | _, .len _ => uintOfNat (o.len (.ref r))
  | _, .has _ => o.has (.ref r)

/-- **A storage reader reads the storage `st`**: at a path that evaluates,
the observation of `st` at the reference it names. -/
def SRd.Rep (S : SRd C) (st : Storage C) : Prop :=
  ∀ (V : Ty) (c : CK V) (Q : SPath C V) (r : SRef C V), Q.eval g ν = some r →
    ((S c Q).eval g ν : Option c.out.Denote) = some (c.obsS st.obs r)

theorem bnd_sto (st : Storage C) {T : Ty} (r : SRef C T) : Bnd (st.obs.find (.ref r)) := by
  rw [Storage.obs_find]
  intro E p
  show SVal.lenOf ((st.find r).bind (·.findM p)) < 2 ^ 256
  cases (st.find r).bind (·.findM p) with
  | none => exact SVal.zero_lt_bound
  | some w => cases w with | array e sh hn => exact hn

theorem SRd.Rep.at {S : SRd C} {st : Storage C} (h : SRd.Rep g ν S st) {T : Ty} {P : SPath C T}
    {r : SRef C T} (hP : P.eval g ν = some r) :
    VRd.Rep g ν (SRd.at S P) (st.obs.find (.ref r)) := by
  intro V c rest p hr
  have e : (P.snoc rest).eval g ν = some (r.append p) := by
    rw [SPath.eval_snoc, hP, Option.bind_some, hr]; rfl
  exact (h V c _ _ e).trans (by cases c <;> rfl)

/-- **`has` read past the segments always there**: `TSegs.hasFrom` reads what
`has` at the whole path reads, where the path evaluates and `acc` reads
`has` at its base. -/
theorem TSegs.hasFrom_eval {S T : Ty} (p : TSegs C S T) :
    ∀ (base : LTm C (.path S)) (acc : LTm C (.val .bool)) (rb : SRef C S) (pp : Path S T),
      (base.eval g ν : Option (SRef C S)) = some rb → p.eval g ν = some pp →
      (acc.eval g ν : Option Bool) = some (g.storage.obs.has (.ref rb)) →
      ((p.hasFrom base acc).eval g ν : Option Bool) =
        some (g.storage.obs.has (.ref (rb.append pp))) := by
  induction p with
  | nil =>
    intro base acc rb pp _ hp ha
    cases hp
    show (acc.eval g ν : Option Bool) = _
    rw [ha, SRef.append_nil]
  | field h rest ih =>
    intro base acc rb pp hb hp ha
    obtain ⟨pp', hpp', rfl⟩ := eval_field_some (g := g) (ν := ν) hp
    have hb' : ((LTm.app1 (.field h) base).eval g ν : Option (SRef C _)) =
        some (rb.append (.field h .nil)) := by
      rw [LTm.eval_field, hb]; rfl
    have ha' : (acc.eval g ν : Option Bool) =
        some (g.storage.obs.has (.ref (rb.append (.field h .nil)))) := by
      rw [ha, has_append _ _ _ (findM_field h)]
    have := ih _ acc _ pp' hb' hpp' ha'
    rw [SRef.append_append, Path.append_field, Path.append_nil] at this
    exact this
  | «at» i rest ih =>
    intro base acc rb pp hb hp _
    obtain ⟨k, pp', hk, hpp', rfl⟩ := eval_at_some (g := g) (ν := ν) hp
    have hb' : ((LTm.index (.arr .dyn) base i).eval g ν : Option (SRef C _)) =
        some (rb.append (.at k .nil)) := by
      rw [LTm.eval_index, hb, hk]; simp only [Option.bind_some, SRef.index, Path.index_dyn]
    have ha' : ((LTm.obsH (.index (.arr .dyn) base i)).eval g ν : Option Bool) =
        some (g.storage.obs.has (.ref (rb.append (.at k .nil)))) := by
      rw [LTm.eval_obsH, hb']; rfl
    have := ih _ _ _ pp' hb' hpp' ha'
    rw [SRef.append_append, Path.append_at, Path.append_nil] at this
    exact this
  | @atF E U n i rest ih =>
    intro base acc rb pp hb hp ha
    obtain ⟨k, pp', hk, hpp', rfl⟩ := eval_atF_some (g := g) (ν := ν) hp
    have hb' : ((LTm.index (.arr .fixed) base i).eval g ν : Option (SRef C _)) =
        some (rb.append (.atF k .nil)) := by
      rw [LTm.eval_index, hb, hk]; simp only [Option.bind_some, SRef.index, Path.index_fixed]
    have ha' : ((if TSegs.litBelow i n then acc else .obsH (.index (.arr .fixed) base i)).eval g ν :
        Option Bool) = some (g.storage.obs.has (.ref (rb.append (.atF k .nil)))) := by
      split
      · rename_i hl
        unfold TSegs.litBelow at hl
        split at hl
        · rename_i w hw
          have hi := LTm.eq_of_litV? hw
          subst hi
          have hkw : k = w := by cases hk; rfl
          subst hkw
          rw [ha, has_append _ _ _ (findM_atF k (of_decide_eq_true hl))]
        · cases hl
      · rw [LTm.eval_obsH, hb']; rfl
    have := ih _ _ _ pp' hb' hpp' ha'
    rw [SRef.append_append, Path.append_atF, Path.append_nil] at this
    exact this
  | key i rest ih =>
    intro base acc rb pp hb hp ha
    obtain ⟨j, pp', hj, hpp', rfl⟩ := eval_key_some (g := g) (ν := ν) hp
    have hb' : ((LTm.index .map base i).eval g ν : Option (SRef C _)) =
        some (rb.append (.key j .nil)) := by
      rw [LTm.eval_index, hb, hj]; simp only [Option.bind_some, SRef.index, Path.index_map]
    have ha' : (acc.eval g ν : Option Bool) =
        some (g.storage.obs.has (.ref (rb.append (.key j .nil)))) := by
      rw [ha, has_append _ _ _ (findM_key j)]
    have := ih _ acc _ pp' hb' hpp' ha'
    rw [SRef.append_append, Path.append_key, Path.append_nil] at this
    exact this

theorem initRd_rep : SRd.Rep g ν initRd g.storage := by
  intro V c Q r hQ
  cases c with
  | word P =>
    show ((LTm.obsW Q.toLTm).eval g ν : Option _) = _
    rw [LTm.eval_obsW, SPath.eval_toLTm, hQ]; rfl
  | len E =>
    show ((LTm.obsL Q.toLTm).eval g ν : Option _) = _
    rw [LTm.eval_obsL, SPath.eval_toLTm, hQ]; rfl
  | has V =>
    show ((Q.segs.hasFrom (.app0 (.root Q.r Q.hr)) .tt).eval g ν : Option _) = _
    unfold SPath.eval at hQ
    obtain ⟨pp, hpp, rfl⟩ := Option.map_eq_some_iff.1 hQ
    have := TSegs.hasFrom_eval g ν Q.segs (.app0 (.root Q.r Q.hr)) .tt (SRef.ofRoot Q.r Q.hr) pp
      rfl hpp (by show some true = _; rw [has_root])
    rw [this]
    simp only [SRef.ofRoot, SRef.append, Path.append_nil]
    rfl

theorem sto_find_findM {U : Ty} (st : Storage C) (r : SRef C U) :
    st.find r = (st.get r.hroot).findM r.path := by
  rw [Storage.find, SVal.find_eq_findM]

/-- **A storage term read as it is.** -/
theorem fbRd_rep {s : LTm C .st} {st : Storage C} (hs : (s.eval g ν : Option (Storage C)) = some st) :
    SRd.Rep g ν (fbRd s) st := by
  intro V c Q r hQ
  have hq : (Q.toLTm.eval g ν : Option (SRef C V)) = some r := by rw [SPath.eval_toLTm, hQ]
  cases c with
  | word P =>
    show ((LTm.orElse (.app2 .find s Q.toLTm) (.lit (PrimTy.dflt P))).eval g ν : Option _) = _
    rw [LTm.eval_orElse, LTm.eval_app2, hs, hq]
    show (((st.find r).bind fun v => some v.view).or (some (PrimTy.dflt P)) : Option P.Denote) =
      some (st.obs.word (.ref r))
    rw [Storage.obs_word_ref, SVal.obs_word, ← sto_find_findM]
    cases st.find r <;> rfl
  | len E =>
    show ((LTm.orElse (.app2 .len s Q.toLTm) (.nat 0)).eval g ν : Option _) = _
    rw [LTm.eval_orElse, LTm.eval_app2, hs, hq]
    show ((st.len r).or (some (uintOfNat 0)) : Option PrimTy.uint.Denote) =
      some (uintOfNat (st.obs.len (.ref r)))
    rw [Storage.obs_len_ref, SVal.obs_len, ← sto_find_findM]
    unfold Storage.len
    cases hf : st.find r with
    | none => rfl
    | some w =>
      cases w with
      | array e sh hn =>
        simp only [SVal.lenOf, SVal.view_array, uintOfNat, dif_pos hn]
        rfl
  | has V =>
    show ((LTm.orElse (.seq (.app2 .sfind s Q.toLTm) .tt) (.lit (p := .bool) false)).eval g ν :
      Option Bool) = _
    rw [LTm.eval_orElse, LTm.eval_seq, LTm.eval_app2, hs, hq]
    show (((st.find r).bind fun _ => some true).or (some false) :
      Option Bool) = some (st.obs.has (.ref r))
    rw [Storage.obs_has_ref, SVal.obs_has, ← sto_find_findM]
    cases st.find r <;> rfl

theorem CK.obsS_save {V U : Ty} (c : CK V) (o : TSto C) (pr : SRef C U) (v : TVal U)
    (qr : SRef C V) :
    c.obsS (o.save (.ref pr) v) qr = match SRef.strip? pr qr with
      | some r => c.obsV v r
      | none => c.obsS o qr := by
  have e : (ObsLoc.strip? (SLoc.ref pr) (SLoc.ref qr) : Option (Path U V)) = pr.strip? qr := rfl
  cases h : pr.strip? qr <;> cases c <;>
    simp only [CK.obsS, CK.obsV, CK.obsC, Obs.save, Comp.word, Comp.len, Comp.has, e, h]

/-- **A storage with a new value at `P`, read** (`Obs.save`). -/
theorem writeAt_rep {S : SRd C} {st st' : Storage C} {T : Ty} {P : SPath C T} {pr : SRef C T}
    {newR : VRd C T} {newT : TVal T} (hS : SRd.Rep g ν S st) (hP : P.eval g ν = some pr)
    (hn : VRd.Rep g ν newR newT) (h' : st'.obs = st.obs.save (.ref pr) newT) :
    SRd.Rep g ν (writeAt S P newR) st' := by
  intro V c Q qr hQ
  rw [h', CK.obsS_save]
  cases P with | mk rp hrp sp =>
  cases Q with | mk rq hrq sq =>
  simp only [SPath.eval, Option.map_eq_some_iff] at hP hQ
  obtain ⟨pp, hpp, rfl⟩ := hP
  obtain ⟨qp, hqp, rfl⟩ := hQ
  unfold writeAt
  by_cases h : rp = rq
  · subst h
    obtain rfl := root_inj rfl hrp hrq
    simp only [dif_pos rfl]
    show ((relSegs sp sq).toTerm _).eval g ν = _
    obtain ⟨ht, hr⟩ := relSegs_sound g ν sp sq hpp hqp
    rw [CTree.toTerm_eval g ν _ _ ht]
    have hs : SRef.strip? ⟨rp, hrp, pp⟩ ⟨rp, hrq, qp⟩ = Path.strip? pp qp := by
      simp only [SRef.strip?, dif_pos rfl]; rfl
    rw [hs]
    revert hr
    cases (relSegs sp sq).sel g ν <;> cases Path.strip? pp qp <;> intro hr
    · exact hS _ c _ _ (by simp only [SPath.eval, hqp]; rfl)
    · exact hr.elim
    · exact hr.elim
    · exact hn _ c _ _ hr
  · simp only [dif_neg h]
    rw [SRef.strip?_root_ne _ _ h]
    exact hS _ c _ _ (by simp only [SPath.eval, hqp]; rfl)


/-! ### A write returns where the location is there -/

theorem findM_of_saveM {T U : Ty} : (x : SVal T) → (p : Path T U) → {v : SVal U} → {x' : SVal T} →
    x.saveM p v = some x' → (x.findM p).isSome
  | x, .nil, _, _, _ => by cases x <;> rfl
  | .struct fs, .field hf p, v, x', h => by
    simp only [SVal.saveM, Option.bind_eq_bind, Option.bind_eq_some_iff] at h
    obtain ⟨z, hz, -⟩ := h
    simp only [SVal.findM]
    exact findM_of_saveM _ p hz
  | .array e sh hn, .at i p, v, x', h => by
    simp only [SVal.saveM] at h
    simp only [SVal.findM]
    split at h
    · rename_i x0 hx
      simp only [Option.bind_eq_bind, Option.bind_eq_some_iff] at h
      obtain ⟨z, hz, -⟩ := h
      exact findM_of_saveM x0 p hz
    · cases h
  | .fixed e, .atF i p, v, x', h => by
    simp only [SVal.saveM] at h
    simp only [SVal.findM]
    split at h
    · rename_i x0 hx
      simp only [Option.bind_eq_bind, Option.bind_eq_some_iff] at h
      obtain ⟨z, hz, -⟩ := h
      exact findM_of_saveM x0 p hz
    · cases h
  | .map m d, .key k p, v, x', h => by
    simp only [SVal.saveM] at h
    simp only [SVal.findM]
    split at h
    · rename_i x0 hx
      simp only [Option.bind_eq_bind, Option.bind_eq_some_iff] at h
      obtain ⟨z, hz, -⟩ := h
      exact findM_of_saveM x0 p hz
    · rename_i hx
      simp only [Option.bind_eq_bind, Option.bind_eq_some_iff] at h
      obtain ⟨z, hz, -⟩ := h
      exact findM_of_saveM d p hz

theorem Storage.save_isSome {U : Ty} (st : Storage C) (r : SRef C U) (v : SVal U) :
    (st.save r v).isSome = (st.find r).isSome := by
  rw [sto_find_findM]
  unfold Storage.save
  rw [SVal.save_eq_saveM]
  cases h : (st.get r.hroot).saveM r.path v with
  | none =>
    cases hf : (st.get r.hroot).findM r.path with
    | none => rfl
    | some y =>
      obtain ⟨x', hx'⟩ := SVal.saveM_of_findM _ _ hf v
      rw [hx'] at h; cases h
  | some x' =>
    have := findM_of_saveM _ _ h
    simp only [Option.bind_eq_bind, Option.bind_some, Option.isSome_some]
    exact this.symm

theorem has_obs (st : Storage C) {U : Ty} (r : SRef C U) :
    st.obs.has (.ref r) = (st.find r).isSome := by
  rw [Storage.obs_has_ref, SVal.obs_has, sto_find_findM]

theorem Storage.write_isSome {U : Ty} (st : Storage C) (r : SRef C U) (v : SVal U) :
    (st.write r v).isSome = st.obs.has (.ref r) := by
  rw [has_obs]
  unfold Storage.write
  split
  · exact Storage.save_isSome st r v
  · cases hf : st.find r with
    | none => rfl
    | some cur =>
      simp only [Option.bind_eq_bind, Option.bind_some, Storage.save_isSome, hf]


/-! ## What the eliminated terms stand for -/

/-- An eliminated storage stands for the term `t`: its term reads `t`, its
guard returns where `t` does, its reader reads what `t` reads to. -/
structure SFun.Rep (F : SFun C) (t : LTm C .st) : Prop where
  orig : (F.orig.eval g ν : Option (Storage C)) = t.eval g ν
  ok : (F.ok.eval g ν : Option Bool) = (t.eval g ν : Option (Storage C)).map fun _ => true
  rd : ∀ st, (t.eval g ν : Option (Storage C)) = some st → SRd.Rep g ν F.rd st

/-- An eliminated path stands for the term `t`. -/
def PRep {T : Ty} (e : Option (LTm C (.val .bool) × SPath C T)) (t : LTm C (.path T)) : Prop :=
  ∀ gd P, e = some (gd, P) →
    (gd.eval g ν : Option Bool) = (t.eval g ν : Option (SRef C T)).map (fun _ => true) ∧
      ∀ r, (t.eval g ν : Option (SRef C T)) = some r → P.eval g ν = some r

/-- An eliminated stored value stands for the term `t`. -/
def VRep {T : Ty} (e : Option (LTm C (.val .bool) × VRd C T)) (t : LTm C (.sv T)) : Prop :=
  ∀ gd V, e = some (gd, V) →
    (gd.eval g ν : Option Bool) = (t.eval g ν : Option (SVal T)).map (fun _ => true) ∧
      ∀ w, (t.eval g ν : Option (SVal T)) = some w → VRd.Rep g ν V w.obs

theorem LTm.eval_assert_some {c : LTm C (.val .bool)} {b : Bool}
    (hc : (c.eval g ν : Option Bool) = some b) :
    ((LTm.assert c).eval g ν : Option Bool) = if b then some true else none := by
  rw [LTm.eval_assert, hc]; cases b <;> rfl

/-! ### The storage operations' guards -/

theorem Storage.delete_isSome {U : Ty} (st : Storage C) (r : SRef C U) :
    (st.delete r).isSome = st.obs.has (.ref r) := by
  rw [has_obs]
  unfold Storage.delete
  cases hf : st.find r with
  | none => rfl
  | some cur => simp only [Option.bind_eq_bind, Option.bind_some, Storage.save_isSome, hf]

theorem len_obs {E : Ty} (st : Storage C) (r : SRef C (.ref (.array E))) {e : SVal _}
    (hf : st.find r = some e) : st.obs.len (.ref r) = (SVal.view e : ArrView E).n := by
  rw [Storage.obs_len_ref, SVal.obs_len, ← sto_find_findM, hf]; rfl

theorem Storage.push_isSome {E : Ty} (st : Storage C) (r : SRef C (.ref (.array E)))
    (f : SVal E → Option (SVal E)) (hf : ∀ x, (f x).isSome) :
    (st.push r f).isSome = (st.obs.has (.ref r) && decide (st.obs.len (.ref r) + 1 < 2 ^ 256)) := by
  rw [has_obs]
  unfold Storage.push
  cases h : st.find r with
  | none => rfl
  | some a =>
    rw [len_obs st r h]
    cases a with
    | array e sh hn =>
      obtain ⟨x, hx⟩ := Option.isSome_iff_exists.1 (hf (pushSlot _ sh.toList).1)
      simp only [Option.bind_eq_bind, Option.bind_some, SVal.view_array, hx, Option.isSome_some,
        Bool.true_and]
      split
      · rename_i h'
        rw [Storage.save_isSome, h, decide_eq_true h']; rfl
      · rename_i h'
        rw [decide_eq_false h']; rfl

theorem Storage.pushPlace_isSome {E : Ty} (st : Storage C) (r : SRef C (.ref (.array E))) :
    (st.pushPlace r).isSome = (st.obs.has (.ref r) && decide (st.obs.len (.ref r) + 1 < 2 ^ 256)) := by
  rw [← Option.isSome_map (f := (·.1)), Storage.pushPlace_fst]
  exact Storage.push_isSome st r some (fun _ => rfl)

theorem Storage.pop_isSome {E : Ty} (st : Storage C) (keep : Bool) (r : SRef C (.ref (.array E))) :
    (st.pop keep r).isSome = (st.obs.has (.ref r) && decide (0 < st.obs.len (.ref r))) := by
  rw [has_obs]
  unfold Storage.pop
  cases h : st.find r with
  | none => rfl
  | some a =>
    rw [len_obs st r h]
    cases a with
    | array e sh hn =>
      rename_i n
      simp only [Option.bind_eq_bind, Option.bind_some, SVal.view_array, Option.isSome_some,
        Bool.true_and]
      have hl : e.toList.length = n := SVec.length_toList e
      split
      · rename_i hr
        have : e.toList = [] := List.reverse_eq_nil_iff.1 hr
        rw [this] at hl
        subst hl
        rfl
      · rename_i last tl hr
        rw [Storage.save_isSome, h]
        have : 0 < n := by
          rw [← hl]
          exact List.length_pos_iff.2 fun he => by simp only [he, List.reverse_nil,
            reduceCtorEq] at hr
        rw [decide_eq_true this]; rfl


/-! ### The storage operations, eliminated -/

theorem guard_has {α : Type} {b : Bool} {x : Option α} (h : x.isSome = b) :
    (if b = true then some true else none) = x.map (fun _ => true) := by
  cases b <;> cases x <;> simp_all only [Option.isSome_none, Option.isSome_some, reduceCtorEq,
    if_true, if_false, Bool.false_eq_true, Option.map_none, Option.map_some]

theorem find_len_nil (o : TSto C) {E : Ty} (r : SRef C (.ref (.array E))) :
    (o.find (.ref r)).len .nil = o.len (.ref r) := by
  rw [Obs.find_len, SLoc.app_ref, SRef.append_nil]

theorem eval_save3 {T : Ty} (s : LTm C .st) (pt : LTm C (.path T)) (vt : LTm C (.sv T)) :
    ((LTm.app3 .save s pt vt).eval g ν : Option (Storage C)) =
      (s.eval g ν : Option (Storage C)).bind fun st => (pt.eval g ν : Option (SRef C T)).bind
        fun r => (vt.eval g ν : Option (SVal T)).bind fun w => st.write r w := rfl

theorem eval_push3 {E : Ty} (s : LTm C .st) (pt : LTm C (.path (.ref (.array E))))
    (vt : LTm C (.sv E)) :
    ((LTm.app3 .push s pt vt).eval g ν : Option (Storage C)) =
      (s.eval g ν : Option (Storage C)).bind fun st => (pt.eval g ν : Option (SRef C _)).bind
        fun r => (vt.eval g ν : Option (SVal E)).bind fun w => st.push r fun _ => some w.strip := by
  rw [LTm.eval_app3]
  cases (s.eval g ν : Option (Storage C)) <;> cases (pt.eval g ν : Option (SRef C _)) <;>
    cases (vt.eval g ν : Option (SVal E)) <;> first | rfl | exact Storage.push_none _ _

theorem rep_ok {S : SFun C} {s : LTm C .st} (hS : S.Rep g ν s) {st : Storage C}
    (hs : (s.eval g ν : Option (Storage C)) = some st) : (S.ok.eval g ν : Option Bool) = some true := by
  rw [hS.ok, hs]; rfl

theorem rep_ok_none {S : SFun C} {s : LTm C .st} (hS : S.Rep g ν s)
    (hs : (s.eval g ν : Option (Storage C)) = none) : (S.ok.eval g ν : Option Bool) = none := by
  rw [hS.ok, hs]; rfl

/-- `save(s, p, v)`, eliminated. -/
theorem SFun.save_rep {T : Ty} {S : SFun C} {s : LTm C .st} {pt : LTm C (.path T)}
    {vt : LTm C (.sv T)} {Pg : LTm C (.val .bool)} {P : SPath C T} {Vok : LTm C (.val .bool)}
    {V : VRd C T} (hS : S.Rep g ν s) (hP : PRep g ν (some (Pg, P)) pt)
    (hV : VRep g ν (some (Vok, V)) vt) :
    (S.save Pg P Vok V (.app3 .save s pt vt)).Rep g ν (.app3 .save s pt vt) := by
  obtain ⟨hPg, hPe⟩ := hP Pg P rfl
  obtain ⟨hVg, hVe⟩ := hV Vok V rfl
  refine ⟨rfl, ?_, ?_⟩
  · show (seqL S.ok (seqL Pg (seqL Vok (LTm.assert (S.rd (.has _) P)))) |>.eval g ν : Option Bool) = _
    rw [eval_save3]
    simp only [seqL_eval]
    cases hs : (s.eval g ν : Option (Storage C)) with
    | none => rw [rep_ok_none g ν hS hs]; rfl
    | some st =>
      rw [rep_ok g ν hS hs, hPg]
      cases hp : (pt.eval g ν : Option (SRef C T)) with
      | none => rfl
      | some r =>
        rw [hVg]
        cases hv : (vt.eval g ν : Option (SVal T)) with
        | none => rfl
        | some w =>
          simp only [Option.map_some, Option.bind_some]
          rw [LTm.eval_assert_some g ν (hS.rd st hs _ (.has _) P r (hPe r hp))]
          exact guard_has (Storage.write_isSome st r w)
  · intro st' ht
    rw [eval_save3] at ht
    simp only [Option.bind_eq_some_iff] at ht
    obtain ⟨st, hs, r, hp, w, hv, hw⟩ := ht
    refine writeAt_rep g ν (hS.rd st hs) (hPe r hp) ?_ (Storage.obs_write hw)
    intro V' c rest q hq
    rw [ovRS_rep g ν rest c ((hS.rd st hs).at g ν (hPe r hp)) (hVe w hv) (bnd_sto st r)
      (bnd_obs w) hq]
    cases c <;> rfl

/-- `delAt(s, p)`, eliminated. -/
theorem SFun.delAt_rep {T : Ty} {S : SFun C} {s : LTm C .st} {pt : LTm C (.path T)}
    {Pg : LTm C (.val .bool)} {P : SPath C T} (hS : S.Rep g ν s) (hP : PRep g ν (some (Pg, P)) pt) :
    (S.delAt Pg P (.app2 .delAt s pt)).Rep g ν (.app2 .delAt s pt) := by
  obtain ⟨hPg, hPe⟩ := hP Pg P rfl
  have ev : ((LTm.app2 .delAt s pt).eval g ν : Option (Storage C)) =
      (s.eval g ν : Option (Storage C)).bind fun st =>
        (pt.eval g ν : Option (SRef C T)).bind fun r => st.delete r := by
    rw [LTm.eval_app2]
    cases (s.eval g ν : Option (Storage C)) <;> cases (pt.eval g ν : Option (SRef C T)) <;> rfl
  refine ⟨rfl, ?_, ?_⟩
  · show (seqL S.ok (seqL Pg (LTm.assert (S.rd (.has _) P))) |>.eval g ν : Option Bool) = _
    rw [ev]
    simp only [seqL_eval]
    cases hs : (s.eval g ν : Option (Storage C)) with
    | none => rw [rep_ok_none g ν hS hs]; rfl
    | some st =>
      rw [rep_ok g ν hS hs, hPg]
      cases hp : (pt.eval g ν : Option (SRef C T)) with
      | none => rfl
      | some r =>
        simp only [Option.map_some, Option.bind_some]
        rw [LTm.eval_assert_some g ν (hS.rd st hs _ (.has _) P r (hPe r hp))]
        exact guard_has (Storage.delete_isSome st r)
  · intro st' ht
    rw [ev] at ht
    simp only [Option.bind_eq_some_iff] at ht
    obtain ⟨st, hs, r, hp, hw⟩ := ht
    refine writeAt_rep g ν (hS.rd st hs) (hPe r hp) ?_ (Storage.obs_delete hw)
    intro V' c rest q hq
    rw [delRS_rep g ν rest c ((hS.rd st hs).at g ν (hPe r hp)) (bnd_sto st r) hq]
    cases c <;> rfl

theorem maxLen_eval : ((maxLen : LTm C (.val .uint)).eval g ν : Option _) =
    some (uintOfNat (2 ^ 256 - 1)) := rfl

theorem lt_maxLen_eval {L : LTm C (.val .uint)} {n : Nat}
    (hL : (L.eval g ν : Option PrimTy.uint.Denote) = some (uintOfNat n)) (hn : n < 2 ^ 256) :
    ((LTm.lt L maxLen).eval g ν : Option Bool) = some (decide (n + 1 < 2 ^ 256)) := by
  rw [LTm.eval_lt_some g ν hL (maxLen_eval g ν), uintOfNat_val hn,
    uintOfNat_val (by decide)]
  exact congrArg some (decide_eq_decide.2 (by omega))

/-- `push(s, p, v)`, eliminated. -/
theorem SFun.push_rep {E : Ty} {S : SFun C} {s : LTm C .st} {pt : LTm C (.path (.ref (.array E)))}
    {vt : LTm C (.sv E)} {Pg : LTm C (.val .bool)} {P : SPath C (.ref (.array E))}
    {Vok : LTm C (.val .bool)} {V : VRd C E} (hS : S.Rep g ν s) (hP : PRep g ν (some (Pg, P)) pt)
    (hV : VRep g ν (some (Vok, V)) vt) :
    (S.push Pg P Vok V (.app3 .push s pt vt)).Rep g ν (.app3 .push s pt vt) := by
  obtain ⟨hPg, hPe⟩ := hP Pg P rfl
  obtain ⟨hVg, hVe⟩ := hV Vok V rfl
  refine ⟨rfl, ?_, ?_⟩
  · show (seqL S.ok (seqL Pg (seqL Vok (seqL (LTm.assert (S.rd (.has _) P))
      (LTm.assert (.lt (S.rd (.len _) P) maxLen))))) |>.eval g ν : Option Bool) = _
    rw [eval_push3]
    simp only [seqL_eval]
    cases hs : (s.eval g ν : Option (Storage C)) with
    | none => rw [rep_ok_none g ν hS hs]; rfl
    | some st =>
      rw [rep_ok g ν hS hs, hPg]
      cases hp : (pt.eval g ν : Option (SRef C _)) with
      | none => rfl
      | some r =>
        rw [hVg]
        cases hv : (vt.eval g ν : Option (SVal E)) with
        | none => rfl
        | some w =>
          simp only [Option.map_some, Option.bind_some]
          rw [LTm.eval_assert_some g ν (hS.rd st hs _ (.has _) P r (hPe r hp))]
          have hw := Storage.push_isSome st r (fun _ => some w.strip) (fun _ => rfl)
          show (if st.obs.has (.ref r) = true then some true else none).bind _ = _
          cases hh : st.obs.has (.ref r)
          · rw [hh, Bool.false_and] at hw
            rw [show (st.push r fun _ => some w.strip) = none from
              Option.not_isSome_iff_eq_none.1 (by rw [hw]; decide)]
            rfl
          · rw [hh, Bool.true_and] at hw
            simp only [if_true, Option.bind_some]
            rw [LTm.eval_assert_some g ν (lt_maxLen_eval g ν
              (hS.rd st hs _ (.len _) P r (hPe r hp)) (obs_len_lt st r))]
            exact guard_has hw
  · intro st' ht
    rw [eval_push3] at ht
    simp only [Option.bind_eq_some_iff] at ht
    obtain ⟨st, hs, r, hp, w, hv, hw⟩ := ht
    have hb : st.obs.len (.ref r) + 1 < 2 ^ 256 := by
      have := Storage.push_isSome st r (fun _ => some w.strip) (fun _ => rfl)
      rw [hw, Option.isSome_some] at this
      have := this.symm
      simp only [Bool.and_eq_true, decide_eq_true_eq] at this
      exact this.2
    refine writeAt_rep g ν (hS.rd st hs) (hPe r hp) ?_ (Storage.obs_push hw)
    rw [SVal.obs_strip]
    refine pushRd_rep g ν ((hS.rd st hs).at g ν (hPe r hp)) ?_
      (by rw [find_len_nil]; exact hS.rd st hs _ (.len _) P r (hPe r hp))
      (by rw [find_len_nil]; exact hb)
    intro V' c rest q hq
    rw [stripRS_rep g ν rest c (hVe w hv) (bnd_obs w) hq]
    cases c <;> rfl


theorem lt0_eval {L : LTm C (.val .uint)} {n : Nat}
    (hL : (L.eval g ν : Option PrimTy.uint.Denote) = some (uintOfNat n)) (hn : n < 2 ^ 256) :
    ((LTm.lt (.nat 0) L).eval g ν : Option Bool) = some (decide (0 < n)) := by
  rw [LTm.eval_lt_some g ν (LTm.eval_nat g ν 0) hL, uintOfNat_val hn, uintOfNat_val (by decide)]
  exact congrArg some (decide_eq_decide.2 (by omega))

/-- An operation on the array at `p` whose guard is the array there and a
condition `cond` on its length, read as `newT` of the array. -/
theorem SFun.arrOp_rep {E : Ty} {S : SFun C} {s : LTm C .st} {pt : LTm C (.path (.ref (.array E)))}
    {Pg : LTm C (.val .bool)} {P : SPath C (.ref (.array E))} {t : LTm C .st}
    (f : Storage C → SRef C (.ref (.array E)) → Option (Storage C)) (cond : Nat → Bool)
    (condT : LTm C (.val .uint) → LTm C (.val .bool))
    (newR : VRd C (.ref (.array E)) → LTm C (.val .uint) → VRd C (.ref (.array E)))
    (newT : TVal (.ref (.array E)) → TVal (.ref (.array E)))
    (hS : S.Rep g ν s) (hP : PRep g ν (some (Pg, P)) pt)
    (ev : (t.eval g ν : Option (Storage C)) =
      (s.eval g ν : Option (Storage C)).bind fun st => (pt.eval g ν : Option (SRef C _)).bind
        fun r => f st r)
    (hc : ∀ (L : LTm C (.val .uint)) (n : Nat), (L.eval g ν : Option PrimTy.uint.Denote) =
      some (uintOfNat n) → n < 2 ^ 256 → ((condT L).eval g ν : Option Bool) = some (cond n))
    (hsome : ∀ (st : Storage C) (r : SRef C (.ref (.array E))), (f st r).isSome = (st.obs.has (.ref r) && cond (st.obs.len (.ref r))))
    (hobs : ∀ (st : Storage C) (r : SRef C (.ref (.array E))) (st' : Storage C), f st r = some st' → st'.obs = st.obs.save (.ref r) (newT (st.obs.find (.ref r))))
    (hnew : ∀ (st : Storage C) (r : SRef C (.ref (.array E))) (a : VRd C (.ref (.array E))) (L : LTm C (.val .uint)),
      VRd.Rep g ν a (st.obs.find (.ref r)) →
      (L.eval g ν : Option PrimTy.uint.Denote) = some (uintOfNat (st.obs.len (.ref r))) →
      cond (st.obs.len (.ref r)) = true → VRd.Rep g ν (newR a L) (newT (st.obs.find (.ref r)))) :
    (⟨seqL S.ok (seqL Pg (seqL (LTm.assert (S.rd (.has _) P)) (LTm.assert (condT (S.rd (.len _) P))))),
      writeAt S.rd P (newR (SRd.at S.rd P) (S.rd (.len _) P)), t⟩ : SFun C).Rep g ν t := by
  obtain ⟨hPg, hPe⟩ := hP Pg P rfl
  refine ⟨rfl, ?_, ?_⟩
  · show (seqL S.ok (seqL Pg (seqL (LTm.assert (S.rd (.has _) P))
      (LTm.assert (condT (S.rd (.len _) P))))) |>.eval g ν : Option Bool) = _
    rw [ev]
    simp only [seqL_eval]
    cases hs : (s.eval g ν : Option (Storage C)) with
    | none => rw [rep_ok_none g ν hS hs]; rfl
    | some st =>
      rw [rep_ok g ν hS hs, hPg]
      cases hp : (pt.eval g ν : Option (SRef C _)) with
      | none => rfl
      | some r =>
        simp only [Option.map_some, Option.bind_some]
        rw [LTm.eval_assert_some g ν (hS.rd st hs _ (.has _) P r (hPe r hp))]
        have hw := hsome st r
        show (if st.obs.has (.ref r) = true then some true else none).bind _ = _
        cases hh : st.obs.has (.ref r)
        · rw [hh, Bool.false_and] at hw
          rw [show f st r = none from Option.not_isSome_iff_eq_none.1 (by rw [hw]; decide)]
          rfl
        · rw [hh, Bool.true_and] at hw
          simp only [if_true, Option.bind_some]
          rw [LTm.eval_assert_some g ν (hc _ _ (hS.rd st hs _ (.len _) P r (hPe r hp))
            (obs_len_lt st r))]
          exact guard_has hw
  · intro st' ht
    rw [ev] at ht
    simp only [Option.bind_eq_some_iff] at ht
    obtain ⟨st, hs, r, hp, hw⟩ := ht
    have hcond := hsome st r
    rw [hw, Option.isSome_some] at hcond
    have hcond' := hcond.symm
    simp only [Bool.and_eq_true] at hcond'
    exact writeAt_rep g ν (hS.rd st hs) (hPe r hp)
      (hnew st r _ _ ((hS.rd st hs).at g ν (hPe r hp)) (hS.rd st hs _ (.len _) P r (hPe r hp))
        hcond'.2) (hobs st r st' hw)

theorem SFun.extend_rep {E : Ty} {S : SFun C} {s : LTm C .st} {pt : LTm C (.path (.ref (.array E)))}
    {Pg : LTm C (.val .bool)} {P : SPath C (.ref (.array E))} {t : LTm C .st}
    (f : Storage C → SRef C (.ref (.array E)) → Option (Storage C))
    (hS : S.Rep g ν s) (hP : PRep g ν (some (Pg, P)) pt)
    (ev : (t.eval g ν : Option (Storage C)) =
      (s.eval g ν : Option (Storage C)).bind fun st => (pt.eval g ν : Option (SRef C _)).bind
        fun r => f st r)
    (hsome : ∀ st r, (f st r).isSome =
      (st.obs.has (.ref r) && decide (st.obs.len (.ref r) + 1 < 2 ^ 256)))
    (hobs : ∀ st r st', f st r = some st' → st'.obs = st.obs.extend (.ref r)) :
    (S.extend Pg P t).Rep g ν t := by
  refine SFun.arrOp_rep g ν f (fun n => decide (n + 1 < 2 ^ 256)) (fun L => .lt L maxLen)
    extendRd TVal.extendA hS hP ev (fun L n hL hn => lt_maxLen_eval g ν hL hn) hsome
    (fun st r st' h => hobs st r st' h) ?_
  intro st r a L ha hL hc
  exact extendRd_rep g ν ha (by rw [find_len_nil]; exact hL)
    (by rw [find_len_nil]; simpa only [decide_eq_true_eq] using hc)

theorem SFun.pop_rep (keep : Bool) {E : Ty} {S : SFun C} {s : LTm C .st}
    {pt : LTm C (.path (.ref (.array E)))} {Pg : LTm C (.val .bool)} {P : SPath C (.ref (.array E))}
    {t : LTm C .st} (hS : S.Rep g ν s) (hP : PRep g ν (some (Pg, P)) pt)
    (ev : (t.eval g ν : Option (Storage C)) =
      (s.eval g ν : Option (Storage C)).bind fun st => (pt.eval g ν : Option (SRef C _)).bind
        fun r => st.pop keep r) :
    (S.pop keep Pg P t).Rep g ν t := by
  refine SFun.arrOp_rep g ν (fun st r => st.pop keep r) (fun n => decide (0 < n))
    (fun L => .lt (.nat 0) L) (popRd keep) (TVal.popA keep) hS hP ev
    (fun L n hL hn => lt0_eval g ν hL hn) (fun st r => Storage.pop_isSome st keep r)
    (fun st r st' h => Storage.obs_pop h) ?_
  intro st r a L ha hL hc
  exact popRd_rep g ν keep ha (bnd_sto st r) (by rw [find_len_nil]; exact hL)
    (by rw [find_len_nil]; simpa only [decide_eq_true_eq] using hc)


/-! ### Paths and stored values, eliminated -/

theorem SPath.eval_snoc_index {R : RefTy} {k : PrimTy} {V : Ty} (it : IndexTy R k V)
    {Q : SPath C (.ref R)} {r : SRef C (.ref R)} (hQ : Q.eval g ν = some r)
    {ei : LTm C (.val k)} {j : k.Denote} (hj : (ei.eval g ν : Option _) = some j) :
    (Q.snoc (TSegs.ofIndex it ei)).eval g ν = some (r.index it j) := by
  rw [SPath.eval_snoc, hQ, Option.bind_some, TSegs.eval_ofIndex, hj]; rfl

theorem atT_eq {R : RefTy} {k : PrimTy} {V : Ty} (st : Storage C) (it : IndexTy R k V)
    (r : SRef C (.ref R)) (j : k.Denote) :
    st.atT it r j = (st.checkIndex r it j).map fun _ => r.index it j := by
  unfold Storage.atT
  cases st.checkIndex r it j <;> rfl

/-- The guard of a checked index returns exactly where the check passes. -/
theorem boundG_eval {R : RefTy} {k : PrimTy} {V : Ty} (it : IndexTy R k V) (rd : SRd C)
    (st : Storage C) (hrd : SRd.Rep g ν rd st) {Q : SPath C (.ref R)} {r : SRef C (.ref R)}
    (hQ : Q.eval g ν = some r) {ei : LTm C (.val k)} {j : k.Denote}
    (hj : (ei.eval g ν : Option _) = some j) {w : SVal (.ref R)} (hw : st.find r = some w) :
    ((boundG it rd Q ei).eval g ν : Option Bool) =
      (Storage.inBounds it j w).map fun _ => true := by
  cases it with
  | map => rfl
  | arr a =>
    cases a with
    | dyn =>
      show ((LTm.assert (.lt ei (rd (.len _) Q))).eval g ν : Option Bool) = _
      rw [LTm.eval_assert_some g ν (LTm.eval_lt_some g ν hj (hrd _ (.len _) Q r hQ))]
      cases w with
      | array e sh hn =>
        rename_i n
        have hl : st.obs.len (.ref r) = n := len_obs st r hw
        show _ = (if j.1.toNat < n then some () else none).map _
        rw [show (CK.len _).obsS st.obs r = uintOfNat (st.obs.len (.ref r)) from rfl, hl,
          idx_lt_iff hn]
        by_cases h : j.1.toNat < n
        · rw [if_pos h, decide_eq_true h]; rfl
        · rw [if_neg h, decide_eq_false h]; rfl
    | fixed =>
      rename_i n
      show ((LTm.assert (.ltNat ei n)).eval g ν : Option Bool) = _
      rw [LTm.eval_assert_some g ν (LTm.eval_ltNat g ν n hj)]
      show _ = (if j.1.toNat < n then some () else none).map _
      by_cases h : j.1.toNat < n
      · rw [if_pos h, decide_eq_true h]; rfl
      · rw [if_neg h, decide_eq_false h]; rfl

/-- `q[i]` checked against a storage, eliminated. -/
theorem pathAtIn_core {R : RefTy} {k : PrimTy} {V : Ty} (it : IndexTy R k V) (S : SFun C)
    (st? : Option (Storage C)) (hok : (S.ok.eval g ν : Option Bool) = st?.map (fun _ => true))
    (hrd : ∀ st, st? = some st → SRd.Rep g ν S.rd st)
    {e : Option (LTm C (.val .bool) × SPath C (.ref R))} {q : LTm C (.path (.ref R))}
    (hP : PRep g ν e q) {ei i : LTm C (.val k)}
    (hi : (ei.eval g ν : Option k.Denote) = i.eval g ν) {t : LTm C (.path V)}
    (ev : (t.eval g ν : Option (SRef C V)) = st?.bind fun st =>
      (q.eval g ν : Option (SRef C _)).bind fun r => (i.eval g ν : Option k.Denote).bind
        fun j => st.atT it r j) :
    PRep g ν (pathAtIn it S e ei) t := by
  intro gd P' he
  cases e with
  | none => cases he
  | some x =>
    obtain ⟨g0, Q⟩ := x
    simp only [pathAtIn, Option.map_some, Option.some.injEq, Prod.mk.injEq] at he
    obtain ⟨rfl, rfl⟩ := he
    obtain ⟨hPg, hPe⟩ := hP g0 Q rfl
    refine ⟨?_, ?_⟩
    · rw [ev]
      simp only [seqL_eval]
      cases hs : st? with
      | none => rw [hs] at hok; rw [hok]; rfl
      | some st =>
        rw [hs] at hok hrd; rw [hok, hPg]
        cases hq : (q.eval g ν : Option (SRef C _)) with
        | none => rfl
        | some r =>
          rw [hi]
          cases hj : (i.eval g ν : Option k.Denote) with
          | none => rfl
          | some j =>
            simp only [Option.map_some, Option.bind_some]
            rw [LTm.eval_assert_some g ν (hrd st rfl _ (.has _) Q r (hPe r hq)), atT_eq]
            show (if st.obs.has (.ref r) = true then some true else none).bind _ = _
            rw [has_obs]
            unfold Storage.checkIndex
            cases hf : st.find r with
            | none => rfl
            | some w =>
              simp only [Option.isSome_some, if_true, Option.bind_some]
              rw [boundG_eval g ν it S.rd st (hrd st rfl) (hPe r hq) (hi.trans hj) hf]
              show _ = Option.map _ (Option.map _ ((some w).bind _))
              rw [Option.bind_some]
              cases Storage.inBounds it j w <;> rfl
    · intro r' ht
      rw [ev] at ht
      simp only [Option.bind_eq_some_iff, atT_eq, Option.map_eq_some_iff] at ht
      obtain ⟨st, -, r, hq, j, hj, -, -, rfl⟩ := ht
      exact SPath.eval_snoc_index g ν it (hPe r hq) (hi.trans hj)

/-- `q[q.length]` in a storage, eliminated. -/
theorem pathNext_core {E : Ty} (S : SFun C) (st? : Option (Storage C))
    (hok : (S.ok.eval g ν : Option Bool) = st?.map (fun _ => true))
    (hrd : ∀ st, st? = some st → SRd.Rep g ν S.rd st)
    {e : Option (LTm C (.val .bool) × SPath C (.ref (.array E)))}
    {q : LTm C (.path (.ref (.array E)))} (hP : PRep g ν e q) {t : LTm C (.path E)}
    (ev : (t.eval g ν : Option (SRef C E)) = st?.bind fun st =>
      (q.eval g ν : Option (SRef C _)).bind fun r => st.nextT r) :
    PRep g ν (pathNext S e) t := by
  intro gd P' he
  cases e with
  | none => cases he
  | some x =>
    obtain ⟨g0, Q⟩ := x
    simp only [pathNext, Option.map_some, Option.some.injEq, Prod.mk.injEq] at he
    obtain ⟨rfl, rfl⟩ := he
    obtain ⟨hPg, hPe⟩ := hP g0 Q rfl
    refine ⟨?_, ?_⟩
    · rw [ev]
      simp only [seqL_eval]
      cases hs : st? with
      | none => rw [hs] at hok; rw [hok]; rfl
      | some st =>
        rw [hs] at hok hrd; rw [hok, hPg]
        cases hq : (q.eval g ν : Option (SRef C _)) with
        | none => rfl
        | some r =>
          simp only [Option.map_some, Option.bind_some]
          rw [LTm.eval_assert_some g ν (hrd st rfl _ (.has _) Q r (hPe r hq))]
          show (if st.obs.has (.ref r) = true then some true else none) = _
          rw [has_obs]
          unfold Storage.nextT
          cases st.find r <;> rfl
    · intro r' ht
      rw [ev] at ht
      simp only [Option.bind_eq_some_iff] at ht
      obtain ⟨st, hs, r, hq, ht⟩ := ht
      unfold Storage.nextT at ht
      rw [Option.map_eq_some_iff] at ht
      obtain ⟨w, hw, rfl⟩ := ht
      cases w with
      | array el sh hn =>
        rename_i n
        have hlen := hrd st hs _ (.len _) Q r (hPe r hq)
        rw [SPath.eval_snoc, hPe r hq, Option.bind_some, TSegs.eval_at, hlen]
        show some (r.append (.at (uintOfNat (st.obs.len (.ref r))) .nil)) = _
        rw [len_obs st r hw, uintOfNat_eq_lenU (n := (SVal.array el sh hn).view.n) hn, SRef.index,
          Path.index_dyn]

/-- A word stored, eliminated. -/
theorem sval_rep {p : PrimTy} {x ex : LTm C (.val p)}
    (hx : (ex.eval g ν : Option p.Denote) = x.eval g ν) :
    VRep g ν (some (seqL ex .tt, svalRd ex)) (.app1 .sval x) := by
  intro gd V he
  simp only [Option.some.injEq, Prod.mk.injEq] at he
  obtain ⟨rfl, rfl⟩ := he
  refine ⟨?_, ?_⟩
  · rw [seqL_eval, hx, LTm.eval_app1]
    cases (x.eval g ν : Option p.Denote) <;> rfl
  · intro w hw
    rw [LTm.eval_app1] at hw
    cases hxe : (x.eval g ν : Option p.Denote) with
    | none => rw [hxe] at hw; cases hw
    | some v =>
      rw [hxe] at hw; cases hw
      exact svalRd_rep g ν (hx.trans hxe)

/-- Fresh allocation's symbolic reader agrees with its stored value. -/
theorem newArr_rep (R : RefTy) (h : R.newArrOk = true) {x ex : LTm C (.val .uint)}
    (hx : ex.eval g ν = x.eval g ν) :
    VRep g ν (some (seqL ex .tt, newArrRd R h ex)) (.app1 (.newArr h) x) := by
  intro gd V he
  simp only [Option.some.injEq, Prod.mk.injEq] at he
  obtain ⟨rfl, rfl⟩ := he
  refine ⟨?_, ?_⟩
  · rw [seqL_eval, hx, LTm.eval_app1]
    cases (x.eval g ν : Option PrimTy.uint.Denote) <;> rfl
  · intro w hw
    rw [LTm.eval_app1] at hw
    cases hxe : (x.eval g ν : Option PrimTy.uint.Denote) with
    | none => rw [hxe] at hw; cases hw
    | some v =>
      rw [hxe] at hw
      cases hw
      exact newArrRd_rep g ν R h ex v (hx.trans hxe)

/-- A subtree of a storage, eliminated. -/
theorem sfind_rep {T : Ty} {S : SFun C} {s : LTm C .st} (hS : S.Rep g ν s)
    {e : Option (LTm C (.val .bool) × SPath C T)} {q : LTm C (.path T)} (hP : PRep g ν e q) :
    VRep g ν (e.map fun x =>
      (seqL (SFun.ok S) (seqL x.1 (LTm.assert (SFun.rd S (.has _) x.2))), SRd.at (SFun.rd S) x.2))
      (.app2 .sfind s q) := by
  intro gd V he
  cases e with
  | none => cases he
  | some x =>
    obtain ⟨g0, Q⟩ := x
    simp only [Option.map_some, Option.some.injEq, Prod.mk.injEq] at he
    obtain ⟨rfl, rfl⟩ := he
    obtain ⟨hPg, hPe⟩ := hP g0 Q rfl
    have ev : ((LTm.app2 .sfind s q).eval g ν : Option (SVal T)) =
        (s.eval g ν : Option (Storage C)).bind fun st =>
          (q.eval g ν : Option (SRef C T)).bind fun r => st.find r := by
      rw [LTm.eval_app2]
      cases (s.eval g ν : Option (Storage C)) <;> cases (q.eval g ν : Option (SRef C T)) <;> rfl
    refine ⟨?_, ?_⟩
    · rw [ev]
      simp only [seqL_eval]
      cases hs : (s.eval g ν : Option (Storage C)) with
      | none => rw [rep_ok_none g ν hS hs]; rfl
      | some st =>
        rw [rep_ok g ν hS hs, hPg]
        cases hq : (q.eval g ν : Option (SRef C T)) with
        | none => rfl
        | some r =>
          simp only [Option.map_some, Option.bind_some]
          rw [LTm.eval_assert_some g ν (hS.rd st hs _ (.has _) Q r (hPe r hq))]
          show (if st.obs.has (.ref r) = true then some true else none) = _
          rw [has_obs]
          cases st.find r <;> rfl
    · intro w hw
      rw [ev] at hw
      simp only [Option.bind_eq_some_iff] at hw
      obtain ⟨st, hs, r, hq, hf⟩ := hw
      rw [← Storage.obs_find_some hf]
      exact (hS.rd st hs).at g ν (hPe r hq)

end Decide

end Solidity
