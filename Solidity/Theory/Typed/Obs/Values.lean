import Solidity.Theory.Typed.Obs.Paths

/-!
# Observations of values and storages

A typed value and a storage as their observations, one component, a read
step by step, and the bridge of a delete, a strip, a copy.

A piece of `Theory/Typed/Obs.lean`, whose docstring describes the whole.
-/

namespace Solidity

open Semantics (structDef lookupBy setBy)

/-! ## A typed value as its observations -/

/-- The word a read finds: the default where nothing is there. -/
def SVal.wordOf {P : PrimTy} : Option (SVal (.prim P)) → P.Denote
  | some w => SVal.view w
  | none => PrimTy.dflt P

/-- The live length a read finds: `0` where nothing is there. -/
def SVal.lenOf {E : Ty} : Option (SVal (.ref (.array E))) → Nat
  | some w => (SVal.view w : ArrView E).n
  | none => 0

/-- A value that may not be there, read below. -/
def SVal.obsOpt {T : Ty} (x : Option (SVal T)) : TVal T :=
  ⟨fun r => SVal.wordOf (x.bind (·.findM r)), fun r => SVal.lenOf (x.bind (·.findM r)),
    fun r => (x.bind (·.findM r)).isSome⟩

/-- **A typed value as its observations.** -/
def SVal.obs {T : Ty} (v : SVal T) : TVal T := SVal.obsOpt (some v)

theorem SVal.obs_word {T : Ty} (v : SVal T) {P : PrimTy} (r : Path T (.prim P)) :
    v.obs.word r = SVal.wordOf (v.findM r) := rfl
theorem SVal.obs_len {T : Ty} (v : SVal T) {E : Ty} (r : Path T (.ref (.array E))) :
    v.obs.len r = SVal.lenOf (v.findM r) := rfl
theorem SVal.obs_has {T : Ty} (v : SVal T) {U : Ty} (r : Path T U) :
    v.obs.has r = (v.findM r).isSome := rfl

/-- What a value holds at `p`, read below. -/
theorem SVal.obs_find {T U : Ty} (v : SVal T) (p : Path T U) : v.obs.find p = SVal.obsOpt (v.findM p) := by
  apply Obs.ext <;> intro _ r <;>
    simp only [Obs.find, SVal.obs, SVal.obsOpt, Option.bind_some, ObsLoc.app_path, SVal.findM_append]

/-- **`findOnSave`, the bridge**: a typed save, read, is the Theory's. -/
theorem SVal.obs_saveM {T U : Ty} {x x' : SVal T} {p : Path T U} {v : SVal U}
    (h : x.saveM p v = some x') : x'.obs = x.obs.save p v.obs := by
  have key : ∀ {W : Ty} (q : Path T W), Path.strip? p q = none →
      (x'.findM q).isSome = (x.findM q).isSome ∧
      (∀ {E : Ty} (hW : W = .ref (.array E)), SVal.lenOf (hW ▸ x'.findM q) = SVal.lenOf (hW ▸ x.findM q)) ∧
      (∀ {P : PrimTy} (hW : W = .prim P), hW ▸ x'.findM q = hW ▸ x.findM q) := by
    intro W q hq
    rcases Path.strip?_none p q hq with hd | ⟨r, hr, rfl⟩
    · have e := SVal.findM_saveM_diverges hd x v h
      exact ⟨by rw [e], fun _ => by rw [e], fun _ => by rw [e]⟩
    · obtain ⟨y, y', hy, hy', hx'⟩ := SVal.saveM_append x q r v h
      have hf : x'.findM q = some y' := SVal.findM_saveM x q y' hx'
      refine ⟨by rw [hf, hy]; rfl, fun hW => ?_, fun hW => ?_⟩
      · subst hW
        cases r with
        | nil => exact absurd Path.labels_nil hr
        | «at» i r => rw [hf, hy]; exact SVal.saveM_at_n hy'
      · subst hW
        cases r with
        | nil => exact absurd Path.labels_nil hr
  apply Obs.ext
  · intro P q
    simp only [Obs.save, ObsLoc.strip?_path]
    split
    · rename_i r hr
      rw [Path.eq_of_strip? p q hr]
      simp only [SVal.obs_word, SVal.findM_append, SVal.findM_saveM x p v h, Option.bind_some]
    · rename_i hr
      simp only [SVal.obs_word, (key q hr).2.2 rfl]
  · intro E q
    simp only [Obs.save, ObsLoc.strip?_path]
    split
    · rename_i r hr
      rw [Path.eq_of_strip? p q hr]
      simp only [SVal.obs_len, SVal.findM_append, SVal.findM_saveM x p v h, Option.bind_some]
    · rename_i hr
      exact (key q hr).2.1 rfl
  · intro W q
    simp only [Obs.save, ObsLoc.strip?_path]
    split
    · rename_i r hr
      rw [Path.eq_of_strip? p q hr]
      simp only [SVal.obs_has, SVal.findM_append, SVal.findM_saveM x p v h, Option.bind_some]
    · rename_i hr
      exact (key q hr).1

theorem SVal.obsOpt_find {T U : Ty} (x : Option (SVal T)) (p : Path T U) :
    (SVal.obsOpt x).find p = SVal.obsOpt (x.bind (·.findM p)) := by
  cases x with
  | none => rfl
  | some v => exact SVal.obs_find v p

/-! ## A storage as its observations -/

/-- **A typed storage as its observations**: at a state variable's path what
the value there shows, a dangling location not there. -/
def Storage.obs {C : Contract} (st : Storage C) : TSto C :=
  ⟨fun l => match l with
     | .ref r => (st.get r.hroot).obs.word r.path
     | .dangling _ _ => PrimTy.dflt _,
   fun l => match l with
     | .ref r => (st.get r.hroot).obs.len r.path
     | .dangling _ _ => 0,
   fun l => match l with
     | .ref r => (st.get r.hroot).obs.has r.path
     | .dangling _ _ => false⟩

namespace Storage

variable {C : Contract}

theorem obs_word_ref (st : Storage C) {P : PrimTy} (r : SRef C (.prim P)) :
    st.obs.word (.ref r) = (st.get r.hroot).obs.word r.path := rfl
theorem obs_len_ref (st : Storage C) {E : Ty} (r : SRef C (.ref (.array E))) :
    st.obs.len (.ref r) = (st.get r.hroot).obs.len r.path := rfl
theorem obs_has_ref (st : Storage C) {U : Ty} (r : SRef C U) :
    st.obs.has (.ref r) = (st.get r.hroot).obs.has r.path := rfl

/-- What a storage holds at `r`, read below. -/
theorem obs_find {U : Ty} (st : Storage C) (r : SRef C U) :
    st.obs.find (.ref r) = SVal.obsOpt (st.find r) := by
  rw [Storage.find, SVal.find_eq_findM, ← SVal.obs_find]
  rfl

/-- The storage read at a root: the value there. -/
theorem obs_find_root (st : Storage C) (n : Name) {T : Ty} (hn : C.rootType n = some T) :
    st.obs.find (.ref (SRef.ofRoot n hn)) = (st.get hn).obs := by
  rw [obs_find, Storage.find, SVal.find_eq_findM]
  cases st.get hn <;> rfl

/-- Two storages that agree at every root agree. -/
theorem obs_ext {o : TSto C} (st : Storage C)
    (h : ∀ (n : Name) {T : Ty} (hn : C.rootType n = some T),
      (st.get hn).obs = o.find (.ref (SRef.ofRoot n hn)))
    (hw : ∀ {P : PrimTy} (U : Ty) (p : Path U (.prim P)), o.word (.dangling U p) = PrimTy.dflt P)
    (hl : ∀ {E : Ty} (U : Ty) (p : Path U (.ref (.array E))), o.len (.dangling U p) = 0)
    (hh : ∀ {V : Ty} (U : Ty) (p : Path U V), o.has (.dangling U p) = false) : st.obs = o := by
  have e : ∀ {W : Ty} (q : SRef C W),
      (SLoc.ref q : SLoc C W) = ObsLoc.app (SLoc.ref (SRef.ofRoot q.root q.hroot)) q.path := by
    intro W q
    rcases q with ⟨n, hn, qp⟩
    show _ = SLoc.ref ⟨n, hn, Path.nil.append qp⟩
    rw [Path.append_nil]
  apply Obs.ext
  · intro P q
    cases q with
    | ref q => rw [obs_word_ref, h, e q]; rfl
    | dangling U p => exact (hw U p).symm
  · intro E q
    cases q with
    | ref q => rw [obs_len_ref, h, e q]; rfl
    | dangling U p => exact (hl U p).symm
  · intro V q
    cases q with
    | ref q => rw [obs_has_ref, h, e q]; rfl
    | dangling U p => exact (hh U p).symm

/-- **The bridge of a save**: a typed save, read, is the Theory's. -/
theorem obs_save {U : Ty} {st st' : Storage C} {r : SRef C U} {v : SVal U}
    (h : st.save r v = some st') : st'.obs = st.obs.save (.ref r) v.obs := by
  unfold Storage.save at h
  rcases r with ⟨n, hn, rp⟩
  cases hs : (st.get hn).save rp v with
  | none => simp only [hs, Option.bind_eq_bind, Option.bind_none, reduceCtorEq] at h
  | some x' =>
    simp only [hs, Option.bind_eq_bind, Option.bind_some, Option.some.injEq] at h
    subst h
    rw [SVal.save_eq_saveM] at hs
    have hv := SVal.obs_saveM hs
    have er : (SLoc.ref ⟨n, hn, rp⟩ : SLoc C U) = ObsLoc.app (SLoc.ref (SRef.ofRoot n hn)) rp := by
      show _ = SLoc.ref ⟨n, hn, Path.nil.append rp⟩
      rw [Path.append_nil]
    refine obs_ext _ (fun n' T' hn' => ?_) (fun _ _ => rfl) (fun _ _ => rfl) (fun _ _ => rfl)
    by_cases e : n' = n
    · subst e
      obtain rfl : T' = _ := Option.some.inj (hn'.symm.trans hn)
      rw [SFields.get_set_same, hv, er, Obs.find_save_below, obs_find_root]
    · rw [SFields.get_set_ne _ hn hn' (Ne.symm e), Obs.find_save_frame, obs_find_root]
      intro V q
      exact SRef.strip?_root_ne _ _ (Ne.symm e)

end Storage

/-! ## One component of the observations

A delete, a strip and a copy are read one component at a time (`Comp`): a
word, a length, or whether a location is there; each is defined once over
the component and is the three of them (`TVal.ofComp`). -/

/-- A component of the observations at the locations of type `V`. -/
structure Comp (V : Ty) (α : Type) where
  /-- The component at `r` of a value. -/
  read : {U : Ty} → TVal U → Path U V → α
  /-- The component of a typed value found, or of nothing. -/
  ofOpt : Option (SVal V) → α
  /-- The component at a location deleted. -/
  reset : TVal V → α
  read_obsOpt : ∀ {U : Ty} (x : Option (SVal U)) (r : Path U V),
    read (SVal.obsOpt x) r = ofOpt (x.bind (·.findM r))
  read_find : ∀ {U W : Ty} (o : TVal U) (p : Path U W) (r : Path W V),
    read (o.find p) r = read o (p.append r)
  overlay_top : ∀ x y : SVal V, ofOpt (some (x.overlay y)) = ofOpt (some y)
  strip_top : ∀ x : SVal V, ofOpt (some x.strip) = ofOpt (some x)
  reset_some : ∀ x : SVal V, reset x.obs = ofOpt (some x.defaultOf)
  reset_none : reset (SVal.obsOpt none) = ofOpt none

namespace Comp

/-- The word at a primitive location. -/
def word (P : PrimTy) : Comp (.prim P) P.Denote where
  read o r := o.word r
  ofOpt := SVal.wordOf
  reset _ := PrimTy.dflt P
  read_obsOpt _ _ := rfl
  read_find _ _ _ := rfl
  overlay_top x y := by cases y; rw [SVal.overlay_prim]
  strip_top x := by cases x; rw [SVal.strip_prim]
  reset_some x := by cases x; rw [SVal.defaultOf_prim]; rfl
  reset_none := rfl

/-- The live length of a dynamic array. -/
def len (E : Ty) : Comp (.ref (.array E)) Nat where
  read o r := o.len r
  ofOpt := SVal.lenOf
  reset _ := 0
  read_obsOpt _ _ := rfl
  read_find _ _ _ := rfl
  overlay_top x y := by cases x; cases y; rw [SVal.overlay_array]; rfl
  strip_top x := by cases x; rw [SVal.strip_array]; rfl
  reset_some x := by cases x; rw [SVal.defaultOf_array]; rfl
  reset_none := rfl

/-- Whether a location is there. -/
def has (V : Ty) : Comp V Bool where
  read o r := o.has r
  ofOpt x := x.isSome
  reset o := o.has .nil
  read_obsOpt _ _ := rfl
  read_find _ _ _ := rfl
  overlay_top _ _ := rfl
  strip_top _ := rfl
  reset_some x := by cases x <;> rfl
  reset_none := rfl

/-- What is not there. -/
abbrev absent {V : Ty} {α : Type} (c : Comp V α) : α := c.ofOpt none

end Comp

namespace TVal

/-- A value from its three components, each read by `f`. -/
def ofComp {U : Ty} (f : {V : Ty} → {α : Type} → Comp V α → Path U V → α) : TVal U :=
  ⟨fun r => f (Comp.word _) r, fun r => f (Comp.len _) r, fun r => f (Comp.has _) r⟩

theorem eq_ofComp {U : Ty} {o : TVal U} {f : {V : Ty} → {α : Type} → Comp V α → Path U V → α}
    (h : ∀ {V : Ty} {α : Type} (c : Comp V α) (r : Path U V), c.read o r = f c r) :
    o = ofComp f :=
  Obs.ext (fun r => h (Comp.word _) r) (fun r => h (Comp.len _) r) (fun r => h (Comp.has _) r)

variable {V : Ty} {α : Type}

/-- A delete, one component (`SVal.defaultOf`): reset below the location,
but a mapping's entries and an array's slots past its live end are kept. -/
def delR (c : Comp V α) : {U : Ty} → TVal U → Path U V → α
  | _, o, .nil => c.reset o
  | _, o, .field h r => delR c (o.find (.field h .nil)) r
  | _, o, .atF i r => delR c (o.find (.atF i .nil)) r
  | _, o, .key k r => c.read o (.key k r)
  | _, o, .at i r =>
    if i.1.toNat < o.len .nil then delR c (o.find (.at i .nil)) r else c.read o (.at i r)

/-- A value as nothing has written it, one component (`SVal.strip`): no
slots past an array's live end. -/
def stripR (c : Comp V α) : {U : Ty} → TVal U → Path U V → α
  | _, o, .nil => c.read o .nil
  | _, o, .field h r => stripR c (o.find (.field h .nil)) r
  | _, o, .atF i r => stripR c (o.find (.atF i .nil)) r
  | _, o, .key k r => c.read o (.key k r)
  | _, o, .at i r =>
    if i.1.toNat < o.len .nil then stripR c (o.find (.at i .nil)) r else c.absent

/-- A copy of `n` laid over `o`, one component (`SVal.overlay`): member by
member, element by element over the old slots (onto fresh ones as nothing
wrote them), the old elements past the new length deleted, the old slots
past both kept, a mapping kept. -/
def ovR (c : Comp V α) : {U : Ty} → TVal U → TVal U → Path U V → α
  | _, _, n, .nil => c.read n .nil
  | _, o, n, .field h r => ovR c (o.find (.field h .nil)) (n.find (.field h .nil)) r
  | _, o, n, .atF i r => ovR c (o.find (.atF i .nil)) (n.find (.atF i .nil)) r
  | _, o, n, .key k r =>
    if n.has .nil then (if o.has .nil then c.read o (.key k r) else c.read n (.key k r))
    else c.absent
  | _, o, n, .at i r =>
    if n.has .nil then
      if i.1.toNat < n.len .nil then ovR c (o.find (.at i .nil)) (n.find (.at i .nil)) r
      else if i.1.toNat < o.len .nil then delR c (o.find (.at i .nil)) r
      else c.read o (.at i r)
    else c.absent

end TVal

/-- **`delValue`** of a stored value: reset, as `delete` resets it. -/
def TVal.del {U : Ty} (o : TVal U) : TVal U := TVal.ofComp fun c r => TVal.delR c o r
/-- A value as written to fresh slots (`SVal.strip`). -/
def TVal.strip {U : Ty} (o : TVal U) : TVal U := TVal.ofComp fun c r => TVal.stripR c o r
/-- **A copy**: `n` laid over `o` (`SVal.overlay`). -/
def TVal.overlay {U : Ty} (o n : TVal U) : TVal U := TVal.ofComp fun c r => TVal.ovR c o n r

/-! ### A read, step by step -/

theorem SVal.findM_nil' {T : Ty} (x : SVal T) : x.findM .nil = some x := by cases x <;> rfl

theorem SVal.findM_field' {s f : Name} {T U : Ty} (fs : SFields (structDef s))
    (h : lookupBy f (structDef s) = some T) (r : Path T U) :
    (SVal.struct fs).findM (.field h r) = (fs.get h).findM r := rfl

theorem SVal.findM_at' {E U : Ty} {n : Nat} (e : SVec E n) (sh : SList E) (hn : n < 2 ^ 256)
    (i : PrimTy.uint.Denote) (r : Path E U) : (SVal.array e sh hn).findM (.at i r) =
      (e.toList ++ sh.toList)[i.1.toNat]?.bind (·.findM r) := by
  simp only [SVal.findM]
  cases (e.toList ++ sh.toList)[i.1.toNat]? <;> rfl

theorem SVal.findM_atF' {E U : Ty} {n : Nat} (e : SVec E n) (i : PrimTy.uint.Denote) (r : Path E U) :
    (SVal.fixed e).findM (.atF i r) =
      e.toList[i.1.toNat]?.bind (·.findM r) := by
  simp only [SVal.findM]
  cases e.toList[i.1.toNat]? <;> rfl

theorem SVal.findM_at_nil {E : Ty} {n : Nat} (e : SVec E n) (sh : SList E) (hn : n < 2 ^ 256)
    (i : PrimTy.uint.Denote) : (SVal.array e sh hn).findM (.at i .nil) =
      (e.toList ++ sh.toList)[i.1.toNat]? := by
  rw [SVal.findM_at']
  cases (e.toList ++ sh.toList)[i.1.toNat]? with
  | none => rfl
  | some w => exact SVal.findM_nil' w

/-! ### Members and elements of a delete, a strip, a copy -/

theorem SFields.get_defaultOf {f : Name} : {fs : List (Name × Ty)} → {T : Ty} →
    (xs : SFields fs) → (h : lookupBy f fs = some T) →
    xs.defaultOf.get h = (xs.get h).defaultOf
  | [], _, .nil, h => by simp only [lookupBy, reduceCtorEq] at h
  | (f', T') :: fs, T, .cons x xs, h => by
    rw [SFields.defaultOf_cons, SFields.get_cons, SFields.get_cons]
    by_cases e : f = f'
    · have hT := SFields.lookupBy_cons_pos e h
      subst hT
      simp only [e, dite_true]
    · simp only [e, dite_false]
      exact SFields.get_defaultOf xs _

theorem SFields.get_strip {f : Name} : {fs : List (Name × Ty)} → {T : Ty} →
    (xs : SFields fs) → (h : lookupBy f fs = some T) →
    xs.strip.get h = (xs.get h).strip
  | [], _, .nil, h => by simp only [lookupBy, reduceCtorEq] at h
  | (f', T') :: fs, T, .cons x xs, h => by
    rw [SFields.strip_cons, SFields.get_cons, SFields.get_cons]
    by_cases e : f = f'
    · have hT := SFields.lookupBy_cons_pos e h
      subst hT
      simp only [e, dite_true]
    · simp only [e, dite_false]
      exact SFields.get_strip xs _

theorem SFields.get_overlay {f : Name} : {fs : List (Name × Ty)} → {T : Ty} →
    (os ns : SFields fs) → (h : lookupBy f fs = some T) →
    (os.overlay ns).get h = (os.get h).overlay (ns.get h)
  | [], _, .nil, .nil, h => by simp only [lookupBy, reduceCtorEq] at h
  | (f', T') :: fs, T, .cons o os, .cons n ns, h => by
    rw [SFields.overlay_cons, SFields.get_cons, SFields.get_cons, SFields.get_cons]
    by_cases e : f = f'
    · have hT := SFields.lookupBy_cons_pos e h
      subst hT
      simp only [e, dite_true]
    · simp only [e, dite_false]
      exact SFields.get_overlay os ns _

/-- A default's member is its type's default. -/
theorem SFields.dflt_get {f : Name} : {fs : List (Name × Ty)} → {T : Ty} →
    (h : lookupBy f fs = some T) → (SFields.dflt fs).get h = SVal.dflt T
  | [], _, h => by simp only [lookupBy, reduceCtorEq] at h
  | (f', T') :: fs, T, h => by
    rw [SFields.dflt, SFields.get_cons]
    by_cases e : f = f'
    · have hT := SFields.lookupBy_cons_pos e h
      subst hT
      simp only [e, dite_true]
    · simp only [e, dite_false]
      exact SFields.dflt_get _

theorem SVec.toList_defaultOf {E : Ty} : {n : Nat} → (e : SVec E n) →
    e.defaultOf.toList = e.toList.map SVal.defaultOf
  | _, .nil => by rw [SVec.defaultOf_nil, SVec.toList_nil]; rfl
  | _, .cons v rest => by
    rw [SVec.defaultOf_cons, SVec.toList_cons, SVec.toList_cons, SVec.toList_defaultOf rest]; rfl

theorem SVec.toList_strip {E : Ty} : {n : Nat} → (e : SVec E n) →
    e.strip.toList = e.toList.map SVal.strip
  | _, .nil => by rw [SVec.strip_nil, SVec.toList_nil]; rfl
  | _, .cons v rest => by
    rw [SVec.strip_cons, SVec.toList_cons, SVec.toList_cons, SVec.toList_strip rest]; rfl

/-- A copy over what may not be there: as nothing wrote it, onto nothing. -/
def SVal.overlayOpt {U : Ty} : Option (SVal U) → Option (SVal U) → Option (SVal U)
  | _, none => none
  | none, some n => some n.strip
  | some o, some n => some (o.overlay n)

theorem SVal.overlayOpt_none {U : Ty} (x : Option (SVal U)) : SVal.overlayOpt x none = none := by
  cases x <;> rfl
theorem SVal.overlayOpt_none_some {U : Ty} (n : SVal U) :
    SVal.overlayOpt none (some n) = some n.strip := rfl
theorem SVal.overlayOpt_some_some {U : Ty} (o n : SVal U) :
    SVal.overlayOpt (some o) (some n) = some (o.overlay n) := rfl

theorem SVal.obsOpt_has_nil {U : Ty} (x : Option (SVal U)) : (SVal.obsOpt x).has .nil = x.isSome := by
  cases x with
  | none => rfl
  | some v => show (v.findM .nil).isSome = true; rw [SVal.findM_nil']; rfl
theorem SVal.obsOpt_len_nil {E : Ty} (x : Option (SVal (.ref (.array E)))) :
    (SVal.obsOpt x).len .nil = SVal.lenOf x := by
  cases x with
  | none => rfl
  | some v => show SVal.lenOf (v.findM .nil) = _; rw [SVal.findM_nil']

/-- The new elements laid over the old slots, slot by slot. -/
theorem SVec.getElem?_overlayOn {E : Ty} : {n : Nat} → (L : List (SVal E)) → (e : SVec E n) →
    (j : Nat) → (SVec.overlayOn L e).toList[j]? = SVal.overlayOpt L[j]? e.toList[j]?
  | _, L, .nil, j => by
    rw [SVec.overlayOn_nil, SVec.toList_nil, List.getElem?_nil]; cases L[j]? <;> rfl
  | _, [], .cons v rest, j => by
    rw [SVec.overlayOn_nil_cons, SVec.toList_cons, SVec.toList_cons, ← SVec.overlayOn_nil_left,
      List.getElem?_nil]
    cases j with
    | zero => rfl
    | succ j =>
      simp only [List.getElem?_cons_succ]
      rw [SVec.getElem?_overlayOn [] rest j, List.getElem?_nil]
  | _, o :: L, .cons v rest, j => by
    rw [SVec.overlayOn_cons_cons, SVec.toList_cons, SVec.toList_cons]
    cases j with
    | zero => rfl
    | succ j =>
      simp only [List.getElem?_cons_succ]
      exact SVec.getElem?_overlayOn L rest j

/-! ### The bridge of a delete, a strip, a copy -/

theorem TVal.delR_obsOpt {V : Ty} {α : Type} (c : Comp V α) : {U : Ty} → (x : Option (SVal U)) →
    (r : Path U V) → TVal.delR c (SVal.obsOpt x) r = c.ofOpt ((x.map SVal.defaultOf).bind (·.findM r))
  | _, none, .nil => c.reset_none
  | _, some v, .nil => by
    show c.reset v.obs = _
    rw [c.reset_some, Option.map_some, Option.bind_some, SVal.findM_nil']
  | _, x, .field h r => by
    show TVal.delR c ((SVal.obsOpt x).find (.field h .nil)) r = _
    rw [SVal.obsOpt_find, TVal.delR_obsOpt c _ r]
    congr 1
    cases x with
    | none => rfl
    | some v =>
      cases v with
      | struct fs =>
        simp only [Option.bind_some, Option.map_some, SVal.defaultOf_struct, SVal.findM_field',
          SFields.get_defaultOf, SVal.findM_nil']
  | _, x, .atF i r => by
    show TVal.delR c ((SVal.obsOpt x).find (.atF i .nil)) r = _
    rw [SVal.obsOpt_find, TVal.delR_obsOpt c _ r]
    congr 1
    cases x with
    | none => rfl
    | some v =>
      cases v with
      | fixed e =>
        simp only [Option.bind_some, Option.map_some, SVal.defaultOf_fixed, SVal.findM_atF',
          SVec.toList_defaultOf, List.getElem?_map, SVal.findM_nil']
        cases e.toList[i.1.toNat]? <;> rfl
  | _, x, .key k r => by
    show c.read (SVal.obsOpt x) (.key k r) = _
    rw [c.read_obsOpt]
    cases x with
    | none => rfl
    | some v => cases v; rw [Option.map_some, SVal.defaultOf_map]
  | _, none, @Path.at E _ i r => by
    have e : (SVal.obsOpt (none : Option (SVal (.ref (.array E))))).len .nil = 0 := rfl
    simp only [TVal.delR, e, Nat.not_lt_zero, and_false, if_false, c.read_obsOpt]
    rfl
  | _, some v, .at i r => by
    cases v with
    | array e sh hn =>
      rename_i n
      show (if i.1.toNat < n then
        TVal.delR c ((SVal.obsOpt (some (SVal.array e sh hn))).find (.at i .nil)) r
        else c.read (SVal.obsOpt (some (SVal.array e sh hn))) (.at i r)) = _
      simp only [Option.map_some, Option.bind_some, SVal.defaultOf_array]
      split
      · rename_i hi
        have hl : i.1.toNat < e.toList.length := by
          rw [SVec.length_toList]; exact hi
        rw [SVal.obsOpt_find, TVal.delR_obsOpt c _ r]
        congr 1
        simp only [Option.bind_some, SVal.findM_at', SList.toList_ofList,
          SVec.toList_nil, List.nil_append, SVec.toList_defaultOf, List.getElem?_append_left
            (show i.1.toNat < (e.toList.map SVal.defaultOf).length by rw [List.length_map]; exact hl),
          List.getElem?_map, List.getElem?_append_left hl, SVal.findM_nil']
        cases e.toList[i.1.toNat]? <;> rfl
      · rename_i hi
        rw [c.read_obsOpt]
        congr 1
        simp only [Option.bind_some, SVal.findM_at', SList.toList_ofList, SVec.toList_nil,
          List.nil_append, SVec.toList_defaultOf]
        have hge : e.toList.length ≤ i.1.toNat := by
          rw [SVec.length_toList]; omega
        rw [List.getElem?_append_right (show (e.toList.map SVal.defaultOf).length ≤ i.1.toNat by
          rw [List.length_map]; exact hge), List.getElem?_append_right hge, List.length_map]

theorem TVal.stripR_obsOpt {V : Ty} {α : Type} (c : Comp V α) : {U : Ty} → (x : Option (SVal U)) →
    (r : Path U V) → TVal.stripR c (SVal.obsOpt x) r = c.ofOpt ((x.map SVal.strip).bind (·.findM r))
  | _, none, .nil => by rw [TVal.stripR, c.read_obsOpt]; rfl
  | _, some v, .nil => by
    rw [TVal.stripR, c.read_obsOpt, Option.map_some, Option.bind_some, Option.bind_some,
      SVal.findM_nil', SVal.findM_nil', c.strip_top]
  | _, x, .field h r => by
    show TVal.stripR c ((SVal.obsOpt x).find (.field h .nil)) r = _
    rw [SVal.obsOpt_find, TVal.stripR_obsOpt c _ r]
    congr 1
    cases x with
    | none => rfl
    | some v =>
      cases v with
      | struct fs =>
        simp only [Option.bind_some, Option.map_some, SVal.strip_struct, SVal.findM_field',
          SFields.get_strip, SVal.findM_nil']
  | _, x, .atF i r => by
    show TVal.stripR c ((SVal.obsOpt x).find (.atF i .nil)) r = _
    rw [SVal.obsOpt_find, TVal.stripR_obsOpt c _ r]
    congr 1
    cases x with
    | none => rfl
    | some v =>
      cases v with
      | fixed e =>
        simp only [Option.bind_some, Option.map_some, SVal.strip_fixed, SVal.findM_atF',
          SVec.toList_strip, List.getElem?_map, SVal.findM_nil']
        cases e.toList[i.1.toNat]? <;> rfl
  | _, x, .key k r => by
    show c.read (SVal.obsOpt x) (.key k r) = _
    rw [c.read_obsOpt]
    cases x with
    | none => rfl
    | some v => cases v; rw [Option.map_some, SVal.strip_map]
  | _, none, @Path.at E _ i r => by
    have e : (SVal.obsOpt (none : Option (SVal (.ref (.array E))))).len .nil = 0 := rfl
    simp only [TVal.stripR, e, Nat.not_lt_zero, and_false, if_false]
    rfl
  | _, some v, .at i r => by
    cases v with
    | array e sh hn =>
      rename_i n
      show (if i.1.toNat < n then
        TVal.stripR c ((SVal.obsOpt (some (SVal.array e sh hn))).find (.at i .nil)) r
        else c.absent) = _
      simp only [Option.map_some, Option.bind_some, SVal.strip_array]
      split
      · rename_i hi
        have hl : i.1.toNat < e.toList.length := by
          rw [SVec.length_toList]; exact hi
        rw [SVal.obsOpt_find, TVal.stripR_obsOpt c _ r]
        congr 1
        simp only [Option.bind_some, SVal.findM_at', SList.toList_nil,
          List.append_nil, SVec.toList_strip, List.getElem?_map, List.getElem?_append_left hl,
          SVal.findM_nil']
        cases e.toList[i.1.toNat]? <;> rfl
      · rename_i hi
        simp only [SVal.findM_at', SList.toList_nil, List.append_nil, SVec.toList_strip]
        have hge : (e.toList.map SVal.strip).length ≤ i.1.toNat := by
          rw [List.length_map, SVec.length_toList]; omega
        rw [List.getElem?_eq_none hge]
        rfl

/-- The slots of an array copy past its new length: the old elements
deleted, then the old slots past them. -/
theorem shadow_getElem?_lt {β : Type} (f : β → β) (oel osh : List β) {n i : Nat} (hi : n ≤ i)
    (him : i < oel.length) :
    ((oel.drop n).map f ++ osh.drop (n - oel.length))[i - n]? = (oel[i]?).map f := by
  have hl : i - n < ((oel.drop n).map f).length := by
    rw [List.length_map, List.length_drop]; omega
  rw [List.getElem?_append_left hl, List.getElem?_map, List.getElem?_drop,
    show n + (i - n) = i by omega]

theorem shadow_getElem?_ge {β : Type} (f : β → β) (oel osh : List β) {n i : Nat} (hi : n ≤ i)
    (him : oel.length ≤ i) :
    ((oel.drop n).map f ++ osh.drop (n - oel.length))[i - n]? = (oel ++ osh)[i]? := by
  have hl : ((oel.drop n).map f).length ≤ i - n := by
    rw [List.length_map, List.length_drop]; omega
  rw [List.getElem?_append_right hl, List.getElem?_drop, List.getElem?_append_right him,
    List.length_map, List.length_drop]
  congr 1
  omega

theorem TVal.ovR_obsOpt {V : Ty} {α : Type} (c : Comp V α) : {U : Ty} → (x y : Option (SVal U)) →
    (r : Path U V) → TVal.ovR c (SVal.obsOpt x) (SVal.obsOpt y) r =
      c.ofOpt ((SVal.overlayOpt x y).bind (·.findM r))
  | _, x, none, .nil => by rw [TVal.ovR, c.read_obsOpt]; cases x <;> rfl
  | _, none, some n, .nil => by
    rw [TVal.ovR, c.read_obsOpt, Option.bind_some, SVal.overlayOpt, Option.bind_some,
      SVal.findM_nil', SVal.findM_nil', c.strip_top]
  | _, some o, some n, .nil => by
    rw [TVal.ovR, c.read_obsOpt, Option.bind_some, SVal.overlayOpt, Option.bind_some,
      SVal.findM_nil', SVal.findM_nil', c.overlay_top]
  | _, x, y, .field h r => by
    show TVal.ovR c ((SVal.obsOpt x).find (.field h .nil)) ((SVal.obsOpt y).find (.field h .nil)) r = _
    rw [SVal.obsOpt_find, SVal.obsOpt_find, TVal.ovR_obsOpt c _ _ r]
    congr 1
    cases y with
    | none => simp only [Option.bind_none, SVal.overlayOpt_none]
    | some n =>
      cases n with
      | struct nfs =>
        cases x with
        | none =>
          simp only [Option.bind_none, Option.bind_some, SVal.findM_nil',
            SVal.overlayOpt_none_some, SVal.findM_field', SVal.strip_struct, SFields.get_strip]
        | some o =>
          cases o with
          | struct ofs =>
            simp only [Option.bind_some, SVal.findM_nil',
              SVal.overlayOpt_some_some, SVal.findM_field', SVal.overlay_struct, SFields.get_overlay]
  | _, x, y, .atF i r => by
    show TVal.ovR c ((SVal.obsOpt x).find (.atF i .nil)) ((SVal.obsOpt y).find (.atF i .nil)) r = _
    rw [SVal.obsOpt_find, SVal.obsOpt_find, TVal.ovR_obsOpt c _ _ r]
    congr 1
    cases y with
    | none => simp only [Option.bind_none, SVal.overlayOpt_none]
    | some n =>
      cases n with
      | fixed nel =>
        cases x with
        | none =>
          simp only [Option.bind_none, Option.bind_some,
            SVal.overlayOpt_none_some, SVal.findM_atF', SVal.strip_fixed, SVec.toList_strip,
            List.getElem?_map, SVal.findM_nil', Option.bind_fun_some]
          cases nel.toList[i.1.toNat]? with
          | none => rfl
          | some w => rw [SVal.overlayOpt_none_some]; rfl
        | some o =>
          cases o with
          | fixed oel =>
            simp only [Option.bind_some, SVal.findM_atF', SVal.findM_nil',
              Option.bind_fun_some, SVal.overlayOpt_some_some, SVal.overlay_fixed,
              SVec.getElem?_overlayOn]
  | _, x, y, .key k r => by
    show (if (SVal.obsOpt y).has .nil then (if (SVal.obsOpt x).has .nil then
      c.read (SVal.obsOpt x) (.key k r) else c.read (SVal.obsOpt y) (.key k r)) else c.absent) = _
    simp only [SVal.obsOpt_has_nil]
    cases y with
    | none => simp only [Option.isSome_none, Bool.false_eq_true, if_false, Option.bind_none,
        SVal.overlayOpt_none]
    | some n =>
      cases n with
      | map ne nd =>
        cases x with
        | none =>
          simp only [Option.isSome_some, Option.isSome_none, if_true, Bool.false_eq_true,
            if_false, c.read_obsOpt, SVal.overlayOpt_none_some, SVal.strip_map, Option.bind_some]
        | some o =>
          cases o with
          | map oe od =>
            simp only [Option.isSome_some, if_true, c.read_obsOpt, SVal.overlayOpt_some_some,
              SVal.overlay_map, Option.bind_some]
  | _, x, y, .at i r => by
    cases y with
    | none =>
      simp only [TVal.ovR, SVal.obsOpt_has_nil, Option.isSome_none, Bool.false_eq_true, if_false,
        Option.bind_none, SVal.overlayOpt_none]
    | some n =>
      cases n with
      | array nel nsh hn =>
        rename_i nn
        have eh : (SVal.obsOpt (some (SVal.array nel nsh hn))).has .nil = true := rfl
        have el : (SVal.obsOpt (some (SVal.array nel nsh hn))).len .nil = nn := rfl
        simp only [TVal.ovR, eh, el, if_true]
        split
        · rename_i hi
          have hl : i.1.toNat < nel.toList.length := by rw [SVec.length_toList]; exact hi
          rw [SVal.obsOpt_find, SVal.obsOpt_find, TVal.ovR_obsOpt c _ _ r]
          congr 1
          cases x with
          | none =>
            simp only [Option.bind_none, Option.bind_some, SVal.findM_at',
              SVal.overlayOpt_none_some, SVal.strip_array, SList.toList_nil,
              List.append_nil, SVec.toList_strip, List.getElem?_map, List.getElem?_append_left hl, SVal.findM_nil', Option.bind_fun_some]
            cases nel.toList[i.1.toNat]? with
            | none => rfl
            | some w => rw [SVal.overlayOpt_none_some]; rfl
          | some o =>
            cases o with
            | array oel osh hm =>
              simp only [Option.bind_some, SVal.findM_at',
                SVal.overlayOpt_some_some, SVal.overlay_array, SList.toList_ofList, SVal.findM_nil', Option.bind_fun_some]
              have hl' : i.1.toNat < (SVec.overlayOn (oel.toList ++ osh.toList) nel).toList.length := by
                rw [SVec.length_toList]; exact hi
              rw [List.getElem?_append_left hl', SVec.getElem?_overlayOn,
                List.getElem?_append_left hl]
        · rename_i hi
          cases x with
          | none =>
            simp only [SVal.obsOpt_len_nil, SVal.lenOf, Nat.not_lt_zero, and_false, if_false, c.read_obsOpt]
            simp only [Option.bind_none, SVal.overlayOpt_none_some, Option.bind_some, SVal.strip_array,
              SVal.findM_at', SList.toList_nil, List.append_nil, SVec.toList_strip]
            have hge : (nel.toList.map SVal.strip).length ≤ i.1.toNat := by
              rw [List.length_map, SVec.length_toList]; omega
            rw [List.getElem?_eq_none hge]; rfl
          | some o =>
            cases o with
            | array oel osh hm =>
              rename_i mm
              have el' : (SVal.obsOpt (some (SVal.array oel osh hm))).len .nil = mm := rfl
              simp only [el']
              split
              · rename_i hi'
                rw [SVal.obsOpt_find, TVal.delR_obsOpt]
                congr 1
                have hge : nn ≤ i.1.toNat := by omega
                have hlt : i.1.toNat < oel.toList.length := by rw [SVec.length_toList]; exact hi'
                simp only [Option.bind_some, SVal.findM_at', SVal.findM_nil',
                  SVal.overlayOpt, SVal.overlay_array, SList.toList_ofList, Option.bind_fun_some]
                have hl' : (SVec.overlayOn (oel.toList ++ osh.toList) nel).toList.length ≤ i.1.toNat := by
                  rw [SVec.length_toList]; exact hge
                rw [List.getElem?_append_right hl', SVec.length_toList, show nn - mm =
                  nn - oel.toList.length by rw [SVec.length_toList], shadow_getElem?_lt _ _ _ hge hlt,
                  List.getElem?_append_left hlt]
              · rename_i hi'
                rw [c.read_obsOpt]
                congr 1
                simp only [Option.bind_some, SVal.findM_at', SVal.overlayOpt, SVal.overlay_array,
                  SList.toList_ofList]
                have hge : nn ≤ i.1.toNat := by omega
                have hge' : oel.toList.length ≤ i.1.toNat := by rw [SVec.length_toList]; omega
                have hl' : (SVec.overlayOn (oel.toList ++ osh.toList) nel).toList.length ≤
                    i.1.toNat := by
                  rw [SVec.length_toList]; exact hge
                rw [List.getElem?_append_right hl', SVec.length_toList, show nn - mm =
                  nn - oel.toList.length by rw [SVec.length_toList],
                  shadow_getElem?_ge _ _ _ hge hge']

theorem SVal.obs_defaultOf {U : Ty} (x : SVal U) : x.defaultOf.obs = x.obs.del :=
  TVal.eq_ofComp fun c r => by
    rw [SVal.obs, c.read_obsOpt, SVal.obs, TVal.delR_obsOpt]; rfl

theorem SVal.obs_strip {U : Ty} (x : SVal U) : x.strip.obs = x.obs.strip :=
  TVal.eq_ofComp fun c r => by
    rw [SVal.obs, c.read_obsOpt, SVal.obs, TVal.stripR_obsOpt]; rfl

/-- Stripping a fixed array and then reading a child strips that child;
the fixed outer vector has no shadow slots of its own. -/
theorem TVal.strip_find_atF {E : Ty} {n : Nat} (o : TVal (.ref (.fixed E n)))
    (i : PrimTy.uint.Denote) :
    o.strip.find (.atF i .nil) = (o.find (.atF i .nil)).strip := by
  apply Obs.ext <;> intro _ r <;>
    simp only [Obs.find, ObsLoc.app_path, Path.append_atF, Path.append_nil,
      TVal.strip, TVal.ofComp, TVal.stripR, Comp.word, Comp.len, Comp.has]

/-- The length of a converted array: source length for a dynamic target, declared length for a fixed one. -/
def FixedCopy.targetLength {E : Ty} {n : Nat} {R : RefTy} : FixedCopy E n R → Nat
  | .dynamic _ => n
  | .fixed m _ => m

/-- A converted array element, read lazily: source, padded default, or absence. The source observation is assumed defined. -/
def FixedCopy.child {E : Ty} {n : Nat} {R : RefTy} (c : FixedCopy E n R)
    (o : TVal (.ref (.fixed E n))) (i : PrimTy.uint.Denote) : TVal E :=
  if i.1.toNat < c.targetLength then
    if i.1.toNat < n then o.strip.find (.atF i .nil)
    else (SVal.dflt E).strip.obs
  else SVal.obsOpt none

/-- The destination-shaped observations of a successful fixed-array snapshot. -/
def FixedCopy.observe {E : Ty} {n : Nat} : {R : RefTy} → (c : FixedCopy E n R) →
    TVal (.ref (.fixed E n)) → TVal (.ref R)
  | _, .dynamic hn, o =>
    ⟨fun q => match q with | .at i r => ((FixedCopy.dynamic hn).child o i).word r,
     fun q => match q with | .nil => n | .at i r => ((FixedCopy.dynamic hn).child o i).len r,
     fun q => match q with | .nil => true | .at i r => ((FixedCopy.dynamic hn).child o i).has r⟩
  | _, .fixed m hm, o =>
    ⟨fun q => match q with | .atF i r => ((FixedCopy.fixed m hm).child o i).word r,
     fun q => match q with | .atF i r => ((FixedCopy.fixed m hm).child o i).len r,
     fun q => match q with | .nil => true | .atF i r => ((FixedCopy.fixed m hm).child o i).has r⟩

/-- A fixed array viewed as a dynamic one has its length. -/
theorem FixedCopy.observe_len {E : Ty} {n : Nat} (c : FixedCopy E n (.array E))
    (o : TVal (.ref (.fixed E n))) : (c.observe o).len .nil = n := by
  cases c; rfl

/-- An element selector at the destination's array shape. -/
def FixedCopy.index {E : Ty} {n : Nat} {R : RefTy} : FixedCopy E n R →
    PrimTy.uint.Denote → Path (.ref R) E
  | .dynamic _, i => .at i .nil
  | .fixed _ _, i => .atF i .nil

/-- A converted array element has exactly the lazy observation of its source or padded default. -/
theorem FixedCopy.child_apply {E : Ty} {n : Nat} {R : RefTy}
    (c : FixedCopy E n R) (v : SVal (.ref (.fixed E n))) (i : PrimTy.uint.Denote) :
    c.child v.obs i = (c.apply v).obs.find (c.index i) := by
  cases v with
  | fixed vs =>
    cases c with
    | dynamic bound =>
      simp only [FixedCopy.child, FixedCopy.targetLength, FixedCopy.apply, FixedCopy.index]
      rw [← SVal.obs_strip, SVal.strip_fixed]
      simp only [SVal.obs_find, SVal.findM_atF', SVal.findM_at', SList.toList_nil,
        List.append_nil, SVal.findM_nil', Option.bind_fun_some]
      by_cases hi : i.1.toNat < n
      · simp only [hi, ↓reduceIte]
      · simp only [hi, ↓reduceIte]
        rw [List.getElem?_eq_none (by rw [SVec.length_toList]; omega)]
    | fixed m fits =>
      simp only [FixedCopy.child, FixedCopy.targetLength, FixedCopy.apply, FixedCopy.index]
      rw [← SVal.obs_strip, SVal.strip_fixed]
      simp only [SVal.obs_find, SVal.findM_atF', SVal.findM_nil', Option.bind_fun_some,
        SVec.getElem?_padRight]
      split
      · split <;> rfl
      · rfl

/-- Every component below a converted element agrees with the actual converted snapshot. -/
theorem FixedCopy.child_apply_read {E : Ty} {n : Nat} {R : RefTy} {V : Ty} {α : Type}
    (k : Comp V α) (c : FixedCopy E n R) (v : SVal (.ref (.fixed E n)))
    (i : PrimTy.uint.Denote) (r : Path E V) :
    k.read (c.child v.obs i) r = k.read (c.apply v).obs ((c.index i).append r) := by
  rw [FixedCopy.child_apply, k.read_find]

/-- The converted snapshot agrees with its lazy observation for all word, length and presence reads. -/
theorem FixedCopy.observe_apply {E : Ty} {n : Nat} {R : RefTy}
    (c : FixedCopy E n R) (v : SVal (.ref (.fixed E n))) :
    (c.apply v).obs = c.observe v.obs := by
  cases c with
  | dynamic bound =>
    apply Obs.ext
    · intro P q
      cases q with
      | «at» i r =>
        simpa only [Comp.word, FixedCopy.observe, FixedCopy.index, Path.append_at,
          Path.append_nil] using (FixedCopy.child_apply_read (Comp.word P) (.dynamic bound) v i r).symm
    · intro E' q
      cases q with
      | nil => cases v; rfl
      | «at» i r =>
        simpa only [Comp.len, FixedCopy.observe, FixedCopy.index, Path.append_at,
          Path.append_nil] using (FixedCopy.child_apply_read (Comp.len E') (.dynamic bound) v i r).symm
    · intro U q
      cases q with
      | nil => cases v; rfl
      | «at» i r =>
        simpa only [Comp.has, FixedCopy.observe, FixedCopy.index, Path.append_at,
          Path.append_nil] using (FixedCopy.child_apply_read (Comp.has U) (.dynamic bound) v i r).symm
  | fixed m fits =>
    apply Obs.ext
    · intro P q
      cases q with
      | atF i r =>
        simpa only [Comp.word, FixedCopy.observe, FixedCopy.index, Path.append_atF,
          Path.append_nil] using (FixedCopy.child_apply_read (Comp.word P) (.fixed m fits) v i r).symm
    · intro E' q
      cases q with
      | atF i r =>
        simpa only [Comp.len, FixedCopy.observe, FixedCopy.index, Path.append_atF,
          Path.append_nil] using (FixedCopy.child_apply_read (Comp.len E') (.fixed m fits) v i r).symm
    · intro U q
      cases q with
      | nil => cases v; rfl
      | atF i r =>
        simpa only [Comp.has, FixedCopy.observe, FixedCopy.index, Path.append_atF,
          Path.append_nil] using (FixedCopy.child_apply_read (Comp.has U) (.fixed m fits) v i r).symm

theorem SVal.obs_overlay {U : Ty} (x y : SVal U) : (x.overlay y).obs = x.obs.overlay y.obs :=
  TVal.eq_ofComp fun c r => by
    rw [SVal.obs, c.read_obsOpt, SVal.obs, SVal.obs, TVal.ovR_obsOpt]; rfl

end Solidity
