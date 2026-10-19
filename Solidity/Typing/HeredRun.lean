import Solidity.Typing.Values
import Solidity.Typing.TypedRunInv

/-!
# A hereditary predicate the typed run keeps

`Typing/Values.lean`'s `SVal.All P` holds of a run's storage when each
storage operation keeps `P`'s node conditions: a slot or entry replaced
(`save`), an array's slots dropped (`strip`) or cleared (`delete`), copied
over (`overlay`), an element pushed or popped, a word or a copy out of
memory written.  `HeredRun P G` is that list, over the node conditions
alone; `G` is a property of every type the contract reaches (`Ty.okDeep`
for `Typing/Tight.lean`'s tight storage, nothing otherwise),
which only a push and a copy out of memory read.

The invariant (`heredInv P`) is the storage's `All P`.  It is carried along
the typed run statement by statement (`Stmt.keeps_all`), each leaf on
`TRun.*`, once for all three predicates of `Typing/Reachability.lean`,
`Typing/Tight.lean` and `Typing/Fits.lean`.
-/

namespace Solidity

open Semantics (structDef lookupBy setBy nodupKeysB)

variable {C : Contract}

/-- What a run's storage operations ask of a hereditary predicate's node
conditions, `G` holding of the types the contract reaches. -/
structure HeredRun (P : Hered) (G : Ty → Prop) : Prop where
  /-- A slot replaced, live if the array holds words. -/
  save : ∀ {E : Ty} {n : Nat} (e : SVec E n) (sh : SList E) (i : Nat) (x : SVal E),
    i < e.toList.length + sh.toList.length → (E.isPrimitive = true → i < n) → P.arr e sh →
    x.All P →
    P.arr (SVec.ofList (((e.toList ++ sh.toList).set i x).take n))
      (SList.ofList (((e.toList ++ sh.toList).set i x).drop n))
  /-- An entry written, at a key a program writes. -/
  map : ∀ {K : PrimTy} {V : Ty} (m : SMap K V) (d : SVal V) (k : K.Denote) (x : SVal V),
    x.All P → P.map K m d → P.map K (SMap.ofList (setBy k x m.toList)) d
  /-- The slots past the end dropped (a copy's source). -/
  strip : ∀ {E : Ty} {n : Nat} (e : SVec E n) (sh : SList E), P.arr e sh → e.All P →
    P.arr e.strip SList.nil
  /-- The elements cleared into the slots past the end (`delete`). -/
  del : ∀ {E : Ty} {n : Nat} (e : SVec E n) (sh : SList E), P.arr e sh → e.All P →
    P.arr SVec.nil (SList.ofList (e.defaultOf.toList ++ sh.toList))
  /-- An array copied over another. -/
  ov : ∀ {E : Ty} {m n : Nat} (oel : SVec E m) (osh : SList E) (nel : SVec E n) (nsh : SList E),
    P.arr oel osh → P.arr nel nsh → oel.All P → osh.All P → nel.All P →
    P.arr (SVec.overlayOn (oel.toList ++ osh.toList) nel)
      (SList.ofList ((oel.toList.drop n).map SVal.defaultOf ++ osh.toList.drop (n - m)))
  /-- An element pushed onto the slot `pushSlot` hands it, below the bound. -/
  push : ∀ {E : Ty} {n : Nat} (e : SVec E n) (sh : SList E) (x : SVal E),
    G (.ref (.array E)) → n + 1 < 2 ^ 256 → P.arr e sh → e.All P → sh.All P → x.All P →
    P.arr (SVec.ofList (e.toList ++ [x])) (SList.ofList (pushSlot E sh.toList).2)
  /-- The last element popped into the slots past the end: kept as it is
(an element of a mapping type) or cleared. -/
  pop : ∀ {E : Ty} {n : Nat} (e : SVec E n) (sh : SList E) (last : SVal E) (keep : Bool),
    last ∈ e.toList → (keep = true → E.isPrimitive = false) → P.arr e sh → e.All P →
    sh.All P →
    P.arr (SVec.ofList e.toList.dropLast)
      (SList.ofList ((if keep then last else last.defaultOf) :: sh.toList))
  /-- A default. -/
  dflt : ∀ T, (SVal.dflt T).All P
  /-- A copy out of memory. -/
  plain : ∀ {T : Ty} (v : SVal T), G T → v.Plain → v.All P

namespace HeredRun

variable {P : Hered} {G : Ty → Prop} (hP : HeredRun P G)

include hP

theorem strip_all {T : Ty} {v : SVal T} (h : v.All P) : v.strip.All P :=
  SVal.strip_all hP.strip h

theorem defaultOf_all {T : Ty} {v : SVal T} (h : v.All P) : v.defaultOf.All P :=
  SVal.defaultOf_all hP.del h

theorem overlay_all {T : Ty} {o v : SVal T} (ho : o.All P) (hv : v.All P) :
    (o.overlay v).All P :=
  SVal.overlay_all hP.strip hP.del hP.ov o v ho hv

theorem saveM_all {T U : Ty} {x : SVal T} {p : Path T U} {new : SVal U} {x' : SVal T}
    (hx : x.All P) (hn : new.All P) (hl : x.Live p)
    (h : x.saveM p new = some x') : x'.All P :=
  SVal.saveM_all hP.save hP.map p hx hn hl h

/-- The slot a push lands on. -/
theorem pushSlot_all {E : Ty} {sh : List (SVal E)} (h : ∀ w ∈ sh, w.All P) :
    (pushSlot E sh).1.All P ∧ ∀ w ∈ (pushSlot E sh).2, w.All P := by
  cases sh with
  | nil => exact ⟨hP.dflt E, fun _ h => nomatch h⟩
  | cons c rest =>
    refine ⟨?_, fun w hw => h w (List.mem_cons_of_mem _ hw)⟩
    show (if E.isPrimitive then SVal.dflt E else c).All P
    split
    · exact hP.dflt E
    · exact h c List.mem_cons_self

end HeredRun

/-! ## The storage operations -/

namespace Storage

variable {P : Hered} {G : Ty → Prop} (hP : HeredRun P G)

include hP

/-- **A save keeps the predicate**, along keys a program writes, entering
arrays of words at live slots. -/
theorem save_all {st st' : Storage C} {U : Ty} {r : SRef C U} {new : SVal U}
    (hs : st.All P) (hn : new.All P)
    (hl : (st.get r.hroot).Live r.path) (h : st.save r new = some st') : st'.All P := by
  obtain ⟨v', hv, rfl⟩ := save_eq_some h
  exact SFields.all_set r.hroot hs (hP.saveM_all (root_all r hs) hn hl hv)

theorem write_all {st st' : Storage C} {U : Ty} {r : SRef C U} {new : SVal U}
    (hs : st.All P) (hn : new.All P)
    (hl : (st.get r.hroot).Live r.path) (h : st.write r new = some st') : st'.All P := by
  unfold Storage.write at h
  split at h
  · exact save_all hP hs hn hl h
  · simp only [Option.bind_eq_bind, Option.bind_eq_some_iff] at h
    obtain ⟨old, hold, h⟩ := h
    exact save_all hP hs (hP.overlay_all (find_all hs hold) hn) hl h

theorem delete_all {st st' : Storage C} {U : Ty} {r : SRef C U}
    (hs : st.All P)
    (hl : (st.get r.hroot).Live r.path) (h : st.delete r = some st') : st'.All P := by
  simp only [Storage.delete, Option.bind_eq_bind, Option.bind_eq_some_iff] at h
  obtain ⟨old, hold, h⟩ := h
  exact save_all hP hs (hP.defaultOf_all (find_all hs hold)) hl h

theorem push_all {st st' : Storage C} {E : Ty} {r : SRef C (.ref (.array E))}
    {val : SVal E → Option (SVal E)} (hs : st.All P) (hG : G (.ref (.array E)))
    (hval : ∀ s x, s.All P → val s = some x → x.All P)
    (h : st.push r val = some st') : st'.All P := by
  unfold Storage.push at h
  simp only [Option.bind_eq_bind, Option.bind_eq_some_iff] at h
  obtain ⟨v, hv, h⟩ := h
  have hvA := find_all hs hv
  cases v with
  | array e sh hn =>
    simp only [SVal.view_array] at h
    obtain ⟨x, hx, h⟩ := h
    split at h
    · rename_i hb
      simp only [SVal.All] at hvA
      have hsl := hP.pushSlot_all (SList.all_iff.mp hvA.2.2)
      have hxA := hval _ x hsl.1 hx
      refine save_all hP hs ?_ (SVal.live_of_ref _ _ rfl) h
      simp only [SVal.All]
      refine ⟨hP.push e sh x hG hb hvA.1 hvA.2.1 hvA.2.2 hxA, SVec.all_ofList.mpr fun w hw => ?_,
        SList.all_ofList.mpr hsl.2⟩
      rcases List.mem_append.mp hw with hw | hw
      · exact SVec.all_iff.mp hvA.2.1 w hw
      · rw [List.mem_singleton.mp hw]; exact hxA
    · exact nomatch h

theorem pushPlace_all {st st' : Storage C} {E : Ty} {r : SRef C (.ref (.array E))}
    {k : PrimTy.uint.Denote}
    (hs : st.All P) (hG : G (.ref (.array E)))
    (h : st.pushPlace r = some (st', k)) : st'.All P :=
  push_all hP hs hG (fun _ _ hx e => Option.some.inj e ▸ hx) (Storage.push_of_pushPlace h)

theorem pop_all {st st' : Storage C} {E : Ty} {r : SRef C (.ref (.array E))} {keep : Bool}
    (hs : st.All P) (hkeep : keep = true → E.isPrimitive = false)
    (h : st.pop keep r = some st') : st'.All P := by
  unfold Storage.pop at h
  simp only [Option.bind_eq_bind, Option.bind_eq_some_iff] at h
  obtain ⟨v, hv, h⟩ := h
  have hvA := find_all hs hv
  cases v with
  | array e sh hn =>
    simp only [SVal.view_array] at h
    split at h
    · exact nomatch h
    · rename_i last rest hrev
      simp only [SVal.All] at hvA
      have hlast : last ∈ e.toList := by
        rw [← List.mem_reverse, hrev]; exact List.mem_cons_self
      have hlA := SVec.all_iff.mp hvA.2.1 last hlast
      have hy : (if keep then last else last.defaultOf).All P := by
        split
        · exact hlA
        · exact hP.defaultOf_all hlA
      refine save_all hP hs ?_ (SVal.live_of_ref _ _ rfl) h
      simp only [SVal.All]
      refine ⟨hP.pop e sh last keep hlast hkeep hvA.1 hvA.2.1 hvA.2.2,
        SVec.all_ofList.mpr fun w hw => SVec.all_iff.mp hvA.2.1 w (List.dropLast_subset _ hw),
        SList.all_ofList.mpr fun w hw => ?_⟩
      rcases List.mem_cons.mp hw with hw | hw
      · rw [hw]; exact hy
      · exact SList.all_iff.mp hvA.2.2 w hw

end Storage

/-! ## Resolved references -/

theorem SVal.live_nil {T : Ty} (x : SVal T) : x.Live .nil := by cases x <;> simp only [SVal.Live]

section Resolve

variable {Γ : Ctx} (σ : State C Γ)


/-- An index the program takes is in bounds where it takes it. -/
theorem Storage.checkIndex_some {st : Storage C} {R : RefTy} {k : PrimTy} {V : Ty}
    {r : SRef C (.ref R)} {it : IndexTy R k V} {i : k.Denote} (h : st.checkIndex r it i = some ()) :
    ∃ y, st.find r = some y ∧ Storage.inBounds it i y = some () := by
  simp only [Storage.checkIndex, Option.bind_eq_bind, Option.bind_eq_some_iff] at h
  exact h

/-- **A location resolves to live slots**: an index the program takes was
checked against the length where it took it, and a reference reaches no
array of words but at its last step. -/
theorem Loc.resolveT_live : {T : Ty} → (l : Loc C Γ T) → ∀ {r : SRef C T},
    l.resolveT σ = .ok r → (σ.storage.get r.hroot).Live r.path
  | _, .root _ _, r, h => by
    cases h
    exact SVal.live_nil _
  | _, .field b f hf, r, h => by
    obtain ⟨r0, h0, h⟩ := tbind_ok_inv h
    cases h
    show (σ.storage.get r0.hroot).Live (r0.path.append (.field hf .nil))
    refine SVal.live_append _ _ _ rfl fun y _ => ?_
    cases y with
    | struct fs => simp only [SVal.Live]
  | _, .index it b i, r, h => by
    obtain ⟨r0, h0, h⟩ := tbind_ok_inv h
    obtain ⟨k, _, h⟩ := tbind_ok_inv h
    obtain ⟨u, hck, h⟩ := tbind_ok_inv h
    cases h
    show (σ.storage.get r0.hroot).Live (r0.path.append (Path.index it k))
    obtain ⟨y0, hy0, hin⟩ := Storage.checkIndex_some (TRes.ofOpt_ok hck)
    refine SVal.live_append _ _ _ rfl fun y hy => ?_
    have hyy : y = y0 := by
      have : (σ.storage.get r0.hroot).find r0.path = some y := by
        rw [SVal.find_eq_findM]; exact hy
      rw [show σ.storage.find r0 = (σ.storage.get r0.hroot).find r0.path from rfl, this] at hy0
      exact Option.some.inj hy0
    subst hyy
    cases it with
    | map =>
      rw [Path.index_map]
      cases y with
      | map m d => simp only [SVal.Live]; split <;> trivial
    | arr a =>
      cases a with
      | dyn =>
        rw [Path.index_dyn]
        cases y with
        | array e sh hn =>
          change (if (k : PrimTy.uint.Denote).1.toNat < _ then some () else none) = _ at hin
          split at hin
          · rename_i hb
            simp only [SVal.Live]
            exact fun z _ => ⟨fun _ => hb, trivial⟩
          · exact nomatch hin
      | fixed =>
        rw [Path.index_fixed]
        cases y with
        | fixed e => simp only [SVal.Live]; exact fun _ _ => trivial

/-- A path resolves to live slots: an alias names a reference, which reaches
no array of words. -/
theorem SPath.resolveT_live : {T : Ty} → (b : SPath C Γ T) → ∀ {r : SRef C T},
    b.resolveT σ = .ok r → (σ.storage.get r.hroot).Live r.path
  | _, .alias _, _, _ => SVal.live_of_ref _ _ rfl
  | _, .loc l, _, h => Loc.resolveT_live σ l h

end Resolve

/-- In `values.push() += e`, the newly appended primitive slot is live
before the arithmetic write, even if it was recycled from the shadow. -/
theorem Storage.pushPlace_live {p : PrimTy} {st st' : Storage C}
    {r : SRef C (.array (.prim p))} {k : PrimTy.uint.Denote}
    (h : st.pushPlace r = some (st', k)) :
    (st'.get (r.index (.arr .dyn) k).hroot).Live (r.index (.arr .dyn) k).path := by
  obtain ⟨n, e, sh, hn, hcap, rfl, hf⟩ := Storage.pushPlace_shape h
  change (st'.get r.hroot).Live (r.path.append (Path.index (.arr .dyn) (lenU n hn)))
  refine SVal.live_append _ _ _ rfl fun y hy => ?_
  have hsame : y = SVal.array (SVec.ofList (e.toList ++ [(pushSlot (.prim p) sh.toList).1]))
      (.ofList (pushSlot (.prim p) sh.toList).2) (SVec.snoc_lt_bound e _ hcap) := by
    apply Option.some.inj
    exact hy.symm.trans (by rw [← SVal.find_eq_findM]; exact hf)
  subst y
  rw [Path.index_dyn]
  simp only [SVal.Live]
  intro z hz
  refine ⟨fun _ => ?_, trivial⟩
  simp only [lenU, Int.toNat_natCast, List.length_append, List.length_singleton,
    SVec.length_toList]
  omega

/-! ## The invariant -/

/-- What a run keeps of a hereditary predicate: the storage satisfies it. -/
def heredInv (C : Contract) (P : Hered) : RunInv C where
  glob st := st.All P
  loc _ _ := True
  loc_wk _ _ _ _ := trivial

theorem heredInv.valMemOk {P : Hered} : (heredInv C P).ValMemOk :=
  ⟨fun _ _ _ => trivial, fun _ _ _ => trivial, fun _ _ _ => trivial⟩

section Leaves

variable {P : Hered} {G : Ty → Prop} (hP : HeredRun P G) (hG : ∀ {U : Ty}, SRef C U → G U)
  {Γ : Ctx}

include hP in
/-- The storage value a source stores satisfies what the storage does. -/
theorem Src.valueT_all {σ : State C Γ} {T : Ty} (hg : G T) (hs : σ.storage.All P) :
    (r : Src C Γ T) → {v : SVal T} → r.valueT σ = .ok v → v.All P
  | .val _, v, h => by
    obtain ⟨x, _, h⟩ := tbind_ok_inv h
    cases h
    simp only [SVal.All]
  | .copy _ _, v, h => by
    obtain ⟨_, _, h⟩ := tbind_ok_inv h
    exact Storage.find_all hs (TRes.ofOpt_ok h)
  | .copyMem _, v, h => by
    obtain ⟨mv, _, h⟩ := tbind_ok_inv h
    cases h
    exact hP.plain _ hg (MVal.copyMToSt_plain σ.heap mv)
  | .fixedCopy _ shape hm, v, h => by
    obtain ⟨_, _, h⟩ := tbind_ok_inv h
    obtain ⟨sv, _, h⟩ := tbind_ok_inv h
    cases h
    exact hP.plain _ hg (shape.apply_plain sv hm)

include hP hG

theorem ARhs.evalT_all {σ : State C Γ} (hσ : (heredInv C P).HoldsT σ) {R : RefTy} :
    (r : ARhs C Γ R) → {st : Storage C} → {ref : SRef C (.ref R)} →
      r.evalT σ = .ok (st, ref) → st.All P
  | .path p, st, ref, h => by
    obtain ⟨r0, h0, h⟩ := tbind_ok_inv h
    cases h
    exact hσ.1
  | .push b _, st, ref, h => by
    obtain ⟨r0, h0, h⟩ := tbind_ok_inv h
    split at h
    · exact nomatch h
    · obtain ⟨⟨st', k⟩, hst, h⟩ := tbind_ok_inv h
      cases h
      exact Storage.pushPlace_all hP hσ.1 (hG r0) (TRes.ofOpt_ok hst)

omit hP hG in
theorem MRhs.evalT_holds {σ : State C Γ} (hσ : (heredInv C P).HoldsT σ) {R : RefTy} :
    (r : MRhs C Γ R) → {g : Grew C Γ σ.H (HRef · R)} → r.evalT σ = .ok g →
      (heredInv C P).HoldsT g.st
  | .alias _, g, h => by
    obtain ⟨_, _, h⟩ := tbind_ok_inv h
    cases h
    exact hσ
  | .copy _ _, g, h => by
    obtain ⟨_, _, h⟩ := tbind_ok_inv h
    obtain ⟨_, _, h⟩ := tbind_ok_inv h
    cases h
    exact hσ.adopt _
  | .newArr _ _, g, h => by
    cases h
    exact hσ.adopt _

omit hG in
theorem opStoreT_holds {σ : State C Γ} (hσ : (heredInv C P).HoldsT σ) (op : BinOp)
    {p : PrimTy} {r : SRef C (.prim p)}
    (hl : (σ.storage.get r.hroot).Live r.path) (v : p.Denote) {o : Out C σ.H Γ}
    (h : opStoreT σ op r v = .ok o) : (heredInv C P).HoldsT o.st := by
  unfold opStoreT at h
  obtain ⟨_, _, h⟩ := tbind_ok_inv h
  obtain ⟨_, _, h⟩ := tbind_ok_inv h
  obtain ⟨st, hst, h⟩ := tbind_ok_inv h
  cases h
  exact hσ.withStorage (Storage.save_all hP hσ.1 (by simp only [SVal.All]) hl (TRes.ofOpt_ok hst))

omit hP hG in
theorem opMemT_holds {σ : State C Γ} (hσ : (heredInv C P).HoldsT σ) (op : BinOp) {p : PrimTy}
    (a : MAddr σ.H (.prim p)) (v : p.Denote) {o : Out C σ.H Γ} (h : opMemT σ op a v = .ok o) :
    (heredInv C P).HoldsT o.st := by
  unfold opMemT at h
  obtain ⟨_, _, h⟩ := tbind_ok_inv h
  obtain ⟨_, _, h⟩ := tbind_ok_inv h
  obtain ⟨_, _, h⟩ := tbind_ok_inv h
  cases h
  exact hσ

omit hG in
theorem OpLoc.storeT_holds {σ : State C Γ} (hσ : (heredInv C P).HoldsT σ) (op : BinOp) :
    {p : PrimTy} → (l : OpLoc C Γ p) → (v : p.Denote) → {o : Out C σ.H Γ} →
      l.storeT σ op v = .ok o → (heredInv C P).HoldsT o.st
  | _, .local i, _, o, h => by
    obtain ⟨_, _, h⟩ := tbind_ok_inv h
    cases h
    exact hσ.setLocal i trivial
  | _, .root r hr, v, o, h =>
    opStoreT_holds hP hσ op (r := SRef.ofRoot r hr) (SVal.live_nil _) v h
  | _, .field b f hf, v, o, h => by
    obtain ⟨ref, href, h⟩ := tbind_ok_inv h
    exact opStoreT_holds hP hσ op
      (Loc.resolveT_live σ _ href) v h
  | _, .index it b i, v, o, h => by
    obtain ⟨ref, href, h⟩ := tbind_ok_inv h
    exact opStoreT_holds hP hσ op
      (Loc.resolveT_live σ _ href) v h
  | _, .mfield .., v, o, h => by
    obtain ⟨a, _, h⟩ := tbind_ok_inv h
    exact opMemT_holds hσ op a v h
  | _, .mindex .., v, o, h => by
    obtain ⟨a, _, h⟩ := tbind_ok_inv h
    exact opMemT_holds hσ op a v h

omit hG in
theorem bumpStoreT_holds {σ : State C Γ} (hσ : (heredInv C P).HoldsT σ) (op : IncDec)
    {p : PrimTy} {r : SRef C (.prim p)}
    (hl : (σ.storage.get r.hroot).Live r.path) {o : Out C σ.H Γ} {w : p.Denote}
    (h : bumpStoreT σ op r = .ok (o, w)) : (heredInv C P).HoldsT o.st := by
  unfold bumpStoreT at h
  obtain ⟨_, _, h⟩ := tbind_ok_inv h
  obtain ⟨_, _, h⟩ := tbind_ok_inv h
  obtain ⟨st, hst, h⟩ := tbind_ok_inv h
  cases h
  exact hσ.withStorage (Storage.save_all hP hσ.1 (by simp only [SVal.All]) hl (TRes.ofOpt_ok hst))

omit hP hG in
theorem bumpMemT_holds {σ : State C Γ} (hσ : (heredInv C P).HoldsT σ) (op : IncDec) {p : PrimTy}
    (a : MAddr σ.H (.prim p)) {o : Out C σ.H Γ} {w : p.Denote} (h : bumpMemT σ op a = .ok (o, w)) :
    (heredInv C P).HoldsT o.st := by
  unfold bumpMemT at h
  obtain ⟨_, _, h⟩ := tbind_ok_inv h
  obtain ⟨_, _, h⟩ := tbind_ok_inv h
  obtain ⟨_, _, h⟩ := tbind_ok_inv h
  cases h
  exact hσ

omit hG in
theorem OpLoc.bumpT_holds {σ : State C Γ} (hσ : (heredInv C P).HoldsT σ) (op : IncDec) :
    {p : PrimTy} → (l : OpLoc C Γ p) → {o : Out C σ.H Γ} → {w : p.Denote} →
      l.bumpT σ op = .ok (o, w) → (heredInv C P).HoldsT o.st
  | _, .local i, o, w, h => by
    obtain ⟨_, _, h⟩ := tbind_ok_inv h
    cases h
    exact hσ.setLocal i trivial
  | _, .root r hr, o, w, h =>
    bumpStoreT_holds hP hσ op (r := SRef.ofRoot r hr) (SVal.live_nil _) h
  | _, .field b f hf, o, w, h => by
    obtain ⟨ref, href, h⟩ := tbind_ok_inv h
    exact bumpStoreT_holds hP hσ op
      (Loc.resolveT_live σ _ href) h
  | _, .index it b i, o, w, h => by
    obtain ⟨ref, href, h⟩ := tbind_ok_inv h
    exact bumpStoreT_holds hP hσ op
      (Loc.resolveT_live σ _ href) h
  | _, .mfield .., o, w, h => by
    obtain ⟨a, _, h⟩ := tbind_ok_inv h
    exact bumpMemT_holds hσ op a h
  | _, .mindex .., o, w, h => by
    obtain ⟨a, _, h⟩ := tbind_ok_inv h
    exact bumpMemT_holds hσ op a h

omit hP hG in
theorem clearT_holds {σ : State C Γ} (hσ : (heredInv C P).HoldsT σ) :
    {T : Ty} → (a : MAddr σ.H T) → (hm : T.mapFree = true) → {o : Out C σ.H Γ} →
      TRun.clearT σ a hm = .ok o → (heredInv C P).HoldsT o.st
  | .prim _, _, _, o, h => by
    obtain ⟨_, _, h⟩ := tbind_ok_inv h
    cases h
    exact hσ
  | .ref R, a, hm, o, h => by
    simp only [TRun.clearT] at h
    split at h
    · cases h
      exact hσ.adopt _
    · exact nomatch h

theorem keeps_assign {T : Ty} (l : Loc C Γ T) (r : Src C Γ T) :
    (heredInv C P).TKeeps (TRun.assign l r) := by
  intro σ o hσ h
  unfold TRun.assign at h
  obtain ⟨sv, hsv, h⟩ := tbind_ok_inv h
  obtain ⟨ref, href, h⟩ := tbind_ok_inv h
  obtain ⟨st, hst, h⟩ := tbind_ok_inv h
  cases h
  exact hσ.withStorage (Storage.write_all hP hσ.1 (Src.valueT_all hP (hG ref) hσ.1 r hsv)
    (Loc.resolveT_live σ l href) (TRes.ofOpt_ok hst))

theorem keeps_rebind {R : RefTy} (i : Idx Γ (.alias R)) (r : ARhs C Γ R) :
    (heredInv C P).TKeeps (TRun.rebind i r) := by
  intro σ o hσ h
  unfold TRun.rebind at h
  obtain ⟨⟨st, ref⟩, he, h⟩ := tbind_ok_inv h
  cases h
  exact (hσ.withStorage (ARhs.evalT_all hP hG hσ r he)).setLocal i trivial

omit hP hG in
theorem keeps_assignLocal {p : PrimTy} (i : Idx Γ (.val p)) (r : Val C Γ p) :
    (heredInv C P).TKeeps (TRun.assignLocal i r) := by
  intro σ o hσ h
  unfold TRun.assignLocal at h
  obtain ⟨_, _, h⟩ := tbind_ok_inv h
  cases h
  exact hσ.setLocal i trivial

omit hP hG in
theorem keeps_declLocal (p : PrimTy) (init : Option (Val C Γ p)) :
    (heredInv C P).TKeeps (TRun.declLocal p init) := by
  intro σ o hσ h
  unfold TRun.declLocal at h
  cases init with
  | none => cases h; exact hσ.push trivial
  | some e =>
    dsimp only at h
    obtain ⟨_, _, h⟩ := tbind_ok_inv h
    cases h
    exact hσ.push trivial

theorem keeps_declStorage (R : RefTy) (init : Option (ARhs C Γ R)) :
    (heredInv C P).TKeeps (TRun.declStorage R init) := by
  intro σ o hσ h
  unfold TRun.declStorage at h
  cases init with
  | none => cases h; exact hσ.push trivial
  | some r =>
    obtain ⟨⟨st, ref⟩, he, h⟩ := tbind_ok_inv h
    cases h
    exact (hσ.withStorage (ARhs.evalT_all hP hG hσ r he)).push trivial

omit hG in
theorem keeps_opAssign {p : PrimTy} (op : BinOp) (l : OpLoc C Γ p) (r : Val C Γ p) :
    (heredInv C P).TKeeps (TRun.opAssign op l r) := by
  intro σ o hσ h
  unfold TRun.opAssign at h
  obtain ⟨v, _, h⟩ := tbind_ok_inv h
  exact OpLoc.storeT_holds hP hσ op l v h

omit hG in
theorem keeps_incDec {p : PrimTy} (op : IncDec) (l : OpLoc C Γ p) :
    (heredInv C P).TKeeps (TRun.incDec op l) := by
  intro σ o hσ h
  unfold TRun.incDec at h
  obtain ⟨⟨o', w⟩, hb, h⟩ := tbind_ok_inv h
  cases h
  exact OpLoc.bumpT_holds hP hσ op l hb

omit hG in
theorem keeps_assignIncDec {p : PrimTy} (i : Idx Γ (.val p)) (op : IncDec) (l : OpLoc C Γ p) :
    (heredInv C P).TKeeps (TRun.assignIncDec i op l) := by
  intro σ o hσ h
  unfold TRun.assignIncDec at h
  obtain ⟨⟨o', w⟩, hb, h⟩ := tbind_ok_inv h
  cases h
  exact (OpLoc.bumpT_holds hP hσ op l hb).setLocal i trivial

theorem keeps_push {E : Ty} (b : SPath C Γ (.array E)) (v : Option (Src C Γ E)) :
    (heredInv C P).TKeeps (TRun.push b v) := by
  intro σ o hσ h
  unfold TRun.push at h
  obtain ⟨ref, href, h⟩ := tbind_ok_inv h
  obtain ⟨x, hx, h⟩ : ∃ x : Option (SVal E), (∀ x0, x = some x0 → x0.All P) ∧
      (if σ.storage.full ref = true then Except.error THalt.exhausted
       else do
        let st ← TRes.ofOpt (σ.storage.push ref fun slot => some (x.getD slot))
        pure ({ st := σ.withStorage st, ext := List.prefix_refl _ } : Out C σ.H Γ)) = .ok o := by
    cases v with
    | none => exact ⟨none, (fun _ h => nomatch h), h⟩
    | some r =>
      dsimp only at h
      obtain ⟨sv, hsv, h⟩ := tbind_ok_inv h
      refine ⟨some sv.strip, (fun x0 hx0 => ?_), h⟩
      cases hx0
      exact hP.strip_all (Src.valueT_all hP (hG (ref.index (.arr .dyn) (PrimTy.dflt .uint))) hσ.1 r hsv)
  split at h
  · exact nomatch h
  · obtain ⟨st, hst, h⟩ := tbind_ok_inv h
    cases h
    refine hσ.withStorage (Storage.push_all hP hσ.1 (hG ref)
      (fun s y hs hy => ?_) (TRes.ofOpt_ok hst))
    cases hy
    cases x with
    | none => exact hs
    | some x0 => exact hx x0 rfl

/-- The deferred operand of `f().push(e)` retains hereditary storage facts. -/
theorem keeps_pushAfterPrefix {Γv : Ctx} {E : Ty} (he : Ext Γ Γv)
    (code : TStep C Γ Γv) (value : Src C Γv E) (ref : SRef C (.array E))
    (hc : (heredInv C P).TKeeps code) :
    (heredInv C P).TKeeps (TRun.pushAfterPrefix he code value ref) := by
  intro σ o hσ h
  unfold TRun.pushAfterPrefix at h
  obtain ⟨a, ha, h⟩ := tbind_ok_inv h
  have hσ' : (heredInv C P).HoldsT a.st := hc σ a hσ ha
  obtain ⟨v, hv, h⟩ := tbind_ok_inv h
  split at h
  · exact nomatch h
  · obtain ⟨st, hst, h⟩ := tbind_ok_inv h
    cases h
    have hx : v.strip.All P := hP.strip_all
      (Src.valueT_all hP (hG (ref.index (.arr .dyn) (PrimTy.dflt .uint))) hσ'.1 value hv)
    refine (hσ'.withStorage (Storage.push_all hP hσ'.1 (hG ref)
      (fun s y hs hy => ?_) (TRes.ofOpt_ok hst))).drop he
    cases hy
    exact hx

theorem keeps_assignLocalPush {p : PrimTy} (i : Idx Γ (.val p)) (b : SPath C Γ (.array (.prim p))) :
    (heredInv C P).TKeeps (TRun.assignLocalPush i b) := by
  intro σ o hσ h
  unfold TRun.assignLocalPush at h
  obtain ⟨o', ho', h⟩ := tbind_ok_inv h
  cases h
  exact (keeps_push hP hG b none σ o' hσ ho').setLocal i trivial

/-- `values.push() += e` preserves the hereditary storage invariant through
the append/reset and then the primitive arithmetic save. -/
theorem keeps_pushOpAssign {p : PrimTy} (op : BinOp) (b : SPath C Γ (.array (.prim p)))
    (r : Val C Γ p) : (heredInv C P).TKeeps (TRun.pushOpAssign op b r) := by
  intro σ o hσ h
  unfold TRun.pushOpAssign at h
  obtain ⟨v, _, h⟩ := tbind_ok_inv h
  obtain ⟨ref, _, h⟩ := tbind_ok_inv h
  split at h
  · cases h
  · obtain ⟨⟨st, k⟩, hs, h⟩ := tbind_ok_inv h
    have hs' : σ.storage.pushPlace ref = some (st, k) := TRes.ofOpt_ok hs
    have hst := hσ.withStorage (Storage.pushPlace_all hP hσ.1 (hG ref) hs')
    exact opStoreT_holds hP hst op (Storage.pushPlace_live hs') v h

/-- Standalone prefix/postfix `values.push()++` preserves the hereditary
storage invariant; the returned numeric value is discarded. -/
theorem keeps_pushIncDec {p : PrimTy} (op : IncDec) (b : SPath C Γ (.array (.prim p))) :
    (heredInv C P).TKeeps (TRun.pushIncDec op b) := by
  intro σ o hσ h
  unfold TRun.pushIncDec at h
  obtain ⟨ref, _, h⟩ := tbind_ok_inv h
  split at h
  · cases h
  · obtain ⟨⟨st, k⟩, hs, h⟩ := tbind_ok_inv h
    obtain ⟨⟨o', value⟩, hb, h⟩ := tbind_ok_inv h
    cases h
    have hs' : σ.storage.pushPlace ref = some (st, k) := TRes.ofOpt_ok hs
    have hst := hσ.withStorage (Storage.pushPlace_all hP hσ.1 (hG ref) hs')
    exact bumpStoreT_holds hP hst op (Storage.pushPlace_live hs') hb

omit hG in
theorem keeps_pop {E : Ty} (b : SPath C Γ (.array E)) : (heredInv C P).TKeeps (TRun.pop b) := by
  intro σ o hσ h
  unfold TRun.pop at h
  obtain ⟨ref, href, h⟩ := tbind_ok_inv h
  obtain ⟨st, hst, h⟩ := tbind_ok_inv h
  cases h
  refine hσ.withStorage (Storage.pop_all hP hσ.1
    (fun hm => ?_) (TRes.ofOpt_ok hst))
  cases E with
  | prim _ => exact nomatch hm
  | ref _ => rfl

omit hP hG in
theorem keeps_transfer (r a : Val C Γ .uint) : (heredInv C P).TKeeps (TRun.transfer r a) := by
  intro σ o hσ h
  unfold TRun.transfer at h
  obtain ⟨_, _, h⟩ := tbind_ok_inv h
  obtain ⟨_, _, h⟩ := tbind_ok_inv h
  cases h
  exact hσ

omit hP hG in
theorem keeps_send (pv : Idx Γ (.val .bool)) (r a : Val C Γ .uint) :
    (heredInv C P).TKeeps (TRun.send pv r a) := by
  intro σ o hσ h
  unfold TRun.send at h
  obtain ⟨_, _, h⟩ := tbind_ok_inv h
  obtain ⟨_, _, h⟩ := tbind_ok_inv h
  cases h
  unfold sendT
  split
  · exact RunInv.HoldsT.setLocal (I := heredInv C P) (σ := σ.pay _ _) hσ pv trivial
  · exact hσ.setLocal pv trivial
  · exact hσ.setLocal pv trivial

omit hP hG in
theorem keeps_declMem (R : RefTy) (init : Option (MRhs C Γ R)) (hm : (Ty.ref R).mapFree = true) :
    (heredInv C P).TKeeps (TRun.declMem R init hm) := by
  intro σ o hσ h
  unfold TRun.declMem at h
  cases init with
  | none => cases h; exact (hσ.adopt _).push trivial
  | some r =>
    obtain ⟨g, hg, h⟩ := tbind_ok_inv h
    cases h
    exact (MRhs.evalT_holds hσ r hg).push trivial

omit hP hG in
theorem keeps_rebindMem {R : RefTy} (i : Idx Γ (.mem R)) (r : MRhs C Γ R) :
    (heredInv C P).TKeeps (TRun.rebindMem i r) := by
  intro σ o hσ h
  unfold TRun.rebindMem at h
  obtain ⟨g, hg, h⟩ := tbind_ok_inv h
  cases h
  exact (MRhs.evalT_holds hσ r hg).setLocal i trivial

theorem keeps_assignFromMem {R : RefTy} (l : Loc C Γ (.ref R)) (p : MPath C Γ (.ref R)) :
    (heredInv C P).TKeeps (TRun.assignFromMem l p) := by
  intro σ o hσ h
  unfold TRun.assignFromMem at h
  obtain ⟨m, _, h⟩ := tbind_ok_inv h
  obtain ⟨ref, href, h⟩ := tbind_ok_inv h
  obtain ⟨st, hst, h⟩ := tbind_ok_inv h
  cases h
  exact hσ.withStorage (Storage.write_all hP hσ.1
    (hP.plain _ (hG ref) (MVal.copyMToSt_plain σ.heap m))
    (Loc.resolveT_live σ l href) (TRes.ofOpt_ok hst))

omit hP hG in
theorem keeps_assignMem {T : Ty} (l : MLoc C Γ T) (r : MSrc C Γ T) :
    (heredInv C P).TKeeps (TRun.assignMem l r) := by
  intro σ o hσ h
  unfold TRun.assignMem at h
  obtain ⟨_, _, h⟩ := tbind_ok_inv h
  obtain ⟨_, _, h⟩ := tbind_ok_inv h
  obtain ⟨_, _, h⟩ := tbind_ok_inv h
  cases h
  exact hσ

omit hG in
theorem keeps_delete {T : Ty} (l : Loc C Γ T) : (heredInv C P).TKeeps (TRun.delete l) := by
  intro σ o hσ h
  unfold TRun.delete at h
  obtain ⟨ref, href, h⟩ := tbind_ok_inv h
  obtain ⟨st, hst, h⟩ := tbind_ok_inv h
  cases h
  exact hσ.withStorage (Storage.delete_all hP hσ.1
    (Loc.resolveT_live σ l href) (TRes.ofOpt_ok hst))

omit hP hG in
theorem keeps_deleteMem {T : Ty} (p : MPath C Γ T) : (heredInv C P).TKeeps (TRun.deleteMem p) := by
  intro σ o hσ h
  unfold TRun.deleteMem at h
  cases p with
  | var i _ => cases h; exact (hσ.adopt _).setLocal i trivial
  | loc l =>
    obtain ⟨a, _, h⟩ := tbind_ok_inv h
    exact clearT_holds hσ a l.mapFree h

theorem keeps_assignNew {R : RefTy} (l : NewLhs C Γ R) (n : Simple C Γ .uint)
    (hn : R.newArrOk = true) : (heredInv C P).TKeeps (TRun.assignNew l n hn) := by
  intro σ o hσ h
  unfold TRun.assignNew at h
  have hg : (heredInv C P).HoldsT
      (σ.copyStToMG (newArrT R (n.evalT σ) hn) (RefTy.mapFree_of_newArrOk hn)).st :=
    hσ.adopt _
  cases l with
  | store l =>
    obtain ⟨ref, href, h⟩ := tbind_ok_inv h
    obtain ⟨st, hst, h⟩ := tbind_ok_inv h
    cases h
    exact hg.withStorage (Storage.write_all hP hg.1
      (hP.plain _ (hG ref) (MVal.copyMToSt_plain _ _))
      (Loc.resolveT_live _ l href) (TRes.ofOpt_ok hst))
  | mem l =>
    obtain ⟨_, _, h⟩ := tbind_ok_inv h
    obtain ⟨_, _, h⟩ := tbind_ok_inv h
    cases h
    exact hg

end Leaves

section Run

variable {P : Hered} {G : Ty → Prop}

mutual

/-- **A hereditary predicate, statement level.**  A statement run from a
state whose storage satisfies it, its aliases bound along keys a program
writes, ends in one. -/
theorem Stmt.keeps_all (hP : HeredRun P G) (hG : ∀ {U : Ty}, SRef C U → G U) :
    {Γ Γ' : Ctx} → (s : Stmt C Γ Γ') → (heredInv C P).TKeeps (Stmt.runR s)
  | _, _, .assign l r => keeps_assign hP hG l r
  | _, _, .rebind i r => keeps_rebind hP hG i r
  | _, _, .assignLocal i r => keeps_assignLocal i r
  | _, _, .declLocal p _ init => keeps_declLocal p init
  | _, _, .declStorage R _ init => keeps_declStorage hP hG R init
  | _, _, .opAssign op _ _ l r => keeps_opAssign hP op l r
  | _, _, .incDec op _ l => keeps_incDec hP op l
  | _, _, .pushOpAssign op _ _ b r => keeps_pushOpAssign hP hG op b r
  | _, _, .pushIncDec op _ b => keeps_pushIncDec hP hG op b
  | _, _, .assignIncDec i op _ l _ => keeps_assignIncDec hP i op l
  | _, _, .assignLocalPush i b => keeps_assignLocalPush hP hG i b
  | _, _, .push b v _ => keeps_push hP hG b v
  | _, _, .pop b => keeps_pop hP b
  | _, _, .transfer r a => keeps_transfer r a
  | _, _, .send pv r a _ => keeps_send pv r a
  | _, _, .declMem R _ init _ hm => keeps_declMem R init hm
  | _, _, .rebindMem i r => keeps_rebindMem i r
  | _, _, .assignFromMem l p => keeps_assignFromMem hP hG l p
  | _, _, .assignMem l r => keeps_assignMem l r
  | _, _, .delete l => keeps_delete hP l
  | _, _, .deleteMem p _ => keeps_deleteMem p
  | _, _, .assignNew l n hn => keeps_assignNew hP hG l n hn
  | _, _, .ite c thn els =>
    RunInv.tkeeps_ite c thn.ext els.ext (Prog.keeps_all hP hG thn) (Prog.keeps_all hP hG els)
  | _, _, .require c => RunInv.tkeeps_require c
  | _, _, .assert c => RunInv.tkeeps_assert c
  | _, _, .revert => RunInv.tkeeps_revert
  | _, _, .assumeFalse => RunInv.tkeeps_exhausted
  | _, _, .call _ args ret body =>
    RunInv.tkeeps_call heredInv.valMemOk args ret body.ext (Prog.keeps_all hP hG body)
  | _, _, .callReceiver _ args r body op => by
    intro σ o hσ h
    change TRun.callReceiver args r body.ext body.runR op σ = .ok o at h
    rw [TRun.callReceiver_eq_seq] at h
    refine RunInv.tkeeps_seq
      (RunInv.tkeeps_call heredInv.valMemOk args (.storage _ r) body.ext
        (Prog.keeps_all hP hG body)) ?_ σ o hσ h
    cases op with
    | push v _ =>
      exact (keeps_push hP hG (.alias .here) (v.map (·.wk (.drop .refl)))).drop
        (.push .refl)
    | pop => exact (keeps_pop hP (.alias .here)).drop (.push .refl)
  | _, _, .callReceiverPush _ args r body code value => by
    intro σ o hσ h
    change TRun.callReceiverPush args r body.ext body.runR code.ext code.runR value σ = .ok o at h
    rw [TRun.callReceiverPush_eq_seq] at h
    refine RunInv.tkeeps_seq
      (RunInv.tkeeps_call heredInv.valMemOk args (.storage _ r) body.ext
        (Prog.keeps_all hP hG body)) ?_ σ o hσ h
    intro τ v hτ hv
    unfold TRun.afterReceiverPrefix at hv
    obtain ⟨ref, _, hv⟩ := tbind_ok_inv hv
    exact keeps_pushAfterPrefix hP hG code.ext code.runR value ref
      (Prog.keeps_all hP hG code) _ _ (hτ.drop (.push .refl)) hv
  | _, _, .tryCall call rets ok err code pnc other =>
    RunInv.tkeeps_tryCall heredInv.valMemOk call rets ok.ext err.ext code pnc.ext other.ext
      (Prog.keeps_all hP hG ok) (Prog.keeps_all hP hG err) (Prog.keeps_all hP hG pnc) (Prog.keeps_all hP hG other)
  | _, _, .loop _ c body => RunInv.tkeeps_loop c body.ext (Prog.keeps_all hP hG body)
  | _, _, .block body => RunInv.tkeeps_block body.ext (Prog.keeps_all hP hG body)

/-- **A hereditary predicate, block level.** -/
theorem Prog.keeps_all (hP : HeredRun P G) (hG : ∀ {U : Ty}, SRef C U → G U) :
    {Γ Γ' : Ctx} → (P' : Prog C Γ Γ') → (heredInv C P).TKeeps (Prog.runR P')
  | _, _, .nil => RunInv.tkeeps_nil
  | _, _, .cons s P' => RunInv.tkeeps_seq (Stmt.keeps_all hP hG s) (Prog.keeps_all hP hG P')

end

/-- **What a run keeps**: a block run from a state whose storage satisfies
the predicate, with no alias bound off the keys a program writes, ends, if in
a state, in one whose storage satisfies it. -/
theorem Prog.run_all (hP : HeredRun P G) (hG : ∀ {U : Ty}, SRef C U → G U) {Γ Γ' : Ctx} (P' : Prog C Γ Γ') {σ : State C Γ} {o : Out C σ.H Γ'}
    (hσ : (heredInv C P).HoldsT σ) (h : P'.run σ = .ok o) : o.st.storage.All P :=
  (Prog.keeps_all hP hG P' σ o hσ h).1

end Run

end Solidity
