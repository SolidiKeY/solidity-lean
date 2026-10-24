import Solidity.Calculus.DecideEval.Storages

/-!
# The reduction's evaluation: memory, and the elimination

Reads of memory, a memory object read as the stored value it copies to,
and the elimination keeping what a term reads.

A piece of `Calculus/DecideEval.lean`, whose docstring describes the whole.
-/

namespace Solidity

namespace Decide

open Semantics

variable {C : Contract} (g : State C []) (ν : AEnv)

/-! ## Reads of memory -/

section

variable {g : State C []} {ν : AEnv}

theorem LTm.read_evalT {P : PrimTy} (X : LTm C .mem) (b : LTm C (.addr (.prim P))) :
    ((LTm.app2 .read X b).eval g ν : Option P.Denote) =
      ((X.eval g ν : Option (Grown g.H (fun _ => Unit))).bind fun μ =>
        (b.eval g ν : Option (MAddrT (.prim P))).bind fun bd =>
          (bd.resolve μ.H').bind fun rb => μ.heap.readAddr rb) := rfl

theorem LTm.iread_evalT {R : RefTy} (X : LTm C .mem) (b : LTm C (.addr (.ref R))) :
    ((LTm.app2 .iread X b).eval g ν : Option Nat) =
      ((X.eval g ν : Option (Grown g.H (fun _ => Unit))).bind fun μ =>
        (b.eval g ν : Option (MAddrT (.ref R))).bind fun bd =>
          ((bd.resolve μ.H').bind fun rb => μ.heap.readAddr rb).bind fun r => some r.id) := rfl

theorem LTm.mlen_evalT {E : Ty} (X : LTm C .mem) (t : LTm C (.ident (.array E))) :
    ((LTm.app2 .mlen X t).eval g ν : Option PrimTy.uint.Denote) =
      ((X.eval g ν : Option (Grown g.H (fun _ => Unit))).bind fun μ =>
        (t.eval g ν : Option Nat).bind fun id =>
          (HRef.ofId? μ.H' (.array E) id).map fun r => μ.heap.lenU r) := by
  rw [LTm.eval_app2, Op2.eval_eq_evalM]
  cases (X.eval g ν : Option (Grown g.H (fun _ => Unit))) with
  | none => rfl
  | some μ =>
    cases (t.eval g ν : Option Nat) with
    | none => rfl
    | some id =>
      show (HRef.ofId? μ.H' (.array E) id).bind (fun r => some (μ.heap.lenU r)) =
        (HRef.ofId? μ.H' (.array E) id).map fun r => μ.heap.lenU r
      cases HRef.ofId? μ.H' (.array E) id <;> rfl

end

/-! ## A memory object, read as the stored value it copies to -/

section CopyMem

variable {M : LTm C .mem} {μ : Grown g.H (fun _ => Unit)}

/-- What a memory reader's location stands at: the word a word's copy
holds, read there; the object a reference's copy copies. -/
def MLoc.Rep (M : LTm C .mem) (μ : Grown g.H (fun _ => Unit)) : (T : Ty) → MLoc C T → SVal T → Prop
  | .prim P, loc, v => ∃ w : P.Denote,
      ((LTm.app2 .read M (loc : LTm C (.addr (.prim P)))).eval g ν : Option P.Denote) = some w ∧
        v = .prim w
  | .ref R, loc, v => ∃ r : HRef μ.H' R, ((loc : LTm C (.ident R)).eval g ν : Option Nat) = some r.id ∧
      v = MVal.copyMToSt μ.heap (T := .ref R) r

/-- The location at an address that reads `mv` stands at its copy. -/
theorem MLoc.ofAddr_rep (hM : M.eval g ν = some μ) {T : Ty} {a : LTm C (.addr T)} {ad : MAddrT T}
    {ra : MAddr μ.H' T} {mv : MVal μ.H' T} (ha : (a.eval g ν : Option (MAddrT T)) = some ad)
    (hra : ad.resolve μ.H' = some ra) (hmv : μ.heap.readAddr ra = some mv) :
    MLoc.Rep g ν M μ T (MLoc.ofAddr M T a) (MVal.copyMToSt μ.heap mv) := by
  cases T with
  | prim P =>
    refine ⟨mv, ?_, MVal.copyMToSt_prim μ.heap mv⟩
    show ((LTm.app2 .read M a).eval g ν : Option P.Denote) = _
    rw [LTm.read_evalT, hM, Option.bind_some, ha, Option.bind_some, hra, Option.bind_some, hmv]
  | ref R =>
    refine ⟨mv, ?_, rfl⟩
    show ((LTm.app2 .iread M a).eval g ν : Option Nat) = _
    rw [LTm.iread_evalT, hM, Option.bind_some, ha, Option.bind_some, hra, Option.bind_some, hmv]
    rfl

theorem bind_findM_nil_isSome {H : HTy} {T : Ty} (l : List (MVal H T)) (f : MVal H T → SVal T)
    (n : Nat) : (l[n]?.bind fun v => (f v).findM .nil).isSome = decide (n < l.length) := by
  by_cases hn : n < l.length
  · rw [List.getElem?_eq_getElem hn, Option.bind_some, SVal.findM_nil', decide_eq_true hn]; rfl
  · rw [List.getElem?_eq_none (by omega), decide_eq_false hn]; rfl

/-- **The memory reader reads the copy** (`selectOnCopyMem`): at segments
that evaluate, what the copy observes there, where its location stands at
the copy and `h` says whether the copy is there. -/
theorem memRd_rep (hM : M.eval g ν = some μ) {T V : Ty} (r : TSegs C T V) :
    ∀ (loc : MLoc C T) (h : LTm C (.val .bool)) (x : Option (SVal T)),
      (h.eval g ν : Option Bool) = some x.isSome → (∀ v, x = some v → MLoc.Rep g ν M μ T loc v) →
      ∀ (c : CK V) (p : Path T V), r.eval g ν = some p →
        ((memRd M r loc h c).eval g ν : Option c.out.Denote) =
          some (c.obsC fun cc => cc.ofOpt (x.bind (·.findM p))) := by
  induction r with
  | nil =>
    intro loc h x hh hx c p hp
    cases hp
    have hb : x.bind (·.findM .nil) = x := by
      cases x with
      | none => rfl
      | some v => exact SVal.findM_nil' v
    rw [hb]
    cases c with
    | word P =>
      show ((LTm.kite h .tt (.app2 .read M loc) (.lit (PrimTy.dflt P))).eval g ν :
        Option P.Denote) = _
      rw [LTm.eval_kite, hh]
      cases x with
      | none => rfl
      | some v =>
        obtain ⟨w, hw, rfl⟩ := hx _ rfl
        change (if (true : Bool) = true then ((LTm.app2 .read M loc).eval g ν : Option P.Denote)
          else ((LTm.lit (PrimTy.dflt P) : LTm C (.val P)).eval g ν)) = _
        rw [if_pos rfl, hw]; rfl
    | len E =>
      show ((LTm.kite h .tt (.app2 .mlen M loc) (.nat 0)).eval g ν : Option PrimTy.uint.Denote) = _
      rw [LTm.eval_kite, hh]
      cases x with
      | none => rfl
      | some v =>
        obtain ⟨r, hr, rfl⟩ := hx _ rfl
        change (if (true : Bool) = true then
          ((LTm.app2 .mlen M loc).eval g ν : Option PrimTy.uint.Denote)
          else ((LTm.nat 0 : LTm C (.val .uint)).eval g ν)) = _
        rw [if_pos rfl, LTm.mlen_evalT, hM, Option.bind_some, hr, Option.bind_some,
          HRef.ofId?_self, Option.map_some]
        refine congrArg some ?_
        show μ.heap.lenU r = uintOfNat (SVal.lenOf (some (MVal.copyMToSt μ.heap (T := .ref _) r)))
        simp only [SVal.lenOf, MVal.copyMToSt_len, uintOfNat, dif_pos (μ.heap.len_dyn_lt r)]
        rfl
    | has V => exact hh
  | field hf rest ih =>
    intro loc h x hh hx c p hp
    rw [TSegs.eval_field] at hp
    obtain ⟨p', hp', rfl⟩ := Option.map_eq_some_iff.1 hp
    have e : x.bind (·.findM (.field hf p')) =
        (x.bind (·.findM (.field hf .nil))).bind (·.findM p') := by
      cases x with
      | none => rfl
      | some v =>
        simp only [Option.bind_some]
        rw [← SVal.findM_append, Path.append_field, Path.append_nil]
    rw [e]
    refine ih _ h _ ?_ ?_ c p' hp'
    · cases x with
      | none => exact hh
      | some v =>
        obtain ⟨r, hr, rfl⟩ := hx _ rfl
        rw [hh, Option.bind_some, MVal.copyMToSt_findM_field, SVal.findM_nil']
        rfl
    · intro v' hv'
      cases x with
      | none => cases hv'
      | some v =>
        obtain ⟨r, hr, rfl⟩ := hx _ rfl
        rw [Option.bind_some, MVal.copyMToSt_findM_field, SVal.findM_nil',
          Option.some.injEq] at hv'
        subst hv'
        refine MLoc.ofAddr_rep g ν hM (ad := .field r.id hf) (ra := .field r hf) ?_ ?_ rfl
        · rw [LTm.eval_app1, hr]; rfl
        · simp only [MAddrT.resolve_eq_resolveM, MAddrT.resolveM, HRef.ofId?_self,
            Option.map_some]
  | «at» i rest ih =>
    intro loc h x hh hx c p hp
    rw [TSegs.eval_at] at hp
    obtain ⟨k, hk, hp⟩ := Option.bind_eq_some_iff.1 hp
    obtain ⟨p', hp', rfl⟩ := Option.map_eq_some_iff.1 hp
    have e : x.bind (·.findM (.at k p')) =
        (x.bind (·.findM (.at k .nil))).bind (·.findM p') := by
      cases x with
      | none => rfl
      | some v =>
        simp only [Option.bind_some]
        rw [← SVal.findM_append, Path.append_at, Path.append_nil]
    rw [e]
    refine ih _ _ _ ?_ ?_ c p' hp'
    · rw [LTm.eval_kite, hh]
      cases x with
      | none => rfl
      | some v =>
        obtain ⟨r, hr, rfl⟩ := hx _ rfl
        change (if (true : Bool) = true then ((LTm.lt i (.app2 .mlen M loc)).eval g ν : Option Bool)
          else ((LTm.lit (p := .bool) false : LTm C (.val .bool)).eval g ν)) = _
        rw [if_pos rfl, LTm.eval_lt, hk, Option.bind_some, LTm.mlen_evalT, hM, Option.bind_some, hr,
          Option.bind_some, HRef.ofId?_self, Option.map_some, Option.map_some, Option.bind_some,
          MVal.copyMToSt_findM_at, bind_findM_nil_isSome]
        have e' : (μ.heap.lenU r).1 = (μ.heap.len r .dyn : Int) := rfl
        refine congrArg some ?_
        rw [e']
        simp only [Heap.len, decide_eq_decide]
        have := PrimTy.uint_nonneg k
        omega
    · intro v' hv'
      cases x with
      | none => cases hv'
      | some v =>
        obtain ⟨r, hr, rfl⟩ := hx _ rfl
        rw [Option.bind_some, MVal.copyMToSt_findM_at] at hv'
        obtain ⟨mv, hmv, hv'⟩ := Option.bind_eq_some_iff.1 hv'
        rw [SVal.findM_nil', Option.some.injEq] at hv'
        subst hv'
        refine MLoc.ofAddr_rep g ν hM (ad := .index r.id .dyn k) (ra := .index r .dyn k) ?_ ?_ ?_
        · rw [LTm.eval_app2, hr, hk]; rfl
        · simp only [MAddrT.resolve_eq_resolveM, MAddrT.resolveM, HRef.ofId?_self,
            Option.map_some]
        · show μ.heap.index r .dyn k = some mv
          simp only [Heap.index, hmv]
  | atF i rest ih =>
    rename_i E U n
    intro loc h x hh hx c p hp
    rw [TSegs.eval_atF] at hp
    obtain ⟨k, hk, hp⟩ := Option.bind_eq_some_iff.1 hp
    obtain ⟨p', hp', rfl⟩ := Option.map_eq_some_iff.1 hp
    have e : x.bind (·.findM (.atF k p')) =
        (x.bind (·.findM (.atF k .nil))).bind (·.findM p') := by
      cases x with
      | none => rfl
      | some v =>
        simp only [Option.bind_some]
        rw [← SVal.findM_append, Path.append_atF, Path.append_nil]
    rw [e]
    refine ih _ _ _ ?_ ?_ c p' hp'
    · rw [LTm.eval_kite, hh]
      cases x with
      | none => rfl
      | some v =>
        obtain ⟨r, hr, rfl⟩ := hx _ rfl
        change (if (true : Bool) = true then ((LTm.ltNat i n).eval g ν : Option Bool)
          else ((LTm.lit (p := .bool) false : LTm C (.val .bool)).eval g ν)) = _
        rw [if_pos rfl, LTm.eval_ltNat g ν n hk, Option.bind_some, MVal.copyMToSt_findM_atF,
          bind_findM_nil_isSome]
        have hl : (MObj.elems .fixed (μ.heap.get r)).length = n := by
          rw [MObj.elems_fixed]
          exact (μ.heap.get r : {l : List (MVal μ.H' E) // l.length = n}).2
        rw [hl]
    · intro v' hv'
      cases x with
      | none => cases hv'
      | some v =>
        obtain ⟨r, hr, rfl⟩ := hx _ rfl
        rw [Option.bind_some, MVal.copyMToSt_findM_atF] at hv'
        obtain ⟨mv, hmv, hv'⟩ := Option.bind_eq_some_iff.1 hv'
        rw [SVal.findM_nil', Option.some.injEq] at hv'
        subst hv'
        refine MLoc.ofAddr_rep g ν hM (ad := .index r.id (ArrTy.fixed (n := n)) k)
          (ra := .index r .fixed k)
          ?_ ?_ ?_
        · rw [LTm.eval_app2, hr, hk]; rfl
        · simp only [MAddrT.resolve_eq_resolveM, MAddrT.resolveM, HRef.ofId?_self,
            Option.map_some]
        · show μ.heap.index r .fixed k = some mv
          simp only [Heap.index, hmv]
  | key i rest ih =>
    intro loc h x hh hx c p hp
    rw [TSegs.eval_key] at hp
    obtain ⟨j, hj, hp⟩ := Option.bind_eq_some_iff.1 hp
    obtain ⟨p', hp', rfl⟩ := Option.map_eq_some_iff.1 hp
    cases x with
    | some v =>
      obtain ⟨r, -, -⟩ := hx _ rfl
      exact (μ.heap.get r : Empty).elim
    | none => exact ih _ h none hh (fun _ hv => nomatch hv) c p' hp'

/-- **`copyMem(M, t)`, eliminated**: the guard that it returns, and the
reader of the object it copies. -/
theorem copyMem_rep {R : RefTy} {M' : LTm C .mem} {t t' : LTm C (.ident R)}
    (hM : (M'.eval g ν : Option (Grown g.H (fun _ => Unit))) = M.eval g ν)
    (ht : (t'.eval g ν : Option Nat) = t.eval g ν) :
    VRep g ν (some (seqL (.app2 .copyMem M' t') .tt, copyMemRd M' t')) (.app2 .copyMem M t) := by
  have ev : ∀ (M : LTm C .mem) (t : LTm C (.ident R)),
      ((LTm.app2 .copyMem M t).eval g ν : Option (SVal (.ref R))) =
        (M.eval g ν : Option (Grown g.H (fun _ => Unit))).bind fun μ =>
          (t.eval g ν : Option Nat).bind fun id =>
            (HRef.ofId? μ.H' R id).map fun r => MVal.copyMToSt μ.heap (T := .ref R) r := by
    intro M t
    rw [LTm.eval_app2, Op2.eval_eq_evalM]
    cases (M.eval g ν : Option (Grown g.H (fun _ => Unit))) with
    | none => rfl
    | some μ =>
      cases (t.eval g ν : Option Nat) with
      | none => rfl
      | some id =>
        show (HRef.ofId? μ.H' R id).bind (fun r => some (MVal.copyMToSt μ.heap (T := .ref R) r)) =
          (HRef.ofId? μ.H' R id).map fun r => MVal.copyMToSt μ.heap (T := .ref R) r
        cases HRef.ofId? μ.H' R id <;> rfl
  intro gd V he
  simp only [Option.some.injEq, Prod.mk.injEq] at he
  obtain ⟨rfl, rfl⟩ := he
  refine ⟨?_, fun w hw => ?_⟩
  · rw [seqL_eval, ev, ev, hM, ht]
    cases ((M.eval g ν : Option (Grown g.H (fun _ => Unit))).bind fun μ =>
      (t.eval g ν : Option Nat).bind fun id =>
        (HRef.ofId? μ.H' R id).map fun r => MVal.copyMToSt μ.heap (T := .ref R) r) <;> rfl
  · rw [ev] at hw
    simp only [Option.bind_eq_some_iff, Option.map_eq_some_iff] at hw
    obtain ⟨μ, hμ, id, hid, r, hr, rfl⟩ := hw
    intro V c q p hq
    have hrid : r.id = id := HRef.id_of_ofId? hr
    refine (memRd_rep g ν (hM.trans hμ) q t' .tt (some _) rfl
      (fun v hv => ⟨r, by rw [ht, hid, hrid], (Option.some.inj hv).symm⟩) c p hq).trans ?_
    exact congrArg some (CK.obsC_congr c fun cc => (cc.read_obsOpt (some _) p).symm)

end CopyMem

/-! ## The elimination keeps what a term reads -/

/-- **What an eliminated term stands for**, by its sort. -/
def ElimM.Rep : (s : Srt) → ElimM C s → LTm C s → Prop
  | .st, e, t => SFun.Rep g ν e t
  | .path _, e, t => PRep g ν e t
  | .sv _, e, t => VRep g ν e t
  | .val p, e, t => ((e : LTm C (.val p)).eval g ν) = t.eval g ν
  | .ident _, e, t => ((e : LTm C (.ident _)).eval g ν) = t.eval g ν
  | .addr _, e, t => ((e : LTm C (.addr _)).eval g ν) = t.eval g ν
  | .mem, e, t => ((e : LTm C .mem).eval g ν) = t.eval g ν
  | .mv _, e, t => ((e : LTm C (.mv _)).eval g ν) = t.eval g ν
  | .sts _, e, t => ((e : LTm C (.sts _)).eval g ν) = t.eval g ν
  | .spath _ _, e, t => ((e : LTm C (.spath _ _)).eval g ν) = t.eval g ν
  | .kint, e, t => ((e : LTm C .kint).eval g ν) = t.eval g ν

theorem seqL_tt_eval {s : Srt} (t : LTm C s) :
    ((seqL t .tt).eval g ν : Option Bool) = (t.eval g ν).map fun _ => true := by
  rw [seqL_eval]; cases t.eval g ν <;> rfl

theorem SFun.ofOrig_rep (t : LTm C .st) : (SFun.ofOrig t).Rep g ν t := by
  refine ⟨rfl, ?_, fun st h => fbRd_rep g ν h⟩
  exact seqL_tt_eval g ν t

theorem ElimM.ofOrig_rep : (s : Srt) → (t : LTm C s) → ElimM.Rep g ν s (ElimM.ofOrig s t) t
  | .st, t => SFun.ofOrig_rep g ν t
  | .path _, _ => fun _ _ h => nomatch h
  | .sv _, _ => fun _ _ h => nomatch h
  | .val _, _ | .ident _, _ | .addr _, _ | .mem, _ | .mv _, _ | .sts _, _ | .spath _ _, _
  | .kint, _ => rfl

theorem ElimM.guard_eval : (s : Srt) → (e : ElimM C s) → (t : LTm C s) → ElimM.Rep g ν s e t →
    ((ElimM.guard s e t).eval g ν : Option Bool) = (t.eval g ν).map fun _ => true
  | .st, _, _, h => h.ok
  | .path _, e, t, h => by
    cases e with
    | none => exact seqL_tt_eval g ν t
    | some x => exact (h x.1 x.2 rfl).1
  | .sv _, e, t, h => by
    cases e with
    | none => exact seqL_tt_eval g ν t
    | some x => exact (h x.1 x.2 rfl).1
  | .val _, e, t, h | .ident _, e, t, h | .addr _, e, t, h | .mem, e, t, h | .mv _, e, t, h
  | .sts _, e, t, h | .spath _ _, e, t, h | .kint, e, t, h => by
    unfold ElimM.guard
    rw [seqL_tt_eval]
    exact congrArg _ h

theorem ElimM.guarded_rep {s' : Srt} (d : LTm C s') (gd : LTm C (.val .bool))
    (hg : (gd.eval g ν : Option Bool) = (d.eval g ν).map fun _ => true) :
    (s : Srt) → (e : ElimM C s) → (a : LTm C s) → ElimM.Rep g ν s e a →
    ElimM.Rep g ν s (ElimM.guarded s gd e (.seq d a)) (.seq d a) := by
  have key : ∀ {β : Type} (x : Option β) {s : Srt} (a : LTm C s),
      ((gd.eval g ν : Option Bool).bind fun _ => x) = (d.eval g ν).bind fun _ => x := by
    intro β x s a; rw [hg]; cases d.eval g ν <;> rfl
  intro s e a h
  cases s with
  | st =>
    refine ⟨rfl, ?_, ?_⟩
    · show (seqL gd (SFun.ok e)).eval g ν = _
      rw [seqL_eval, h.ok, key _ a, LTm.eval_seq]
      cases d.eval g ν <;> rfl
    · intro st hst
      rw [LTm.eval_seq] at hst
      cases hd : d.eval g ν with
      | none => rw [hd] at hst; cases hst
      | some _ => rw [hd] at hst; exact h.rd st hst
  | path T =>
    intro gd' P he
    cases e with
    | none => cases he
    | some x =>
      simp only [ElimM.guarded, Option.map_some, Option.some.injEq] at he
      cases he
      obtain ⟨h1, h2⟩ := h x.1 x.2 rfl
      refine ⟨?_, ?_⟩
      · rw [seqL_eval, h1, key _ a, LTm.eval_seq]; cases d.eval g ν <;> rfl
      · intro r hr
        rw [LTm.eval_seq] at hr
        cases hd : d.eval g ν with
        | none => rw [hd] at hr; cases hr
        | some _ => rw [hd] at hr; exact h2 r hr
  | sv T =>
    intro gd' V he
    cases e with
    | none => cases he
    | some x =>
      simp only [ElimM.guarded, Option.map_some, Option.some.injEq] at he
      cases he
      obtain ⟨h1, h2⟩ := h x.1 x.2 rfl
      refine ⟨?_, ?_⟩
      · rw [seqL_eval, h1, key _ a, LTm.eval_seq]; cases d.eval g ν <;> rfl
      · intro w hw
        rw [LTm.eval_seq] at hw
        cases hd : d.eval g ν with
        | none => rw [hd] at hw; cases hw
        | some _ => rw [hd] at hw; exact h2 w hw
  | val _ | ident _ | addr _ | mem | mv _ | sts _ | spath _ _ | kint =>
    show (seqL gd _).eval g ν = _
    rw [seqL_eval, key _ a, LTm.eval_seq]
    exact congrArg _ (funext fun _ => h)

theorem ElimM.orElse_rep : (s : Srt) → (ea eb : ElimM C s) → (a b : LTm C s) →
    ElimM.Rep g ν s ea a → ElimM.Rep g ν s eb b →
    ElimM.Rep g ν s (ElimM.orElse s ea eb (.orElse a b)) (.orElse a b)
  | .val _, ea, eb, a, b, ha, hb => by
    show (LTm.orElse _ _).eval g ν = _
    rw [LTm.eval_orElse, LTm.eval_orElse]
    rw [show (ea : LTm C (.val _)).eval g ν = a.eval g ν from ha,
      show (eb : LTm C (.val _)).eval g ν = b.eval g ν from hb]
  | .st, _, _, _, _, _, _ | .path _, _, _, _, _, _, _ | .sv _, _, _, _, _, _, _
  | .ident _, _, _, _, _, _, _ | .addr _, _, _, _, _, _, _ | .mem, _, _, _, _, _, _
  | .mv _, _, _, _, _, _, _ | .sts _, _, _, _, _, _, _ | .spath _ _, _, _, _, _, _, _
  | .kint, _, _, _, _, _, _ => ElimM.ofOrig_rep g ν _ _

theorem ElimM.kite_rep {p : PrimTy} {ea eb a b : LTm C (.val p)}
    (ha : (ea.eval g ν : Option p.Denote) = a.eval g ν)
    (hb : (eb.eval g ν : Option p.Denote) = b.eval g ν) :
    (s : Srt) → (et ee : ElimM C s) → (t e : LTm C s) →
    ElimM.Rep g ν s et t → ElimM.Rep g ν s ee e →
    ElimM.Rep g ν s (ElimM.kite ea eb s et ee (.kite a b t e)) (.kite a b t e)
  | .val _, et, ee, t, e, ht, he => by
    show (LTm.kite _ _ _ _).eval g ν = _
    rw [LTm.eval_kite, LTm.eval_kite, ha, hb]
    simp only [show (et : LTm C (.val _)).eval g ν = t.eval g ν from ht,
      show (ee : LTm C (.val _)).eval g ν = e.eval g ν from he]
  | .st, _, _, _, _, _, _ | .path _, _, _, _, _, _, _ | .sv _, _, _, _, _, _, _
  | .ident _, _, _, _, _, _, _ | .addr _, _, _, _, _, _, _ | .mem, _, _, _, _, _, _
  | .mv _, _, _, _, _, _, _ | .sts _, _, _, _, _, _, _ | .spath _ _, _, _, _, _, _, _
  | .kint, _, _, _, _, _, _ => ElimM.ofOrig_rep g ν _ _

theorem pathIdx_rep {R : RefTy} {k : PrimTy} {V : Ty} (it : IndexTy R k V)
    {e : Option (LTm C (.val .bool) × SPath C (.ref R))} {q : LTm C (.path (.ref R))}
    (hP : PRep g ν e q) {ei i : LTm C (.val k)}
    (hi : (ei.eval g ν : Option k.Denote) = i.eval g ν) :
    PRep g ν (pathIdx it e ei) (.index it q i) := by
  intro gd P' he
  cases e with
  | none => cases he
  | some x =>
    obtain ⟨g0, Q⟩ := x
    simp only [pathIdx, Option.map_some, Option.some.injEq, Prod.mk.injEq] at he
    obtain ⟨rfl, rfl⟩ := he
    obtain ⟨hPg, hPe⟩ := hP g0 Q rfl
    refine ⟨?_, ?_⟩
    · rw [seqL_eval, hPg, LTm.eval_index]
      simp only [seqL_eval, hi]
      cases (q.eval g ν : Option (SRef C _)) <;> cases (i.eval g ν : Option _) <;> rfl
    · intro r' ht
      rw [LTm.eval_index] at ht
      simp only [Option.bind_eq_some_iff, Option.some.injEq] at ht
      obtain ⟨r, hq, j, hj, rfl⟩ := ht
      exact SPath.eval_snoc_index g ν it (hPe r hq) (hi.trans hj)

theorem field_rep {s f : Name} {T : Ty} (h : C.fieldType s f = some T)
    {e : Option (LTm C (.val .bool) × SPath C (.ref (.struct s)))}
    {q : LTm C (.path (.ref (.struct s)))} (hP : PRep g ν e q) :
    PRep g ν (e.map fun x => (x.1, x.2.snoc (.field h .nil))) (.app1 (.field h) q) := by
  intro gd P' he
  cases e with
  | none => cases he
  | some x =>
    obtain ⟨g0, Q⟩ := x
    simp only [Option.map_some, Option.some.injEq, Prod.mk.injEq] at he
    obtain ⟨rfl, rfl⟩ := he
    obtain ⟨hPg, hPe⟩ := hP g0 Q rfl
    refine ⟨?_, ?_⟩
    · rw [hPg, LTm.eval_field]; cases (q.eval g ν : Option (SRef C _)) <;> rfl
    · intro r' ht
      rw [LTm.eval_field, Option.map_eq_some_iff] at ht
      obtain ⟨r, hq, rfl⟩ := ht
      rw [SPath.eval_snoc, hPe r hq]; rfl

theorem find_rep {p : PrimTy} {S : SFun C} {s : LTm C .st} (hS : S.Rep g ν s) {gd : LTm C (.val .bool)}
    {Q : SPath C (.prim p)} {q : LTm C (.path (.prim p))} (hP : PRep g ν (some (gd, Q)) q) :
    ((seqL (SFun.ok S) (seqL gd (LTm.cond (SFun.rd S (.has _) Q) (SFun.rd S (.word _) Q) .err))).eval g ν :
      Option p.Denote) = (LTm.app2 .find s q).eval g ν := by
  obtain ⟨hPg, hPe⟩ := hP gd Q rfl
  rw [LTm.eval_app2, seqL_eval, seqL_eval, hS.ok, hPg]
  cases hs : (s.eval g ν : Option (Storage C)) with
  | none => rfl
  | some st =>
    cases hq : (q.eval g ν : Option (SRef C _)) with
    | none => rfl
    | some r =>
      simp only [Option.map_some, Option.bind_some]
      rw [LTm.eval_cond_some g ν _ _ (hS.rd st hs _ (.has _) Q r (hPe r hq)),
        hS.rd st hs _ (.word _) Q r (hPe r hq)]
      show (if st.obs.has (.ref r) = true then some (st.obs.word (.ref r)) else none) =
        (st.find r).bind fun v => some v.view
      rw [has_obs, Storage.obs_word_ref, SVal.obs_word, ← sto_find_findM]
      cases st.find r <;> rfl

theorem len_rep {E : Ty} {S : SFun C} {s : LTm C .st} (hS : S.Rep g ν s) {gd : LTm C (.val .bool)}
    {Q : SPath C (.ref (.array E))} {q : LTm C (.path (.ref (.array E)))}
    (hP : PRep g ν (some (gd, Q)) q) :
    ((seqL (SFun.ok S) (seqL gd (LTm.cond (SFun.rd S (.has _) Q) (SFun.rd S (.len _) Q) .err))).eval g ν :
      Option PrimTy.uint.Denote) = (LTm.app2 .len s q).eval g ν := by
  obtain ⟨hPg, hPe⟩ := hP gd Q rfl
  rw [LTm.eval_app2, seqL_eval, seqL_eval, hS.ok, hPg]
  cases hs : (s.eval g ν : Option (Storage C)) with
  | none => rfl
  | some st =>
    cases hq : (q.eval g ν : Option (SRef C _)) with
    | none => rfl
    | some r =>
      simp only [Option.map_some, Option.bind_some]
      rw [LTm.eval_cond_some g ν _ _ (hS.rd st hs _ (.has _) Q r (hPe r hq)),
        hS.rd st hs _ (.len _) Q r (hPe r hq)]
      show (if st.obs.has (.ref r) = true then some (uintOfNat (st.obs.len (.ref r))) else none) =
        st.len r
      rw [has_obs]
      unfold Storage.len
      cases hf : st.find r with
      | none => rfl
      | some w =>
        cases w with
        | array e sh hn =>
          rw [len_obs st r hf]
          simp only [Option.isSome_some, if_true, Option.bind_some, SVal.view_array, uintOfNat,
            dif_pos hn]
          rfl


/-! ### Each symbol -/

/-! ### The empty storage -/

theorem SVal.findM_dflt_at {E U : Ty} (i : PrimTy.uint.Denote) (p : Path E U) :
    (SVal.dflt (.ref (.array E))).findM (.at i p) = none := by
  rw [SVal.dflt_array, SVal.findM_at']
  simp only [SVec.toList, SList.toList, List.append_nil, List.getElem?_nil, Option.bind_none]

theorem SVal.findM_dflt_key {K : PrimTy} {V U : Ty} (k : K.Denote) (p : Path V U) :
    (SVal.dflt (.ref (.mapping K V))).findM (.key k p) = (SVal.dflt V).findM p := by
  rw [SVal.dflt_map]; simp only [SVal.findM, SMap.toList]; rfl

/-- **A default read below** is absent or the default (`selectOnEmptyStorage`):
a dynamic array is empty, a fixed one, a mapping, a struct hold defaults. -/
theorem SVal.findM_dflt : {T U : Ty} → (p : Path T U) →
    (SVal.dflt T).findM p = none ∨ (SVal.dflt T).findM p = some (SVal.dflt U)
  | _, _, .nil => .inr (SVal.findM_nil' _)
  | _, _, .field hf p => by
    rw [SVal.dflt_struct, SVal.findM_field', SFields.dflt_get]
    exact SVal.findM_dflt p
  | _, _, .at i p => .inl (SVal.findM_dflt_at i p)
  | _, _, @Path.atF E _ n i p => by
    rw [SVal.dflt_fixed, SVal.findM_atF', SVec.toList_replicate]
    by_cases h : i.1.toNat < n
    · rw [List.getElem?_replicate_of_lt h, Option.bind_some]
      exact SVal.findM_dflt p
    · rw [List.getElem?_eq_none (by rw [List.length_replicate]; omega), Option.bind_none]
      exact .inl rfl
  | _, _, .key k p => by
    rw [SVal.findM_dflt_key]
    exact SVal.findM_dflt p

/-- The empty storage at a reference: absent or the default. -/
theorem Storage.findM_init {U : Ty} (r : SRef C U) :
    ((Storage.init C).get r.hroot).findM r.path = none ∨
      ((Storage.init C).get r.hroot).findM r.path = some (SVal.dflt U) := by
  rw [Storage.init, SFields.dflt_get]
  exact SVal.findM_dflt r.path

/-- **`TSegs.mtHas` reads `has` on the empty storage**, from a base whose
value there is the default where `acc` reads `true`, absent where `false`. -/
theorem TSegs.mtHas_eval {S T : Ty} (p : TSegs C S T) :
    ∀ (acc : LTm C (.val .bool)) (b : Bool) (pp : Path S T),
      p.eval g ν = some pp → (acc.eval g ν : Option Bool) = some b →
      ((p.mtHas acc).eval g ν : Option Bool) =
        some ((if b then some (SVal.dflt S) else none).bind (·.findM pp)).isSome := by
  induction p with
  | nil =>
    intro acc b pp hp ha
    cases hp
    show (acc.eval g ν : Option Bool) = _
    rw [ha]; cases b <;> simp only [SVal.findM_nil', if_true, Bool.false_eq_true, if_false,
      Option.bind_some, Option.bind_none, Option.isSome_some, Option.isSome_none]
  | field h rest ih =>
    intro acc b pp hp ha
    obtain ⟨pp', hpp', rfl⟩ := eval_field_some (g := g) (ν := ν) hp
    rw [show (TSegs.field h rest).mtHas acc = rest.mtHas acc from rfl, ih acc b pp' hpp' ha]
    cases b <;> simp only [if_true, Bool.false_eq_true, if_false, Option.bind_some,
      Option.bind_none, SVal.dflt_struct, SVal.findM_field', SFields.dflt_get]
  | «at» i rest ih =>
    intro acc b pp hp _
    obtain ⟨k, pp', hk, hpp', rfl⟩ := eval_at_some (g := g) (ν := ν) hp
    show some false = _
    cases b <;> simp only [if_true, Bool.false_eq_true, if_false, Option.bind_some,
      Option.bind_none, Option.isSome_none, SVal.findM_dflt_at]
  | @atF E U n i rest ih =>
    intro acc b pp hp ha
    obtain ⟨k, pp', hk, hpp', rfl⟩ := eval_atF_some (g := g) (ν := ν) hp
    have hb : ((if TSegs.litBelow i n then acc else
        .kite acc .tt (LTm.ltNat i n) (.lit (p := .bool) false)).eval g ν : Option Bool) =
        some (b && decide (k.1.toNat < n)) := by
      split
      · rename_i hl
        unfold TSegs.litBelow at hl
        split at hl
        · rename_i w hw
          have hi := LTm.eq_of_litV? hw
          subst hi
          have hkw : k = w := by cases hk; rfl
          subst hkw
          rw [ha, hl, Bool.and_true]
        · cases hl
      · rw [LTm.eval_kite, ha, Option.bind_some,
          show ((LTm.tt : LTm C (.val .bool)).eval g ν : Option Bool) = some true from rfl,
          Option.bind_some]
        cases b
        · rfl
        · rw [if_pos rfl, Bool.true_and]
          exact LTm.eval_ltNat g ν n hk
    rw [show (TSegs.atF i rest).mtHas acc = rest.mtHas (if TSegs.litBelow i n then acc else
        .kite acc .tt (LTm.ltNat i n) (.lit (p := .bool) false)) from rfl, ih _ _ pp' hpp' hb]
    congr 1
    cases b
    · simp only [Bool.false_and, Bool.false_eq_true, if_false, Option.bind_none]
    · simp only [Bool.true_and, if_true, Option.bind_some, SVal.dflt_fixed, SVal.findM_atF',
        SVec.toList_replicate]
      by_cases h : k.1.toNat < n
      · simp only [h, decide_true, if_true, List.getElem?_replicate_of_lt h, Option.bind_some]
      · rw [List.getElem?_eq_none (by rw [List.length_replicate]; omega)]
        simp only [h, decide_false, Bool.false_eq_true, if_false, Option.bind_none]
  | key i rest ih =>
    intro acc b pp hp ha
    obtain ⟨j, pp', hj, hpp', rfl⟩ := eval_key_some (g := g) (ν := ν) hp
    rw [show (TSegs.key i rest).mtHas acc = rest.mtHas acc from rfl, ih acc b pp' hpp' ha]
    cases b <;> simp only [if_true, Bool.false_eq_true, if_false, Option.bind_some,
      Option.bind_none, SVal.findM_dflt_key]

theorem mtRd_rep : SRd.Rep g ν mtRd (Storage.init C) := by
  intro V c Q r hQ
  cases c with
  | word P =>
    show some (PrimTy.dflt P) = some ((Storage.init C).obs.word (.ref r))
    rw [Storage.obs_word_ref, SVal.obs_word]
    rcases Storage.findM_init r with h | h <;> rw [h] <;> rfl
  | len E =>
    show ((LTm.nat 0 : LTm C (.val .uint)).eval g ν : Option _) = _
    rw [LTm.eval_nat]
    show _ = some (uintOfNat ((Storage.init C).obs.len (.ref r)))
    rw [Storage.obs_len_ref, SVal.obs_len]
    rcases Storage.findM_init r with h | h <;> rw [h] <;> rfl
  | has V =>
    show ((Q.segs.mtHas .tt).eval g ν : Option Bool) = _
    unfold SPath.eval at hQ
    obtain ⟨pp, hpp, rfl⟩ := Option.map_eq_some_iff.1 hQ
    rw [TSegs.mtHas_eval g ν Q.segs .tt true pp hpp rfl]
    show _ = some (((Storage.init C).get Q.hr).findM pp).isSome
    rw [Storage.init, SFields.dflt_get]
    rfl

theorem SFun.mt_rep : (SFun.mt : SFun C).Rep g ν (.app0 .mtSt) :=
  ⟨rfl, rfl, fun st h => by cases h; exact mtRd_rep g ν⟩

theorem SFun.init_rep : (SFun.init : SFun C).Rep g ν (.app0 .storage) :=
  ⟨rfl, rfl, fun st h => by cases h; exact initRd_rep g ν⟩

theorem Op0.elim_rep {s : Srt} (o : Op0 C s) : ElimM.Rep g ν s o.elim (.app0 o) := by
  cases o with
  | lit v => rfl
  | env k => rfl
  | root r h =>
    intro gd P he
    simp only [Op0.elim, Option.some.injEq, Prod.mk.injEq] at he
    obtain ⟨rfl, rfl⟩ := he
    exact ⟨rfl, fun r' hr => by cases hr; rfl⟩
  | storage => exact SFun.init_rep g ν
  | memory => rfl
  | mtSt => exact SFun.mt_rep g ν
  | member s f h => rfl
  | zlit n => rfl

theorem Op1.elim_rep {a s : Srt} (o : Op1 C a s) (x : LTm C a) (ex : ElimM C a)
    (hx : ElimM.Rep g ν a ex x) : ElimM.Rep g ν s (o.elim x ex) (.app1 o x) := by
  cases o with
  | unop op h =>
    show (LTm.app1 _ _).eval g ν = _
    rw [LTm.eval_app1, LTm.eval_app1]; exact congrArg _ hx
  | net =>
    show (LTm.app1 _ _).eval g ν = _
    rw [LTm.eval_app1, LTm.eval_app1]; exact congrArg _ hx
  | delValue =>
    show (LTm.app1 _ _).eval g ν = _
    rw [LTm.eval_app1, LTm.eval_app1]; exact congrArg _ hx
  | field h => exact field_rep g ν h hx
  | next =>
    refine pathNext_core g ν SFun.init (some g.storage) rfl (fun st h => by cases h; exact initRd_rep g ν)
      hx ?_
    rw [LTm.eval_app1]
    cases (x.eval g ν : Option (SRef C _)) <;> rfl
  | sval => exact sval_rep g ν hx
  | newArr h => exact newArr_rep g ν _ h hx
  | alloc R h => rfl
  | mfield h => rfl
  | addM R h => rfl
  | mval => rfl
  | ref => rfl
  | wt => rfl
  | cleanTail => rfl
  | select r h => rfl
  | selectIn h => rfl
  | fieldIn h => rfl
  | toInt =>
    show (LTm.app1 _ _).eval g ν = _
    rw [LTm.eval_app1, LTm.eval_app1]; exact congrArg _ hx
  | fixedCopy shape =>
    show VRep g ν (ex.map fun (gd, rd) => (gd, fixedCopyRd shape rd)) (.app1 (.fixedCopy shape) x)
    cases ex with
    | none => intro gd rd h; cases h
    | some pair =>
      obtain ⟨gd₀, rd₀⟩ := pair
      intro gd rd h
      obtain ⟨rfl, rfl⟩ := Option.some.inj h
      obtain ⟨hg, hrd⟩ := hx gd₀ rd₀ rfl
      constructor
      · rw [hg, LTm.eval_app1, Op1.eval_eq_evalM, Op1.evalM]
        cases (x.eval g ν : Option (SVal _)) <;> rfl
      · intro v hv
        rw [LTm.eval_app1, Op1.eval_eq_evalM, Op1.evalM] at hv
        obtain ⟨w, hw, rfl⟩ := Option.map_eq_some_iff.mp hv
        rw [FixedCopy.observe_apply]
        exact fixedCopyRd_rep g ν shape rd₀ w (hrd w hw)

theorem bind_fst_eq_map {α β : Type} (x : Option (α × β)) :
    (x.bind fun p => some p.1) = x.map Prod.fst := by
  cases x <;> rfl

theorem Op2.elim_rep {a b s : Srt} (o : Op2 C a b s) (x : LTm C a) (y : LTm C b) (ex : ElimM C a)
    (ey : ElimM C b) (hx : ElimM.Rep g ν a ex x) (hy : ElimM.Rep g ν b ey y) :
    ElimM.Rep g ν s (o.elim x y ex ey) (.app2 o x y) := by
  cases o with
  | binop op h =>
    show (LTm.app2 _ _ _).eval g ν = _
    rw [LTm.eval_app2, LTm.eval_app2]
    rw [show (ex : LTm C (.val _)).eval g ν = x.eval g ν from hx,
      show (ey : LTm C (.val _)).eval g ν = y.eval g ν from hy]
  | find =>
    show ElimM.Rep g ν _ (match (ey : Option (LTm C (.val .bool) × SPath C _)) with
      | some (gd, Q) => _ | none => _) _
    cases ey with
    | none => rfl
    | some z => exact find_rep g ν hx hy
  | len =>
    show ElimM.Rep g ν _ (match (ey : Option (LTm C (.val .bool) × SPath C _)) with
      | some (gd, Q) => _ | none => _) _
    cases ey with
    | none => rfl
    | some z => exact len_rep g ν hx hy
  | read => rfl
  | mlen => rfl
  | hash _ => rfl
  | «at» it =>
    refine pathAtIn_core g ν it SFun.init (some g.storage) rfl
      (fun st h => by cases h; exact initRd_rep g ν) hx hy ?_
    rw [LTm.eval_app2]
    cases (x.eval g ν : Option (SRef C _)) <;> cases (y.eval g ν : Option _) <;> rfl
  | nextIn =>
    refine pathNext_core g ν ex (x.eval g ν) hx.ok (fun st h => hx.rd st h) hy ?_
    rw [LTm.eval_app2]
    cases (x.eval g ν : Option (Storage C)) <;> cases (y.eval g ν : Option (SRef C _)) <;> rfl
  | delAt =>
    show ElimM.Rep g ν _ (match (ey : Option (LTm C (.val .bool) × SPath C _)) with
      | some (gd, Q) => _ | none => _) _
    cases ey with
    | none => exact SFun.ofOrig_rep g ν _
    | some z => exact SFun.delAt_rep g ν hx hy
  | pushSlot =>
    show ElimM.Rep g ν _ (match (ey : Option (LTm C (.val .bool) × SPath C _)) with
      | some (gd, Q) => _ | none => _) _
    cases ey with
    | none => exact SFun.ofOrig_rep g ν _
    | some z =>
      refine SFun.extend_rep g ν (fun st r => st.push r some) hx hy ?_
        (fun st r => Storage.push_isSome st r some (fun _ => rfl))
        (fun st r st' h => Storage.obs_push_slot h)
      rw [LTm.eval_app2]
      cases (x.eval g ν : Option (Storage C)) <;> cases (y.eval g ν : Option (SRef C _)) <;> rfl
  | pop =>
    show ElimM.Rep g ν _ (match (ey : Option (LTm C (.val .bool) × SPath C _)) with
      | some (gd, Q) => _ | none => _) _
    cases ey with
    | none => exact SFun.ofOrig_rep g ν _
    | some z =>
      refine SFun.pop_rep g ν false hx hy ?_
      rw [LTm.eval_app2]
      cases (x.eval g ν : Option (Storage C)) <;> cases (y.eval g ν : Option (SRef C _)) <;> rfl
  | shrink =>
    show ElimM.Rep g ν _ (match (ey : Option (LTm C (.val .bool) × SPath C _)) with
      | some (gd, Q) => _ | none => _) _
    cases ey with
    | none => exact SFun.ofOrig_rep g ν _
    | some z =>
      refine SFun.pop_rep g ν true hx hy ?_
      rw [LTm.eval_app2]
      cases (x.eval g ν : Option (Storage C)) <;> cases (y.eval g ν : Option (SRef C _)) <;> rfl
  | extend =>
    show ElimM.Rep g ν _ (match (ey : Option (LTm C (.val .bool) × SPath C _)) with
      | some (gd, Q) => _ | none => _) _
    cases ey with
    | none => exact SFun.ofOrig_rep g ν _
    | some z =>
      refine SFun.extend_rep g ν (fun st r => (st.pushPlace r).map Prod.fst) hx hy ?_
        (fun st r => by rw [Option.isSome_map]; exact Storage.pushPlace_isSome st r)
        (fun st r st' h => by
          rw [Option.map_eq_some_iff] at h
          obtain ⟨⟨st₁, k⟩, h, rfl⟩ := h
          exact Storage.obs_pushPlace h)
      rw [LTm.eval_app2]
      cases (x.eval g ν : Option (Storage C)) <;> cases (y.eval g ν : Option (SRef C _)) <;>
        first | rfl | exact bind_fst_eq_map _
  | sfind => exact sfind_rep g ν hx hy
  | copyMem => exact copyMem_rep g ν hx hy
  | iread => rfl
  | copy h => rfl
  | mat a => rfl
  | copySt h => rfl
  | findIn => rfl
  | delAtIn => rfl
  | sfindIn => exact fun _ _ he => nomatch he
  | zbin op h =>
    show (LTm.app2 _ _ _).eval g ν = _
    rw [LTm.eval_app2, LTm.eval_app2]
    rw [show (ex : LTm C .kint).eval g ν = x.eval g ν from hx,
      show (ey : LTm C .kint).eval g ν = y.eval g ν from hy]
  | zcmp op h =>
    show (LTm.app2 _ _ _).eval g ν = _
    rw [LTm.eval_app2, LTm.eval_app2]
    rw [show (ex : LTm C .kint).eval g ν = x.eval g ν from hx,
      show (ey : LTm C .kint).eval g ν = y.eval g ν from hy]

theorem Op3.elim_rep {a b c s : Srt} (o : Op3 C a b c s) (x : LTm C a) (y : LTm C b) (z : LTm C c)
    (ex : ElimM C a) (ey : ElimM C b) (ez : ElimM C c) (hx : ElimM.Rep g ν a ex x)
    (hy : ElimM.Rep g ν b ey y) (hz : ElimM.Rep g ν c ez z) :
    ElimM.Rep g ν s (o.elim x y z ex ey ez) (.app3 o x y z) := by
  cases o with
  | ite =>
    show (LTm.app3 _ _ _ _).eval g ν = _
    rw [LTm.eval_app3, LTm.eval_app3]
    rw [show (ex : LTm C (.val _)).eval g ν = x.eval g ν from hx,
      show (ey : LTm C (.val _)).eval g ν = y.eval g ν from hy,
      show (ez : LTm C (.val _)).eval g ν = z.eval g ν from hz]
  | save =>
    show ElimM.Rep g ν _ (match (ey : Option (LTm C (.val .bool) × SPath C _)),
      (ez : Option (LTm C (.val .bool) × VRd C _)) with
      | some (gd, Q), some (gv, V) => _ | _, _ => _) _
    cases ey with
    | none => exact SFun.ofOrig_rep g ν _
    | some y' =>
      cases ez with
      | none => exact SFun.ofOrig_rep g ν _
      | some z' => exact SFun.save_rep g ν hx hy hz
  | push =>
    show ElimM.Rep g ν _ (match (ey : Option (LTm C (.val .bool) × SPath C _)),
      (ez : Option (LTm C (.val .bool) × VRd C _)) with
      | some (gd, Q), some (gv, V) => _ | _, _ => _) _
    cases ey with
    | none => exact SFun.ofOrig_rep g ν _
    | some y' =>
      cases ez with
      | none => exact SFun.ofOrig_rep g ν _
      | some z' => exact SFun.push_rep g ν hx hy hz
  | atIn it =>
    refine pathAtIn_core g ν it ex (x.eval g ν) hx.ok (fun st h => hx.rd st h) hy hz ?_
    rw [LTm.eval_app3]
    cases (x.eval g ν : Option (Storage C)) <;> cases (y.eval g ν : Option (SRef C _)) <;>
      cases (z.eval g ν : Option _) <;> rfl
  | write => rfl
  | saveIn => rfl
  | modular op =>
    show (foldModular op ex ey ez).eval g ν = _
    rw [foldModular_eval, LTm.eval_app3, LTm.eval_app3]
    rw [show (ex : LTm C (.val .uint)).eval g ν = x.eval g ν from hx,
      show (ey : LTm C (.val .uint)).eval g ν = y.eval g ν from hy,
      show (ez : LTm C (.val .uint)).eval g ν = z.eval g ν from hz]

/-- **The elimination keeps what a term reads**, at every sort. -/
theorem LTm.elim_rep : {s : Srt} → (t : LTm C s) → ElimM.Rep g ν s t.elim t
  | _, .var k => rfl
  | _, .app0 o => Op0.elim_rep g ν o
  | _, .app1 o x => Op1.elim_rep g ν o x _ (LTm.elim_rep x)
  | _, .app2 o x y => Op2.elim_rep g ν o x y _ _ (LTm.elim_rep x) (LTm.elim_rep y)
  | _, .app3 o x y z =>
    Op3.elim_rep g ν o x y z _ _ _ (LTm.elim_rep x) (LTm.elim_rep y) (LTm.elim_rep z)
  | _, .index it q i => pathIdx_rep g ν it (LTm.elim_rep q) (LTm.elim_rep i)
  | _, .obsW q => ElimM.ofOrig_rep g ν _ _
  | _, .obsL q => ElimM.ofOrig_rep g ν _ _
  | _, .obsH q => ElimM.ofOrig_rep g ν _ _
  | s, .seq (s' := s') d a =>
    ElimM.guarded_rep g ν d _ (ElimM.guard_eval g ν s' _ d (LTm.elim_rep d)) s _ a (LTm.elim_rep a)
  | s, .orElse a b => ElimM.orElse_rep g ν s _ _ a b (LTm.elim_rep a) (LTm.elim_rep b)
  | s, .kite a b t e =>
    ElimM.kite_rep g ν (LTm.elim_rep a) (LTm.elim_rep b) s _ _ t e (LTm.elim_rep t) (LTm.elim_rep e)
  | s, .err => ElimM.ofOrig_rep g ν s _

/-- **The elimination of a word keeps what it reads.** -/
theorem LTm.elim_eval {p : PrimTy} (t : LTm C (.val p)) :
    ((t.elim : LTm C (.val p)).eval g ν : Option p.Denote) = t.eval g ν :=
  LTm.elim_rep g ν t

/-- **The elimination keeps what a formula says.** -/
theorem LFml.elim_holds : (φ : LFml C) → ∀ (ν : AEnv), φ.elim.holds g ν ↔ φ.holds g ν
  | .tt, _ => Iff.rfl
  | .eq a b, ν => by
    simp only [LFml.elim, LFml.holds, LTm.elim_eval]
  | .not φ, ν => by simp only [LFml.elim, LFml.holds, LFml.elim_holds φ ν]
  | .and φ ψ, ν => by simp only [LFml.elim, LFml.holds, LFml.elim_holds φ ν, LFml.elim_holds ψ ν]
  | .imp φ ψ, ν => by simp only [LFml.elim, LFml.holds, LFml.elim_holds φ ν, LFml.elim_holds ψ ν]
  | .all k p φ, ν => by
    simp only [LFml.elim, LFml.holds]
    exact forall_congr' fun v => LFml.elim_holds φ _

end Decide

end Solidity
