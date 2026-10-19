import Solidity.Calculus.DecideEval

/-!
# The elimination leaves no storage operation

`LTm.elim` (`Calculus/Decide.lean`) reads every read of a write as a case
tree over key equalities whose leaves observe the starting storage
(`LTm.elim_eval`, `Calculus/DecideEval.lean`, says it reads what the term
reads).  Here: on the terms it has a reading for, what it leaves mentions
the starting storage only through the observation atoms `obsW`, `obsL`,
`obsH` (`LTm.elim_stoFree`, `LFml.elim_stoFree`).

* **No storage in a term** (`LTm.StoFree`) is said by sorts: no subterm at a
  storage sort (`st`, `sts`) or a stored value's (`sv`), and no path step
  that reads the storage it stands in (`next`, a checked `at`).  Every
  storage symbol (`storage`, `mtSt`, `find`, `len`, `sfind`, `save`,
  `delAt`, `push`, `pushSlot`, `pop`, `shrink`, `extend`, `copyMem`,
  `fixedCopy`, `wt`, `cleanTail`, `select`, …) takes or makes a term at
  one of those sorts, so a test of the sorts excludes them all, and any
  symbol added at those sorts later.
* **The terms with a reading** (`LTm.Elimable`) exclude what
  `ElimM.ofOrig` keeps as it is, since that is the term itself: a memory
  sort, `mtSt`, `wt`, `cleanTail` and `select` (each reads its argument as
  written), `copyMem` (its guard is the term), `sfindIn`; and `orElse`,
  `kite` and `err` at any sort but a word's, where the elimination keeps
  the term.  An observation atom of the input keeps its path as it is
  written, so that path must be storage-free already.
* **The proof** is an induction with an invariant on readers: a reader
  (`VRd`, `SRd`) is free (`VRd.Free`, `SRd.Free`) when it returns a free
  term on free segments, and each reader builder (`writeAt`, `delRS`,
  `ovRS`, `stripRS`, `pushRd`, `popRd`, `extendRd`, `svalRd`, …) keeps it.

A storage in "save normal form" (`LTm.SaveNF`: the starting storage, saves,
`pushSlot`s and `shrink`s on it at readable paths and values) is
`Elimable` (`LTm.SaveNF.elimable`), so a read of it eliminates to a
storage-free term (`LTm.SaveNF.find_stoFree`).
-/

namespace Solidity

namespace Decide

open Semantics

variable {C : Contract}

/-! ## No storage in a term -/

/-- A sort with no storage in it: not a storage's (`st`, `sts`), not a
stored value's (`sv`). -/
def _root_.Solidity.Srt.noSt : Srt → Bool
  | .st | .sts _ | .sv _ => false
  | _ => true

/-- A path step that reads the storage it stands in: `p[p.length]`. -/
def _root_.Solidity.Op1.readsSt {a s : Srt} : Op1 C a s → Bool
  | .next => true
  | _ => false

/-- A path step that reads the storage it stands in: a checked index. -/
def _root_.Solidity.Op2.readsSt {a b s : Srt} : Op2 C a b s → Bool
  | .at _ => true
  | _ => false

/-- **The term mentions no storage**: every subterm at a sort with no
storage in it (`Srt.noSt`), no step reading the storage it stands in; the
starting storage is read only by the observation atoms. -/
inductive LTm.StoFree : {s : Srt} → LTm C s → Prop where
  | var {p : PrimTy} (k : Nat) : LTm.StoFree (.var (p := p) k)
  | app0 {s : Srt} {o : Op0 C s} (hs : s.noSt = true) : LTm.StoFree (.app0 o)
  | app1 {a s : Srt} {o : Op1 C a s} {x : LTm C a} (hs : s.noSt = true) (ho : o.readsSt = false)
      (hx : LTm.StoFree x) : LTm.StoFree (.app1 o x)
  | app2 {a b s : Srt} {o : Op2 C a b s} {x : LTm C a} {y : LTm C b} (hs : s.noSt = true)
      (ho : o.readsSt = false) (hx : LTm.StoFree x) (hy : LTm.StoFree y) :
      LTm.StoFree (.app2 o x y)
  | app3 {a b c s : Srt} {o : Op3 C a b c s} {x : LTm C a} {y : LTm C b} {z : LTm C c}
      (hs : s.noSt = true) (hx : LTm.StoFree x) (hy : LTm.StoFree y) (hz : LTm.StoFree z) :
      LTm.StoFree (.app3 o x y z)
  | index {R : RefTy} {k : PrimTy} {V : Ty} {it : IndexTy R k V} {q : LTm C (.path (.ref R))}
      {i : LTm C (.val k)} (hq : LTm.StoFree q) (hi : LTm.StoFree i) :
      LTm.StoFree (.index it q i)
  | obsW {p : PrimTy} {q : LTm C (.path (.prim p))} (hq : LTm.StoFree q) : LTm.StoFree (.obsW q)
  | obsL {E : Ty} {q : LTm C (.path (.ref (.array E)))} (hq : LTm.StoFree q) :
      LTm.StoFree (.obsL q)
  | obsH {T : Ty} {q : LTm C (.path T)} (hq : LTm.StoFree q) : LTm.StoFree (.obsH q)
  | seq {s' s : Srt} {d : LTm C s'} {a : LTm C s} (hs : s.noSt = true) (hd : LTm.StoFree d)
      (ha : LTm.StoFree a) : LTm.StoFree (.seq d a)
  | orElse {s : Srt} {a b : LTm C s} (hs : s.noSt = true) (ha : LTm.StoFree a)
      (hb : LTm.StoFree b) : LTm.StoFree (.orElse a b)
  | kite {p : PrimTy} {s : Srt} {a b : LTm C (.val p)} {t e : LTm C s} (hs : s.noSt = true)
      (ha : LTm.StoFree a) (hb : LTm.StoFree b) (ht : LTm.StoFree t) (he : LTm.StoFree e) :
      LTm.StoFree (.kite a b t e)
  | err {s : Srt} (hs : s.noSt = true) : LTm.StoFree (.err : LTm C s)

/-- A storage-free term is at a sort with no storage: the starting storage,
a storage operation, a stored value never is one. -/
theorem LTm.StoFree.noSt {s : Srt} {t : LTm C s} (h : t.StoFree) : s.noSt = true := by
  cases h <;> first | rfl | assumption

/-- A formula whose terms mention no storage. -/
def LFml.StoFree : LFml C → Prop
  | .tt => True
  | .eq a b => a.StoFree ∧ b.StoFree
  | .not φ => φ.StoFree
  | .and φ ψ => φ.StoFree ∧ ψ.StoFree
  | .imp φ ψ => φ.StoFree ∧ ψ.StoFree
  | .all _ _ φ => φ.StoFree

/-! ### The builders -/

section Builders

theorem StoFree.lit {p : PrimTy} (v : p.Denote) : (LTm.lit v : LTm C (.val p)).StoFree :=
  .app0 rfl

theorem StoFree.nat (n : Nat) : (LTm.nat n : LTm C (.val .uint)).StoFree := .app0 rfl

theorem StoFree.tt : (LTm.tt : LTm C (.val .bool)).StoFree := .app0 rfl

theorem seqL_free {s' s : Srt} {g : LTm C s'} {a : LTm C s} (hg : g.StoFree) (ha : a.StoFree) :
    (seqL g a).StoFree := by
  unfold seqL
  split
  · exact ha
  · exact .seq ha.noSt hg ha

theorem assert_free {c : LTm C (.val .bool)} (hc : c.StoFree) : (LTm.assert c).StoFree := by
  unfold LTm.assert
  split
  · exact StoFree.tt
  · exact .app3 rfl hc StoFree.tt (.err rfl)

theorem cond_free {p : PrimTy} {c : LTm C (.val .bool)} {a b : LTm C (.val p)} (hc : c.StoFree)
    (ha : a.StoFree) (hb : b.StoFree) : (LTm.cond c a b).StoFree := by
  unfold LTm.cond
  split
  · exact ha
  split
  · exact hb
  split
  · exact seqL_free hc ha
  split
  · exact seqL_free hc hb
  · exact .app3 rfl hc ha hb

theorem lt_free {a b : LTm C (.val .uint)} (ha : a.StoFree) (hb : b.StoFree) :
    (LTm.lt a b).StoFree := by
  unfold LTm.lt
  split
  · exact StoFree.lit _
  · exact .app2 rfl rfl ha hb

theorem ltNat_free {a : LTm C (.val .uint)} (ha : a.StoFree) (n : Nat) :
    (LTm.ltNat a n).StoFree := by
  unfold LTm.ltNat
  split
  · exact lt_free ha (StoFree.nat n)
  · exact StoFree.tt

theorem succK_free {a : LTm C (.val .uint)} (ha : a.StoFree) : (LTm.succK a).StoFree := by
  unfold LTm.succK
  split
  · split
    · exact StoFree.nat _
    · exact .app2 rfl rfl ha (StoFree.nat 1)
  · exact .app2 rfl rfl ha (StoFree.nat 1)

theorem predK_free {a : LTm C (.val .uint)} (ha : a.StoFree) : (LTm.predK a).StoFree := by
  unfold LTm.predK
  split
  · split
    · exact StoFree.nat _
    · exact .app2 rfl rfl ha (StoFree.nat 1)
  · exact .app2 rfl rfl ha (StoFree.nat 1)

theorem kiteK_free {p : PrimTy} {s : Srt} {a b : LTm C (.val p)} {t e : LTm C s}
    (ha : a.StoFree) (hb : b.StoFree) (ht : t.StoFree) (he : e.StoFree) :
    (LTm.kiteK a b t e).StoFree := by
  unfold LTm.kiteK
  split
  · exact ht
  · exact he
  · exact .kite ht.noSt ha hb ht he

theorem CK.absent_free {V : Ty} (c : CK V) : (c.absent : LTm C (.val c.out)).StoFree := by
  cases c <;> exact .app0 rfl

theorem CK.reset_free {V : Ty} (c : CK V) {has : LTm C (.val .bool)} (hh : has.StoFree) :
    (c.reset has).StoFree := by
  cases c
  · exact .app0 rfl
  · exact .app0 rfl
  · exact hh

theorem CK.setLen_free {V : Ty} (c : CK V) {len' : LTm C (.val .uint)} {has : LTm C (.val .bool)}
    (hl : len'.StoFree) (hh : has.StoFree) : (c.setLen len' has).StoFree := by
  cases c
  · exact .app0 rfl
  · exact hl
  · exact hh

theorem foldModular_free {op : ModOp} {x y k : LTm C (.val .uint)} (hx : x.StoFree)
    (hy : y.StoFree) (hk : k.StoFree) : (foldModular op x y k).StoFree := by
  unfold foldModular
  split
  · split
    · exact StoFree.lit _
    · exact .err rfl
  · exact .app3 rfl hx hy hk

end Builders

/-! ## Free segments, paths and readers -/

/-- Segments whose keys mention no storage. -/
inductive TSegs.Free : {S T : Ty} → TSegs C S T → Prop where
  | nil {T : Ty} : TSegs.Free (.nil : TSegs C T T)
  | field {s f : Name} {T U : Ty} (h : lookupBy f (structDef s) = some T) {r : TSegs C T U}
      (hr : TSegs.Free r) : TSegs.Free (.field h r)
  | at {E U : Ty} {i : LTm C (.val .uint)} {r : TSegs C E U} (hi : i.StoFree)
      (hr : TSegs.Free r) : TSegs.Free (.at i r)
  | atF {E U : Ty} {n : Nat} {i : LTm C (.val .uint)} {r : TSegs C E U} (hi : i.StoFree)
      (hr : TSegs.Free r) : TSegs.Free (.atF (n := n) i r)
  | key {k : PrimTy} {V U : Ty} {i : LTm C (.val k)} {r : TSegs C V U} (hi : i.StoFree)
      (hr : TSegs.Free r) : TSegs.Free (.key i r)

/-- A symbolic path whose keys mention no storage. -/
def SPath.Free {T : Ty} (P : SPath C T) : Prop := P.segs.Free

/-- **A free reader**: on free segments, a storage-free term. -/
def VRd.Free {T : Ty} (x : VRd C T) : Prop :=
  ∀ {V : Ty} (c : CK V) (r : TSegs C T V), r.Free → (x c r).StoFree

/-- **A free storage reader**: on a free path, a storage-free term. -/
def SRd.Free (S : SRd C) : Prop :=
  ∀ {V : Ty} (c : CK V) (P : SPath C V), P.Free → (S c P).StoFree

/-- A storage eliminated to a free guard and a free reader. -/
def SFun.Free (S : SFun C) : Prop := S.ok.StoFree ∧ SRd.Free S.rd

section Paths

theorem TSegs.append_free {S U W : Ty} {p : TSegs C S U} {q : TSegs C U W} (hp : p.Free)
    (hq : q.Free) : (p.append q).Free := by
  induction hp with
  | nil => exact hq
  | field h _ ih => exact .field h (ih hq)
  | «at» hi _ ih => exact .at hi (ih hq)
  | atF hi _ ih => exact .atF hi (ih hq)
  | key hi _ ih => exact .key hi (ih hq)

theorem TSegs.ofIndex_free {R : RefTy} {k : PrimTy} {V : Ty} (it : IndexTy R k V)
    {i : LTm C (.val k)} (hi : i.StoFree) : (TSegs.ofIndex it i).Free := by
  cases it with
  | map => exact .key hi .nil
  | arr a => cases a with
    | dyn => exact .at hi .nil
    | fixed => exact .atF hi .nil

theorem TSegs.toLTm_free {S T : Ty} {p : TSegs C S T} (hp : p.Free) :
    ∀ {acc : LTm C (.path S)}, acc.StoFree → (p.toLTm acc).StoFree := by
  induction hp with
  | nil => exact fun h => h
  | field h _ ih => exact fun ha => ih (.app1 rfl rfl ha)
  | «at» hi _ ih => exact fun ha => ih (.index ha hi)
  | atF hi _ ih => exact fun ha => ih (.index ha hi)
  | key hi _ ih => exact fun ha => ih (.index ha hi)

theorem TSegs.hasFrom_free {S T : Ty} {p : TSegs C S T} (hp : p.Free) :
    ∀ {base : LTm C (.path S)} {acc : LTm C (.val .bool)}, base.StoFree → acc.StoFree →
      (p.hasFrom base acc).StoFree := by
  induction hp with
  | nil => exact fun _ h => h
  | field h _ ih => exact fun hb ha => ih (.app1 rfl rfl hb) ha
  | «at» hi _ ih => exact fun hb _ => ih (.index hb hi) (.obsH (.index hb hi))
  | @atF E U n i r hi _ ih =>
    intro base acc hb ha
    show (r.hasFrom _ (if TSegs.litBelow i n then acc else .obsH (.index (.arr .fixed) base i))).StoFree
    split
    · exact ih (.index hb hi) ha
    · exact ih (.index hb hi) (.obsH (.index hb hi))
  | key hi _ ih => exact fun hb ha => ih (.index hb hi) ha

theorem SPath.snoc_free {T U : Ty} {P : SPath C T} {s : TSegs C T U} (hP : P.Free)
    (hs : s.Free) : (P.snoc s).Free :=
  TSegs.append_free hP hs

theorem SPath.toLTm_free {T : Ty} {P : SPath C T} (hP : P.Free) : P.toLTm.StoFree :=
  TSegs.toLTm_free hP (.app0 rfl)

theorem dfltHas_free {U V : Ty} {r : TSegs C U V} (hr : r.Free) : (dfltHas r).StoFree := by
  induction hr with
  | nil => exact StoFree.tt
  | field _ _ ih => exact ih
  | «at» _ _ _ => exact StoFree.lit _
  | @atF E U n i r hi _ ih => exact cond_free (ltNat_free hi n) ih (StoFree.lit _)
  | key _ _ ih => exact ih

end Paths

/-! ### Comparing a write with a read -/

/-- A case tree whose tests mention no storage and whose leaves satisfy `P`. -/
def CTree.Free {α : Type} (P : α → Prop) : CTree C α → Prop
  | .leaf a => P a
  | .node a b t e => a.StoFree ∧ b.StoFree ∧ t.Free P ∧ e.Free P

theorem CTree.toTerm_free {α : Type} {q : PrimTy} {P : α → Prop} {f : α → LTm C (.val q)}
    (hf : ∀ a, P a → (f a).StoFree) : ∀ {t : CTree C α}, t.Free P → (t.toTerm f).StoFree
  | .leaf a, h => hf a h
  | .node _ _ _ _, ⟨ha, hb, ht, he⟩ =>
    .kite rfl ha hb (CTree.toTerm_free hf ht) (CTree.toTerm_free hf he)

theorem keyTree_free {α : Type} {p : PrimTy} {P : α → Prop} {a b : LTm C (.val p)}
    {t e : CTree C α} (ha : a.StoFree) (hb : b.StoFree) (ht : t.Free P) (he : e.Free P) :
    (keyTree a b t e).Free P := by
  unfold keyTree
  split
  · exact ht
  · exact he
  · exact ⟨ha, hb, ht, he⟩

/-- What `relSegs` leaves at a leaf: free segments past the write, or none. -/
def RestFree {T U : Ty} (o : Option (TSegs C T U)) : Prop := ∀ r, o = some r → r.Free

theorem restFree_none {T U : Ty} : RestFree (none : Option (TSegs C T U)) :=
  fun _ h => nomatch h

/-- **`relSegs` of free segments is free.** -/
theorem relSegs_free : ∀ {S T U : Ty} (p : TSegs C S T) (q : TSegs C S U), p.Free → q.Free →
    (relSegs p q).Free RestFree
  | _, _, _, .nil, q, _, hq => by
    rw [relSegs_nil]
    intro r h
    cases h
    exact hq
  | _, _, _, .field h p, .nil, _, _ => restFree_none
  | _, _, _, @TSegs.field _ _ f _ _ h p, @TSegs.field _ _ f' _ _ h' q, hp, hq => by
    rw [relSegs_field_field]
    cases hp with | field _ hp =>
    cases hq with | field _ hq =>
    by_cases ef : f = f'
    · subst ef
      obtain rfl := field_ty_eq h h' rfl rfl
      rw [dif_pos rfl]
      exact relSegs_free p q hp hq
    · simp only [ef, dif_neg, not_false_eq_true]
      exact restFree_none
  | _, _, _, .at i p, .nil, _, _ => restFree_none
  | _, _, _, .at i p, .at j q, hp, hq => by
    rw [relSegs_at_at]
    cases hp with | «at» hi hp =>
    cases hq with | «at» hj hq =>
    exact keyTree_free hi hj (relSegs_free p q hp hq) restFree_none
  | _, _, _, .atF i p, .nil, _, _ => restFree_none
  | _, _, _, .atF i p, .atF j q, hp, hq => by
    rw [relSegs_atF_atF]
    cases hp with | atF hi hp =>
    cases hq with | atF hj hq =>
    exact keyTree_free hi hj (relSegs_free p q hp hq) restFree_none
  | _, _, _, .key i p, .nil, _, _ => restFree_none
  | _, _, _, .key i p, .key j q, hp, hq => by
    rw [relSegs_key_key]
    cases hp with | key hi hp =>
    cases hq with | key hj hq =>
    exact keyTree_free hi hj (relSegs_free p q hp hq) restFree_none

/-! ### The readers -/

section Readers

theorem VRd.find_free {T U : Ty} {x : VRd C T} {s : TSegs C T U} (hx : x.Free) (hs : s.Free) :
    VRd.Free (x.find s) :=
  fun {_} c _ hr => hx c _ (TSegs.append_free hs hr)

theorem SRd.at_free {T : Ty} {S : SRd C} {P : SPath C T} (hS : S.Free) (hP : P.Free) :
    VRd.Free (S.at P) :=
  fun {_} c _ hr => hS c _ (SPath.snoc_free hP hr)

theorem delRS_free {U V : Ty} {r : TSegs C U V} (hr : r.Free) (c : CK V) :
    ∀ {x : VRd C U}, x.Free → (delRS x r c).StoFree := by
  induction hr with
  | nil => exact fun hx => CK.reset_free c (hx _ _ .nil)
  | field h _ ih => exact fun hx => ih c (VRd.find_free hx (.field h .nil))
  | «at» hi hr ih =>
    exact fun hx => cond_free (lt_free hi (hx _ _ .nil)) (ih c (VRd.find_free hx (.at hi .nil)))
      (hx c _ (.at hi hr))
  | atF hi _ ih => exact fun hx => ih c (VRd.find_free hx (.atF hi .nil))
  | key hi hr _ => exact fun hx => hx c _ (.key hi hr)

theorem stripRS_free {U V : Ty} {r : TSegs C U V} (hr : r.Free) (c : CK V) :
    ∀ {x : VRd C U}, x.Free → (stripRS x r c).StoFree := by
  induction hr with
  | nil => exact fun hx => hx c _ .nil
  | field h _ ih => exact fun hx => ih c (VRd.find_free hx (.field h .nil))
  | «at» hi _ ih =>
    exact fun hx => cond_free (lt_free hi (hx _ _ .nil)) (ih c (VRd.find_free hx (.at hi .nil)))
      (CK.absent_free c)
  | atF hi _ ih => exact fun hx => ih c (VRd.find_free hx (.atF hi .nil))
  | key hi hr _ => exact fun hx => hx c _ (.key hi hr)

theorem ovRS_free {U V : Ty} {r : TSegs C U V} (hr : r.Free) (c : CK V) :
    ∀ {o n : VRd C U}, o.Free → n.Free → (ovRS o n r c).StoFree := by
  induction hr with
  | nil => exact fun _ hn => hn c _ .nil
  | field h _ ih =>
    exact fun ho hn => ih c (VRd.find_free ho (.field h .nil)) (VRd.find_free hn (.field h .nil))
  | «at» hi hr ih =>
    exact fun ho hn => cond_free (hn _ _ .nil)
      (cond_free (lt_free hi (hn _ _ .nil))
        (ih c (VRd.find_free ho (.at hi .nil)) (VRd.find_free hn (.at hi .nil)))
        (cond_free (lt_free hi (ho _ _ .nil)) (delRS_free hr c (VRd.find_free ho (.at hi .nil)))
          (ho c _ (.at hi hr))))
      (CK.absent_free c)
  | atF hi _ ih =>
    exact fun ho hn => ih c (VRd.find_free ho (.atF hi .nil)) (VRd.find_free hn (.atF hi .nil))
  | key hi hr _ =>
    exact fun ho hn => cond_free (hn _ _ .nil) (cond_free (ho _ _ .nil) (ho c _ (.key hi hr))
      (hn c _ (.key hi hr))) (CK.absent_free c)

theorem arrRd_free {E : Ty} {len' : LTm C (.val .uint)} {has : LTm C (.val .bool)}
    {below : LTm C (.val .uint) → VRd C E} (hl : len'.StoFree) (hh : has.StoFree)
    (hb : ∀ i : LTm C (.val .uint), i.StoFree → VRd.Free (below i)) : VRd.Free (arrRd len' has below) := by
  intro V c r hr
  cases hr with
  | nil => exact CK.setLen_free c hl hh
  | «at» hi hr => exact hb _ hi c _ hr

theorem pushRd_free {E : Ty} {a : VRd C (.ref (.array E))} {x : VRd C E} {L : LTm C (.val .uint)}
    (ha : a.Free) (hx : x.Free) (hL : L.StoFree) : VRd.Free (pushRd a x L) :=
  arrRd_free (succK_free hL) (ha _ _ .nil) fun _ hi {_} c _ hr =>
    kiteK_free hi hL (hx c _ hr) (ha c _ (.at hi hr))

theorem setLenRd_free {E : Ty} {a : VRd C (.ref (.array E))} {L : LTm C (.val .uint)}
    (ha : a.Free) (hL : L.StoFree) : VRd.Free (setLenRd a L) :=
  arrRd_free hL (ha _ _ .nil) fun _ hi {_} c _ hr => ha c _ (.at hi hr)

theorem dfltRd_free (E : Ty) : VRd.Free (dfltRd E : VRd C E) :=
  fun {_} c _ hr => CK.reset_free c (dfltHas_free hr)

theorem newArrRd_free {R : RefTy} (h : R.newArrOk = true) {n : LTm C (.val .uint)}
    (hn : n.StoFree) : VRd.Free (newArrRd R h n) := by
  cases R with
  | array E =>
    exact arrRd_free hn StoFree.tt fun _ hi {_} c _ hr =>
      cond_free (lt_free hi hn) (dfltRd_free E c _ hr) (CK.absent_free c)
  | _ => exact absurd h Bool.false_ne_true

theorem fixedCopyChildRd_free {E : Ty} {n : Nat} {R : RefTy} (shape : FixedCopy E n R)
    {a : VRd C (.ref (.fixed E n))} (ha : a.Free) {i : LTm C (.val .uint)} (hi : i.StoFree) :
    VRd.Free (fixedCopyChildRd shape a i) :=
  fun {_} c _ hr => cond_free (ltNat_free hi _)
    (cond_free (ltNat_free hi _) (stripRS_free hr c (VRd.find_free ha (.atF hi .nil)))
      (stripRS_free hr c (dfltRd_free E))) (CK.absent_free c)

theorem fixedArrRd_free {E : Ty} {n : Nat} {has : LTm C (.val .bool)}
    {below : LTm C (.val .uint) → VRd C E} (hh : has.StoFree)
    (hb : ∀ i : LTm C (.val .uint), i.StoFree → VRd.Free (below i)) :
    VRd.Free (fixedArrRd n has below) := by
  intro V c r hr
  cases hr with
  | nil => exact CK.reset_free c hh
  | atF hi hr => exact hb _ hi c _ hr

theorem fixedCopyRd_free {E : Ty} {n : Nat} {R : RefTy} (shape : FixedCopy E n R)
    {a : VRd C (.ref (.fixed E n))} (ha : a.Free) : VRd.Free (fixedCopyRd shape a) := by
  cases shape with
  | dynamic hb =>
    exact arrRd_free (StoFree.nat n) StoFree.tt fun _ hi => fixedCopyChildRd_free _ ha hi
  | fixed m hm =>
    exact fixedArrRd_free StoFree.tt fun _ hi => fixedCopyChildRd_free _ ha hi

theorem extendRd_free {E : Ty} {a : VRd C (.ref (.array E))} {L : LTm C (.val .uint)}
    (ha : a.Free) (hL : L.StoFree) : VRd.Free (extendRd a L) := by
  unfold extendRd
  split
  · exact pushRd_free ha (dfltRd_free E) hL
  · exact fun {_} c _ hr => cond_free (ha _ _ (.at hL .nil)) (setLenRd_free ha (succK_free hL) c _ hr)
      (pushRd_free ha (dfltRd_free E) hL c _ hr)

theorem popRd_free (keep : Bool) {E : Ty} {a : VRd C (.ref (.array E))} {L : LTm C (.val .uint)}
    (ha : a.Free) (hL : L.StoFree) : VRd.Free (popRd keep a L) := by
  cases keep
  · exact arrRd_free (predK_free hL) (ha _ _ .nil) fun _ hi {_} c _ hr =>
      kiteK_free hi (predK_free hL) (delRS_free hr c (VRd.find_free ha (.at (predK_free hL) .nil)))
        (ha c _ (.at hi hr))
  · exact setLenRd_free ha (predK_free hL)

theorem svalRd_free {p : PrimTy} {w : LTm C (.val p)} (hw : w.StoFree) : VRd.Free (svalRd w) := by
  intro V c r hr
  cases hr with
  | nil =>
    cases c with
    | word P => exact hw
    | has V => exact StoFree.tt

theorem writeAt_free {T : Ty} {S : SRd C} {P : SPath C T} {newR : VRd C T} (hS : S.Free)
    (hP : P.Free) (hn : newR.Free) : SRd.Free (writeAt S P newR) := by
  intro V c Q hQ
  cases P with | mk rp hrp sp =>
  cases Q with | mk rq hrq sq =>
  unfold writeAt
  by_cases h : rp = rq
  · subst h
    obtain rfl := root_inj rfl hrp hrq
    dsimp only; rw [dif_pos rfl]
    refine CTree.toTerm_free ?_ (relSegs_free sp sq hP hQ)
    intro o ho
    cases o with
    | none => exact hS c _ hQ
    | some r => exact hn c r (ho r rfl)
  · simp only [dif_neg h]
    exact hS c _ hQ

theorem initRd_free : SRd.Free (initRd : SRd C) := by
  intro V c P hP
  cases c with
  | word _ => exact .obsW (SPath.toLTm_free hP)
  | len _ => exact .obsL (SPath.toLTm_free hP)
  | has _ => exact TSegs.hasFrom_free hP (.app0 rfl) StoFree.tt

end Readers

/-! ### The storages -/

section Storages

theorem SFun.init_free : (SFun.init : SFun C).Free := ⟨StoFree.tt, initRd_free⟩

variable {S : SFun C} {Pg : LTm C (.val .bool)} {orig : LTm C .st}

theorem SFun.save_free {T : Ty} {P : SPath C T} {Vok : LTm C (.val .bool)} {V : VRd C T}
    (hS : S.Free) (hPg : Pg.StoFree) (hP : P.Free) (hVok : Vok.StoFree) (hV : V.Free) :
    (S.save Pg P Vok V orig).Free :=
  ⟨seqL_free hS.1 (seqL_free hPg (seqL_free hVok (assert_free (hS.2 _ P hP)))),
    writeAt_free hS.2 hP fun {_} c _ hr => ovRS_free hr c (SRd.at_free hS.2 hP) hV⟩

theorem SFun.delAt_free {T : Ty} {P : SPath C T} (hS : S.Free) (hPg : Pg.StoFree) (hP : P.Free) :
    (S.delAt Pg P orig).Free :=
  ⟨seqL_free hS.1 (seqL_free hPg (assert_free (hS.2 _ P hP))),
    writeAt_free hS.2 hP fun {_} c _ hr => delRS_free hr c (SRd.at_free hS.2 hP)⟩

theorem SFun.push_free {E : Ty} {P : SPath C (.ref (.array E))} {Vok : LTm C (.val .bool)}
    {V : VRd C E} (hS : S.Free) (hPg : Pg.StoFree) (hP : P.Free) (hVok : Vok.StoFree)
    (hV : V.Free) : (S.push Pg P Vok V orig).Free :=
  ⟨seqL_free hS.1 (seqL_free hPg (seqL_free hVok (seqL_free (assert_free (hS.2 _ P hP))
      (assert_free (lt_free (hS.2 _ P hP) (.app0 rfl)))))),
    writeAt_free hS.2 hP (pushRd_free (SRd.at_free hS.2 hP) (fun {_} c _ hr => stripRS_free hr c hV)
      (hS.2 _ P hP))⟩

theorem SFun.extend_free {E : Ty} {P : SPath C (.ref (.array E))} (hS : S.Free)
    (hPg : Pg.StoFree) (hP : P.Free) : (S.extend Pg P orig).Free :=
  ⟨seqL_free hS.1 (seqL_free hPg (seqL_free (assert_free (hS.2 _ P hP))
      (assert_free (lt_free (hS.2 _ P hP) (.app0 rfl))))),
    writeAt_free hS.2 hP (extendRd_free (SRd.at_free hS.2 hP) (hS.2 _ P hP))⟩

theorem SFun.pop_free (keep : Bool) {E : Ty} {P : SPath C (.ref (.array E))} (hS : S.Free)
    (hPg : Pg.StoFree) (hP : P.Free) : (S.pop keep Pg P orig).Free :=
  ⟨seqL_free hS.1 (seqL_free hPg (seqL_free (assert_free (hS.2 _ P hP))
      (assert_free (lt_free (StoFree.nat 0) (hS.2 _ P hP))))),
    writeAt_free hS.2 hP (popRd_free keep (SRd.at_free hS.2 hP) (hS.2 _ P hP))⟩

end Storages

/-! ## The elimination -/

/-- **What the elimination leaves, free**: a storage a free guard and a free
reader; a path or a stored value a reading (not `none`, which keeps the
term) with a free guard; a word or a KeY `int` a storage-free term; nothing
at a memory sort. -/
def ElimM.Free : (s : Srt) → ElimM C s → Prop
  | .st, e => SFun.Free (e : SFun C)
  | .path _, e => match (e : Option (LTm C (.val .bool) × SPath C _)) with
    | some (g, P) => g.StoFree ∧ P.Free
    | none => False
  | .sv _, e => match (e : Option (LTm C (.val .bool) × VRd C _)) with
    | some (g, V) => g.StoFree ∧ VRd.Free V
    | none => False
  | .val _, e => LTm.StoFree (e : LTm C (.val _))
  | .kint, e => LTm.StoFree (e : LTm C .kint)
  | _, _ => False

/-- The constants the elimination reads: not `memory`, `mtSt` (kept as
written) or a member under `select`. -/
def _root_.Solidity.Op0.elimOk {s : Srt} : Op0 C s → Bool
  | .lit _ | .env _ | .root _ _ | .storage | .zlit _ => true
  | _ => false

/-- The unary symbols the elimination reads: not the memory ones, nor `wt`,
`cleanTail`, `select` and the symbols under it (each kept as written). -/
def _root_.Solidity.Op1.elimOk {a s : Srt} : Op1 C a s → Bool
  | .unop _ _ | .net | .delValue | .field _ | .next | .sval | .newArr _ | .toInt
  | .fixedCopy _ => true
  | _ => false

/-- The binary symbols the elimination reads: not the memory ones (`copyMem`
among them: its guard is the term), nor those under `select`. -/
def _root_.Solidity.Op2.elimOk {a b s : Srt} : Op2 C a b s → Bool
  | .binop _ _ | .find | .len | .at _ | .nextIn | .delAt | .pushSlot | .pop | .shrink | .extend
  | .sfind | .zbin _ _ | .zcmp _ _ => true
  | _ => false

/-- The ternary symbols the elimination reads: not `write` and `saveIn`. -/
def _root_.Solidity.Op3.elimOk {a b c s : Srt} : Op3 C a b c s → Bool
  | .ite | .save | .push | .atIn _ | .modular _ => true
  | _ => false

/-- **A term the elimination has a reading for** at every node: the symbols
it reads (`Op0.elimOk` … `Op3.elimOk`), an observation of the starting
storage at a storage-free path (kept as written), and `orElse`, `kite`,
`err` only at a word (elsewhere kept as written). -/
inductive LTm.Elimable : {s : Srt} → LTm C s → Prop where
  | var {p : PrimTy} (k : Nat) : LTm.Elimable (.var (p := p) k)
  | app0 {s : Srt} {o : Op0 C s} (ho : o.elimOk = true) : LTm.Elimable (.app0 o)
  | app1 {a s : Srt} {o : Op1 C a s} {x : LTm C a} (ho : o.elimOk = true) (hx : LTm.Elimable x) :
      LTm.Elimable (.app1 o x)
  | app2 {a b s : Srt} {o : Op2 C a b s} {x : LTm C a} {y : LTm C b} (ho : o.elimOk = true)
      (hx : LTm.Elimable x) (hy : LTm.Elimable y) : LTm.Elimable (.app2 o x y)
  | app3 {a b c s : Srt} {o : Op3 C a b c s} {x : LTm C a} {y : LTm C b} {z : LTm C c}
      (ho : o.elimOk = true) (hx : LTm.Elimable x) (hy : LTm.Elimable y) (hz : LTm.Elimable z) :
      LTm.Elimable (.app3 o x y z)
  | index {R : RefTy} {k : PrimTy} {V : Ty} {it : IndexTy R k V} {q : LTm C (.path (.ref R))}
      {i : LTm C (.val k)} (hq : LTm.Elimable q) (hi : LTm.Elimable i) :
      LTm.Elimable (.index it q i)
  | obsW {p : PrimTy} {q : LTm C (.path (.prim p))} (hq : q.StoFree) : LTm.Elimable (.obsW q)
  | obsL {E : Ty} {q : LTm C (.path (.ref (.array E)))} (hq : q.StoFree) :
      LTm.Elimable (.obsL q)
  | obsH {T : Ty} {q : LTm C (.path T)} (hq : q.StoFree) : LTm.Elimable (.obsH q)
  | seq {s' s : Srt} {d : LTm C s'} {a : LTm C s} (hd : LTm.Elimable d) (ha : LTm.Elimable a) :
      LTm.Elimable (.seq d a)
  | orElse {p : PrimTy} {a b : LTm C (.val p)} (ha : LTm.Elimable a) (hb : LTm.Elimable b) :
      LTm.Elimable (.orElse a b)
  | kite {p q : PrimTy} {a b : LTm C (.val p)} {t e : LTm C (.val q)} (ha : LTm.Elimable a)
      (hb : LTm.Elimable b) (ht : LTm.Elimable t) (he : LTm.Elimable e) :
      LTm.Elimable (.kite a b t e)
  | err {p : PrimTy} : LTm.Elimable (.err : LTm C (.val p))

/-- A formula whose terms the elimination has a reading for. -/
def LFml.Elimable : LFml C → Prop
  | .tt => True
  | .eq a b => a.Elimable ∧ b.Elimable
  | .not φ => φ.Elimable
  | .and φ ψ => φ.Elimable ∧ ψ.Elimable
  | .imp φ ψ => φ.Elimable ∧ ψ.Elimable
  | .all _ _ φ => φ.Elimable

section Elim

theorem pathIdx_free {R : RefTy} {k : PrimTy} {V : Ty} (it : IndexTy R k V)
    {q : ElimM C (.path (.ref R))} {i : LTm C (.val k)} (hq : ElimM.Free _ q) (hi : i.StoFree) :
    ElimM.Free (.path V) (pathIdx it q i) := by
  rcases q with _ | ⟨g, P⟩
  · exact hq.elim
  · exact ⟨seqL_free hq.1 (seqL_free hi StoFree.tt), SPath.snoc_free hq.2 (TSegs.ofIndex_free it hi)⟩

theorem boundG_free {R : RefTy} {k : PrimTy} {V : Ty} (it : IndexTy R k V) {rd : SRd C}
    {Q : SPath C (.ref R)} {i : LTm C (.val k)} (hS : SRd.Free rd) (hQ : Q.Free) (hi : i.StoFree) :
    (boundG it rd Q i).StoFree := by
  cases it with
  | map => exact StoFree.tt
  | arr a => cases a with
    | dyn => exact assert_free (lt_free hi (hS _ Q hQ))
    | fixed => exact assert_free (ltNat_free hi _)

theorem pathAtIn_free {R : RefTy} {k : PrimTy} {V : Ty} (it : IndexTy R k V) {S : SFun C}
    {q : ElimM C (.path (.ref R))} {i : LTm C (.val k)} (hS : S.Free) (hq : ElimM.Free _ q)
    (hi : i.StoFree) : ElimM.Free (.path V) (pathAtIn it S q i) := by
  rcases q with _ | ⟨g, P⟩
  · exact hq.elim
  · exact ⟨seqL_free hS.1 (seqL_free hq.1 (seqL_free hi (seqL_free (assert_free (hS.2 _ P hq.2))
      (boundG_free it hS.2 hq.2 hi)))), SPath.snoc_free hq.2 (TSegs.ofIndex_free it hi)⟩

theorem pathNext_free {E : Ty} {S : SFun C} {q : ElimM C (.path (.ref (.array E)))}
    (hS : S.Free) (hq : ElimM.Free _ q) : ElimM.Free (.path E) (pathNext S q) := by
  rcases q with _ | ⟨g, P⟩
  · exact hq.elim
  · exact ⟨seqL_free hS.1 (seqL_free hq.1 (assert_free (hS.2 _ P hq.2))),
      SPath.snoc_free hq.2 (.at (hS.2 _ P hq.2) .nil)⟩

theorem Op0.elim_free {s : Srt} (o : Op0 C s) (ho : o.elimOk = true) : ElimM.Free s o.elim := by
  cases o with
  | lit v => exact .app0 rfl
  | env k => exact .app0 rfl
  | root r h => exact ⟨StoFree.tt, .nil⟩
  | storage => exact SFun.init_free
  | zlit n => exact .app0 rfl
  | _ => exact absurd ho Bool.false_ne_true

theorem Op1.elim_free {a s : Srt} (o : Op1 C a s) (ho : o.elimOk = true) (x : LTm C a)
    {ex : ElimM C a} (hx : ElimM.Free a ex) : ElimM.Free s (o.elim x ex) := by
  cases o with
  | unop op h => exact .app1 rfl rfl hx
  | net => exact .app1 rfl rfl hx
  | delValue => exact .app1 rfl rfl hx
  | field h =>
    rcases ex with _ | ⟨g, P⟩
    · exact hx.elim
    · exact ⟨hx.1, SPath.snoc_free hx.2 (.field h .nil)⟩
  | next => exact pathNext_free SFun.init_free hx
  | sval => exact ⟨seqL_free hx StoFree.tt, svalRd_free hx⟩
  | newArr h => exact ⟨seqL_free hx StoFree.tt, newArrRd_free h hx⟩
  | toInt => exact .app1 rfl rfl hx
  | fixedCopy shape =>
    rcases ex with _ | ⟨g, V⟩
    · exact hx.elim
    · exact ⟨hx.1, fixedCopyRd_free shape hx.2⟩
  | _ => exact absurd ho Bool.false_ne_true

theorem Op2.elim_free {a b s : Srt} (o : Op2 C a b s) (ho : o.elimOk = true) (x : LTm C a)
    (y : LTm C b) {ex : ElimM C a} {ey : ElimM C b} (hx : ElimM.Free a ex)
    (hy : ElimM.Free b ey) : ElimM.Free s (o.elim x y ex ey) := by
  cases o with
  | binop op h => exact .app2 rfl rfl hx hy
  | find =>
    rcases ey with _ | ⟨g, Q⟩
    · exact hy.elim
    · exact seqL_free hx.1 (seqL_free hy.1 (cond_free (hx.2 _ Q hy.2) (hx.2 _ Q hy.2) (.err rfl)))
  | len =>
    rcases ey with _ | ⟨g, Q⟩
    · exact hy.elim
    · exact seqL_free hx.1 (seqL_free hy.1 (cond_free (hx.2 _ Q hy.2) (hx.2 _ Q hy.2) (.err rfl)))
  | «at» it => exact pathAtIn_free it SFun.init_free hx hy
  | nextIn => exact pathNext_free hx hy
  | delAt =>
    rcases ey with _ | ⟨g, Q⟩
    · exact hy.elim
    · exact SFun.delAt_free hx hy.1 hy.2
  | pushSlot =>
    rcases ey with _ | ⟨g, Q⟩
    · exact hy.elim
    · exact SFun.extend_free hx hy.1 hy.2
  | pop =>
    rcases ey with _ | ⟨g, Q⟩
    · exact hy.elim
    · exact SFun.pop_free false hx hy.1 hy.2
  | shrink =>
    rcases ey with _ | ⟨g, Q⟩
    · exact hy.elim
    · exact SFun.pop_free true hx hy.1 hy.2
  | extend =>
    rcases ey with _ | ⟨g, Q⟩
    · exact hy.elim
    · exact SFun.extend_free hx hy.1 hy.2
  | sfind =>
    rcases ey with _ | ⟨g, Q⟩
    · exact hy.elim
    · exact ⟨seqL_free hx.1 (seqL_free hy.1 (assert_free (hx.2 _ Q hy.2))),
        SRd.at_free hx.2 hy.2⟩
  | zbin op h => exact .app2 rfl rfl hx hy
  | zcmp op h => exact .app2 rfl rfl hx hy
  | _ => exact absurd ho Bool.false_ne_true

theorem Op3.elim_free {a b c s : Srt} (o : Op3 C a b c s) (ho : o.elimOk = true) (x : LTm C a)
    (y : LTm C b) (z : LTm C c) {ex : ElimM C a} {ey : ElimM C b} {ez : ElimM C c}
    (hx : ElimM.Free a ex) (hy : ElimM.Free b ey) (hz : ElimM.Free c ez) :
    ElimM.Free s (o.elim x y z ex ey ez) := by
  cases o with
  | ite => exact .app3 rfl hx hy hz
  | save =>
    rcases ey with _ | ⟨g, Q⟩
    · exact hy.elim
    rcases ez with _ | ⟨gv, V⟩
    · exact hz.elim
    · exact SFun.save_free hx hy.1 hy.2 hz.1 hz.2
  | push =>
    rcases ey with _ | ⟨g, Q⟩
    · exact hy.elim
    rcases ez with _ | ⟨gv, V⟩
    · exact hz.elim
    · exact SFun.push_free hx hy.1 hy.2 hz.1 hz.2
  | atIn it => exact pathAtIn_free it hx hy hz
  | modular op => exact foldModular_free hx hy hz
  | _ => exact absurd ho Bool.false_ne_true

theorem ElimM.guard_free {s : Srt} {e : ElimM C s} (t : LTm C s) (h : ElimM.Free s e) :
    (ElimM.guard s e t).StoFree := by
  cases s with
  | st => exact h.1
  | path T =>
    rcases e with _ | ⟨g, P⟩
    · exact h.elim
    · exact h.1
  | sv T =>
    rcases e with _ | ⟨g, V⟩
    · exact h.elim
    · exact h.1
  | val p => exact seqL_free h StoFree.tt
  | kint => exact seqL_free h StoFree.tt
  | _ => exact h.elim

theorem ElimM.guarded_free {s : Srt} {g : LTm C (.val .bool)} {e : ElimM C s} (o : LTm C s)
    (hg : g.StoFree) (h : ElimM.Free s e) : ElimM.Free s (ElimM.guarded s g e o) := by
  cases s with
  | st => exact ⟨seqL_free hg h.1, h.2⟩
  | path T =>
    rcases e with _ | ⟨g', P⟩
    · exact h.elim
    · exact ⟨seqL_free hg h.1, h.2⟩
  | sv T =>
    rcases e with _ | ⟨g', V⟩
    · exact h.elim
    · exact ⟨seqL_free hg h.1, h.2⟩
  | val p => exact seqL_free hg h
  | kint => exact seqL_free hg h
  | _ => exact h.elim

/-- **The elimination of a term with a reading leaves a free reading.** -/
theorem LTm.elim_free {s : Srt} {t : LTm C s} (h : t.Elimable) : ElimM.Free s t.elim := by
  induction h with
  | var k => exact .var k
  | app0 ho => exact Op0.elim_free _ ho
  | app1 ho _ ih => exact Op1.elim_free _ ho _ ih
  | app2 ho _ _ ihx ihy => exact Op2.elim_free _ ho _ _ ihx ihy
  | app3 ho _ _ _ ihx ihy ihz => exact Op3.elim_free _ ho _ _ _ ihx ihy ihz
  | index _ _ ihq ihi => exact pathIdx_free _ ihq ihi
  | obsW hq => exact .obsW hq
  | obsL hq => exact .obsL hq
  | obsH hq => exact .obsH hq
  | seq _ _ ihd iha => exact ElimM.guarded_free _ (ElimM.guard_free _ ihd) iha
  | orElse _ _ iha ihb => exact .orElse rfl iha ihb
  | kite _ _ _ _ iha ihb iht ihe => exact .kite rfl iha ihb iht ihe
  | err => exact .err rfl

/-- **The elimination leaves no storage operation**: a word term with a
reading eliminates to a term that reads the starting storage only through
`obsW`, `obsL`, `obsH`. -/
theorem LTm.elim_stoFree {p : PrimTy} {t : LTm C (.val p)} (h : t.Elimable) :
    (t.elim : LTm C (.val p)).StoFree :=
  LTm.elim_free h

/-- **The elimination of a formula leaves no storage operation.** -/
theorem LFml.elim_stoFree : ∀ (φ : LFml C), φ.Elimable → φ.elim.StoFree
  | .tt, _ => trivial
  | .eq _ _, ⟨ha, hb⟩ => ⟨LTm.elim_stoFree ha, LTm.elim_stoFree hb⟩
  | .not φ, h => LFml.elim_stoFree φ h
  | .and φ ψ, ⟨h, h'⟩ => ⟨LFml.elim_stoFree φ h, LFml.elim_stoFree ψ h'⟩
  | .imp φ ψ, ⟨h, h'⟩ => ⟨LFml.elim_stoFree φ h, LFml.elim_stoFree ψ h'⟩
  | .all _ _ φ, h => LFml.elim_stoFree φ h

end Elim

/-! ## Save normal form -/

/-- **A storage in save normal form**: the starting storage, with saves,
`pushSlot`s and `shrink`s on it at paths and values the elimination reads
(reads of the start, no write of their own needed). -/
inductive LTm.SaveNF : LTm C .st → Prop where
  | storage : LTm.SaveNF (.app0 .storage)
  | save {T : Ty} {s : LTm C .st} {p : LTm C (.path T)} {v : LTm C (.sv T)} (hs : LTm.SaveNF s)
      (hp : p.Elimable) (hv : v.Elimable) : LTm.SaveNF (.app3 .save s p v)
  | pushSlot {E : Ty} {s : LTm C .st} {p : LTm C (.path (.ref (.array E)))} (hs : LTm.SaveNF s)
      (hp : p.Elimable) : LTm.SaveNF (.app2 .pushSlot s p)
  | shrink {E : Ty} {s : LTm C .st} {p : LTm C (.path (.ref (.array E)))} (hs : LTm.SaveNF s)
      (hp : p.Elimable) : LTm.SaveNF (.app2 .shrink s p)

theorem LTm.SaveNF.elimable {s : LTm C .st} (h : s.SaveNF) : s.Elimable := by
  induction h with
  | storage => exact .app0 rfl
  | save _ hp hv ih => exact .app3 rfl ih hp hv
  | pushSlot _ hp ih => exact .app2 rfl ih hp
  | shrink _ hp ih => exact .app2 rfl ih hp

/-- A word read in a storage in save normal form eliminates to a
storage-free term. -/
theorem LTm.SaveNF.find_stoFree {p : PrimTy} {s : LTm C .st} {q : LTm C (.path (.prim p))}
    (hs : s.SaveNF) (hq : q.Elimable) :
    ((LTm.app2 .find s q).elim : LTm C (.val p)).StoFree :=
  LTm.elim_stoFree (.app2 rfl hs.elimable hq)

end Decide

end Solidity
