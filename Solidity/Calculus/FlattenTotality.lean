import Solidity.Calculus.LeafTotality

/-!
# Read flattening never refuses its fragment

The source leaf's storage reads (`obsW` of a root, field and mapping-key
path) become fresh atoms with a guard (`Calculus/FlattenReads.lean`); this
module proves that, on the source fragment `LTm.Src`, flattening, its path
views and guards, the occurrence layout and the read-free checks all
succeed, under a node budget, and that the flattened leaf lies in the
arithmetic compiler's fragment (`LFml.Arith`, `Calculus/LeafTotality.lean`).
-/

namespace Solidity.Decide

open Semantics ReadRealization

variable {C : Contract}

/-- The number of nodes of a term. -/
def LTm.nodes : {s : Srt} → LTm C s → Nat
  | _, .var _ | _, .app0 _ | _, .err => 1
  | _, .app1 _ a | _, .obsW a | _, .obsL a | _, .obsH a => a.nodes + 1
  | _, .app2 _ a b | _, .index _ a b | _, .seq a b | _, .orElse a b => a.nodes + b.nodes + 1
  | _, .app3 _ a b c => a.nodes + b.nodes + c.nodes + 1
  | _, .kite a b t e => a.nodes + b.nodes + t.nodes + e.nodes + 1

theorem LTm.depth_le_nodes {s : Srt} (t : LTm C s) : t.depth ≤ t.nodes := by
  induction t <;> simp only [LTm.depth, LTm.nodes] <;> omega

/-- The flattened paths: a root, fields and mapping keys. -/
inductive LTm.PathF (ps : Parameter → Prop) (es : EnvKey → Prop) : {T : Ty} → LTm C (.path T) → Prop
  | root (r : Name) {T : Ty} (h : C.rootType r = some T) : LTm.PathF ps es (.app0 (.root r h))
  | field {s f : Name} {T : Ty} (h : C.fieldType s f = some T) {q : LTm C (.path (.ref (.struct s)))} :
      LTm.PathF ps es q → LTm.PathF ps es (.app1 (.field h) q)
  | key {K : PrimTy} {V : Ty} {q : LTm C (.path (.ref (.mapping K V)))} {k : LTm C (.val K)} :
      LTm.PathF ps es q → k.Num ps es → LTm.PathF ps es (.index .map q k)

/-! ## Flattened terms read nothing -/

/-- A recognized query that reads nothing. -/
def ReadFreeOf {s : Srt} (t : LTm C s) : Prop := ∃ e, ReadExpr.ofTerm? t = some e ∧ e.readBound = 0

theorem ReadFreeOf.app2 {a b s : Srt} (o : Op2 C a b s) {x : LTm C a} {y : LTm C b}
    (hx : ReadFreeOf x) (hy : ReadFreeOf y)
    (h : ∀ ex ey, ReadExpr.ofTerm? x = some ex → ReadExpr.ofTerm? y = some ey →
      ∃ e, ReadExpr.ofTerm? (LTm.app2 o x y) = some e ∧ e.readBound = ex.readBound + ey.readBound) :
    ReadFreeOf (LTm.app2 o x y) := by
  obtain ⟨ex, hex, hx0⟩ := hx
  obtain ⟨ey, hey, hy0⟩ := hy
  obtain ⟨e, he, h0⟩ := h ex ey hex hey
  exact ⟨e, he, by rw [h0, hx0, hy0]⟩

theorem LTm.Num.readFree {ps : Parameter → Prop} {es : EnvKey → Prop} :
    ∀ {p : PrimTy} {t : LTm C (.val p)}, t.Num ps es → ReadFreeOf t := by
  intro p t h
  induction h with
  | var k _ => exact ⟨.var k, rfl, rfl⟩
  | @lit p v => exact ⟨.lit v, by cases p <;> rfl, rfl⟩
  | env e _ => exact ⟨.env e, rfl, rfl⟩
  | @neg hp a _ iha | @bnot hp a _ iha =>
    obtain ⟨ea, hea, ha0⟩ := iha
    exact ⟨.unop _ hp ea, by change (ReadExpr.ofTerm? a).map (ReadExpr.unop _ hp) = _; rw [hea]; rfl, ha0⟩
  | @add p hp a b _ _ iha ihb =>
    obtain ⟨ea, hea, ha0⟩ := iha
    obtain ⟨eb, heb, hb0⟩ := ihb
    refine ⟨.binop .add hp ea eb, ?_, ?_⟩
    · change (Option.bind (ReadExpr.ofTerm? a) fun x => Option.bind (ReadExpr.ofTerm? b) fun y =>
        some (ReadExpr.binop .add hp x y)) = _
      rw [hea, heb]; rfl
    · change ea.readBound + eb.readBound = 0
      rw [ha0, hb0]
  | @sub p hp a b _ _ iha ihb =>
    obtain ⟨ea, hea, ha0⟩ := iha
    obtain ⟨eb, heb, hb0⟩ := ihb
    refine ⟨.binop .sub hp ea eb, ?_, ?_⟩
    · change (Option.bind (ReadExpr.ofTerm? a) fun x => Option.bind (ReadExpr.ofTerm? b) fun y =>
        some (ReadExpr.binop .sub hp x y)) = _
      rw [hea, heb]; rfl
    · change ea.readBound + eb.readBound = 0
      rw [ha0, hb0]
  | @mulL p hp v b _ ihb =>
    obtain ⟨eb, heb, hb0⟩ := ihb
    refine ⟨.binop .mul hp (.lit v) eb, ?_, ?_⟩
    · change (Option.bind (ReadExpr.ofTerm? (LTm.app0 (C := C) (.lit v))) fun x =>
        Option.bind (ReadExpr.ofTerm? b) fun y => some (ReadExpr.binop .mul hp x y)) = _
      rw [show ReadExpr.ofTerm? (LTm.app0 (C := C) (.lit v)) = some (.lit v) by cases p <;> rfl, heb]
      rfl
    · change (ReadExpr.lit (C := C) v).readBound + eb.readBound = 0
      rw [hb0]; rfl
  | @mulR p hp a v _ iha =>
    obtain ⟨ea, hea, ha0⟩ := iha
    refine ⟨.binop .mul hp ea (.lit v), ?_, ?_⟩
    · change (Option.bind (ReadExpr.ofTerm? a) fun x =>
        Option.bind (ReadExpr.ofTerm? (LTm.app0 (C := C) (.lit v))) fun y =>
          some (ReadExpr.binop .mul hp x y)) = _
      rw [show ReadExpr.ofTerm? (LTm.app0 (C := C) (.lit v)) = some (.lit v) by cases p <;> rfl, hea]
      rfl
    · change ea.readBound + (ReadExpr.lit (C := C) v).readBound = 0
      rw [ha0]; rfl
  | @seq q p d a _ _ ihd iha =>
    obtain ⟨ed, hed, hd0⟩ := ihd
    obtain ⟨ea, hea, ha0⟩ := iha
    refine ⟨.seq ed ea, ?_, ?_⟩
    · change (Option.bind (ReadExpr.ofTerm? d) fun x => Option.bind (ReadExpr.ofTerm? a) fun y =>
        some (ReadExpr.seq x y)) = _
      rw [hed, hea]; rfl
    · change ed.readBound + ea.readBound = 0
      rw [hd0, ha0]
  | err => exact ⟨.err, rfl, rfl⟩

theorem LTm.PathF.readFree {ps : Parameter → Prop} {es : EnvKey → Prop} :
    ∀ {T : Ty} {t : LTm C (.path T)}, t.PathF ps es → ReadFreeOf t := by
  intro T t h
  induction h with
  | root r h => exact ⟨.root r h, rfl, rfl⟩
  | @field s f T h q _ ih =>
    obtain ⟨e, he, h0⟩ := ih
    refine ⟨.field h e, ?_, h0⟩
    change (ReadExpr.ofTerm? q).map (ReadExpr.field h) = _
    rw [he]; rfl
  | @key K V q k _ hk ih =>
    obtain ⟨e, he, h0⟩ := ih
    obtain ⟨ek, hek, hk0⟩ := hk.readFree
    refine ⟨.index e ek, ?_, ?_⟩
    · change (Option.bind (ReadExpr.ofTerm? q) fun x => Option.bind (ReadExpr.ofTerm? k) fun y =>
        some (ReadExpr.index x y)) = _
      rw [he, hek]; rfl
    · change e.readBound + ek.readBound = 0
      rw [h0, hk0]

/-! ## Paths: segments, views and guards -/

theorem TSegs.toLTm_append {S U W : Ty} (p : TSegs C S U) (q : TSegs C U W) :
    ∀ acc : LTm C (.path S), (p.append q).toLTm acc = q.toLTm (p.toLTm acc) := by
  induction p with
  | nil => intro acc; rfl
  | field h p ih => intro acc; exact ih q _
  | «at» i p ih => intro acc; exact ih q _
  | atF i p ih => intro acc; exact ih q _
  | key i p ih => intro acc; exact ih q _

/-- Segments of fields and mapping keys, each key satisfying `K`. -/
inductive TSegs.FK (K : {k : PrimTy} → LTm C (.val k) → Prop) : {T U : Ty} → TSegs C T U → Prop
  | nil {T : Ty} : TSegs.FK K (.nil : TSegs C T T)
  | field {s f : Name} {T U : Ty} (h : lookupBy f (structDef s) = some T) {r : TSegs C T U} :
      TSegs.FK K r → TSegs.FK K (.field h r)
  | key {k : PrimTy} {V U : Ty} {i : LTm C (.val k)} {r : TSegs C V U} :
      K i → TSegs.FK K r → TSegs.FK K (.key i r)

theorem TSegs.FK.append {K : {k : PrimTy} → LTm C (.val k) → Prop} {S U W : Ty}
    {p : TSegs C S U} {q : TSegs C U W} (hp : p.FK K) (hq : q.FK K) : (p.append q).FK K := by
  induction hp with
  | nil => exact hq
  | field h _ ih => exact .field h (ih hq)
  | key hi _ ih => exact .key hi (ih hq)

theorem TSegs.FK.mono {K K' : {k : PrimTy} → LTm C (.val k) → Prop}
    (hK : ∀ {k : PrimTy} (i : LTm C (.val k)), K i → K' i) {S U : Ty} {p : TSegs C S U}
    (hp : p.FK K) : p.FK K' := by
  induction hp with
  | nil => exact .nil
  | field h _ ih => exact .field h ih
  | key hi _ ih => exact .key (hK _ hi) ih

/-- The number of segments. -/
def TSegs.len {T U : Ty} : TSegs C T U → Nat
  | .nil => 0
  | .field _ r | .at _ r | .atF _ r | .key _ r => r.len + 1

theorem TSegs.len_append {S U W : Ty} (p : TSegs C S U) (q : TSegs C U W) :
    (p.append q).len = p.len + q.len := by
  induction p with
  | nil => simp only [TSegs.len, Nat.zero_add]; rfl
  | field h p ih | «at» i p ih | atF i p ih | key i p ih =>
    show (p.append q).len + 1 = _
    rw [ih q]
    simp only [TSegs.len]
    omega

theorem TSegs.len_le_toLTm {S T : Ty} (p : TSegs C S T) :
    ∀ acc : LTm C (.path S), p.len + acc.depth ≤ (p.toLTm acc).depth := by
  induction p with
  | nil => intro acc; simp only [TSegs.len, Nat.zero_add]; exact Nat.le_refl _
  | field h p ih =>
    intro acc
    have := ih (.app1 (.field h) acc)
    simp only [TSegs.len, LTm.depth] at this ⊢
    exact Nat.le_trans (by omega) this
  | «at» i p ih =>
    intro acc
    have := ih (.index (.arr .dyn) acc i)
    simp only [TSegs.len, LTm.depth] at this ⊢
    exact Nat.le_trans (by omega) this
  | atF i p ih =>
    intro acc
    have := ih (.index (.arr .fixed) acc i)
    simp only [TSegs.len, LTm.depth] at this ⊢
    exact Nat.le_trans (by omega) this
  | key i p ih =>
    intro acc
    have := ih (.index .map acc i)
    simp only [TSegs.len, LTm.depth] at this ⊢
    exact Nat.le_trans (by omega) this

/-- **A flattened path's view**: the closer's path, with the same term, its
segments fields and keys. -/
theorem SPath.viewFuel?_PathF {ps : Parameter → Prop} {es : EnvKey → Prop} :
    ∀ {T : Ty} {t : LTm C (.path T)}, t.PathF ps es → ∀ n, t.depth < n →
      ∃ v, SPath.viewFuel? n t = some v ∧ v.path.toLTm = t ∧
        v.path.segs.FK (fun i => i.Num ps es ∧ i.depth < t.depth) := by
  intro T t h
  induction h with
  | root r h =>
    intro n hn
    obtain ⟨n, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by simp only [LTm.depth] at hn; omega⟩
    exact ⟨_, rfl, rfl, .nil⟩
  | @field s f T h q _ ih =>
    intro n hn
    obtain ⟨n, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by simp only [LTm.depth] at hn; omega⟩
    simp only [LTm.depth] at hn
    obtain ⟨v, hv, ht, hf⟩ := ih n (by omega)
    refine ⟨_, by show Option.bind (SPath.viewFuel? n q) _ = _; rw [hv]; rfl, ?_, ?_⟩
    · show (v.path.segs.append (.field h .nil)).toLTm (.app0 (.root v.path.r v.path.hr)) = _
      rw [TSegs.toLTm_append]
      show LTm.app1 (.field h) v.path.toLTm = _
      rw [ht]
    · exact (hf.mono fun i hi => ⟨hi.1, by simp only [LTm.depth]; omega⟩).append (.field h .nil)
  | @key K V q k _ hk ih =>
    intro n hn
    obtain ⟨n, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by simp only [LTm.depth] at hn; omega⟩
    simp only [LTm.depth] at hn
    obtain ⟨v, hv, ht, hf⟩ := ih n (by omega)
    refine ⟨_, by show Option.bind (SPath.viewFuel? n q) _ = _; rw [hv]; rfl, ?_, ?_⟩
    · show (v.path.segs.append (.key k .nil)).toLTm (.app0 (.root v.path.r v.path.hr)) = _
      rw [TSegs.toLTm_append]
      show LTm.index .map v.path.toLTm k = _
      rw [ht]
    · exact (hf.mono fun i hi => ⟨hi.1, by simp only [LTm.depth]; omega⟩).append
        (.key ⟨hk, by simp only [LTm.depth]; omega⟩ .nil)

theorem TSegs.atomBound_le_toLTm {S T : Ty} (p : TSegs C S T) :
    ∀ acc : LTm C (.path S), acc.atomBound ≤ (p.toLTm acc).atomBound := by
  induction p with
  | nil => intro acc; exact Nat.le_refl _
  | field h p ih => intro acc; exact Nat.le_trans (Nat.le_refl _) (ih (.app1 (.field h) acc))
  | «at» i p ih => intro acc; exact Nat.le_trans (Nat.le_max_left _ _) (ih (.index (.arr .dyn) acc i))
  | atF i p ih => intro acc; exact Nat.le_trans (Nat.le_max_left _ _) (ih (.index (.arr .fixed) acc i))
  | key i p ih => intro acc; exact Nat.le_trans (Nat.le_max_left _ _) (ih (.index .map acc i))

/-- **A path's guard**: the test of its keys, scalar. -/
theorem TSegs.guardFuel?_FK {ps : Parameter → Prop} {es : EnvKey → Prop}
    {K : {k : PrimTy} → LTm C (.val k) → Prop} (hK : ∀ {k : PrimTy} (i : LTm C (.val k)), K i → i.Num ps es) :
    ∀ {T U : Ty} {p : TSegs C T U}, p.FK K → ∀ n, p.len < n →
      ∃ g, TSegs.guardFuel? n p = some g ∧ g.test.Num ps es ∧
        ∀ acc : LTm C (.path T), g.test.nodes + acc.nodes ≤ (p.toLTm acc).nodes + 1 ∧
          g.test.atomBound ≤ (p.toLTm acc).atomBound := by
  intro T U p h
  induction h with
  | nil =>
    intro n hn
    obtain ⟨n, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by omega⟩
    refine ⟨_, rfl, .lit (p := .bool) true, fun acc => ⟨?_, Nat.zero_le _⟩⟩
    show 1 + acc.nodes ≤ acc.nodes + 1
    omega
  | @field s f T U h r _ ih =>
    intro n hn
    obtain ⟨n, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by omega⟩
    simp only [TSegs.len] at hn
    obtain ⟨g, hg, hn', hb⟩ := ih n (by omega)
    refine ⟨_, by show Option.bind (TSegs.guardFuel? n r) _ = _; rw [hg]; rfl, hn', fun acc => ?_⟩
    obtain ⟨h1, h2⟩ := hb (.app1 (.field h) acc)
    refine ⟨?_, h2⟩
    show g.test.nodes + acc.nodes ≤ (r.toLTm (.app1 (.field h) acc)).nodes + 1
    simp only [LTm.nodes] at h1
    omega
  | @key k V U i r hi _ ih =>
    intro n hn
    obtain ⟨n, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by omega⟩
    simp only [TSegs.len] at hn
    obtain ⟨g, hg, hn', hb⟩ := ih n (by omega)
    refine ⟨_, by show Option.bind (TSegs.guardFuel? n r) _ = _; rw [hg]; rfl, .seq (hK _ hi) hn',
      fun acc => ?_⟩
    obtain ⟨h1, h2⟩ := hb (.index .map acc i)
    have ha : i.atomBound ≤ (r.toLTm (.index .map acc i)).atomBound :=
      Nat.le_trans (Nat.le_max_right _ _) (TSegs.atomBound_le_toLTm r (.index .map acc i))
    refine ⟨?_, ?_⟩
    · show (LTm.seq i g.test).nodes + acc.nodes ≤ (r.toLTm (.index .map acc i)).nodes + 1
      simp only [LTm.nodes] at h1 ⊢
      omega
    · show max i.atomBound g.test.atomBound ≤ (r.toLTm (.index .map acc i)).atomBound
      omega

/-! ## Occurrence layouts -/

theorem readFree?_isSome {s : Srt} {t : LTm C s} (h : ReadFreeOf t) : (readFree? t).isSome = true := by
  obtain ⟨e, he, h0⟩ := h
  simp only [readFree?, he, Option.bind_eq_bind, Option.bind_some, h0, dif_pos]
  rfl

/-- The checks `occurrenceLayout?` makes, as a property. -/
inductive Laid : List (ReadOccurrence C) → Nat → Prop
  | nil (start : Nat) : Laid [] start
  | cons {r : ReadOccurrence C} {rs : List (ReadOccurrence C)} {start : Nat}
      (slot : r.slot = start) (bound : r.path.toLTm.atomBound ≤ start)
      (free : ReadFreeOf r.path.toLTm) : Laid rs (start + 1) → Laid (r :: rs) start

theorem Laid.append {a b : List (ReadOccurrence C)} {start : Nat} (ha : Laid a start)
    (hb : Laid b (start + a.length)) : Laid (a ++ b) start := by
  induction ha with
  | nil => simpa only [List.nil_append, List.length_nil, Nat.add_zero] using hb
  | cons hs hbd hf _ ih =>
    refine .cons hs hbd hf (ih ?_)
    simpa only [List.length_cons, Nat.add_assoc, Nat.add_comm 1] using hb

theorem occurrenceLayout?_isSome : ∀ (fuel : Nat) {rs : List (ReadOccurrence C)} {start : Nat},
    Laid rs start → rs.length ≤ fuel → (occurrenceLayout? fuel rs start).isSome = true
  | 0, _, _, .nil _, _ => rfl
  | _ + 1, _, _, .nil _, _ => rfl
  | 0, _ :: _, _, .cons .., h => by simp only [List.length_cons] at h; omega
  | fuel + 1, r :: rs, start, .cons hs hb hf tail, h => by
    obtain ⟨q, hq⟩ := Option.isSome_iff_exists.mp (readFree?_isSome hf)
    obtain ⟨l, hl⟩ := Option.isSome_iff_exists.mp
      (occurrenceLayout?_isSome fuel tail (by simp only [List.length_cons] at h; omega))
    simp only [occurrenceLayout?, hs, hb, dif_pos, hq, hl, Option.bind_eq_bind, Option.bind_some]
    rfl

/-! ## The source fragment -/

/-- Where the ledger may be read: nowhere (the M4 fragment), at addresses
(before the ledger cut), at constants (after it). -/
inductive LedgerMode where
  | none | pre | post
  deriving DecidableEq

/-- The three kinds of source term: a scalar, a Boolean, a path. -/
inductive SrcKind where
  | num | bool | path
  /-- A KeY `int` (`Srt.kint`). -/
  | znum

/-- **The source leaf's terms** the flattener and the compilers accept:
`LTm.Num`/`LTm.BoolV` with storage reads (`obsW`) of root/field/mapping-key
paths whose keys are scalars. -/
inductive LTm.SrcL (c : Bool) (w : Bool) (l : LedgerMode) : SrcKind → {s : Srt} → LTm C s → Prop
  | var {p : PrimTy} (k : Nat) : LTm.SrcL c w l .num (.var (p := p) k)
  | lit {p : PrimTy} (v : p.Denote) : LTm.SrcL c w l .num (.app0 (.lit v))
  | env (e : EnvKey) : LTm.SrcL c w l .num (.app0 (.env e))
  | add {p : PrimTy} (h : BinOp.add.accepts p = true) {a b : LTm C (.val p)} :
      LTm.SrcL c w l .num a → LTm.SrcL c w l .num b → LTm.SrcL c w l .num (.app2 (.binop .add h) a b)
  | sub {p : PrimTy} (h : BinOp.sub.accepts p = true) {a b : LTm C (.val p)} :
      LTm.SrcL c w l .num a → LTm.SrcL c w l .num b → LTm.SrcL c w l .num (.app2 (.binop .sub h) a b)
  | mulL {p : PrimTy} (h : BinOp.mul.accepts p = true) (v : p.Denote) {b : LTm C (.val p)} :
      LTm.SrcL c w l .num b → LTm.SrcL c w l .num (.app2 (.binop .mul h) (.app0 (.lit v)) b)
  | mulR {p : PrimTy} (h : BinOp.mul.accepts p = true) {a : LTm C (.val p)} (v : p.Denote) :
      LTm.SrcL c w l .num a → LTm.SrcL c w l .num (.app2 (.binop .mul h) a (.app0 (.lit v)))
  | neg (h : UnOp.neg.accepts .int = true) {a : LTm C (.val .int)} :
      LTm.SrcL c w l .num a → LTm.SrcL c w l .num (.app1 (.unop .neg h) a)
  | bnot (h : UnOp.bnot.accepts .uint = true) {a : LTm C (.val .uint)} :
      LTm.SrcL c w l .num a → LTm.SrcL c w l .num (.app1 (.unop .bnot h) a)
  /-- The operators cut into fresh atoms (`Calculus/QuotientCut.lean`), before the cut. -/
  | toInt (hw : w = true) (h : UnOp.toInt.accepts .uint = true) {a : LTm C (.val .uint)} :
      LTm.SrcL c w l .num a → LTm.SrcL c w l .num (.app1 (.unop .toInt h) a)
  | toUint (hw : w = true) (h : UnOp.toUint.accepts .int = true) {a : LTm C (.val .int)} :
      LTm.SrcL c w l .num a → LTm.SrcL c w l .num (.app1 (.unop .toUint h) a)
  | divL (hw : w = true) (h : BinOp.div.accepts .uint = true) {a : LTm C (.val .uint)}
      (v : PrimTy.uint.Denote) (hv : v.val ≠ 0) :
      LTm.SrcL c w l .num a → LTm.SrcL c w l .num (.app2 (.binop .div h) a (.app0 (.lit v)))
  | modL (hw : w = true) (h : BinOp.mod.accepts .uint = true) {a : LTm C (.val .uint)}
      (v : PrimTy.uint.Denote) (hv : v.val ≠ 0) :
      LTm.SrcL c w l .num a → LTm.SrcL c w l .num (.app2 (.binop .mod h) a (.app0 (.lit v)))
  | shrL (hw : w = true) {p : PrimTy} (h : BinOp.shr.accepts p = true) {a : LTm C (.val p)}
      (v : p.Denote) : LTm.SrcL c w l .num a → LTm.SrcL c w l .num (.app2 (.binop .shr h) a (.app0 (.lit v)))
  | shlL (hw : w = true) (h : BinOp.shl.accepts .uint = true) {a : LTm C (.val .uint)}
      (v : PrimTy.uint.Denote) :
      LTm.SrcL c w l .num a → LTm.SrcL c w l .num (.app2 (.binop .shl h) a (.app0 (.lit v)))
  | bandR (hw : w = true) (h : BinOp.band.accepts .uint = true) {a : LTm C (.val .uint)}
      (v : PrimTy.uint.Denote) (hv : (lowMask? v).isSome = true) :
      LTm.SrcL c w l .num a → LTm.SrcL c w l .num (.app2 (.binop .band h) a (.app0 (.lit v)))
  | bandL (hw : w = true) (h : BinOp.band.accepts .uint = true) (v : PrimTy.uint.Denote)
      (hv : (lowMask? v).isSome = true) {b : LTm C (.val .uint)} :
      LTm.SrcL c w l .num b → LTm.SrcL c w l .num (.app2 (.binop .band h) (.app0 (.lit v)) b)
  | addW (hw : w = true) (h : BinOp.addW.accepts .uint = true) {a b : LTm C (.val .uint)} :
      LTm.SrcL c w l .num a → LTm.SrcL c w l .num b → LTm.SrcL c w l .num (.app2 (.binop .addW h) a b)
  | subW (hw : w = true) (h : BinOp.subW.accepts .uint = true) {a b : LTm C (.val .uint)} :
      LTm.SrcL c w l .num a → LTm.SrcL c w l .num b → LTm.SrcL c w l .num (.app2 (.binop .subW h) a b)
  /-- The operators the cut writes through the others, with a literal operand. -/
  | litR (hw : w = true) {p : PrimTy} (op : BinOp) (h : op.accepts p = true) {a : LTm C (.val p)}
      (v : p.Denote) (hv : litCutR op p v = true) :
      LTm.SrcL c w l .num a → LTm.SrcL c w l .num (.app2 (.binop op h) a (.app0 (.lit v)))
  | litL (hw : w = true) {p : PrimTy} (op : BinOp) (h : op.accepts p = true) (v : p.Denote)
      (hv : litCutL op p = true) {b : LTm C (.val p)} :
      LTm.SrcL c w l .num b → LTm.SrcL c w l .num (.app2 (.binop op h) (.app0 (.lit v)) b)
  | seq {q p : PrimTy} {d : LTm C (.val q)} {a : LTm C (.val p)} :
      LTm.SrcL c w l .num d → LTm.SrcL c w l .num a → LTm.SrcL c w l .num (.seq d a)
  | err {p : PrimTy} : LTm.SrcL c w l .num (LTm.err (C := C) (s := .val p))
  | word {p : PrimTy} {q : LTm C (.path (.prim p))} : LTm.SrcL c w l .path q → LTm.SrcL c w l .num (.obsW q)
  | ofNum {t : LTm C (.val .bool)} : LTm.SrcL c w l .num t → LTm.SrcL c w l .bool t
  | not {a : LTm C (.val .bool)} : LTm.SrcL c w l .bool a → LTm.SrcL c w l .bool (.app1 (.unop .not rfl) a)
  | and {a b : LTm C (.val .bool)} : LTm.SrcL c w l .bool a → LTm.SrcL c w l .bool b →
      LTm.SrcL c w l .bool (.app2 (.binop .and rfl) a b)
  | or {a b : LTm C (.val .bool)} : LTm.SrcL c w l .bool a → LTm.SrcL c w l .bool b →
      LTm.SrcL c w l .bool (.app2 (.binop .or rfl) a b)
  | eqB {a b : LTm C (.val .bool)} : LTm.SrcL c w l .bool a → LTm.SrcL c w l .bool b →
      LTm.SrcL c w l .bool (.app2 (.binop .eqB rfl) a b)
  | neB {a b : LTm C (.val .bool)} : LTm.SrcL c w l .bool a → LTm.SrcL c w l .bool b →
      LTm.SrcL c w l .bool (.app2 (.binop .neB rfl) a b)
  | eqN {p : PrimTy} (hp : p.isNumeric = true) {a b : LTm C (.val p)} :
      LTm.SrcL c w l .num a → LTm.SrcL c w l .num b → LTm.SrcL c w l .bool (.app2 (.binop .eqB rfl) a b)
  | neN {p : PrimTy} (hp : p.isNumeric = true) {a b : LTm C (.val p)} :
      LTm.SrcL c w l .num a → LTm.SrcL c w l .num b → LTm.SrcL c w l .bool (.app2 (.binop .neB rfl) a b)
  | lt {p : PrimTy} (h : BinOp.lt.accepts p = true) {a b : LTm C (.val p)} :
      LTm.SrcL c w l .num a → LTm.SrcL c w l .num b → LTm.SrcL c w l .bool (.app2 (.binop .lt h) a b)
  | gt {p : PrimTy} (h : BinOp.gt.accepts p = true) {a b : LTm C (.val p)} :
      LTm.SrcL c w l .num a → LTm.SrcL c w l .num b → LTm.SrcL c w l .bool (.app2 (.binop .gt h) a b)
  | le {p : PrimTy} (h : BinOp.le.accepts p = true) {a b : LTm C (.val p)} :
      LTm.SrcL c w l .num a → LTm.SrcL c w l .num b → LTm.SrcL c w l .bool (.app2 (.binop .le h) a b)
  | ge {p : PrimTy} (h : BinOp.ge.accepts p = true) {a b : LTm C (.val p)} :
      LTm.SrcL c w l .num a → LTm.SrcL c w l .num b → LTm.SrcL c w l .bool (.app2 (.binop .ge h) a b)
  | seqB {d a : LTm C (.val .bool)} : LTm.SrcL c w l .bool d → LTm.SrcL c w l .bool a →
      LTm.SrcL c w l .bool (.seq d a)
  | seqN {q : PrimTy} (hq : q.isNumeric = true) {d : LTm C (.val q)} {a : LTm C (.val .bool)} :
      LTm.SrcL c w l .num d → LTm.SrcL c w l .bool a → LTm.SrcL c w l .bool (.seq d a)
  | root (r : Name) {T : Ty} (h : C.rootType r = some T) : LTm.SrcL c w l .path (.app0 (.root r h))
  | field {s f : Name} {T : Ty} (h : C.fieldType s f = some T) {q : LTm C (.path (.ref (.struct s)))} :
      LTm.SrcL c w l .path q → LTm.SrcL c w l .path (.app1 (.field h) q)
  | key {K : PrimTy} {V : Ty} {q : LTm C (.path (.ref (.mapping K V)))} {k : LTm C (.val K)} :
      LTm.SrcL c w l .path q → LTm.SrcL c w l .num k → LTm.SrcL c w l .path (.index .map q k)
  | kite (hc : c = true) {p q : PrimTy} {k : SrcKind} (hk : k ≠ .path) {x y : LTm C (.val p)}
      {t e : LTm C (.val q)} : LTm.SrcL c w l .num x → LTm.SrcL c w l .num y → LTm.SrcL c w l k t →
      LTm.SrcL c w l k e → LTm.SrcL c w l k (.kite x y t e)
  | ite (hc : c = true) {p : PrimTy} {k : SrcKind} (hk : k ≠ .path) {d : LTm C (.val .bool)}
      {t e : LTm C (.val p)} : LTm.SrcL c w l .bool d → LTm.SrcL c w l k t → LTm.SrcL c w l k e →
      LTm.SrcL c w l k (.app3 .ite d t e)
  /-- KeY `int` (`Srt.kint`, M7 step 3): a literal, a `uint` widened
  (`toInt`), `+`, `-`, a product by a literal, and the comparisons. -/
  | zlit (n : Int) : LTm.SrcL c w l .znum (.app0 (.zlit n))
  | zint {a : LTm C (.val .uint)} : LTm.SrcL c w l .num a → LTm.SrcL c w l .znum (.app1 .toInt a)
  | zadd (h : BinOp.add.zArith = true) {a b : LTm C .kint} :
      LTm.SrcL c w l .znum a → LTm.SrcL c w l .znum b → LTm.SrcL c w l .znum (.app2 (.zbin .add h) a b)
  | zsub (h : BinOp.sub.zArith = true) {a b : LTm C .kint} :
      LTm.SrcL c w l .znum a → LTm.SrcL c w l .znum b → LTm.SrcL c w l .znum (.app2 (.zbin .sub h) a b)
  | zmulL (h : BinOp.mul.zArith = true) (n : Int) {b : LTm C .kint} :
      LTm.SrcL c w l .znum b → LTm.SrcL c w l .znum (.app2 (.zbin .mul h) (.app0 (.zlit n)) b)
  | zmulR (h : BinOp.mul.zArith = true) {a : LTm C .kint} (n : Int) :
      LTm.SrcL c w l .znum a → LTm.SrcL c w l .znum (.app2 (.zbin .mul h) a (.app0 (.zlit n)))
  | zcmp (op : BinOp) (h : op.zCmp = true) {a b : LTm C .kint} :
      LTm.SrcL c w l .znum a → LTm.SrcL c w l .znum b → LTm.SrcL c w l .bool (.app2 (.zcmp op h) a b)
  /-- A ledger read (`net(a)`, its address a scalar), before the ledger cut
  (`Calculus/LedgerCut.lean`). -/
  | znet (hl : l = .pre) {a : LTm C (.val .uint)} :
      LTm.SrcL c w l .num a → LTm.SrcL c w l .znum (.app1 .net a)
  /-- A ledger read at a constant, after it, and the address guarding it. -/
  | znetLit (hl : l = .post) (v : PrimTy.uint.Denote) :
      LTm.SrcL c w l .znum (.app1 .net (.app0 (.lit v)))
  | zseq (hl : l = .post) {q : PrimTy} {d : LTm C (.val q)} {a : LTm C .kint} :
      LTm.SrcL c w l .num d → LTm.SrcL c w l .znum a → LTm.SrcL c w l .znum (.seq d a)

/-- The source fragment without ledger reads. -/
abbrev LTm.Src (c w : Bool) : SrcKind → {s : Srt} → LTm C s → Prop := LTm.SrcL c w .none

/-- What the flattened term of a source kind is. -/
def FlatOK (l : LedgerMode) : SrcKind → (s : Srt) → LTm C s → Prop
  | .num, .val _, t => t.Num (fun _ => True) (fun _ => True)
  | .bool, .val .bool, t => t.BoolV (fun _ => True) (fun _ => True) (fun _ => l = .post)
  | .path, .path _, t => t.PathF (fun _ => True) (fun _ => True)
  | .znum, .kint, t => t.ZNum (fun _ => True) (fun _ => True) (fun _ => l = .post)
  | _, _, _ => False

/-- An occurrence whose guard and path keys the compilers accept. -/
def OccOK (r : ReadOccurrence C) : Prop :=
  r.guard.test.Num (fun _ => True) (fun _ => True) ∧ r.guard.test.depth ≤ 1022 ∧
    r.path.segs.FK (fun i => i.Num (fun _ => True) (fun _ => True) ∧ i.depth ≤ 1022)

/-- What flattening a source term returns. -/
def FlatGood (l : LedgerMode) {s : Srt} (k : SrcKind) (t : LTm C s) (start : Nat)
    (a : Flattened t start) : Prop :=
  FlatOK l k s a.term ∧ a.reads.length = t.words ∧ Laid a.reads start ∧
    a.term.atomBound ≤ a.next ∧ a.term.nodes ≤ 2 * t.nodes ∧ ∀ o ∈ a.reads, OccOK o


theorem flattenFuel?_lit {p : PrimTy} (v : p.Denote) (d r start : Nat) :
    flattenFuel? (C := C) (d + 1) (r + 1) (LTm.app0 (.lit v)) start =
      some (Flattened.pure (LTm.app0 (.lit v)) start, r) := by
  cases p <;> rfl

theorem flattenFuel?_zlit (n : Int) (d r start : Nat) :
    flattenFuel? (C := C) (d + 1) (r + 1) (LTm.app0 (.zlit n)) start =
      some (Flattened.pure (LTm.app0 (.zlit n)) start, r) := rfl

/-- **Flattening never refuses a source term**: under a node budget, with its
atoms below `start`, it returns a flattened term of the compilers' fragment,
one laid-out occurrence per storage read. -/
theorem flattenFuel?_Src {l : LedgerMode} (hpre : l ≠ .pre) :
    ∀ {k : SrcKind} {s : Srt} {t : LTm C s}, t.SrcL false false l k →
    ∀ (d r start : Nat), t.depth ≤ d → t.nodes ≤ r → t.atomBound ≤ start → t.nodes ≤ 511 →
      ∃ a, flattenFuel? d r t start = some (a, r - t.nodes) ∧ FlatGood l k t start a := by
  intro k s t h
  induction h with
  | znet hl => exact absurd hl hpre
  | kite hc => cases hc
  | ite hc => cases hc
  | toInt hw | toUint hw | divL hw | modL hw | shrL hw | shlL hw | addW hw | subW hw | bandR hw
    | bandL hw | litR hw | litL hw => cases hw
  | @var p k =>
    intro d r start hd hr hb hs
    obtain ⟨d, rfl⟩ : ∃ m, d = m + 1 := ⟨d - 1, by simp only [LTm.depth] at hd; omega⟩
    obtain ⟨r, rfl⟩ : ∃ m, r = m + 1 := ⟨r - 1, by simp only [LTm.nodes] at hr; omega⟩
    refine ⟨Flattened.pure (LTm.var (C := C) (p := p) k) start, ?_, .var k trivial, rfl, .nil start, ?_, ?_, fun _ h => by cases h⟩
    · show some (Flattened.pure (LTm.var (C := C) (p := p) k) start, r) = _
      simp only [LTm.nodes, Nat.add_sub_cancel]
    · show (LTm.var (C := C) (p := p) k).atomBound ≤ start + 0
      exact hb
    · show (LTm.var (C := C) (p := p) k).nodes ≤ 2 * (LTm.var (C := C) (p := p) k).nodes
      omega
  | @lit p v =>
    intro d r start hd hr hb hs
    obtain ⟨d, rfl⟩ : ∃ m, d = m + 1 := ⟨d - 1, by simp only [LTm.depth] at hd; omega⟩
    obtain ⟨r, rfl⟩ : ∃ m, r = m + 1 := ⟨r - 1, by simp only [LTm.nodes] at hr; omega⟩
    refine ⟨Flattened.pure (LTm.app0 (C := C) (.lit v)) start, ?_, .lit v, rfl, .nil start, ?_, ?_, fun _ h => by cases h⟩
    · cases p <;>
      · show some (Flattened.pure (LTm.app0 (C := C) (.lit _)) start, r) = _
        simp only [LTm.nodes, Nat.add_sub_cancel]
    · show (LTm.app0 (C := C) (.lit v)).atomBound ≤ start + 0
      exact hb
    · show (LTm.app0 (C := C) (.lit v)).nodes ≤ 2 * (LTm.app0 (C := C) (.lit v)).nodes
      omega
  | env e =>
    intro d r start hd hr hb hs
    obtain ⟨d, rfl⟩ : ∃ m, d = m + 1 := ⟨d - 1, by simp only [LTm.depth] at hd; omega⟩
    obtain ⟨r, rfl⟩ : ∃ m, r = m + 1 := ⟨r - 1, by simp only [LTm.nodes] at hr; omega⟩
    refine ⟨Flattened.pure (LTm.app0 (C := C) (.env e)) start, ?_, .env e trivial, rfl, .nil start, ?_, ?_, fun _ h => by cases h⟩
    · show some (Flattened.pure (LTm.app0 (C := C) (.env e)) start, r) = _
      simp only [LTm.nodes, Nat.add_sub_cancel]
    · show (LTm.app0 (C := C) (.env e)).atomBound ≤ start + 0
      exact hb
    · show (LTm.app0 (C := C) (.env e)).nodes ≤ 2 * (LTm.app0 (C := C) (.env e)).nodes
      omega
  | @err p =>
    intro d r start hd hr hb hs
    obtain ⟨d, rfl⟩ : ∃ m, d = m + 1 := ⟨d - 1, by simp only [LTm.depth] at hd; omega⟩
    obtain ⟨r, rfl⟩ : ∃ m, r = m + 1 := ⟨r - 1, by simp only [LTm.nodes] at hr; omega⟩
    refine ⟨Flattened.pure (LTm.err (C := C) (s := .val p)) start, ?_, .err, rfl, .nil start, ?_, ?_, fun _ h => by cases h⟩
    · show some (Flattened.pure (LTm.err (C := C) (s := .val p)) start, r) = _
      simp only [LTm.nodes, Nat.add_sub_cancel]
    · show (LTm.err (C := C) (s := .val p)).atomBound ≤ start + 0
      exact hb
    · show (LTm.err (C := C) (s := .val p)).nodes ≤ 2 * (LTm.err (C := C) (s := .val p)).nodes
      omega
  | root rt hrt =>
    intro d r start hd hr hb hs
    obtain ⟨d, rfl⟩ : ∃ m, d = m + 1 := ⟨d - 1, by simp only [LTm.depth] at hd; omega⟩
    obtain ⟨r, rfl⟩ : ∃ m, r = m + 1 := ⟨r - 1, by simp only [LTm.nodes] at hr; omega⟩
    refine ⟨Flattened.pure (LTm.app0 (C := C) (.root rt hrt)) start, ?_, .root rt hrt, rfl, .nil start, ?_, ?_, fun _ h => by cases h⟩
    · show some (Flattened.pure (LTm.app0 (C := C) (.root rt hrt)) start, r) = _
      simp only [LTm.nodes, Nat.add_sub_cancel]
    · show (LTm.app0 (C := C) (.root rt hrt)).atomBound ≤ start + 0
      exact hb
    · show (LTm.app0 (C := C) (.root rt hrt)).nodes ≤ 2 * (LTm.app0 (C := C) (.root rt hrt)).nodes
      omega
  | @field sn f T h q _ ih =>
    intro d r start hd hr hb hs
    obtain ⟨d, rfl⟩ : ∃ m, d = m + 1 := ⟨d - 1, by simp only [LTm.depth] at hd; omega⟩
    obtain ⟨r, rfl⟩ : ∃ m, r = m + 1 := ⟨r - 1, by simp only [LTm.nodes] at hr; omega⟩
    simp only [LTm.depth, LTm.nodes, LTm.atomBound] at hd hr hb hs
    obtain ⟨a, ha, aok, alen, alaid, aab, an, aocc⟩ := ih d r start (by omega) (by omega) hb (by omega)
    refine ⟨Flattened.app1 (.field h) a, ?_, LTm.PathF.field h aok, alen, alaid, aab, ?_, aocc⟩
    · show Option.bind (flattenFuel? (C := C) d r q start) _ = _
      rw [ha]
      show some (Flattened.app1 (.field h) a, r - q.nodes) = _
      simp only [LTm.nodes, Option.some.injEq, Prod.mk.injEq, true_and]
      omega
    · show a.term.nodes + 1 ≤ 2 * (q.nodes + 1)
      omega
  | @not x _ ih =>
    intro d r start hd hr hb hs
    obtain ⟨d, rfl⟩ : ∃ m, d = m + 1 := ⟨d - 1, by simp only [LTm.depth] at hd; omega⟩
    obtain ⟨r, rfl⟩ : ∃ m, r = m + 1 := ⟨r - 1, by simp only [LTm.nodes] at hr; omega⟩
    simp only [LTm.depth, LTm.nodes, LTm.atomBound] at hd hr hb hs
    obtain ⟨a, ha, aok, alen, alaid, aab, an, aocc⟩ := ih d r start (by omega) (by omega) hb (by omega)
    refine ⟨Flattened.app1 (Op1.unop UnOp.not (p := .bool) rfl) a, ?_, LTm.BoolV.not aok, alen, alaid, aab, ?_, aocc⟩
    · show Option.bind (flattenFuel? (C := C) d r x start) _ = _
      rw [ha]
      show some (Flattened.app1 (Op1.unop UnOp.not (p := .bool) rfl) a, r - x.nodes) = _
      simp only [LTm.nodes, Option.some.injEq, Prod.mk.injEq, true_and]
      omega
    · show a.term.nodes + 1 ≤ 2 * (x.nodes + 1)
      omega
  | @neg h x _ ih =>
    intro d r start hd hr hb hs
    obtain ⟨d, rfl⟩ : ∃ m, d = m + 1 := ⟨d - 1, by simp only [LTm.depth] at hd; omega⟩
    obtain ⟨r, rfl⟩ : ∃ m, r = m + 1 := ⟨r - 1, by simp only [LTm.nodes] at hr; omega⟩
    simp only [LTm.depth, LTm.nodes, LTm.atomBound] at hd hr hb hs
    obtain ⟨a, ha, aok, alen, alaid, aab, an, aocc⟩ := ih d r start (by omega) (by omega) hb (by omega)
    refine ⟨Flattened.app1 (Op1.unop UnOp.neg h) a, ?_, LTm.Num.neg h aok, alen, alaid, aab, ?_, aocc⟩
    · show Option.bind (flattenFuel? (C := C) d r x start) _ = _
      rw [ha]
      show some (Flattened.app1 (Op1.unop UnOp.neg h) a, r - x.nodes) = _
      simp only [LTm.nodes, Option.some.injEq, Prod.mk.injEq, true_and]
      omega
    · show a.term.nodes + 1 ≤ 2 * (x.nodes + 1)
      omega
  | @bnot h x _ ih =>
    intro d r start hd hr hb hs
    obtain ⟨d, rfl⟩ : ∃ m, d = m + 1 := ⟨d - 1, by simp only [LTm.depth] at hd; omega⟩
    obtain ⟨r, rfl⟩ : ∃ m, r = m + 1 := ⟨r - 1, by simp only [LTm.nodes] at hr; omega⟩
    simp only [LTm.depth, LTm.nodes, LTm.atomBound] at hd hr hb hs
    obtain ⟨a, ha, aok, alen, alaid, aab, an, aocc⟩ := ih d r start (by omega) (by omega) hb (by omega)
    refine ⟨Flattened.app1 (Op1.unop UnOp.bnot h) a, ?_, LTm.Num.bnot h aok, alen, alaid, aab, ?_, aocc⟩
    · show Option.bind (flattenFuel? (C := C) d r x start) _ = _
      rw [ha]
      show some (Flattened.app1 (Op1.unop UnOp.bnot h) a, r - x.nodes) = _
      simp only [LTm.nodes, Option.some.injEq, Prod.mk.injEq, true_and]
      omega
    · show a.term.nodes + 1 ≤ 2 * (x.nodes + 1)
      omega
  | @add p h x y _ _ ihx ihy =>
    intro d r start hd hr hb hs
    obtain ⟨d, rfl⟩ : ∃ m, d = m + 1 := ⟨d - 1, by simp only [LTm.depth] at hd; omega⟩
    obtain ⟨r, rfl⟩ : ∃ m, r = m + 1 := ⟨r - 1, by simp only [LTm.nodes] at hr; omega⟩
    simp only [LTm.depth, LTm.nodes, LTm.atomBound] at hd hr hb hs
    obtain ⟨a, ha, aok, alen, alaid, aab, an, aocc⟩ := ihx d r start (by omega) (by omega) (by omega) (by omega)
    obtain ⟨b, hb', bok, blen, blaid, bab, bn, bocc⟩ := ihy d (r - x.nodes) a.next (by omega) (by omega)
      (by simp only [Flattened.next]; omega) (by omega)
    refine ⟨Flattened.app2 (.binop .add h) a b, ?_, LTm.Num.add h aok bok, ?_, alaid.append blaid, ?_, ?_,
      fun o ho => (List.mem_append.mp ho).elim (aocc o) (bocc o)⟩
    · show Option.bind (flattenFuel? (C := C) d r x start) _ = _
      rw [ha]
      show Option.bind (flattenFuel? (C := C) d (r - x.nodes) y a.next) _ = _
      rw [hb']
      show some (Flattened.app2 (.binop .add h) a b, r - x.nodes - y.nodes) = _
      simp only [LTm.nodes, Option.some.injEq, Prod.mk.injEq, true_and]
      omega
    · show (a.reads ++ b.reads).length = x.words + y.words
      rw [List.length_append, alen, blen]
    · show max a.term.atomBound b.term.atomBound ≤ start + (a.reads ++ b.reads).length
      simp only [Flattened.next] at aab bab
      rw [List.length_append]
      omega
    · show a.term.nodes + b.term.nodes + 1 ≤ 2 * (x.nodes + y.nodes + 1)
      omega
  | @mulL p h v y _ ihy =>
    intro d r start hd hr hb hs
    obtain ⟨d, rfl⟩ : ∃ m, d = m + 1 := ⟨d - 1, by simp only [LTm.depth] at hd; omega⟩
    obtain ⟨r, rfl⟩ : ∃ m, r = m + 1 := ⟨r - 1, by simp only [LTm.nodes] at hr; omega⟩
    simp only [LTm.depth, LTm.nodes, LTm.atomBound] at hd hr hb hs
    obtain ⟨d, rfl⟩ : ∃ m, d = m + 1 := ⟨d - 1, by omega⟩
    obtain ⟨r, rfl⟩ : ∃ m, r = m + 1 := ⟨r - 1, by omega⟩
    let a := Flattened.pure (LTm.app0 (C := C) (.lit v)) start
    obtain ⟨b, hb', bok, blen, blaid, bab, bn, bocc⟩ := ihy (d + 1) r a.next (by omega) (by omega)
      (by show y.atomBound ≤ start + 0; omega) (by omega)
    refine ⟨Flattened.app2 (.binop .mul h) a b, ?_, LTm.Num.mulL h v bok, ?_,
      (Laid.nil start).append blaid, ?_, ?_,
      fun o ho => (List.mem_append.mp ho).elim (fun h => nomatch h) (bocc o)⟩
    · show Option.bind (flattenFuel? (C := C) (d + 1) (r + 1) (LTm.app0 (.lit v)) start) _ = _
      rw [flattenFuel?_lit]
      show Option.bind (flattenFuel? (C := C) (d + 1) r y a.next) _ = _
      rw [hb']
      show some (Flattened.app2 (.binop .mul h) a b, r - y.nodes) = _
      simp only [LTm.nodes, Option.some.injEq, Prod.mk.injEq, true_and]
      omega
    · show ([] ++ b.reads).length = (LTm.app0 (C := C) (.lit v)).words + y.words
      rw [List.nil_append, blen]
      simp only [LTm.words, Nat.zero_add]
    · show max (LTm.app0 (C := C) (.lit v)).atomBound b.term.atomBound ≤ start + ([] ++ b.reads).length
      simp only [Flattened.next] at bab
      simp only [List.nil_append, LTm.atomBound]
      show max 0 b.term.atomBound ≤ start + b.reads.length
      have h0 : a.reads.length = 0 := rfl
      omega
    · show (LTm.app0 (C := C) (.lit v)).nodes + b.term.nodes + 1 ≤ 2 * ((LTm.app0 (C := C) (.lit v)).nodes + y.nodes + 1)
      simp only [LTm.nodes]
      omega
  | @mulR p h x v _ ihx =>
    intro d r start hd hr hb hs
    obtain ⟨d, rfl⟩ : ∃ m, d = m + 1 := ⟨d - 1, by simp only [LTm.depth] at hd; omega⟩
    obtain ⟨r, rfl⟩ : ∃ m, r = m + 1 := ⟨r - 1, by simp only [LTm.nodes] at hr; omega⟩
    simp only [LTm.depth, LTm.nodes, LTm.atomBound] at hd hr hb hs
    obtain ⟨d, rfl⟩ : ∃ m, d = m + 1 := ⟨d - 1, by omega⟩
    obtain ⟨a, ha, aok, alen, alaid, aab, an, aocc⟩ := ihx (d + 1) r start (by omega) (by omega) (by omega) (by omega)
    obtain ⟨k, hk⟩ : ∃ k, r - x.nodes = k + 1 := ⟨r - x.nodes - 1, by omega⟩
    let b := Flattened.pure (LTm.app0 (C := C) (.lit v)) a.next
    refine ⟨Flattened.app2 (.binop .mul h) a b, ?_, LTm.Num.mulR h v aok, ?_,
      alaid.append (Laid.nil _), ?_, ?_,
      fun o ho => (List.mem_append.mp ho).elim (aocc o) (fun h => nomatch h)⟩
    · show Option.bind (flattenFuel? (C := C) (d + 1) r x start) _ = _
      rw [ha]
      show Option.bind (flattenFuel? (C := C) (d + 1) (r - x.nodes) (LTm.app0 (.lit v)) a.next) _ = _
      rw [hk, flattenFuel?_lit]
      show some (Flattened.app2 (.binop .mul h) a b, k) = _
      simp only [LTm.nodes, Option.some.injEq, Prod.mk.injEq, true_and]
      omega
    · show (a.reads ++ []).length = x.words + (LTm.app0 (C := C) (.lit v)).words
      rw [List.append_nil, alen]
      simp only [LTm.words, Nat.add_zero]
    · show max a.term.atomBound (LTm.app0 (C := C) (.lit v)).atomBound ≤ start + (a.reads ++ []).length
      simp only [Flattened.next] at aab
      simp only [List.append_nil, LTm.atomBound]
      omega
    · show a.term.nodes + (LTm.app0 (C := C) (.lit v)).nodes + 1 ≤ 2 * (x.nodes + (LTm.app0 (C := C) (.lit v)).nodes + 1)
      simp only [LTm.nodes]
      omega
  | @sub p h x y _ _ ihx ihy =>
    intro d r start hd hr hb hs
    obtain ⟨d, rfl⟩ : ∃ m, d = m + 1 := ⟨d - 1, by simp only [LTm.depth] at hd; omega⟩
    obtain ⟨r, rfl⟩ : ∃ m, r = m + 1 := ⟨r - 1, by simp only [LTm.nodes] at hr; omega⟩
    simp only [LTm.depth, LTm.nodes, LTm.atomBound] at hd hr hb hs
    obtain ⟨a, ha, aok, alen, alaid, aab, an, aocc⟩ := ihx d r start (by omega) (by omega) (by omega) (by omega)
    obtain ⟨b, hb', bok, blen, blaid, bab, bn, bocc⟩ := ihy d (r - x.nodes) a.next (by omega) (by omega)
      (by simp only [Flattened.next]; omega) (by omega)
    refine ⟨Flattened.app2 (.binop .sub h) a b, ?_, LTm.Num.sub h aok bok, ?_, alaid.append blaid, ?_, ?_,
      fun o ho => (List.mem_append.mp ho).elim (aocc o) (bocc o)⟩
    · show Option.bind (flattenFuel? (C := C) d r x start) _ = _
      rw [ha]
      show Option.bind (flattenFuel? (C := C) d (r - x.nodes) y a.next) _ = _
      rw [hb']
      show some (Flattened.app2 (.binop .sub h) a b, r - x.nodes - y.nodes) = _
      simp only [LTm.nodes, Option.some.injEq, Prod.mk.injEq, true_and]
      omega
    · show (a.reads ++ b.reads).length = x.words + y.words
      rw [List.length_append, alen, blen]
    · show max a.term.atomBound b.term.atomBound ≤ start + (a.reads ++ b.reads).length
      simp only [Flattened.next] at aab bab
      rw [List.length_append]
      omega
    · show a.term.nodes + b.term.nodes + 1 ≤ 2 * (x.nodes + y.nodes + 1)
      omega
  | @and x y _ _ ihx ihy =>
    intro d r start hd hr hb hs
    obtain ⟨d, rfl⟩ : ∃ m, d = m + 1 := ⟨d - 1, by simp only [LTm.depth] at hd; omega⟩
    obtain ⟨r, rfl⟩ : ∃ m, r = m + 1 := ⟨r - 1, by simp only [LTm.nodes] at hr; omega⟩
    simp only [LTm.depth, LTm.nodes, LTm.atomBound] at hd hr hb hs
    obtain ⟨a, ha, aok, alen, alaid, aab, an, aocc⟩ := ihx d r start (by omega) (by omega) (by omega) (by omega)
    obtain ⟨b, hb', bok, blen, blaid, bab, bn, bocc⟩ := ihy d (r - x.nodes) a.next (by omega) (by omega)
      (by simp only [Flattened.next]; omega) (by omega)
    refine ⟨Flattened.app2 (.binop .and rfl) a b, ?_, LTm.BoolV.and aok bok, ?_, alaid.append blaid, ?_, ?_,
      fun o ho => (List.mem_append.mp ho).elim (aocc o) (bocc o)⟩
    · show Option.bind (flattenFuel? (C := C) d r x start) _ = _
      rw [ha]
      show Option.bind (flattenFuel? (C := C) d (r - x.nodes) y a.next) _ = _
      rw [hb']
      show some (Flattened.app2 (.binop .and rfl) a b, r - x.nodes - y.nodes) = _
      simp only [LTm.nodes, Option.some.injEq, Prod.mk.injEq, true_and]
      omega
    · show (a.reads ++ b.reads).length = x.words + y.words
      rw [List.length_append, alen, blen]
    · show max a.term.atomBound b.term.atomBound ≤ start + (a.reads ++ b.reads).length
      simp only [Flattened.next] at aab bab
      rw [List.length_append]
      omega
    · show a.term.nodes + b.term.nodes + 1 ≤ 2 * (x.nodes + y.nodes + 1)
      omega
  | @or x y _ _ ihx ihy =>
    intro d r start hd hr hb hs
    obtain ⟨d, rfl⟩ : ∃ m, d = m + 1 := ⟨d - 1, by simp only [LTm.depth] at hd; omega⟩
    obtain ⟨r, rfl⟩ : ∃ m, r = m + 1 := ⟨r - 1, by simp only [LTm.nodes] at hr; omega⟩
    simp only [LTm.depth, LTm.nodes, LTm.atomBound] at hd hr hb hs
    obtain ⟨a, ha, aok, alen, alaid, aab, an, aocc⟩ := ihx d r start (by omega) (by omega) (by omega) (by omega)
    obtain ⟨b, hb', bok, blen, blaid, bab, bn, bocc⟩ := ihy d (r - x.nodes) a.next (by omega) (by omega)
      (by simp only [Flattened.next]; omega) (by omega)
    refine ⟨Flattened.app2 (.binop .or rfl) a b, ?_, LTm.BoolV.or aok bok, ?_, alaid.append blaid, ?_, ?_,
      fun o ho => (List.mem_append.mp ho).elim (aocc o) (bocc o)⟩
    · show Option.bind (flattenFuel? (C := C) d r x start) _ = _
      rw [ha]
      show Option.bind (flattenFuel? (C := C) d (r - x.nodes) y a.next) _ = _
      rw [hb']
      show some (Flattened.app2 (.binop .or rfl) a b, r - x.nodes - y.nodes) = _
      simp only [LTm.nodes, Option.some.injEq, Prod.mk.injEq, true_and]
      omega
    · show (a.reads ++ b.reads).length = x.words + y.words
      rw [List.length_append, alen, blen]
    · show max a.term.atomBound b.term.atomBound ≤ start + (a.reads ++ b.reads).length
      simp only [Flattened.next] at aab bab
      rw [List.length_append]
      omega
    · show a.term.nodes + b.term.nodes + 1 ≤ 2 * (x.nodes + y.nodes + 1)
      omega
  | @eqB x y _ _ ihx ihy =>
    intro d r start hd hr hb hs
    obtain ⟨d, rfl⟩ : ∃ m, d = m + 1 := ⟨d - 1, by simp only [LTm.depth] at hd; omega⟩
    obtain ⟨r, rfl⟩ : ∃ m, r = m + 1 := ⟨r - 1, by simp only [LTm.nodes] at hr; omega⟩
    simp only [LTm.depth, LTm.nodes, LTm.atomBound] at hd hr hb hs
    obtain ⟨a, ha, aok, alen, alaid, aab, an, aocc⟩ := ihx d r start (by omega) (by omega) (by omega) (by omega)
    obtain ⟨b, hb', bok, blen, blaid, bab, bn, bocc⟩ := ihy d (r - x.nodes) a.next (by omega) (by omega)
      (by simp only [Flattened.next]; omega) (by omega)
    refine ⟨Flattened.app2 (.binop .eqB rfl) a b, ?_, LTm.BoolV.eqB aok bok, ?_, alaid.append blaid, ?_, ?_,
      fun o ho => (List.mem_append.mp ho).elim (aocc o) (bocc o)⟩
    · show Option.bind (flattenFuel? (C := C) d r x start) _ = _
      rw [ha]
      show Option.bind (flattenFuel? (C := C) d (r - x.nodes) y a.next) _ = _
      rw [hb']
      show some (Flattened.app2 (.binop .eqB rfl) a b, r - x.nodes - y.nodes) = _
      simp only [LTm.nodes, Option.some.injEq, Prod.mk.injEq, true_and]
      omega
    · show (a.reads ++ b.reads).length = x.words + y.words
      rw [List.length_append, alen, blen]
    · show max a.term.atomBound b.term.atomBound ≤ start + (a.reads ++ b.reads).length
      simp only [Flattened.next] at aab bab
      rw [List.length_append]
      omega
    · show a.term.nodes + b.term.nodes + 1 ≤ 2 * (x.nodes + y.nodes + 1)
      omega
  | @neB x y _ _ ihx ihy =>
    intro d r start hd hr hb hs
    obtain ⟨d, rfl⟩ : ∃ m, d = m + 1 := ⟨d - 1, by simp only [LTm.depth] at hd; omega⟩
    obtain ⟨r, rfl⟩ : ∃ m, r = m + 1 := ⟨r - 1, by simp only [LTm.nodes] at hr; omega⟩
    simp only [LTm.depth, LTm.nodes, LTm.atomBound] at hd hr hb hs
    obtain ⟨a, ha, aok, alen, alaid, aab, an, aocc⟩ := ihx d r start (by omega) (by omega) (by omega) (by omega)
    obtain ⟨b, hb', bok, blen, blaid, bab, bn, bocc⟩ := ihy d (r - x.nodes) a.next (by omega) (by omega)
      (by simp only [Flattened.next]; omega) (by omega)
    refine ⟨Flattened.app2 (.binop .neB rfl) a b, ?_, LTm.BoolV.neB aok bok, ?_, alaid.append blaid, ?_, ?_,
      fun o ho => (List.mem_append.mp ho).elim (aocc o) (bocc o)⟩
    · show Option.bind (flattenFuel? (C := C) d r x start) _ = _
      rw [ha]
      show Option.bind (flattenFuel? (C := C) d (r - x.nodes) y a.next) _ = _
      rw [hb']
      show some (Flattened.app2 (.binop .neB rfl) a b, r - x.nodes - y.nodes) = _
      simp only [LTm.nodes, Option.some.injEq, Prod.mk.injEq, true_and]
      omega
    · show (a.reads ++ b.reads).length = x.words + y.words
      rw [List.length_append, alen, blen]
    · show max a.term.atomBound b.term.atomBound ≤ start + (a.reads ++ b.reads).length
      simp only [Flattened.next] at aab bab
      rw [List.length_append]
      omega
    · show a.term.nodes + b.term.nodes + 1 ≤ 2 * (x.nodes + y.nodes + 1)
      omega
  | @eqN p hp x y _ _ ihx ihy =>
    intro d r start hd hr hb hs
    obtain ⟨d, rfl⟩ : ∃ m, d = m + 1 := ⟨d - 1, by simp only [LTm.depth] at hd; omega⟩
    obtain ⟨r, rfl⟩ : ∃ m, r = m + 1 := ⟨r - 1, by simp only [LTm.nodes] at hr; omega⟩
    simp only [LTm.depth, LTm.nodes, LTm.atomBound] at hd hr hb hs
    obtain ⟨a, ha, aok, alen, alaid, aab, an, aocc⟩ := ihx d r start (by omega) (by omega) (by omega) (by omega)
    obtain ⟨b, hb', bok, blen, blaid, bab, bn, bocc⟩ := ihy d (r - x.nodes) a.next (by omega) (by omega)
      (by simp only [Flattened.next]; omega) (by omega)
    refine ⟨Flattened.app2 (.binop .eqB rfl) a b, ?_, LTm.BoolV.eqN hp aok bok, ?_, alaid.append blaid, ?_, ?_,
      fun o ho => (List.mem_append.mp ho).elim (aocc o) (bocc o)⟩
    · show Option.bind (flattenFuel? (C := C) d r x start) _ = _
      rw [ha]
      show Option.bind (flattenFuel? (C := C) d (r - x.nodes) y a.next) _ = _
      rw [hb']
      show some (Flattened.app2 (.binop .eqB rfl) a b, r - x.nodes - y.nodes) = _
      simp only [LTm.nodes, Option.some.injEq, Prod.mk.injEq, true_and]
      omega
    · show (a.reads ++ b.reads).length = x.words + y.words
      rw [List.length_append, alen, blen]
    · show max a.term.atomBound b.term.atomBound ≤ start + (a.reads ++ b.reads).length
      simp only [Flattened.next] at aab bab
      rw [List.length_append]
      omega
    · show a.term.nodes + b.term.nodes + 1 ≤ 2 * (x.nodes + y.nodes + 1)
      omega
  | @neN p hp x y _ _ ihx ihy =>
    intro d r start hd hr hb hs
    obtain ⟨d, rfl⟩ : ∃ m, d = m + 1 := ⟨d - 1, by simp only [LTm.depth] at hd; omega⟩
    obtain ⟨r, rfl⟩ : ∃ m, r = m + 1 := ⟨r - 1, by simp only [LTm.nodes] at hr; omega⟩
    simp only [LTm.depth, LTm.nodes, LTm.atomBound] at hd hr hb hs
    obtain ⟨a, ha, aok, alen, alaid, aab, an, aocc⟩ := ihx d r start (by omega) (by omega) (by omega) (by omega)
    obtain ⟨b, hb', bok, blen, blaid, bab, bn, bocc⟩ := ihy d (r - x.nodes) a.next (by omega) (by omega)
      (by simp only [Flattened.next]; omega) (by omega)
    refine ⟨Flattened.app2 (.binop .neB rfl) a b, ?_, LTm.BoolV.neN hp aok bok, ?_, alaid.append blaid, ?_, ?_,
      fun o ho => (List.mem_append.mp ho).elim (aocc o) (bocc o)⟩
    · show Option.bind (flattenFuel? (C := C) d r x start) _ = _
      rw [ha]
      show Option.bind (flattenFuel? (C := C) d (r - x.nodes) y a.next) _ = _
      rw [hb']
      show some (Flattened.app2 (.binop .neB rfl) a b, r - x.nodes - y.nodes) = _
      simp only [LTm.nodes, Option.some.injEq, Prod.mk.injEq, true_and]
      omega
    · show (a.reads ++ b.reads).length = x.words + y.words
      rw [List.length_append, alen, blen]
    · show max a.term.atomBound b.term.atomBound ≤ start + (a.reads ++ b.reads).length
      simp only [Flattened.next] at aab bab
      rw [List.length_append]
      omega
    · show a.term.nodes + b.term.nodes + 1 ≤ 2 * (x.nodes + y.nodes + 1)
      omega
  | @lt p h x y _ _ ihx ihy =>
    intro d r start hd hr hb hs
    obtain ⟨d, rfl⟩ : ∃ m, d = m + 1 := ⟨d - 1, by simp only [LTm.depth] at hd; omega⟩
    obtain ⟨r, rfl⟩ : ∃ m, r = m + 1 := ⟨r - 1, by simp only [LTm.nodes] at hr; omega⟩
    simp only [LTm.depth, LTm.nodes, LTm.atomBound] at hd hr hb hs
    obtain ⟨a, ha, aok, alen, alaid, aab, an, aocc⟩ := ihx d r start (by omega) (by omega) (by omega) (by omega)
    obtain ⟨b, hb', bok, blen, blaid, bab, bn, bocc⟩ := ihy d (r - x.nodes) a.next (by omega) (by omega)
      (by simp only [Flattened.next]; omega) (by omega)
    refine ⟨Flattened.app2 (.binop .lt h) a b, ?_, LTm.BoolV.lt h aok bok, ?_, alaid.append blaid, ?_, ?_,
      fun o ho => (List.mem_append.mp ho).elim (aocc o) (bocc o)⟩
    · show Option.bind (flattenFuel? (C := C) d r x start) _ = _
      rw [ha]
      show Option.bind (flattenFuel? (C := C) d (r - x.nodes) y a.next) _ = _
      rw [hb']
      show some (Flattened.app2 (.binop .lt h) a b, r - x.nodes - y.nodes) = _
      simp only [LTm.nodes, Option.some.injEq, Prod.mk.injEq, true_and]
      omega
    · show (a.reads ++ b.reads).length = x.words + y.words
      rw [List.length_append, alen, blen]
    · show max a.term.atomBound b.term.atomBound ≤ start + (a.reads ++ b.reads).length
      simp only [Flattened.next] at aab bab
      rw [List.length_append]
      omega
    · show a.term.nodes + b.term.nodes + 1 ≤ 2 * (x.nodes + y.nodes + 1)
      omega
  | @gt p h x y _ _ ihx ihy =>
    intro d r start hd hr hb hs
    obtain ⟨d, rfl⟩ : ∃ m, d = m + 1 := ⟨d - 1, by simp only [LTm.depth] at hd; omega⟩
    obtain ⟨r, rfl⟩ : ∃ m, r = m + 1 := ⟨r - 1, by simp only [LTm.nodes] at hr; omega⟩
    simp only [LTm.depth, LTm.nodes, LTm.atomBound] at hd hr hb hs
    obtain ⟨a, ha, aok, alen, alaid, aab, an, aocc⟩ := ihx d r start (by omega) (by omega) (by omega) (by omega)
    obtain ⟨b, hb', bok, blen, blaid, bab, bn, bocc⟩ := ihy d (r - x.nodes) a.next (by omega) (by omega)
      (by simp only [Flattened.next]; omega) (by omega)
    refine ⟨Flattened.app2 (.binop .gt h) a b, ?_, LTm.BoolV.gt h aok bok, ?_, alaid.append blaid, ?_, ?_,
      fun o ho => (List.mem_append.mp ho).elim (aocc o) (bocc o)⟩
    · show Option.bind (flattenFuel? (C := C) d r x start) _ = _
      rw [ha]
      show Option.bind (flattenFuel? (C := C) d (r - x.nodes) y a.next) _ = _
      rw [hb']
      show some (Flattened.app2 (.binop .gt h) a b, r - x.nodes - y.nodes) = _
      simp only [LTm.nodes, Option.some.injEq, Prod.mk.injEq, true_and]
      omega
    · show (a.reads ++ b.reads).length = x.words + y.words
      rw [List.length_append, alen, blen]
    · show max a.term.atomBound b.term.atomBound ≤ start + (a.reads ++ b.reads).length
      simp only [Flattened.next] at aab bab
      rw [List.length_append]
      omega
    · show a.term.nodes + b.term.nodes + 1 ≤ 2 * (x.nodes + y.nodes + 1)
      omega
  | @le p h x y _ _ ihx ihy =>
    intro d r start hd hr hb hs
    obtain ⟨d, rfl⟩ : ∃ m, d = m + 1 := ⟨d - 1, by simp only [LTm.depth] at hd; omega⟩
    obtain ⟨r, rfl⟩ : ∃ m, r = m + 1 := ⟨r - 1, by simp only [LTm.nodes] at hr; omega⟩
    simp only [LTm.depth, LTm.nodes, LTm.atomBound] at hd hr hb hs
    obtain ⟨a, ha, aok, alen, alaid, aab, an, aocc⟩ := ihx d r start (by omega) (by omega) (by omega) (by omega)
    obtain ⟨b, hb', bok, blen, blaid, bab, bn, bocc⟩ := ihy d (r - x.nodes) a.next (by omega) (by omega)
      (by simp only [Flattened.next]; omega) (by omega)
    refine ⟨Flattened.app2 (.binop .le h) a b, ?_, LTm.BoolV.le h aok bok, ?_, alaid.append blaid, ?_, ?_,
      fun o ho => (List.mem_append.mp ho).elim (aocc o) (bocc o)⟩
    · show Option.bind (flattenFuel? (C := C) d r x start) _ = _
      rw [ha]
      show Option.bind (flattenFuel? (C := C) d (r - x.nodes) y a.next) _ = _
      rw [hb']
      show some (Flattened.app2 (.binop .le h) a b, r - x.nodes - y.nodes) = _
      simp only [LTm.nodes, Option.some.injEq, Prod.mk.injEq, true_and]
      omega
    · show (a.reads ++ b.reads).length = x.words + y.words
      rw [List.length_append, alen, blen]
    · show max a.term.atomBound b.term.atomBound ≤ start + (a.reads ++ b.reads).length
      simp only [Flattened.next] at aab bab
      rw [List.length_append]
      omega
    · show a.term.nodes + b.term.nodes + 1 ≤ 2 * (x.nodes + y.nodes + 1)
      omega
  | @ge p h x y _ _ ihx ihy =>
    intro d r start hd hr hb hs
    obtain ⟨d, rfl⟩ : ∃ m, d = m + 1 := ⟨d - 1, by simp only [LTm.depth] at hd; omega⟩
    obtain ⟨r, rfl⟩ : ∃ m, r = m + 1 := ⟨r - 1, by simp only [LTm.nodes] at hr; omega⟩
    simp only [LTm.depth, LTm.nodes, LTm.atomBound] at hd hr hb hs
    obtain ⟨a, ha, aok, alen, alaid, aab, an, aocc⟩ := ihx d r start (by omega) (by omega) (by omega) (by omega)
    obtain ⟨b, hb', bok, blen, blaid, bab, bn, bocc⟩ := ihy d (r - x.nodes) a.next (by omega) (by omega)
      (by simp only [Flattened.next]; omega) (by omega)
    refine ⟨Flattened.app2 (.binop .ge h) a b, ?_, LTm.BoolV.ge h aok bok, ?_, alaid.append blaid, ?_, ?_,
      fun o ho => (List.mem_append.mp ho).elim (aocc o) (bocc o)⟩
    · show Option.bind (flattenFuel? (C := C) d r x start) _ = _
      rw [ha]
      show Option.bind (flattenFuel? (C := C) d (r - x.nodes) y a.next) _ = _
      rw [hb']
      show some (Flattened.app2 (.binop .ge h) a b, r - x.nodes - y.nodes) = _
      simp only [LTm.nodes, Option.some.injEq, Prod.mk.injEq, true_and]
      omega
    · show (a.reads ++ b.reads).length = x.words + y.words
      rw [List.length_append, alen, blen]
    · show max a.term.atomBound b.term.atomBound ≤ start + (a.reads ++ b.reads).length
      simp only [Flattened.next] at aab bab
      rw [List.length_append]
      omega
    · show a.term.nodes + b.term.nodes + 1 ≤ 2 * (x.nodes + y.nodes + 1)
      omega
  | @seq q p x y _ _ ihx ihy =>
    intro d r start hd hr hb hs
    obtain ⟨d, rfl⟩ : ∃ m, d = m + 1 := ⟨d - 1, by simp only [LTm.depth] at hd; omega⟩
    obtain ⟨r, rfl⟩ : ∃ m, r = m + 1 := ⟨r - 1, by simp only [LTm.nodes] at hr; omega⟩
    simp only [LTm.depth, LTm.nodes, LTm.atomBound] at hd hr hb hs
    obtain ⟨a, ha, aok, alen, alaid, aab, an, aocc⟩ := ihx d r start (by omega) (by omega) (by omega) (by omega)
    obtain ⟨b, hb', bok, blen, blaid, bab, bn, bocc⟩ := ihy d (r - x.nodes) a.next (by omega) (by omega)
      (by simp only [Flattened.next]; omega) (by omega)
    refine ⟨Flattened.seq a b, ?_, LTm.Num.seq aok bok, ?_, alaid.append blaid, ?_, ?_,
      fun o ho => (List.mem_append.mp ho).elim (aocc o) (bocc o)⟩
    · show Option.bind (flattenFuel? (C := C) d r x start) _ = _
      rw [ha]
      show Option.bind (flattenFuel? (C := C) d (r - x.nodes) y a.next) _ = _
      rw [hb']
      show some (Flattened.seq a b, r - x.nodes - y.nodes) = _
      simp only [LTm.nodes, Option.some.injEq, Prod.mk.injEq, true_and]
      omega
    · show (a.reads ++ b.reads).length = x.words + y.words
      rw [List.length_append, alen, blen]
    · show max a.term.atomBound b.term.atomBound ≤ start + (a.reads ++ b.reads).length
      simp only [Flattened.next] at aab bab
      rw [List.length_append]
      omega
    · show a.term.nodes + b.term.nodes + 1 ≤ 2 * (x.nodes + y.nodes + 1)
      omega
  | @seqB x y _ _ ihx ihy =>
    intro d r start hd hr hb hs
    obtain ⟨d, rfl⟩ : ∃ m, d = m + 1 := ⟨d - 1, by simp only [LTm.depth] at hd; omega⟩
    obtain ⟨r, rfl⟩ : ∃ m, r = m + 1 := ⟨r - 1, by simp only [LTm.nodes] at hr; omega⟩
    simp only [LTm.depth, LTm.nodes, LTm.atomBound] at hd hr hb hs
    obtain ⟨a, ha, aok, alen, alaid, aab, an, aocc⟩ := ihx d r start (by omega) (by omega) (by omega) (by omega)
    obtain ⟨b, hb', bok, blen, blaid, bab, bn, bocc⟩ := ihy d (r - x.nodes) a.next (by omega) (by omega)
      (by simp only [Flattened.next]; omega) (by omega)
    refine ⟨Flattened.seq a b, ?_, LTm.BoolV.seqB aok bok, ?_, alaid.append blaid, ?_, ?_,
      fun o ho => (List.mem_append.mp ho).elim (aocc o) (bocc o)⟩
    · show Option.bind (flattenFuel? (C := C) d r x start) _ = _
      rw [ha]
      show Option.bind (flattenFuel? (C := C) d (r - x.nodes) y a.next) _ = _
      rw [hb']
      show some (Flattened.seq a b, r - x.nodes - y.nodes) = _
      simp only [LTm.nodes, Option.some.injEq, Prod.mk.injEq, true_and]
      omega
    · show (a.reads ++ b.reads).length = x.words + y.words
      rw [List.length_append, alen, blen]
    · show max a.term.atomBound b.term.atomBound ≤ start + (a.reads ++ b.reads).length
      simp only [Flattened.next] at aab bab
      rw [List.length_append]
      omega
    · show a.term.nodes + b.term.nodes + 1 ≤ 2 * (x.nodes + y.nodes + 1)
      omega
  | @seqN q hq x y _ _ ihx ihy =>
    intro d r start hd hr hb hs
    obtain ⟨d, rfl⟩ : ∃ m, d = m + 1 := ⟨d - 1, by simp only [LTm.depth] at hd; omega⟩
    obtain ⟨r, rfl⟩ : ∃ m, r = m + 1 := ⟨r - 1, by simp only [LTm.nodes] at hr; omega⟩
    simp only [LTm.depth, LTm.nodes, LTm.atomBound] at hd hr hb hs
    obtain ⟨a, ha, aok, alen, alaid, aab, an, aocc⟩ := ihx d r start (by omega) (by omega) (by omega) (by omega)
    obtain ⟨b, hb', bok, blen, blaid, bab, bn, bocc⟩ := ihy d (r - x.nodes) a.next (by omega) (by omega)
      (by simp only [Flattened.next]; omega) (by omega)
    refine ⟨Flattened.seq a b, ?_, LTm.BoolV.seqN hq aok bok, ?_, alaid.append blaid, ?_, ?_,
      fun o ho => (List.mem_append.mp ho).elim (aocc o) (bocc o)⟩
    · show Option.bind (flattenFuel? (C := C) d r x start) _ = _
      rw [ha]
      show Option.bind (flattenFuel? (C := C) d (r - x.nodes) y a.next) _ = _
      rw [hb']
      show some (Flattened.seq a b, r - x.nodes - y.nodes) = _
      simp only [LTm.nodes, Option.some.injEq, Prod.mk.injEq, true_and]
      omega
    · show (a.reads ++ b.reads).length = x.words + y.words
      rw [List.length_append, alen, blen]
    · show max a.term.atomBound b.term.atomBound ≤ start + (a.reads ++ b.reads).length
      simp only [Flattened.next] at aab bab
      rw [List.length_append]
      omega
    · show a.term.nodes + b.term.nodes + 1 ≤ 2 * (x.nodes + y.nodes + 1)
      omega
  | @key K V x y _ _ ihx ihy =>
    intro d r start hd hr hb hs
    obtain ⟨d, rfl⟩ : ∃ m, d = m + 1 := ⟨d - 1, by simp only [LTm.depth] at hd; omega⟩
    obtain ⟨r, rfl⟩ : ∃ m, r = m + 1 := ⟨r - 1, by simp only [LTm.nodes] at hr; omega⟩
    simp only [LTm.depth, LTm.nodes, LTm.atomBound] at hd hr hb hs
    obtain ⟨a, ha, aok, alen, alaid, aab, an, aocc⟩ := ihx d r start (by omega) (by omega) (by omega) (by omega)
    obtain ⟨b, hb', bok, blen, blaid, bab, bn, bocc⟩ := ihy d (r - x.nodes) a.next (by omega) (by omega)
      (by simp only [Flattened.next]; omega) (by omega)
    refine ⟨Flattened.index .map a b, ?_, LTm.PathF.key aok bok, ?_, alaid.append blaid, ?_, ?_,
      fun o ho => (List.mem_append.mp ho).elim (aocc o) (bocc o)⟩
    · show Option.bind (flattenFuel? (C := C) d r x start) _ = _
      rw [ha]
      show Option.bind (flattenFuel? (C := C) d (r - x.nodes) y a.next) _ = _
      rw [hb']
      show some (Flattened.index .map a b, r - x.nodes - y.nodes) = _
      simp only [LTm.nodes, Option.some.injEq, Prod.mk.injEq, true_and]
      omega
    · show (a.reads ++ b.reads).length = x.words + y.words
      rw [List.length_append, alen, blen]
    · show max a.term.atomBound b.term.atomBound ≤ start + (a.reads ++ b.reads).length
      simp only [Flattened.next] at aab bab
      rw [List.length_append]
      omega
    · show a.term.nodes + b.term.nodes + 1 ≤ 2 * (x.nodes + y.nodes + 1)
      omega
  | zlit n =>
    intro d r start hd hr hb hs
    obtain ⟨d, rfl⟩ : ∃ m, d = m + 1 := ⟨d - 1, by simp only [LTm.depth] at hd; omega⟩
    obtain ⟨r, rfl⟩ : ∃ m, r = m + 1 := ⟨r - 1, by simp only [LTm.nodes] at hr; omega⟩
    refine ⟨Flattened.pure (LTm.app0 (C := C) (.zlit n)) start, ?_, .zlit n, rfl, .nil start, ?_, ?_, fun _ h => by cases h⟩
    · show some (Flattened.pure (LTm.app0 (C := C) (.zlit n)) start, r) = _
      simp only [LTm.nodes, Nat.add_sub_cancel]
    · show (LTm.app0 (C := C) (.zlit n)).atomBound ≤ start + 0
      exact hb
    · show (LTm.app0 (C := C) (.zlit n)).nodes ≤ 2 * (LTm.app0 (C := C) (.zlit n)).nodes
      omega
  | @zint x _ ih =>
    intro d r start hd hr hb hs
    obtain ⟨d, rfl⟩ : ∃ m, d = m + 1 := ⟨d - 1, by simp only [LTm.depth] at hd; omega⟩
    obtain ⟨r, rfl⟩ : ∃ m, r = m + 1 := ⟨r - 1, by simp only [LTm.nodes] at hr; omega⟩
    simp only [LTm.depth, LTm.nodes, LTm.atomBound] at hd hr hb hs
    obtain ⟨a, ha, aok, alen, alaid, aab, an, aocc⟩ := ih d r start (by omega) (by omega) hb (by omega)
    refine ⟨Flattened.app1 .toInt a, ?_, LTm.ZNum.toInt aok, alen, alaid, aab, ?_, aocc⟩
    · show Option.bind (flattenFuel? (C := C) d r x start) _ = _
      rw [ha]
      show some (Flattened.app1 .toInt a, r - x.nodes) = _
      simp only [LTm.nodes, Option.some.injEq, Prod.mk.injEq, true_and]
      omega
    · show a.term.nodes + 1 ≤ 2 * (x.nodes + 1)
      omega
  | @zadd h x y _ _ ihx ihy =>
    intro d r start hd hr hb hs
    obtain ⟨d, rfl⟩ : ∃ m, d = m + 1 := ⟨d - 1, by simp only [LTm.depth] at hd; omega⟩
    obtain ⟨r, rfl⟩ : ∃ m, r = m + 1 := ⟨r - 1, by simp only [LTm.nodes] at hr; omega⟩
    simp only [LTm.depth, LTm.nodes, LTm.atomBound] at hd hr hb hs
    obtain ⟨a, ha, aok, alen, alaid, aab, an, aocc⟩ := ihx d r start (by omega) (by omega) (by omega) (by omega)
    obtain ⟨b, hb', bok, blen, blaid, bab, bn, bocc⟩ := ihy d (r - x.nodes) a.next (by omega) (by omega)
      (by simp only [Flattened.next]; omega) (by omega)
    refine ⟨Flattened.app2 (.zbin .add h) a b, ?_, LTm.ZNum.add h aok bok, ?_, alaid.append blaid, ?_, ?_,
      fun o ho => (List.mem_append.mp ho).elim (aocc o) (bocc o)⟩
    · show Option.bind (flattenFuel? (C := C) d r x start) _ = _
      rw [ha]
      show Option.bind (flattenFuel? (C := C) d (r - x.nodes) y a.next) _ = _
      rw [hb']
      show some (Flattened.app2 (.zbin .add h) a b, r - x.nodes - y.nodes) = _
      simp only [LTm.nodes, Option.some.injEq, Prod.mk.injEq, true_and]
      omega
    · show (a.reads ++ b.reads).length = x.words + y.words
      rw [List.length_append, alen, blen]
    · show max a.term.atomBound b.term.atomBound ≤ start + (a.reads ++ b.reads).length
      simp only [Flattened.next] at aab bab
      rw [List.length_append]
      omega
    · show a.term.nodes + b.term.nodes + 1 ≤ 2 * (x.nodes + y.nodes + 1)
      omega
  | @zsub h x y _ _ ihx ihy =>
    intro d r start hd hr hb hs
    obtain ⟨d, rfl⟩ : ∃ m, d = m + 1 := ⟨d - 1, by simp only [LTm.depth] at hd; omega⟩
    obtain ⟨r, rfl⟩ : ∃ m, r = m + 1 := ⟨r - 1, by simp only [LTm.nodes] at hr; omega⟩
    simp only [LTm.depth, LTm.nodes, LTm.atomBound] at hd hr hb hs
    obtain ⟨a, ha, aok, alen, alaid, aab, an, aocc⟩ := ihx d r start (by omega) (by omega) (by omega) (by omega)
    obtain ⟨b, hb', bok, blen, blaid, bab, bn, bocc⟩ := ihy d (r - x.nodes) a.next (by omega) (by omega)
      (by simp only [Flattened.next]; omega) (by omega)
    refine ⟨Flattened.app2 (.zbin .sub h) a b, ?_, LTm.ZNum.sub h aok bok, ?_, alaid.append blaid, ?_, ?_,
      fun o ho => (List.mem_append.mp ho).elim (aocc o) (bocc o)⟩
    · show Option.bind (flattenFuel? (C := C) d r x start) _ = _
      rw [ha]
      show Option.bind (flattenFuel? (C := C) d (r - x.nodes) y a.next) _ = _
      rw [hb']
      show some (Flattened.app2 (.zbin .sub h) a b, r - x.nodes - y.nodes) = _
      simp only [LTm.nodes, Option.some.injEq, Prod.mk.injEq, true_and]
      omega
    · show (a.reads ++ b.reads).length = x.words + y.words
      rw [List.length_append, alen, blen]
    · show max a.term.atomBound b.term.atomBound ≤ start + (a.reads ++ b.reads).length
      simp only [Flattened.next] at aab bab
      rw [List.length_append]
      omega
    · show a.term.nodes + b.term.nodes + 1 ≤ 2 * (x.nodes + y.nodes + 1)
      omega
  | @zcmp op h x y _ _ ihx ihy =>
    intro d r start hd hr hb hs
    obtain ⟨d, rfl⟩ : ∃ m, d = m + 1 := ⟨d - 1, by simp only [LTm.depth] at hd; omega⟩
    obtain ⟨r, rfl⟩ : ∃ m, r = m + 1 := ⟨r - 1, by simp only [LTm.nodes] at hr; omega⟩
    simp only [LTm.depth, LTm.nodes, LTm.atomBound] at hd hr hb hs
    obtain ⟨a, ha, aok, alen, alaid, aab, an, aocc⟩ := ihx d r start (by omega) (by omega) (by omega) (by omega)
    obtain ⟨b, hb', bok, blen, blaid, bab, bn, bocc⟩ := ihy d (r - x.nodes) a.next (by omega) (by omega)
      (by simp only [Flattened.next]; omega) (by omega)
    refine ⟨Flattened.app2 (.zcmp op h) a b, ?_, LTm.BoolV.zcmp op h aok bok, ?_, alaid.append blaid, ?_, ?_,
      fun o ho => (List.mem_append.mp ho).elim (aocc o) (bocc o)⟩
    · show Option.bind (flattenFuel? (C := C) d r x start) _ = _
      rw [ha]
      show Option.bind (flattenFuel? (C := C) d (r - x.nodes) y a.next) _ = _
      rw [hb']
      show some (Flattened.app2 (.zcmp op h) a b, r - x.nodes - y.nodes) = _
      simp only [LTm.nodes, Option.some.injEq, Prod.mk.injEq, true_and]
      omega
    · show (a.reads ++ b.reads).length = x.words + y.words
      rw [List.length_append, alen, blen]
    · show max a.term.atomBound b.term.atomBound ≤ start + (a.reads ++ b.reads).length
      simp only [Flattened.next] at aab bab
      rw [List.length_append]
      omega
    · show a.term.nodes + b.term.nodes + 1 ≤ 2 * (x.nodes + y.nodes + 1)
      omega
  | @zmulL h n y _ ihy =>
    intro d r start hd hr hb hs
    obtain ⟨d, rfl⟩ : ∃ m, d = m + 1 := ⟨d - 1, by simp only [LTm.depth] at hd; omega⟩
    obtain ⟨r, rfl⟩ : ∃ m, r = m + 1 := ⟨r - 1, by simp only [LTm.nodes] at hr; omega⟩
    simp only [LTm.depth, LTm.nodes, LTm.atomBound] at hd hr hb hs
    obtain ⟨d, rfl⟩ : ∃ m, d = m + 1 := ⟨d - 1, by omega⟩
    obtain ⟨r, rfl⟩ : ∃ m, r = m + 1 := ⟨r - 1, by omega⟩
    let a := Flattened.pure (LTm.app0 (C := C) (.zlit n)) start
    obtain ⟨b, hb', bok, blen, blaid, bab, bn, bocc⟩ := ihy (d + 1) r a.next (by omega) (by omega)
      (by show y.atomBound ≤ start + 0; omega) (by omega)
    refine ⟨Flattened.app2 (.zbin .mul h) a b, ?_, LTm.ZNum.mulL h n bok, ?_,
      (Laid.nil start).append blaid, ?_, ?_,
      fun o ho => (List.mem_append.mp ho).elim (fun h => nomatch h) (bocc o)⟩
    · rw [flattenFuel?_zbin, flattenKInt?_zbin, flattenFuel?_zlit]
      show Option.bind (flattenFuel? (C := C) (d + 1) r y a.next) _ = _
      rw [hb']
      show some (Flattened.app2 (.zbin .mul h) a b, r - y.nodes) = _
      simp only [LTm.nodes, Option.some.injEq, Prod.mk.injEq, true_and]
      omega
    · show ([] ++ b.reads).length = (LTm.app0 (C := C) (.zlit n)).words + y.words
      rw [List.nil_append, blen]
      simp only [LTm.words, Nat.zero_add]
    · show max (LTm.app0 (C := C) (.zlit n)).atomBound b.term.atomBound ≤ start + ([] ++ b.reads).length
      simp only [Flattened.next] at bab
      simp only [List.nil_append, LTm.atomBound]
      show max 0 b.term.atomBound ≤ start + b.reads.length
      have h0 : a.reads.length = 0 := rfl
      omega
    · show (LTm.app0 (C := C) (.zlit n)).nodes + b.term.nodes + 1 ≤ 2 * ((LTm.app0 (C := C) (.zlit n)).nodes + y.nodes + 1)
      simp only [LTm.nodes]
      omega
  | @zmulR h x n _ ihx =>
    intro d r start hd hr hb hs
    obtain ⟨d, rfl⟩ : ∃ m, d = m + 1 := ⟨d - 1, by simp only [LTm.depth] at hd; omega⟩
    obtain ⟨r, rfl⟩ : ∃ m, r = m + 1 := ⟨r - 1, by simp only [LTm.nodes] at hr; omega⟩
    simp only [LTm.depth, LTm.nodes, LTm.atomBound] at hd hr hb hs
    obtain ⟨d, rfl⟩ : ∃ m, d = m + 1 := ⟨d - 1, by omega⟩
    obtain ⟨a, ha, aok, alen, alaid, aab, an, aocc⟩ := ihx (d + 1) r start (by omega) (by omega) (by omega) (by omega)
    obtain ⟨k, hk⟩ : ∃ k, r - x.nodes = k + 1 := ⟨r - x.nodes - 1, by omega⟩
    let b := Flattened.pure (LTm.app0 (C := C) (.zlit n)) a.next
    refine ⟨Flattened.app2 (.zbin .mul h) a b, ?_, LTm.ZNum.mulR h n aok, ?_,
      alaid.append (Laid.nil _), ?_, ?_,
      fun o ho => (List.mem_append.mp ho).elim (aocc o) (fun h => nomatch h)⟩
    · show Option.bind (flattenFuel? (C := C) (d + 1) r x start) _ = _
      rw [ha]
      show Option.bind (flattenFuel? (C := C) (d + 1) (r - x.nodes) (LTm.app0 (.zlit n)) a.next) _ = _
      rw [hk, flattenFuel?_zlit]
      show some (Flattened.app2 (.zbin .mul h) a b, k) = _
      simp only [LTm.nodes, Option.some.injEq, Prod.mk.injEq, true_and]
      omega
    · show (a.reads ++ []).length = x.words + (LTm.app0 (C := C) (.zlit n)).words
      rw [List.append_nil, alen]
      simp only [LTm.words, Nat.add_zero]
    · show max a.term.atomBound (LTm.app0 (C := C) (.zlit n)).atomBound ≤ start + (a.reads ++ []).length
      simp only [Flattened.next] at aab
      simp only [List.append_nil, LTm.atomBound]
      omega
    · show a.term.nodes + (LTm.app0 (C := C) (.zlit n)).nodes + 1 ≤ 2 * (x.nodes + (LTm.app0 (C := C) (.zlit n)).nodes + 1)
      simp only [LTm.nodes]
      omega
  | @znetLit hl v =>
    intro d r start hd hr hb hs
    obtain ⟨d, rfl⟩ : ∃ m, d = m + 1 := ⟨d - 1, by simp only [LTm.depth] at hd; omega⟩
    obtain ⟨r, rfl⟩ : ∃ m, r = m + 1 := ⟨r - 1, by simp only [LTm.nodes] at hr; omega⟩
    simp only [LTm.depth, LTm.nodes] at hd hr
    obtain ⟨d, rfl⟩ : ∃ m, d = m + 1 := ⟨d - 1, by omega⟩
    obtain ⟨r, rfl⟩ : ∃ m, r = m + 1 := ⟨r - 1, by omega⟩
    refine ⟨Flattened.app1 .net (Flattened.pure (LTm.app0 (C := C) (.lit v)) start), ?_,
      LTm.ZNum.netLit v hl, rfl, .nil start, ?_, ?_, fun _ h => by cases h⟩
    · rw [flattenFuel?_net, flattenKInt?_net, flattenFuel?_lit]
      simp only [LTm.nodes]
      rfl
    · show (LTm.app1 .net (LTm.app0 (C := C) (.lit v))).atomBound ≤ start + 0
      exact hb
    · show (LTm.app1 .net (LTm.app0 (C := C) (.lit v))).nodes ≤ 2 * (LTm.app1 .net (LTm.app0 (C := C) (.lit v))).nodes
      omega
  | @zseq hl q x y _ _ ihx ihy =>
    intro d r start hd hr hb hs
    obtain ⟨d, rfl⟩ : ∃ m, d = m + 1 := ⟨d - 1, by simp only [LTm.depth] at hd; omega⟩
    obtain ⟨r, rfl⟩ : ∃ m, r = m + 1 := ⟨r - 1, by simp only [LTm.nodes] at hr; omega⟩
    simp only [LTm.depth, LTm.nodes, LTm.atomBound] at hd hr hb hs
    obtain ⟨a, ha, aok, alen, alaid, aab, an, aocc⟩ := ihx d r start (by omega) (by omega) (by omega) (by omega)
    obtain ⟨b, hb', bok, blen, blaid, bab, bn, bocc⟩ := ihy d (r - x.nodes) a.next (by omega) (by omega)
      (by simp only [Flattened.next]; omega) (by omega)
    refine ⟨Flattened.seq a b, ?_, LTm.ZNum.zseq aok bok, ?_, alaid.append blaid, ?_, ?_,
      fun o ho => (List.mem_append.mp ho).elim (aocc o) (bocc o)⟩
    · show Option.bind (flattenFuel? (C := C) d r x start) _ = _
      rw [ha]
      show Option.bind (flattenFuel? (C := C) d (r - x.nodes) y a.next) _ = _
      rw [hb']
      show some (Flattened.seq a b, r - x.nodes - y.nodes) = _
      simp only [LTm.nodes, Option.some.injEq, Prod.mk.injEq, true_and]
      omega
    · show (a.reads ++ b.reads).length = x.words + y.words
      rw [List.length_append, alen, blen]
    · show max a.term.atomBound b.term.atomBound ≤ start + (a.reads ++ b.reads).length
      simp only [Flattened.next] at aab bab
      rw [List.length_append]
      omega
    · show a.term.nodes + b.term.nodes + 1 ≤ 2 * (x.nodes + y.nodes + 1)
      omega
  | @ofNum t _ ih =>
    intro d r start hd hr hb hs
    obtain ⟨a, ha, aok, alen, alaid, aab, an, aocc⟩ := ih d r start hd hr hb hs
    exact ⟨a, ha, (LTm.Num.toBoolV aok rfl).ledger_mono (fun _ h => h.elim), alen, alaid, aab, an, aocc⟩
  | @word p q _ ih =>
    intro d r start hd hr hb hs
    obtain ⟨d, rfl⟩ : ∃ m, d = m + 1 := ⟨d - 1, by simp only [LTm.depth] at hd; omega⟩
    obtain ⟨r, rfl⟩ : ∃ m, r = m + 1 := ⟨r - 1, by simp only [LTm.nodes] at hr; omega⟩
    simp only [LTm.depth, LTm.nodes, LTm.atomBound] at hd hr hb hs
    obtain ⟨a, ha, aok, alen, alaid, aab, an, aocc⟩ := ih d r start (by omega) (by omega) hb (by omega)
    have hpf : a.term.PathF (fun _ => True) (fun _ => True) := aok
    have hdn := LTm.depth_le_nodes a.term
    obtain ⟨v, hv, hvt, hvf⟩ := SPath.viewFuel?_PathF hpf 1024 (by omega)
    have hlen : v.path.segs.len < 1024 := by
      have h1 := TSegs.len_le_toLTm v.path.segs (.app0 (.root v.path.r v.path.hr))
      have h2 : (v.path.segs.toLTm (.app0 (.root v.path.r v.path.hr))).depth = a.term.depth :=
        congrArg LTm.depth hvt
      simp only [LTm.depth] at h1
      omega
    obtain ⟨gd, hgd, gnum, gb⟩ := TSegs.guardFuel?_FK (fun _ hi => hi.1) hvf 1024 hlen
    obtain ⟨gn, gab⟩ := gb (.app0 (.root v.path.r v.path.hr))
    have hroot : v.path.segs.toLTm (.app0 (.root v.path.r v.path.hr)) = a.term := hvt
    rw [hroot] at gn gab
    obtain ⟨G, hG, hGt⟩ : ∃ G : SPath.Guard v.path, SPath.guard? v.path = some G ∧ G.test = gd.test := by
      have h1 : (SPath.guard? v.path).map SPath.Guard.test = some gd.test := by
        show Option.map _ (Option.bind (TSegs.guardFuel? 1024 v.path.segs) _) = _
        rw [hgd]
        rfl
      cases hG : SPath.guard? v.path with
      | none => rw [hG] at h1; cases h1
      | some G => rw [hG] at h1; exact ⟨G, rfl, Option.some.inj h1⟩
    refine ⟨Flattened.word a v G, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · show Option.bind (flattenFuel? (C := C) d r q start) _ = _
      rw [ha]
      show Option.bind (SPath.viewFuel? 1024 a.term) _ = _
      rw [hv]
      show Option.bind (SPath.guard? v.path) _ = _
      rw [hG]
      show some (Flattened.word a v G, r - q.nodes) = _
      simp only [LTm.nodes, Option.some.injEq, Prod.mk.injEq, true_and]
      omega
    · show (LTm.seq G.test (LTm.var (p := p) a.next)).Num (fun _ => True) (fun _ => True)
      rw [hGt]
      exact .seq gnum (.var _ trivial)
    · show (a.reads ++ [_]).length = q.words + 1
      rw [List.length_append, alen]
      rfl
    · refine alaid.append (.cons rfl ?_ ?_ (.nil _))
      · show v.path.toLTm.atomBound ≤ start + a.reads.length
        rw [hvt]
        exact aab
      · show ReadFreeOf v.path.toLTm
        rw [hvt]
        exact hpf.readFree
    · show max G.test.atomBound (a.next + 1) ≤ start + (a.reads ++ [_]).length
      rw [hGt, List.length_append]
      simp only [Flattened.next, List.length_cons, List.length_nil] at aab ⊢
      omega
    · show G.test.nodes + 1 + 1 ≤ 2 * (q.nodes + 1)
      rw [hGt]
      simp only [LTm.nodes] at gn
      omega
    · intro o ho
      rcases List.mem_append.mp ho with ho | ho
      · exact aocc o ho
      · rw [List.mem_singleton.mp ho]
        have htd := LTm.depth_le_nodes gd.test
        simp only [LTm.nodes] at gn
        refine ⟨?_, ?_, hvf.mono fun i hi => ⟨hi.1, by omega⟩⟩
        · show G.test.Num _ _
          rw [hGt]
          exact gnum
        · show G.test.depth ≤ 1022
          rw [hGt]
          omega

/-! ## Formulas -/

/-- **The source leaf**: Boolean equations of Boolean terms and numeric
equations of scalar terms, under `¬`, `∧`, `→`. -/
inductive LFml.SrcL (c : Bool) (w : Bool) (l : LedgerMode) : LFml C → Prop
  | tt : LFml.SrcL c w l .tt
  | eqB {a b : LTm C (.val .bool)} : a.SrcL c w l .bool → b.SrcL c w l .bool → LFml.SrcL c w l (.eq a b)
  | eqN {p : PrimTy} (hp : p.isNumeric = true) {a b : LTm C (.val p)} :
      a.SrcL c w l .num → b.SrcL c w l .num → LFml.SrcL c w l (.eq a b)
  | not {φ : LFml C} : LFml.SrcL c w l φ → LFml.SrcL c w l (.not φ)
  | and {φ ψ : LFml C} : LFml.SrcL c w l φ → LFml.SrcL c w l ψ → LFml.SrcL c w l (.and φ ψ)
  | imp {φ ψ : LFml C} : LFml.SrcL c w l φ → LFml.SrcL c w l ψ → LFml.SrcL c w l (.imp φ ψ)
  /-- The defining equations of cut atoms, after the cut. -/
  | defDiv (hw : w = false) (h : BinOp.div.accepts .uint = true) (v : PrimTy.uint.Denote)
      (hv : v.val ≠ 0) (k : Nat) {a : LTm C (.val .uint)} : a.SrcL c w l .num →
      LFml.SrcL c w l (.eq (.app2 (.binop .div h) a (.app0 (.lit v))) (.var k))
  | defDivI (hw : w = false) (h : BinOp.div.accepts .int = true) (v : PrimTy.int.Denote)
      (hv : v.val ≠ 0) (k : Nat) {a : LTm C (.val .int)} : a.SrcL c w l .num →
      LFml.SrcL c w l (.eq (.app2 (.binop .div h) a (.app0 (.lit v))) (.var k))
  | defShr (hw : w = false) {p : PrimTy} (h : BinOp.shr.accepts p = true) (v : p.Denote) (k : Nat)
      {a : LTm C (.val p)} : a.SrcL c w l .num →
      LFml.SrcL c w l (.eq (.app2 (.binop .shr h) a (.app0 (.lit v))) (.var k))
  | defAddW (hw : w = false) (h : BinOp.addW.accepts .uint = true) (k : Nat) {a b : LTm C (.val .uint)} :
      a.SrcL c w l .num → b.SrcL c w l .num → LFml.SrcL c w l (.eq (.app2 (.binop .addW h) a b) (.var k))
  | defSubW (hw : w = false) (h : BinOp.subW.accepts .uint = true) (k : Nat) {a b : LTm C (.val .uint)} :
      a.SrcL c w l .num → b.SrcL c w l .num → LFml.SrcL c w l (.eq (.app2 (.binop .subW h) a b) (.var k))
  | defToInt (hw : w = false) (h : UnOp.toInt.accepts .uint = true) (k : Nat) {a : LTm C (.val .uint)} :
      a.SrcL c w l .num → LFml.SrcL c w l (.eq (.app1 (.unop .toInt h) a) (.var k))
  | defToUint (hw : w = false) (h : UnOp.toUint.accepts .int = true) (k : Nat) {a : LTm C (.val .int)} :
      a.SrcL c w l .num → LFml.SrcL c w l (.eq (.app1 (.unop .toUint h) a) (.var k))

/-- The source leaves without ledger reads. -/
abbrev LFml.Src (c w : Bool) : LFml C → Prop := LFml.SrcL c w .none

def LFml.nodes : LFml C → Nat
  | .tt => 1
  | .eq a b => a.nodes + b.nodes + 1
  | .not φ | .all _ _ φ => φ.nodes + 1
  | .and φ ψ | .imp φ ψ => φ.nodes + ψ.nodes + 1

def LFml.depth : LFml C → Nat
  | .tt => 1
  | .eq a b => max a.depth b.depth + 1
  | .not φ | .all _ _ φ => φ.depth + 1
  | .and φ ψ | .imp φ ψ => max φ.depth ψ.depth + 1

theorem LFml.depth_le_nodes (φ : LFml C) : φ.depth ≤ φ.nodes := by
  induction φ with
  | tt => exact Nat.le_refl _
  | eq a b =>
    have := LTm.depth_le_nodes a
    have := LTm.depth_le_nodes b
    simp only [LFml.depth, LFml.nodes]
    omega
  | not φ ih | all k p φ ih => simp only [LFml.depth, LFml.nodes]; omega
  | and φ ψ ih1 ih2 | imp φ ψ ih1 ih2 => simp only [LFml.depth, LFml.nodes]; omega

/-- What flattening a source formula returns. -/
def FlatFGood (l : LedgerMode) (φ : LFml C) (start : Nat) (a : FlattenedFormula φ start) : Prop :=
  a.formula.Arith (fun _ => True) (fun _ => True) (fun _ => l = .post) ∧ a.reads.length = φ.words ∧
    Laid a.reads start ∧ ∀ o ∈ a.reads, OccOK o

/-! ### The defining equations of cut atoms -/

theorem flattenFuel?_binLit {p : PrimTy} (op : BinOp) (h : op.accepts p = true) {x : LTm C (.val p)}
    {l : LedgerMode} (hpre : l ≠ .pre) (hx : x.SrcL false false l .num) (v : p.Denote) (d r start : Nat)
    (hd : (LTm.app2 (.binop op h) x (.app0 (.lit v))).depth ≤ d)
    (hr : (LTm.app2 (.binop op h) x (.app0 (.lit v))).nodes ≤ r) (hb : x.atomBound ≤ start)
    (hs : (LTm.app2 (.binop op h) x (.app0 (.lit v))).nodes ≤ 511) :
    ∃ a : Flattened x start, flattenFuel? d r (LTm.app2 (.binop op h) x (.app0 (.lit v))) start =
        some (Flattened.app2 (.binop op h) a (Flattened.pure (.app0 (.lit v)) a.next),
          r - (LTm.app2 (.binop op h) x (.app0 (.lit v))).nodes) ∧
      a.term.Num (fun _ => True) (fun _ => True) ∧ a.reads.length = x.words ∧ Laid a.reads start ∧
      a.term.nodes ≤ 2 * x.nodes ∧ ∀ o ∈ a.reads, OccOK o := by
  obtain ⟨d, rfl⟩ : ∃ m, d = m + 1 := ⟨d - 1, by simp only [LTm.depth] at hd; omega⟩
  obtain ⟨r, rfl⟩ : ∃ m, r = m + 1 := ⟨r - 1, by simp only [LTm.nodes] at hr; omega⟩
  simp only [LTm.depth, LTm.nodes] at hd hr hs
  obtain ⟨d, rfl⟩ : ∃ m, d = m + 1 := ⟨d - 1, by omega⟩
  obtain ⟨a, ha, aok, alen, alaid, -, an, aocc⟩ :=
    flattenFuel?_Src hpre hx (d + 1) r start (by omega) (by omega) hb (by omega)
  obtain ⟨k, hk⟩ : ∃ k, r - x.nodes = k + 1 := ⟨r - x.nodes - 1, by omega⟩
  refine ⟨a, ?_, aok, alen, alaid, an, aocc⟩
  show Option.bind (flattenFuel? (C := C) (d + 1) r x start) _ = _
  rw [ha]
  show Option.bind (flattenFuel? (C := C) (d + 1) (r - x.nodes) (LTm.app0 (.lit v)) a.next) _ = _
  rw [hk, flattenFuel?_lit]
  show some (Flattened.app2 (.binop op h) a (Flattened.pure (LTm.app0 (.lit v)) a.next), k) = _
  simp only [LTm.nodes, Option.some.injEq, Prod.mk.injEq, true_and]
  omega

theorem flattenFuel?_bin {p : PrimTy} (op : BinOp) (h : op.accepts p = true) {x y : LTm C (.val p)}
    {l : LedgerMode} (hpre : l ≠ .pre) (hx : x.SrcL false false l .num) (hy : y.SrcL false false l .num) (d r start : Nat)
    (hd : (LTm.app2 (.binop op h) x y).depth ≤ d) (hr : (LTm.app2 (.binop op h) x y).nodes ≤ r)
    (hb : max x.atomBound y.atomBound ≤ start) (hs : (LTm.app2 (.binop op h) x y).nodes ≤ 511) :
    ∃ (a : Flattened x start) (b : Flattened y a.next),
      flattenFuel? d r (LTm.app2 (.binop op h) x y) start =
        some (Flattened.app2 (.binop op h) a b, r - (LTm.app2 (.binop op h) x y).nodes) ∧
      a.term.Num (fun _ => True) (fun _ => True) ∧ b.term.Num (fun _ => True) (fun _ => True) ∧
      (a.reads ++ b.reads).length = x.words + y.words ∧ Laid (a.reads ++ b.reads) start ∧
      a.term.nodes ≤ 2 * x.nodes ∧ b.term.nodes ≤ 2 * y.nodes ∧ ∀ o ∈ a.reads ++ b.reads, OccOK o := by
  obtain ⟨d, rfl⟩ : ∃ m, d = m + 1 := ⟨d - 1, by simp only [LTm.depth] at hd; omega⟩
  obtain ⟨r, rfl⟩ : ∃ m, r = m + 1 := ⟨r - 1, by simp only [LTm.nodes] at hr; omega⟩
  simp only [LTm.depth, LTm.nodes] at hd hr hs
  obtain ⟨a, ha, aok, alen, alaid, aab, an, aocc⟩ :=
    flattenFuel?_Src hpre hx d r start (by omega) (by omega) (by omega) (by omega)
  obtain ⟨b, hb', bok, blen, blaid, bab, bn, bocc⟩ := flattenFuel?_Src hpre hy d (r - x.nodes) a.next
    (by omega) (by omega) (by simp only [Flattened.next]; omega) (by omega)
  refine ⟨a, b, ?_, aok, bok, by rw [List.length_append, alen, blen], alaid.append blaid, an, bn,
    fun o ho => (List.mem_append.mp ho).elim (aocc o) (bocc o)⟩
  show Option.bind (flattenFuel? (C := C) d r x start) _ = _
  rw [ha]
  show Option.bind (flattenFuel? (C := C) d (r - x.nodes) y a.next) _ = _
  rw [hb']
  show some (Flattened.app2 (.binop op h) a b, r - x.nodes - y.nodes) = _
  simp only [LTm.nodes, Option.some.injEq, Prod.mk.injEq, true_and]
  omega

theorem flattenFuel?_un {p : PrimTy} (op : UnOp) (h : op.accepts p = true) {x : LTm C (.val p)}
    {l : LedgerMode} (hpre : l ≠ .pre) (hx : x.SrcL false false l .num) (d r start : Nat)
    (hd : (LTm.app1 (.unop op h) x).depth ≤ d) (hr : (LTm.app1 (.unop op h) x).nodes ≤ r)
    (hb : x.atomBound ≤ start) (hs : (LTm.app1 (.unop op h) x).nodes ≤ 511) :
    ∃ a : Flattened x start, flattenFuel? d r (LTm.app1 (.unop op h) x) start =
        some (Flattened.app1 (.unop op h) a, r - (LTm.app1 (.unop op h) x).nodes) ∧
      a.term.Num (fun _ => True) (fun _ => True) ∧ a.reads.length = x.words ∧ Laid a.reads start ∧
      a.term.nodes ≤ 2 * x.nodes ∧ ∀ o ∈ a.reads, OccOK o := by
  obtain ⟨d, rfl⟩ : ∃ m, d = m + 1 := ⟨d - 1, by simp only [LTm.depth] at hd; omega⟩
  obtain ⟨r, rfl⟩ : ∃ m, r = m + 1 := ⟨r - 1, by simp only [LTm.nodes] at hr; omega⟩
  simp only [LTm.depth, LTm.nodes] at hd hr hs
  obtain ⟨a, ha, aok, alen, alaid, -, an, aocc⟩ :=
    flattenFuel?_Src hpre hx d r start (by omega) (by omega) hb (by omega)
  refine ⟨a, ?_, aok, alen, alaid, an, aocc⟩
  show Option.bind (flattenFuel? (C := C) d r x start) _ = _
  rw [ha]
  show some (Flattened.app1 (.unop op h) a, r - x.nodes) = _
  simp only [LTm.nodes, Option.some.injEq, Prod.mk.injEq, true_and]
  omega

theorem flattenFormulaFuel?_eqVar {r : PrimTy} (e : LTm C (.val r)) (k : Nat) (d rr start : Nat)
    (fe : Flattened e start) (he : flattenFuel? d rr e start = some (fe, rr - e.nodes))
    (hd : 1 ≤ d) (hr : e.nodes + 1 ≤ rr) :
    flattenFormulaFuel? (d + 1) (rr + 1) (.eq e (.var k)) start =
      some (FlattenedFormula.eq fe (Flattened.pure (.var k) fe.next),
        rr + 1 - (LFml.eq e (.var k)).nodes) := by
  obtain ⟨d, rfl⟩ : ∃ m, d = m + 1 := ⟨d - 1, by omega⟩
  obtain ⟨m, hm⟩ : ∃ m, rr - e.nodes = m + 1 := ⟨rr - e.nodes - 1, by omega⟩
  show Option.bind (flattenFuel? (C := C) (d + 1) rr e start) _ = _
  rw [he]
  show Option.bind (flattenFuel? (C := C) (d + 1) (rr - e.nodes) (LTm.var k) fe.next) _ = _
  rw [hm]
  show some (FlattenedFormula.eq fe (Flattened.pure (.var k) fe.next), m) = _
  simp only [LFml.nodes, LTm.nodes, Option.some.injEq, Prod.mk.injEq, true_and]
  omega

theorem flattenFormulaFuel?_Src {l : LedgerMode} (hpre : l ≠ .pre) :
    ∀ {φ : LFml C}, φ.SrcL false false l →
    ∀ (d r start : Nat), φ.depth ≤ d → φ.nodes ≤ r → φ.atomBound ≤ start → φ.nodes ≤ 511 →
      ∃ a, flattenFormulaFuel? (C := C) d r φ start = some (a, r - φ.nodes) ∧ FlatFGood l φ start a := by
  intro φ h
  induction h with
  | tt =>
    intro d r start hd hr hb hs
    obtain ⟨d, rfl⟩ : ∃ m, d = m + 1 := ⟨d - 1, by simp only [LFml.depth] at hd; omega⟩
    obtain ⟨r, rfl⟩ : ∃ m, r = m + 1 := ⟨r - 1, by simp only [LFml.nodes] at hr; omega⟩
    exact ⟨FlattenedFormula.tt start, by simp only [LFml.nodes, Nat.add_sub_cancel]; rfl,
      .tt, rfl, .nil start, fun _ h => by cases h⟩
  | @eqB x y hx hy =>
    intro d r start hd hr hb hs
    obtain ⟨d, rfl⟩ : ∃ m, d = m + 1 := ⟨d - 1, by simp only [LFml.depth] at hd; omega⟩
    obtain ⟨r, rfl⟩ : ∃ m, r = m + 1 := ⟨r - 1, by simp only [LFml.nodes] at hr; omega⟩
    simp only [LFml.depth, LFml.nodes, LFml.atomBound] at hd hr hb hs
    obtain ⟨a, ha, aok, alen, alaid, aab, an, aocc⟩ :=
      flattenFuel?_Src hpre hx d r start (by omega) (by omega) (by omega) (by omega)
    obtain ⟨b, hb', bok, blen, blaid, bab, bn, bocc⟩ := flattenFuel?_Src hpre hy d (r - x.nodes) a.next
      (by omega) (by omega) (by simp only [Flattened.next]; omega) (by omega)
    have hda := LTm.depth_le_nodes a.term
    have hdb := LTm.depth_le_nodes b.term
    refine ⟨FlattenedFormula.eq a b, ?_, LFml.Arith.eqB aok bok (by omega) (by omega), ?_, alaid.append blaid,
      fun o ho => (List.mem_append.mp ho).elim (aocc o) (bocc o)⟩
    · show Option.bind (flattenFuel? (C := C) d r x start) _ = _
      rw [ha]
      show Option.bind (flattenFuel? (C := C) d (r - x.nodes) y a.next) _ = _
      rw [hb']
      show some (FlattenedFormula.eq a b, r - x.nodes - y.nodes) = _
      simp only [LFml.nodes, Option.some.injEq, Prod.mk.injEq, true_and]
      omega
    · show (a.reads ++ b.reads).length = x.words + y.words
      rw [List.length_append, alen, blen]
  | @eqN p hp x y hx hy =>
    intro d r start hd hr hb hs
    obtain ⟨d, rfl⟩ : ∃ m, d = m + 1 := ⟨d - 1, by simp only [LFml.depth] at hd; omega⟩
    obtain ⟨r, rfl⟩ : ∃ m, r = m + 1 := ⟨r - 1, by simp only [LFml.nodes] at hr; omega⟩
    simp only [LFml.depth, LFml.nodes, LFml.atomBound] at hd hr hb hs
    obtain ⟨a, ha, aok, alen, alaid, aab, an, aocc⟩ :=
      flattenFuel?_Src hpre hx d r start (by omega) (by omega) (by omega) (by omega)
    obtain ⟨b, hb', bok, blen, blaid, bab, bn, bocc⟩ := flattenFuel?_Src hpre hy d (r - x.nodes) a.next
      (by omega) (by omega) (by simp only [Flattened.next]; omega) (by omega)
    have hda := LTm.depth_le_nodes a.term
    have hdb := LTm.depth_le_nodes b.term
    refine ⟨FlattenedFormula.eq a b, ?_, LFml.Arith.eqN hp aok bok (by omega) (by omega), ?_, alaid.append blaid,
      fun o ho => (List.mem_append.mp ho).elim (aocc o) (bocc o)⟩
    · show Option.bind (flattenFuel? (C := C) d r x start) _ = _
      rw [ha]
      show Option.bind (flattenFuel? (C := C) d (r - x.nodes) y a.next) _ = _
      rw [hb']
      show some (FlattenedFormula.eq a b, r - x.nodes - y.nodes) = _
      simp only [LFml.nodes, Option.some.injEq, Prod.mk.injEq, true_and]
      omega
    · show (a.reads ++ b.reads).length = x.words + y.words
      rw [List.length_append, alen, blen]
  | @not φ _ ih =>
    intro d r start hd hr hb hs
    obtain ⟨d, rfl⟩ : ∃ m, d = m + 1 := ⟨d - 1, by simp only [LFml.depth] at hd; omega⟩
    obtain ⟨r, rfl⟩ : ∃ m, r = m + 1 := ⟨r - 1, by simp only [LFml.nodes] at hr; omega⟩
    simp only [LFml.depth, LFml.nodes, LFml.atomBound] at hd hr hb hs
    obtain ⟨a, ha, aok, alen, alaid, aocc⟩ := ih d r start (by omega) (by omega) hb (by omega)
    refine ⟨FlattenedFormula.not a, ?_, .not aok, alen, alaid, aocc⟩
    show Option.bind (flattenFormulaFuel? (C := C) d r φ start) _ = _
    rw [ha]
    show some (FlattenedFormula.not a, r - φ.nodes) = _
    simp only [LFml.nodes, Option.some.injEq, Prod.mk.injEq, true_and]
    omega
  | @and φ ψ _ _ ihφ ihψ =>
    intro d r start hd hr hb hs
    obtain ⟨d, rfl⟩ : ∃ m, d = m + 1 := ⟨d - 1, by simp only [LFml.depth] at hd; omega⟩
    obtain ⟨r, rfl⟩ : ∃ m, r = m + 1 := ⟨r - 1, by simp only [LFml.nodes] at hr; omega⟩
    simp only [LFml.depth, LFml.nodes, LFml.atomBound] at hd hr hb hs
    obtain ⟨a, ha, aok, alen, alaid, aocc⟩ := ihφ d r start (by omega) (by omega) (by omega) (by omega)
    obtain ⟨b, hb', bok, blen, blaid, bocc⟩ := ihψ d (r - φ.nodes) a.next (by omega) (by omega)
      (by simp only [FlattenedFormula.next]; omega) (by omega)
    refine ⟨FlattenedFormula.and a b, ?_, .and aok bok, ?_, alaid.append blaid,
      fun o ho => (List.mem_append.mp ho).elim (aocc o) (bocc o)⟩
    · show Option.bind (flattenFormulaFuel? (C := C) d r φ start) _ = _
      rw [ha]
      show Option.bind (flattenFormulaFuel? (C := C) d (r - φ.nodes) ψ a.next) _ = _
      rw [hb']
      show some (FlattenedFormula.and a b, r - φ.nodes - ψ.nodes) = _
      simp only [LFml.nodes, Option.some.injEq, Prod.mk.injEq, true_and]
      omega
    · show (a.reads ++ b.reads).length = φ.words + ψ.words
      rw [List.length_append, alen, blen]
  | @imp φ ψ _ _ ihφ ihψ =>
    intro d r start hd hr hb hs
    obtain ⟨d, rfl⟩ : ∃ m, d = m + 1 := ⟨d - 1, by simp only [LFml.depth] at hd; omega⟩
    obtain ⟨r, rfl⟩ : ∃ m, r = m + 1 := ⟨r - 1, by simp only [LFml.nodes] at hr; omega⟩
    simp only [LFml.depth, LFml.nodes, LFml.atomBound] at hd hr hb hs
    obtain ⟨a, ha, aok, alen, alaid, aocc⟩ := ihφ d r start (by omega) (by omega) (by omega) (by omega)
    obtain ⟨b, hb', bok, blen, blaid, bocc⟩ := ihψ d (r - φ.nodes) a.next (by omega) (by omega)
      (by simp only [FlattenedFormula.next]; omega) (by omega)
    refine ⟨FlattenedFormula.imp a b, ?_, .imp aok bok, ?_, alaid.append blaid,
      fun o ho => (List.mem_append.mp ho).elim (aocc o) (bocc o)⟩
    · show Option.bind (flattenFormulaFuel? (C := C) d r φ start) _ = _
      rw [ha]
      show Option.bind (flattenFormulaFuel? (C := C) d (r - φ.nodes) ψ a.next) _ = _
      rw [hb']
      show some (FlattenedFormula.imp a b, r - φ.nodes - ψ.nodes) = _
      simp only [LFml.nodes, Option.some.injEq, Prod.mk.injEq, true_and]
      omega
    · show (a.reads ++ b.reads).length = φ.words + ψ.words
      rw [List.length_append, alen, blen]

  | @defDiv hw h v hv k x hx =>
    intro d r start hd hr hb hs
    simp only [LFml.depth, LFml.nodes, LFml.atomBound, LTm.depth, LTm.nodes, LTm.atomBound] at hd hr hb hs
    obtain ⟨d, rfl⟩ : ∃ m, d = m + 1 := ⟨d - 1, by omega⟩
    obtain ⟨r, rfl⟩ : ∃ m, r = m + 1 := ⟨r - 1, by omega⟩
    obtain ⟨a, ha, aok, alen, alaid, an, aocc⟩ := flattenFuel?_binLit .div h hpre hx v d r start
      (by simp only [LTm.depth]; omega) (by simp only [LTm.nodes]; omega) (by omega)
      (by simp only [LTm.nodes]; omega)
    have hda := LTm.depth_le_nodes a.term
    refine ⟨_, flattenFormulaFuel?_eqVar _ k d r start _ ha (by omega) (by simp only [LTm.nodes]; omega),
      LFml.Arith.defDiv h v hv k aok trivial (by omega), ?_, ?_, ?_⟩
    · show ((a.reads ++ []) ++ []).length = _
      simp only [List.append_nil, LFml.words, LTm.words, alen, Nat.add_zero]
    · show Laid ((a.reads ++ []) ++ []) start
      simpa only [List.append_nil] using alaid
    · intro o ho
      change o ∈ ((a.reads ++ []) ++ []) at ho
      simp only [List.append_nil] at ho
      exact aocc o ho
  | @defDivI hw h v hv k x hx =>
    intro d r start hd hr hb hs
    simp only [LFml.depth, LFml.nodes, LFml.atomBound, LTm.depth, LTm.nodes, LTm.atomBound] at hd hr hb hs
    obtain ⟨d, rfl⟩ : ∃ m, d = m + 1 := ⟨d - 1, by omega⟩
    obtain ⟨r, rfl⟩ : ∃ m, r = m + 1 := ⟨r - 1, by omega⟩
    obtain ⟨a, ha, aok, alen, alaid, an, aocc⟩ := flattenFuel?_binLit .div h hpre hx v d r start
      (by simp only [LTm.depth]; omega) (by simp only [LTm.nodes]; omega) (by omega)
      (by simp only [LTm.nodes]; omega)
    have hda := LTm.depth_le_nodes a.term
    refine ⟨_, flattenFormulaFuel?_eqVar _ k d r start _ ha (by omega) (by simp only [LTm.nodes]; omega),
      LFml.Arith.defDivI h v hv k aok trivial (by omega), ?_, ?_, ?_⟩
    · show ((a.reads ++ []) ++ []).length = _
      simp only [List.append_nil, LFml.words, LTm.words, alen, Nat.add_zero]
    · show Laid ((a.reads ++ []) ++ []) start
      simpa only [List.append_nil] using alaid
    · intro o ho
      change o ∈ ((a.reads ++ []) ++ []) at ho
      simp only [List.append_nil] at ho
      exact aocc o ho
  | @defShr hw p h v k x hx =>
    intro d r start hd hr hb hs
    simp only [LFml.depth, LFml.nodes, LFml.atomBound, LTm.depth, LTm.nodes, LTm.atomBound] at hd hr hb hs
    obtain ⟨d, rfl⟩ : ∃ m, d = m + 1 := ⟨d - 1, by omega⟩
    obtain ⟨r, rfl⟩ : ∃ m, r = m + 1 := ⟨r - 1, by omega⟩
    obtain ⟨a, ha, aok, alen, alaid, an, aocc⟩ := flattenFuel?_binLit .shr h hpre hx v d r start
      (by simp only [LTm.depth]; omega) (by simp only [LTm.nodes]; omega) (by omega)
      (by simp only [LTm.nodes]; omega)
    have hda := LTm.depth_le_nodes a.term
    refine ⟨_, flattenFormulaFuel?_eqVar _ k d r start _ ha (by omega) (by simp only [LTm.nodes]; omega),
      LFml.Arith.defShr h v k aok trivial (by omega), ?_, ?_, ?_⟩
    · show ((a.reads ++ []) ++ []).length = _
      simp only [List.append_nil, LFml.words, LTm.words, alen, Nat.add_zero]
    · show Laid ((a.reads ++ []) ++ []) start
      simpa only [List.append_nil] using alaid
    · intro o ho
      change o ∈ ((a.reads ++ []) ++ []) at ho
      simp only [List.append_nil] at ho
      exact aocc o ho
  | @defAddW hw h k x y hx hy =>
    intro d r start hd hr hb hs
    simp only [LFml.depth, LFml.nodes, LFml.atomBound, LTm.depth, LTm.nodes, LTm.atomBound] at hd hr hb hs
    obtain ⟨d, rfl⟩ : ∃ m, d = m + 1 := ⟨d - 1, by omega⟩
    obtain ⟨r, rfl⟩ : ∃ m, r = m + 1 := ⟨r - 1, by omega⟩
    obtain ⟨a, b, ha, aok, bok, alen, alaid, an, bn, aocc⟩ := flattenFuel?_bin .addW h hpre hx hy d r start
      (by simp only [LTm.depth]; omega) (by simp only [LTm.nodes]; omega) (by omega)
      (by simp only [LTm.nodes]; omega)
    have hda := LTm.depth_le_nodes a.term
    have hdb := LTm.depth_le_nodes b.term
    refine ⟨_, flattenFormulaFuel?_eqVar _ k d r start _ ha (by omega) (by simp only [LTm.nodes]; omega),
      LFml.Arith.defAddW h k aok bok trivial (by omega) (by omega), ?_, ?_, ?_⟩
    · show ((a.reads ++ b.reads) ++ []).length = _
      simp only [List.append_nil, LFml.words, LTm.words, alen, Nat.add_zero]
    · show Laid ((a.reads ++ b.reads) ++ []) start
      simpa only [List.append_nil] using alaid
    · intro o ho
      change o ∈ ((a.reads ++ b.reads) ++ []) at ho
      simp only [List.append_nil] at ho
      exact aocc o ho
  | @defSubW hw h k x y hx hy =>
    intro d r start hd hr hb hs
    simp only [LFml.depth, LFml.nodes, LFml.atomBound, LTm.depth, LTm.nodes, LTm.atomBound] at hd hr hb hs
    obtain ⟨d, rfl⟩ : ∃ m, d = m + 1 := ⟨d - 1, by omega⟩
    obtain ⟨r, rfl⟩ : ∃ m, r = m + 1 := ⟨r - 1, by omega⟩
    obtain ⟨a, b, ha, aok, bok, alen, alaid, an, bn, aocc⟩ := flattenFuel?_bin .subW h hpre hx hy d r start
      (by simp only [LTm.depth]; omega) (by simp only [LTm.nodes]; omega) (by omega)
      (by simp only [LTm.nodes]; omega)
    have hda := LTm.depth_le_nodes a.term
    have hdb := LTm.depth_le_nodes b.term
    refine ⟨_, flattenFormulaFuel?_eqVar _ k d r start _ ha (by omega) (by simp only [LTm.nodes]; omega),
      LFml.Arith.defSubW h k aok bok trivial (by omega) (by omega), ?_, ?_, ?_⟩
    · show ((a.reads ++ b.reads) ++ []).length = _
      simp only [List.append_nil, LFml.words, LTm.words, alen, Nat.add_zero]
    · show Laid ((a.reads ++ b.reads) ++ []) start
      simpa only [List.append_nil] using alaid
    · intro o ho
      change o ∈ ((a.reads ++ b.reads) ++ []) at ho
      simp only [List.append_nil] at ho
      exact aocc o ho
  | @defToInt hw h k x hx =>
    intro d r start hd hr hb hs
    simp only [LFml.depth, LFml.nodes, LFml.atomBound, LTm.depth, LTm.nodes, LTm.atomBound] at hd hr hb hs
    obtain ⟨d, rfl⟩ : ∃ m, d = m + 1 := ⟨d - 1, by omega⟩
    obtain ⟨r, rfl⟩ : ∃ m, r = m + 1 := ⟨r - 1, by omega⟩
    obtain ⟨a, ha, aok, alen, alaid, an, aocc⟩ := flattenFuel?_un .toInt h hpre hx d r start
      (by simp only [LTm.depth]; omega) (by simp only [LTm.nodes]; omega) (by omega)
      (by simp only [LTm.nodes]; omega)
    have hda := LTm.depth_le_nodes a.term
    refine ⟨_, flattenFormulaFuel?_eqVar _ k d r start _ ha (by omega) (by simp only [LTm.nodes]; omega),
      LFml.Arith.defToInt h k aok trivial (by omega), ?_, ?_, ?_⟩
    · show (a.reads ++ []).length = _
      simp only [List.append_nil, LFml.words, LTm.words, alen, Nat.add_zero]
    · show Laid (a.reads ++ []) start
      simpa only [List.append_nil] using alaid
    · intro o ho
      change o ∈ (a.reads ++ []) at ho
      simp only [List.append_nil] at ho
      exact aocc o ho
  | @defToUint hw h k x hx =>
    intro d r start hd hr hb hs
    simp only [LFml.depth, LFml.nodes, LFml.atomBound, LTm.depth, LTm.nodes, LTm.atomBound] at hd hr hb hs
    obtain ⟨d, rfl⟩ : ∃ m, d = m + 1 := ⟨d - 1, by omega⟩
    obtain ⟨r, rfl⟩ : ∃ m, r = m + 1 := ⟨r - 1, by omega⟩
    obtain ⟨a, ha, aok, alen, alaid, an, aocc⟩ := flattenFuel?_un .toUint h hpre hx d r start
      (by simp only [LTm.depth]; omega) (by simp only [LTm.nodes]; omega) (by omega)
      (by simp only [LTm.nodes]; omega)
    have hda := LTm.depth_le_nodes a.term
    refine ⟨_, flattenFormulaFuel?_eqVar _ k d r start _ ha (by omega) (by simp only [LTm.nodes]; omega),
      LFml.Arith.defToUint h k aok trivial (by omega), ?_, ?_, ?_⟩
    · show (a.reads ++ []).length = _
      simp only [List.append_nil, LFml.words, LTm.words, alen, Nat.add_zero]
    · show Laid (a.reads ++ []) start
      simpa only [List.append_nil] using alaid
    · intro o ho
      change o ∈ (a.reads ++ []) at ho
      simp only [List.append_nil] at ho
      exact aocc o ho

/-! ## Alias constraints -/

/-- A key of the flattened leaf: scalar, of bounded depth. -/
def KeyOK {p : PrimTy} (t : LTm C (.val p)) : Prop :=
  t.Num (fun _ => True) (fun _ => True) ∧ t.depth ≤ 1022

theorem LFml.Arith.ofNum {p : PrimTy} {a b : LTm C (.val p)} (ha : KeyOK a) (hb : KeyOK b) :
    (LFml.eq a b).Arith (fun _ => True) (fun _ => True) := by
  have hda := ha.2
  have hdb := hb.2
  cases p with
  | bool =>
    have hA : a.BoolV (fun _ => True) (fun _ => True) := LTm.Num.toBoolV ha.1 rfl
    have hB : b.BoolV (fun _ => True) (fun _ => True) := LTm.Num.toBoolV hb.1 rfl
    exact .eqB hA hB (by omega) (by omega)
  | uint => exact .eqN rfl ha.1 hb.1 (by omega) (by omega)
  | int => exact .eqN rfl ha.1 hb.1 (by omega) (by omega)

theorem KeyOK.var_cast {p p' : PrimTy} (e : p' = p) (k : Nat) :
    KeyOK (e ▸ (LTm.var (C := C) (p := p') k) : LTm C (.val p)) := by
  subst e
  exact ⟨.var _ trivial, by show 1 ≤ 1022; omega⟩

/-- Every comparison of a tree satisfies `K`. -/
inductive CTree.Keys {α : Type} (K : {p : PrimTy} → LTm C (.val p) → Prop) : CTree C α → Prop
  | leaf (a : α) : CTree.Keys K (.leaf a)
  | node {p : PrimTy} {a b : LTm C (.val p)} {t e : CTree C α} :
      K a → K b → CTree.Keys K t → CTree.Keys K e → CTree.Keys K (.node a b t e)

theorem keyTree_keys {α : Type} {K : {p : PrimTy} → LTm C (.val p) → Prop} {p : PrimTy}
    {a b : LTm C (.val p)} {t e : CTree C α} (ha : K a) (hb : K b) (ht : t.Keys K)
    (he : e.Keys K) : (keyTree a b t e).Keys K := by
  unfold keyTree
  cases keyCmp a b with
  | none => exact .node ha hb ht he
  | some v => cases v; exact he; exact ht

theorem TSegs.FK.cast {K : {k : PrimTy} → LTm C (.val k) → Prop} {T T' U : Ty} (e : T' = T)
    {q : TSegs C T' U} (hq : q.FK K) : (e ▸ q : TSegs C T U).FK K := by
  subst e
  exact hq

theorem relSegsM_keys {K : {k : PrimTy} → LTm C (.val k) → Prop} :
    ∀ {S T : Ty} {p : TSegs C S T}, p.FK K → ∀ {U : Ty} {q : TSegs C S U}, q.FK K →
      (relSegsM p q).Keys K := by
  intro S T p hp
  induction hp with
  | nil => intro U q _; exact .leaf _
  | @field s f T' U' h r _ ih =>
    intro U q hq
    cases hq with
    | nil => exact .leaf _
    | @field _ f' T'' _ h' r' hr' =>
      show (if e : f = f' then relSegsM r (field_ty_eq h h' rfl e ▸ r') else .leaf none).Keys K
      by_cases e : f = f'
      · rw [dif_pos e]
        exact ih (hr'.cast _)
      · rw [dif_neg e]
        exact .leaf _
  | @key k V U' i r hi _ ih =>
    intro U q hq
    cases hq with
    | nil => exact .leaf _
    | @key _ _ _ j r' hj hr' =>
      exact keyTree_keys hi hj (ih hr') (.leaf _)

theorem CTree.toFormula_arith {α : Type} {leaf : α → LFml C}
    (hl : ∀ x, (leaf x).Arith (fun _ => True) (fun _ => True)) :
    ∀ {tree : CTree C α}, tree.Keys (fun t => KeyOK t) →
      (tree.toFormula leaf).Arith (fun _ => True) (fun _ => True) := by
  intro tree h
  induction h with
  | leaf x => exact hl x
  | node ha hb _ _ iht ihe =>
    exact .and (.imp (LFml.Arith.ofNum ha hb) iht) (.imp (.not (LFml.Arith.ofNum ha hb)) ihe)

theorem SPath.alias_arith {p q : PrimTy} {P : SPath C (.prim p)} {Q : SPath C (.prim q)}
    (hP : P.segs.FK (fun t => KeyOK t)) (hQ : Q.segs.FK (fun t => KeyOK t)) :
    (P.alias Q).Arith (fun _ => True) (fun _ => True) := by
  unfold SPath.alias
  by_cases h : P.r = Q.r
  · rw [dif_pos h, relSegs_eq_relSegsM]
    refine CTree.toFormula_arith ?_ (relSegsM_keys hP (hQ.cast _))
    intro x
    cases x
    · exact .not .tt
    · exact .tt
  · rw [dif_neg h]
    exact .not .tt

theorem ReadOccurrence.constraint_arith {r q : ReadOccurrence C} (hr : OccOK r) (hq : OccOK q) :
    (r.constraint q).Arith (fun _ => True) (fun _ => True) := by
  have hrt : KeyOK r.guard.test := ⟨hr.1, hr.2.1⟩
  have hqt : KeyOK q.guard.test := ⟨hq.1, hq.2.1⟩
  refine .imp (LFml.Arith.ofNum hrt hrt) (.imp (LFml.Arith.ofNum hqt hqt) ?_)
  show (SymbolicRead.constraint ⟨r.prim, r.path, .var r.slot⟩ ⟨q.prim, q.path, .var q.slot⟩).Arith _ _
  unfold SymbolicRead.constraint
  by_cases h : r.prim = q.prim
  · rw [dif_pos h]
    exact .imp (SPath.alias_arith hr.2.2 hq.2.2)
      (LFml.Arith.ofNum ⟨.var _ trivial, by show 1 ≤ 1022; omega⟩ (KeyOK.var_cast h.symm q.slot))
  · rw [dif_neg h]
    exact .tt

theorem ReadOccurrence.constraints_arith {rs : List (ReadOccurrence C)} (h : ∀ o ∈ rs, OccOK o) :
    (ReadOccurrence.constraints rs).Arith (fun _ => True) (fun _ => True) := by
  unfold ReadOccurrence.constraints
  generalize hL : rs.flatMap (fun r => rs.map fun q => r.constraint q) = L
  have hL' : ∀ φ ∈ L, φ.Arith (fun _ => True) (fun _ => True) := by
    intro φ hφ
    rw [← hL] at hφ
    obtain ⟨r, hr, hm⟩ := List.mem_flatMap.mp hφ
    obtain ⟨q, hq, rfl⟩ := List.mem_map.mp hm
    exact ReadOccurrence.constraint_arith (h r hr) (h q hq)
  clear hL
  induction L with
  | nil => exact .tt
  | cons φ L ih =>
    exact .and (hL' φ List.mem_cons_self) (ih fun ψ hψ => hL' ψ (List.mem_cons_of_mem φ hψ))

/-! ## Read-free checks -/

theorem LTm.ZNum.readFree {ps : Parameter → Prop} {es : EnvKey → Prop} {L : PrimTy.uint.Denote → Prop} :
    ∀ {t : LTm C .kint}, t.ZNum ps es L → ReadFreeOf t := by
  intro t h
  induction h with
  | zlit n => exact ⟨.zlit n, rfl, rfl⟩
  | @toInt a ha =>
    obtain ⟨e, he, h0⟩ := ha.readFree
    exact ⟨.toInt e, by change (ReadExpr.ofTerm? a).map ReadExpr.toInt = _; rw [he]; rfl, h0⟩
  | @add h x y _ _ iha ihb =>
    obtain ⟨ea, hea, ha0⟩ := iha
    obtain ⟨eb, heb, hb0⟩ := ihb
    refine ⟨ReadExpr.zbin .add h ea eb, ?_, ?_⟩
    · change (Option.bind (ReadExpr.ofTerm? x) fun x => Option.bind (ReadExpr.ofTerm? y) fun y =>
        some (ReadExpr.zbin .add h x y)) = _
      rw [hea, heb]; rfl
    · change ea.readBound + eb.readBound = 0
      rw [ha0, hb0]
  | @sub h x y _ _ iha ihb =>
    obtain ⟨ea, hea, ha0⟩ := iha
    obtain ⟨eb, heb, hb0⟩ := ihb
    refine ⟨ReadExpr.zbin .sub h ea eb, ?_, ?_⟩
    · change (Option.bind (ReadExpr.ofTerm? x) fun x => Option.bind (ReadExpr.ofTerm? y) fun y =>
        some (ReadExpr.zbin .sub h x y)) = _
      rw [hea, heb]; rfl
    · change ea.readBound + eb.readBound = 0
      rw [ha0, hb0]
  | @mulL h n y _ ihb =>
    obtain ⟨eb, heb, hb0⟩ := ihb
    refine ⟨.zbin .mul h (.zlit n) eb, ?_, ?_⟩
    · change (Option.bind (ReadExpr.ofTerm? (LTm.app0 (C := C) (.zlit n))) fun x =>
        Option.bind (ReadExpr.ofTerm? y) fun y => some (ReadExpr.zbin .mul h x y)) = _
      rw [heb]; rfl
    · change 0 + eb.readBound = 0
      rw [hb0]
  | @mulR h x n _ iha =>
    obtain ⟨ea, hea, ha0⟩ := iha
    refine ⟨.zbin .mul h ea (.zlit n), ?_, ?_⟩
    · change (Option.bind (ReadExpr.ofTerm? x) fun x =>
        Option.bind (ReadExpr.ofTerm? (LTm.app0 (C := C) (.zlit n))) fun y =>
          some (ReadExpr.zbin .mul h x y)) = _
      rw [hea]; rfl
    · change ea.readBound + 0 = 0
      rw [ha0]
  | netLit v _ =>
    refine ⟨.net (.lit v), rfl, rfl⟩
  | @zseq q d a hd _ iha =>
    obtain ⟨ed, hed, hd0⟩ := hd.readFree
    obtain ⟨ea, hea, ha0⟩ := iha
    refine ⟨.seq ed ea, ?_, ?_⟩
    · change (Option.bind (ReadExpr.ofTerm? d) fun x => Option.bind (ReadExpr.ofTerm? a) fun y =>
        some (ReadExpr.seq x y)) = _
      rw [hed, hea]; rfl
    · change ed.readBound + ea.readBound = 0
      rw [hd0, ha0]

theorem LTm.BoolV.readFree {ps : Parameter → Prop} {es : EnvKey → Prop} {L : PrimTy.uint.Denote → Prop} :
    ∀ {t : LTm C (.val .bool)}, t.BoolV ps es L → ReadFreeOf t := by
  intro t h
  induction h with
  | var k _ => exact ⟨.var k, rfl, rfl⟩
  | lit v => exact ⟨.lit (p := .bool) v, rfl, rfl⟩
  | err => exact ⟨.err, rfl, rfl⟩
  | @not x _ ih =>
    obtain ⟨e, he, h0⟩ := ih
    refine ⟨.unop .not (p := .bool) rfl e, ?_, h0⟩
    change (ReadExpr.ofTerm? x).map (ReadExpr.unop .not rfl) = _
    rw [he]; rfl
  | @and x y _ _ iha ihb =>
    obtain ⟨ea, hea, ha0⟩ := iha
    obtain ⟨eb, heb, hb0⟩ := ihb
    refine ⟨.binop .and rfl ea eb, ?_, ?_⟩
    · change (Option.bind (ReadExpr.ofTerm? x) fun x => Option.bind (ReadExpr.ofTerm? y) fun y =>
        some (ReadExpr.binop .and rfl x y)) = _
      rw [hea, heb]; rfl
    · change ea.readBound + eb.readBound = 0
      rw [ha0, hb0]
  | @or x y _ _ iha ihb =>
    obtain ⟨ea, hea, ha0⟩ := iha
    obtain ⟨eb, heb, hb0⟩ := ihb
    refine ⟨.binop .or rfl ea eb, ?_, ?_⟩
    · change (Option.bind (ReadExpr.ofTerm? x) fun x => Option.bind (ReadExpr.ofTerm? y) fun y =>
        some (ReadExpr.binop .or rfl x y)) = _
      rw [hea, heb]; rfl
    · change ea.readBound + eb.readBound = 0
      rw [ha0, hb0]
  | @eqB x y _ _ iha ihb =>
    obtain ⟨ea, hea, ha0⟩ := iha
    obtain ⟨eb, heb, hb0⟩ := ihb
    refine ⟨.binop .eqB rfl ea eb, ?_, ?_⟩
    · change (Option.bind (ReadExpr.ofTerm? x) fun x => Option.bind (ReadExpr.ofTerm? y) fun y =>
        some (ReadExpr.binop .eqB rfl x y)) = _
      rw [hea, heb]; rfl
    · change ea.readBound + eb.readBound = 0
      rw [ha0, hb0]
  | @neB x y _ _ iha ihb =>
    obtain ⟨ea, hea, ha0⟩ := iha
    obtain ⟨eb, heb, hb0⟩ := ihb
    refine ⟨.binop .neB rfl ea eb, ?_, ?_⟩
    · change (Option.bind (ReadExpr.ofTerm? x) fun x => Option.bind (ReadExpr.ofTerm? y) fun y =>
        some (ReadExpr.binop .neB rfl x y)) = _
      rw [hea, heb]; rfl
    · change ea.readBound + eb.readBound = 0
      rw [ha0, hb0]
  | @eqN p hp x y ha hb =>
    obtain ⟨ea, hea, ha0⟩ := LTm.Num.readFree ha
    obtain ⟨eb, heb, hb0⟩ := LTm.Num.readFree hb
    refine ⟨.binop .eqB rfl ea eb, ?_, ?_⟩
    · change (Option.bind (ReadExpr.ofTerm? x) fun x => Option.bind (ReadExpr.ofTerm? y) fun y =>
        some (ReadExpr.binop .eqB rfl x y)) = _
      rw [hea, heb]; rfl
    · change ea.readBound + eb.readBound = 0
      rw [ha0, hb0]
  | @neN p hp x y ha hb =>
    obtain ⟨ea, hea, ha0⟩ := LTm.Num.readFree ha
    obtain ⟨eb, heb, hb0⟩ := LTm.Num.readFree hb
    refine ⟨.binop .neB rfl ea eb, ?_, ?_⟩
    · change (Option.bind (ReadExpr.ofTerm? x) fun x => Option.bind (ReadExpr.ofTerm? y) fun y =>
        some (ReadExpr.binop .neB rfl x y)) = _
      rw [hea, heb]; rfl
    · change ea.readBound + eb.readBound = 0
      rw [ha0, hb0]
  | @lt p h x y ha hb =>
    obtain ⟨ea, hea, ha0⟩ := LTm.Num.readFree ha
    obtain ⟨eb, heb, hb0⟩ := LTm.Num.readFree hb
    refine ⟨.binop .lt h ea eb, ?_, ?_⟩
    · change (Option.bind (ReadExpr.ofTerm? x) fun x => Option.bind (ReadExpr.ofTerm? y) fun y =>
        some (ReadExpr.binop .lt h x y)) = _
      rw [hea, heb]; rfl
    · change ea.readBound + eb.readBound = 0
      rw [ha0, hb0]
  | @gt p h x y ha hb =>
    obtain ⟨ea, hea, ha0⟩ := LTm.Num.readFree ha
    obtain ⟨eb, heb, hb0⟩ := LTm.Num.readFree hb
    refine ⟨.binop .gt h ea eb, ?_, ?_⟩
    · change (Option.bind (ReadExpr.ofTerm? x) fun x => Option.bind (ReadExpr.ofTerm? y) fun y =>
        some (ReadExpr.binop .gt h x y)) = _
      rw [hea, heb]; rfl
    · change ea.readBound + eb.readBound = 0
      rw [ha0, hb0]
  | @le p h x y ha hb =>
    obtain ⟨ea, hea, ha0⟩ := LTm.Num.readFree ha
    obtain ⟨eb, heb, hb0⟩ := LTm.Num.readFree hb
    refine ⟨.binop .le h ea eb, ?_, ?_⟩
    · change (Option.bind (ReadExpr.ofTerm? x) fun x => Option.bind (ReadExpr.ofTerm? y) fun y =>
        some (ReadExpr.binop .le h x y)) = _
      rw [hea, heb]; rfl
    · change ea.readBound + eb.readBound = 0
      rw [ha0, hb0]
  | @ge p h x y ha hb =>
    obtain ⟨ea, hea, ha0⟩ := LTm.Num.readFree ha
    obtain ⟨eb, heb, hb0⟩ := LTm.Num.readFree hb
    refine ⟨.binop .ge h ea eb, ?_, ?_⟩
    · change (Option.bind (ReadExpr.ofTerm? x) fun x => Option.bind (ReadExpr.ofTerm? y) fun y =>
        some (ReadExpr.binop .ge h x y)) = _
      rw [hea, heb]; rfl
    · change ea.readBound + eb.readBound = 0
      rw [ha0, hb0]
  | @seqB d a _ _ ihd iha =>
    obtain ⟨ed, hed, hd0⟩ := ihd
    obtain ⟨ea, hea, ha0⟩ := iha
    refine ⟨.seq ed ea, ?_, ?_⟩
    · change (Option.bind (ReadExpr.ofTerm? d) fun x => Option.bind (ReadExpr.ofTerm? a) fun y =>
        some (ReadExpr.seq x y)) = _
      rw [hed, hea]; rfl
    · change ed.readBound + ea.readBound = 0
      rw [hd0, ha0]
  | @seqN q hq d a hd _ iha =>
    obtain ⟨ed, hed, hd0⟩ := LTm.Num.readFree hd
    obtain ⟨ea, hea, ha0⟩ := iha
    refine ⟨.seq ed ea, ?_, ?_⟩
    · change (Option.bind (ReadExpr.ofTerm? d) fun x => Option.bind (ReadExpr.ofTerm? a) fun y =>
        some (ReadExpr.seq x y)) = _
      rw [hed, hea]; rfl
    · change ed.readBound + ea.readBound = 0
      rw [hd0, ha0]
  | @zcmp op h x y ha hb =>
    have iha := ha.readFree
    have ihb := hb.readFree
    obtain ⟨ea, hea, ha0⟩ := iha
    obtain ⟨eb, heb, hb0⟩ := ihb
    refine ⟨ReadExpr.zcmp op h ea eb, ?_, ?_⟩
    · change (Option.bind (ReadExpr.ofTerm? x) fun x => Option.bind (ReadExpr.ofTerm? y) fun y =>
        some (ReadExpr.zcmp op h x y)) = _
      rw [hea, heb]; rfl
    · change ea.readBound + eb.readBound = 0
      rw [ha0, hb0]

theorem ReadFreeOf.binop (op : BinOp) {p : PrimTy} (h : op.accepts p = true) {x y : LTm C (.val p)}
    (hx : ReadFreeOf x) (hy : ReadFreeOf y) : ReadFreeOf (LTm.app2 (.binop op h) x y) := by
  obtain ⟨ex, hex, hx0⟩ := hx
  obtain ⟨ey, hey, hy0⟩ := hy
  refine ⟨.binop op h ex ey, ?_, ?_⟩
  · change (Option.bind (ReadExpr.ofTerm? x) fun x' => Option.bind (ReadExpr.ofTerm? y) fun y' =>
      some (ReadExpr.binop op h x' y')) = _
    rw [hex, hey]; rfl
  · change ex.readBound + ey.readBound = 0
    rw [hx0, hy0]

theorem ReadFreeOf.unop (op : UnOp) {p : PrimTy} (h : op.accepts p = true) {x : LTm C (.val p)}
    (hx : ReadFreeOf x) : ReadFreeOf (LTm.app1 (.unop op h) x) := by
  obtain ⟨ex, hex, hx0⟩ := hx
  exact ⟨.unop op h ex, by change (ReadExpr.ofTerm? x).map (ReadExpr.unop op h) = _; rw [hex]; rfl, hx0⟩

theorem ReadFreeOf.lit {p : PrimTy} (v : p.Denote) : ReadFreeOf (LTm.app0 (C := C) (.lit v)) :=
  ⟨.lit v, by cases p <;> rfl, rfl⟩

theorem ReadFreeOf.var {p : PrimTy} (k : Nat) : ReadFreeOf (LTm.var (C := C) (p := p) k) :=
  ⟨.var k, rfl, rfl⟩

theorem ReadFreeOf.eq {p : PrimTy} {a b : LTm C (.val p)} (ha : ReadFreeOf a) (hb : ReadFreeOf b) :
    ∃ rf, ReadFormula.ofFormula? (LFml.eq a b) = some rf ∧ rf.readBound = 0 := by
  obtain ⟨ea, hea, ha0⟩ := ha
  obtain ⟨eb, heb, hb0⟩ := hb
  refine ⟨.eq ea eb, ?_, ?_⟩
  · change (Option.bind (ReadExpr.ofTerm? a) fun x => Option.bind (ReadExpr.ofTerm? b) fun y =>
      some (ReadFormula.eq x y)) = _
    rw [hea, heb]; rfl
  · change ea.readBound + eb.readBound = 0
    rw [ha0, hb0]

theorem LFml.Arith.readFree {ps : Parameter → Prop} {es : EnvKey → Prop} {L : PrimTy.uint.Denote → Prop} :
    ∀ {φ : LFml C}, φ.Arith ps es L → ∃ rf, ReadFormula.ofFormula? φ = some rf ∧ rf.readBound = 0 := by
  intro φ h
  induction h with
  | tt => exact ⟨.tt, rfl, rfl⟩
  | @eqB a b ha hb _ _ =>
    obtain ⟨ea, hea, ha0⟩ := LTm.BoolV.readFree ha
    obtain ⟨eb, heb, hb0⟩ := LTm.BoolV.readFree hb
    refine ⟨.eq ea eb, ?_, ?_⟩
    · change (Option.bind (ReadExpr.ofTerm? a) fun x => Option.bind (ReadExpr.ofTerm? b) fun y =>
        some (ReadFormula.eq x y)) = _
      rw [hea, heb]; rfl
    · change ea.readBound + eb.readBound = 0
      rw [ha0, hb0]
  | @eqN p hp a b ha hb _ _ =>
    obtain ⟨ea, hea, ha0⟩ := LTm.Num.readFree ha
    obtain ⟨eb, heb, hb0⟩ := LTm.Num.readFree hb
    refine ⟨.eq ea eb, ?_, ?_⟩
    · change (Option.bind (ReadExpr.ofTerm? a) fun x => Option.bind (ReadExpr.ofTerm? b) fun y =>
        some (ReadFormula.eq x y)) = _
      rw [hea, heb]; rfl
    · change ea.readBound + eb.readBound = 0
      rw [ha0, hb0]
  | @not φ _ ih =>
    obtain ⟨e, he, h0⟩ := ih
    refine ⟨.not e, ?_, h0⟩
    change (ReadFormula.ofFormula? φ).map ReadFormula.not = _
    rw [he]; rfl
  | @and φ ψ _ _ ihφ ihψ =>
    obtain ⟨a, ha, ha0⟩ := ihφ
    obtain ⟨b, hb, hb0⟩ := ihψ
    refine ⟨.and a b, ?_, ?_⟩
    · change (Option.bind (ReadFormula.ofFormula? φ) fun x => Option.bind (ReadFormula.ofFormula? ψ)
        fun y => some (ReadFormula.and x y)) = _
      rw [ha, hb]; rfl
    · change a.readBound + b.readBound = 0
      rw [ha0, hb0]
  | @imp φ ψ _ _ ihφ ihψ =>
    obtain ⟨a, ha, ha0⟩ := ihφ
    obtain ⟨b, hb, hb0⟩ := ihψ
    refine ⟨.imp a b, ?_, ?_⟩
    · change (Option.bind (ReadFormula.ofFormula? φ) fun x => Option.bind (ReadFormula.ofFormula? ψ)
        fun y => some (ReadFormula.imp x y)) = _
      rw [ha, hb]; rfl
    · change a.readBound + b.readBound = 0
      rw [ha0, hb0]
  | @defDiv h c hc k a ha _ _ =>
    exact ReadFreeOf.eq (ReadFreeOf.binop _ h (LTm.Num.readFree ha) (.lit c)) (.var k)
  | @defDivI h c hc k a ha _ _ =>
    exact ReadFreeOf.eq (ReadFreeOf.binop _ h (LTm.Num.readFree ha) (.lit c)) (.var k)
  | @defShr p h v k a ha _ _ =>
    exact ReadFreeOf.eq (ReadFreeOf.binop _ h (LTm.Num.readFree ha) (.lit v)) (.var k)
  | @defAddW h k a b ha hb _ _ _ | @defSubW h k a b ha hb _ _ _ =>
    exact ReadFreeOf.eq (ReadFreeOf.binop _ h (LTm.Num.readFree ha) (LTm.Num.readFree hb)) (.var k)
  | @defToInt h k a ha _ _ | @defToUint h k a ha _ _ =>
    exact ReadFreeOf.eq (ReadFreeOf.unop _ h (LTm.Num.readFree ha)) (.var k)

/-- The source fragment has read queries (with reads). -/
theorem LTm.SrcL.readExpr {w : Bool} {l : LedgerMode} : ∀ {k : SrcKind} {s : Srt} {t : LTm C s},
    t.SrcL false w l k →
    ∃ e, ReadExpr.ofTerm? t = some e := by
  intro k s t h
  induction h with
  | kite hc => cases hc
  | ite hc => cases hc
  | var k => exact ⟨.var k, rfl⟩
  | @lit p v => exact ⟨.lit v, by cases p <;> rfl⟩
  | env e => exact ⟨.env e, rfl⟩
  | err => exact ⟨.err, rfl⟩
  | root r h => exact ⟨.root r h, rfl⟩
  | ofNum _ ih => exact ih
  | zlit n => exact ⟨.zlit n, rfl⟩
  | @znet _ x _ ih =>
    obtain ⟨e, he⟩ := ih
    exact ⟨.net e, by change (ReadExpr.ofTerm? x).map ReadExpr.net = _; rw [he]; rfl⟩
  | znetLit _ v => exact ⟨.net (.lit v), rfl⟩
  | @zseq _ q x y _ _ iha ihb =>
    obtain ⟨ea, hea⟩ := iha
    obtain ⟨eb, heb⟩ := ihb
    exact ⟨ReadExpr.seq ea eb, by
      change (Option.bind (ReadExpr.ofTerm? x) fun x' => Option.bind (ReadExpr.ofTerm? y) fun y' =>
        some (ReadExpr.seq x' y')) = _
      rw [hea, heb]; rfl⟩
  | @zint x _ ih =>
    obtain ⟨e, he⟩ := ih
    exact ⟨.toInt e, by change (ReadExpr.ofTerm? x).map ReadExpr.toInt = _; rw [he]; rfl⟩
  | @zadd h x y _ _ iha ihb =>
    obtain ⟨ea, hea⟩ := iha
    obtain ⟨eb, heb⟩ := ihb
    exact ⟨ReadExpr.zbin .add h ea eb, by
      change (Option.bind (ReadExpr.ofTerm? x) fun x' => Option.bind (ReadExpr.ofTerm? y) fun y' =>
        some (ReadExpr.zbin .add h x' y')) = _
      rw [hea, heb]; rfl⟩
  | @zsub h x y _ _ iha ihb =>
    obtain ⟨ea, hea⟩ := iha
    obtain ⟨eb, heb⟩ := ihb
    exact ⟨ReadExpr.zbin .sub h ea eb, by
      change (Option.bind (ReadExpr.ofTerm? x) fun x' => Option.bind (ReadExpr.ofTerm? y) fun y' =>
        some (ReadExpr.zbin .sub h x' y')) = _
      rw [hea, heb]; rfl⟩
  | @zcmp op h x y _ _ iha ihb =>
    obtain ⟨ea, hea⟩ := iha
    obtain ⟨eb, heb⟩ := ihb
    exact ⟨ReadExpr.zcmp op h ea eb, by
      change (Option.bind (ReadExpr.ofTerm? x) fun x' => Option.bind (ReadExpr.ofTerm? y) fun y' =>
        some (ReadExpr.zcmp op h x' y')) = _
      rw [hea, heb]; rfl⟩
  | @zmulL h n y _ ihb =>
    obtain ⟨eb, heb⟩ := ihb
    exact ⟨ReadExpr.zbin .mul h (.zlit n) eb, by
      change (Option.bind (ReadExpr.ofTerm? (LTm.app0 (C := C) (.zlit n))) fun x' =>
        Option.bind (ReadExpr.ofTerm? y) fun y' => some (ReadExpr.zbin .mul h x' y')) = _
      rw [heb]; rfl⟩
  | @zmulR h x n _ iha =>
    obtain ⟨ea, hea⟩ := iha
    exact ⟨ReadExpr.zbin .mul h ea (.zlit n), by
      change (Option.bind (ReadExpr.ofTerm? x) fun x' =>
        Option.bind (ReadExpr.ofTerm? (LTm.app0 (C := C) (.zlit n))) fun y' =>
          some (ReadExpr.zbin .mul h x' y')) = _
      rw [hea]; rfl⟩
  | @word p q _ ih =>
    obtain ⟨e, he⟩ := ih
    exact ⟨.word e, by change (ReadExpr.ofTerm? q).map ReadExpr.word = _; rw [he]; rfl⟩
  | @field sn f T h q _ ih =>
    obtain ⟨e, he⟩ := ih
    exact ⟨.field h e, by change (ReadExpr.ofTerm? q).map (ReadExpr.field h) = _; rw [he]; rfl⟩
  | @not x _ ih =>
    obtain ⟨e, he⟩ := ih
    exact ⟨.unop .not (p := .bool) rfl e, by change (ReadExpr.ofTerm? x).map (ReadExpr.unop .not rfl) = _; rw [he]; rfl⟩
  | @neg h x _ ih | @bnot h x _ ih | @toInt _ h x _ ih | @toUint _ h x _ ih =>
    obtain ⟨e, he⟩ := ih
    exact ⟨.unop _ h e, by change (ReadExpr.ofTerm? x).map (ReadExpr.unop _ h) = _; rw [he]; rfl⟩
  | @divL _ h x v _ _ ih | @modL _ h x v _ _ ih | @shrL _ _ h x v _ ih | @shlL _ h x v _ ih =>
    obtain ⟨e, he⟩ := ih
    exact ⟨ReadExpr.binop _ h e (.lit v), by
      change (Option.bind (ReadExpr.ofTerm? x) fun x' =>
        Option.bind (ReadExpr.ofTerm? (LTm.app0 (C := C) (.lit v))) fun y' =>
          some (ReadExpr.binop _ h x' y')) = _
      rw [he, show ReadExpr.ofTerm? (LTm.app0 (C := C) (.lit v)) = some (.lit v) by
        first | rfl | (cases ‹PrimTy› <;> rfl)]
      rfl⟩
  | @litR _ p op h x v _ _ ih =>
    obtain ⟨e, he⟩ := ih
    exact ⟨ReadExpr.binop _ h e (.lit v), by
      change (Option.bind (ReadExpr.ofTerm? x) fun x' =>
        Option.bind (ReadExpr.ofTerm? (LTm.app0 (C := C) (.lit v))) fun y' =>
          some (ReadExpr.binop _ h x' y')) = _
      rw [he, show ReadExpr.ofTerm? (LTm.app0 (C := C) (.lit v)) = some (.lit v) by cases p <;> rfl]
      rfl⟩
  | @litL _ p op h v _ y _ ih =>
    obtain ⟨e, he⟩ := ih
    exact ⟨ReadExpr.binop _ h (.lit v) e, by
      change (Option.bind (ReadExpr.ofTerm? (LTm.app0 (C := C) (.lit v))) fun x' =>
        Option.bind (ReadExpr.ofTerm? y) fun y' => some (ReadExpr.binop _ h x' y')) = _
      rw [he, show ReadExpr.ofTerm? (LTm.app0 (C := C) (.lit v)) = some (.lit v) by cases p <;> rfl]
      rfl⟩
  | @bandR _ h x v _ _ ih =>
    obtain ⟨e, he⟩ := ih
    exact ⟨ReadExpr.binop _ h e (.lit v), by
      change (Option.bind (ReadExpr.ofTerm? x) fun x' =>
        Option.bind (ReadExpr.ofTerm? (LTm.app0 (C := C) (.lit v))) fun y' =>
          some (ReadExpr.binop _ h x' y')) = _
      rw [he]
      rfl⟩
  | @bandL _ h v _ y _ ih =>
    obtain ⟨e, he⟩ := ih
    exact ⟨ReadExpr.binop _ h (.lit v) e, by
      change (Option.bind (ReadExpr.ofTerm? (LTm.app0 (C := C) (.lit v))) fun x' =>
        Option.bind (ReadExpr.ofTerm? y) fun y' => some (ReadExpr.binop _ h x' y')) = _
      rw [he]
      rfl⟩
  | @addW _ h x y _ _ iha ihb | @subW _ h x y _ _ iha ihb =>
    obtain ⟨ea, hea⟩ := iha
    obtain ⟨eb, heb⟩ := ihb
    exact ⟨ReadExpr.binop _ h ea eb, by
      change (Option.bind (ReadExpr.ofTerm? x) fun x' => Option.bind (ReadExpr.ofTerm? y) fun y' =>
        some (ReadExpr.binop _ h x' y')) = _
      rw [hea, heb]; rfl⟩
  | @add p h x y _ _ iha ihb =>
    obtain ⟨ea, hea⟩ := iha
    obtain ⟨eb, heb⟩ := ihb
    exact ⟨ReadExpr.binop .add h ea eb, by
      change (Option.bind (ReadExpr.ofTerm? x) fun x' => Option.bind (ReadExpr.ofTerm? y) fun y' =>
        some (ReadExpr.binop .add h x' y')) = _
      rw [hea, heb]; rfl⟩
  | @mulL p h v y _ ihb =>
    obtain ⟨eb, heb⟩ := ihb
    exact ⟨ReadExpr.binop .mul h (.lit v) eb, by
      change (Option.bind (ReadExpr.ofTerm? (LTm.app0 (C := C) (.lit v))) fun x' =>
        Option.bind (ReadExpr.ofTerm? y) fun y' => some (ReadExpr.binop .mul h x' y')) = _
      rw [show ReadExpr.ofTerm? (LTm.app0 (C := C) (.lit v)) = some (.lit v) by cases p <;> rfl, heb]
      rfl⟩
  | @mulR p h x v _ iha =>
    obtain ⟨ea, hea⟩ := iha
    exact ⟨ReadExpr.binop .mul h ea (.lit v), by
      change (Option.bind (ReadExpr.ofTerm? x) fun x' =>
        Option.bind (ReadExpr.ofTerm? (LTm.app0 (C := C) (.lit v))) fun y' =>
          some (ReadExpr.binop .mul h x' y')) = _
      rw [show ReadExpr.ofTerm? (LTm.app0 (C := C) (.lit v)) = some (.lit v) by cases p <;> rfl, hea]
      rfl⟩
  | @sub p h x y _ _ iha ihb =>
    obtain ⟨ea, hea⟩ := iha
    obtain ⟨eb, heb⟩ := ihb
    exact ⟨ReadExpr.binop .sub h ea eb, by
      change (Option.bind (ReadExpr.ofTerm? x) fun x' => Option.bind (ReadExpr.ofTerm? y) fun y' =>
        some (ReadExpr.binop .sub h x' y')) = _
      rw [hea, heb]; rfl⟩
  | @and x y _ _ iha ihb =>
    obtain ⟨ea, hea⟩ := iha
    obtain ⟨eb, heb⟩ := ihb
    exact ⟨ReadExpr.binop .and rfl ea eb, by
      change (Option.bind (ReadExpr.ofTerm? x) fun x' => Option.bind (ReadExpr.ofTerm? y) fun y' =>
        some (ReadExpr.binop .and rfl x' y')) = _
      rw [hea, heb]; rfl⟩
  | @or x y _ _ iha ihb =>
    obtain ⟨ea, hea⟩ := iha
    obtain ⟨eb, heb⟩ := ihb
    exact ⟨ReadExpr.binop .or rfl ea eb, by
      change (Option.bind (ReadExpr.ofTerm? x) fun x' => Option.bind (ReadExpr.ofTerm? y) fun y' =>
        some (ReadExpr.binop .or rfl x' y')) = _
      rw [hea, heb]; rfl⟩
  | @eqB x y _ _ iha ihb =>
    obtain ⟨ea, hea⟩ := iha
    obtain ⟨eb, heb⟩ := ihb
    exact ⟨ReadExpr.binop .eqB rfl ea eb, by
      change (Option.bind (ReadExpr.ofTerm? x) fun x' => Option.bind (ReadExpr.ofTerm? y) fun y' =>
        some (ReadExpr.binop .eqB rfl x' y')) = _
      rw [hea, heb]; rfl⟩
  | @neB x y _ _ iha ihb =>
    obtain ⟨ea, hea⟩ := iha
    obtain ⟨eb, heb⟩ := ihb
    exact ⟨ReadExpr.binop .neB rfl ea eb, by
      change (Option.bind (ReadExpr.ofTerm? x) fun x' => Option.bind (ReadExpr.ofTerm? y) fun y' =>
        some (ReadExpr.binop .neB rfl x' y')) = _
      rw [hea, heb]; rfl⟩
  | @eqN p hp x y _ _ iha ihb =>
    obtain ⟨ea, hea⟩ := iha
    obtain ⟨eb, heb⟩ := ihb
    exact ⟨ReadExpr.binop .eqB rfl ea eb, by
      change (Option.bind (ReadExpr.ofTerm? x) fun x' => Option.bind (ReadExpr.ofTerm? y) fun y' =>
        some (ReadExpr.binop .eqB rfl x' y')) = _
      rw [hea, heb]; rfl⟩
  | @neN p hp x y _ _ iha ihb =>
    obtain ⟨ea, hea⟩ := iha
    obtain ⟨eb, heb⟩ := ihb
    exact ⟨ReadExpr.binop .neB rfl ea eb, by
      change (Option.bind (ReadExpr.ofTerm? x) fun x' => Option.bind (ReadExpr.ofTerm? y) fun y' =>
        some (ReadExpr.binop .neB rfl x' y')) = _
      rw [hea, heb]; rfl⟩
  | @lt p h x y _ _ iha ihb =>
    obtain ⟨ea, hea⟩ := iha
    obtain ⟨eb, heb⟩ := ihb
    exact ⟨ReadExpr.binop .lt h ea eb, by
      change (Option.bind (ReadExpr.ofTerm? x) fun x' => Option.bind (ReadExpr.ofTerm? y) fun y' =>
        some (ReadExpr.binop .lt h x' y')) = _
      rw [hea, heb]; rfl⟩
  | @gt p h x y _ _ iha ihb =>
    obtain ⟨ea, hea⟩ := iha
    obtain ⟨eb, heb⟩ := ihb
    exact ⟨ReadExpr.binop .gt h ea eb, by
      change (Option.bind (ReadExpr.ofTerm? x) fun x' => Option.bind (ReadExpr.ofTerm? y) fun y' =>
        some (ReadExpr.binop .gt h x' y')) = _
      rw [hea, heb]; rfl⟩
  | @le p h x y _ _ iha ihb =>
    obtain ⟨ea, hea⟩ := iha
    obtain ⟨eb, heb⟩ := ihb
    exact ⟨ReadExpr.binop .le h ea eb, by
      change (Option.bind (ReadExpr.ofTerm? x) fun x' => Option.bind (ReadExpr.ofTerm? y) fun y' =>
        some (ReadExpr.binop .le h x' y')) = _
      rw [hea, heb]; rfl⟩
  | @ge p h x y _ _ iha ihb =>
    obtain ⟨ea, hea⟩ := iha
    obtain ⟨eb, heb⟩ := ihb
    exact ⟨ReadExpr.binop .ge h ea eb, by
      change (Option.bind (ReadExpr.ofTerm? x) fun x' => Option.bind (ReadExpr.ofTerm? y) fun y' =>
        some (ReadExpr.binop .ge h x' y')) = _
      rw [hea, heb]; rfl⟩
  | @seq q p x y _ _ iha ihb =>
    obtain ⟨ea, hea⟩ := iha
    obtain ⟨eb, heb⟩ := ihb
    exact ⟨ReadExpr.seq ea eb, by
      change (Option.bind (ReadExpr.ofTerm? x) fun x' => Option.bind (ReadExpr.ofTerm? y) fun y' =>
        some (ReadExpr.seq x' y')) = _
      rw [hea, heb]; rfl⟩
  | @seqB x y _ _ iha ihb =>
    obtain ⟨ea, hea⟩ := iha
    obtain ⟨eb, heb⟩ := ihb
    exact ⟨ReadExpr.seq ea eb, by
      change (Option.bind (ReadExpr.ofTerm? x) fun x' => Option.bind (ReadExpr.ofTerm? y) fun y' =>
        some (ReadExpr.seq x' y')) = _
      rw [hea, heb]; rfl⟩
  | @seqN q hq x y _ _ iha ihb =>
    obtain ⟨ea, hea⟩ := iha
    obtain ⟨eb, heb⟩ := ihb
    exact ⟨ReadExpr.seq ea eb, by
      change (Option.bind (ReadExpr.ofTerm? x) fun x' => Option.bind (ReadExpr.ofTerm? y) fun y' =>
        some (ReadExpr.seq x' y')) = _
      rw [hea, heb]; rfl⟩
  | @key K V x y _ _ iha ihb =>
    obtain ⟨ea, hea⟩ := iha
    obtain ⟨eb, heb⟩ := ihb
    exact ⟨ReadExpr.index ea eb, by
      change (Option.bind (ReadExpr.ofTerm? x) fun x' => Option.bind (ReadExpr.ofTerm? y) fun y' =>
        some (ReadExpr.index x' y')) = _
      rw [hea, heb]; rfl⟩

theorem LFml.SrcL.readFormula {w : Bool} {l : LedgerMode} : ∀ {φ : LFml C}, φ.SrcL false w l → ∃ rf, ReadFormula.ofFormula? φ = some rf := by
  intro φ h
  induction h with
  | tt => exact ⟨.tt, rfl⟩
  | @eqB a b ha hb | @eqN p hp a b ha hb =>
    obtain ⟨ea, hea⟩ := ha.readExpr
    obtain ⟨eb, heb⟩ := hb.readExpr
    exact ⟨.eq ea eb, by
      change (Option.bind (ReadExpr.ofTerm? a) fun x => Option.bind (ReadExpr.ofTerm? b) fun y =>
        some (ReadFormula.eq x y)) = _
      rw [hea, heb]; rfl⟩
  | @not φ _ ih =>
    obtain ⟨e, he⟩ := ih
    exact ⟨.not e, by change (ReadFormula.ofFormula? φ).map ReadFormula.not = _; rw [he]; rfl⟩
  | @and φ ψ _ _ ihφ ihψ =>
    obtain ⟨a, ha⟩ := ihφ
    obtain ⟨b, hb⟩ := ihψ
    exact ⟨.and a b, by
      change (Option.bind (ReadFormula.ofFormula? φ) fun x => Option.bind (ReadFormula.ofFormula? ψ)
        fun y => some (ReadFormula.and x y)) = _
      rw [ha, hb]; rfl⟩
  | @imp φ ψ _ _ ihφ ihψ =>
    obtain ⟨a, ha⟩ := ihφ
    obtain ⟨b, hb⟩ := ihψ
    exact ⟨.imp a b, by
      change (Option.bind (ReadFormula.ofFormula? φ) fun x => Option.bind (ReadFormula.ofFormula? ψ)
        fun y => some (ReadFormula.imp x y)) = _
      rw [ha, hb]; rfl⟩
  | @defDiv _ h v _ k x hx | @defDivI _ h v _ k x hx | @defShr _ _ h v k x hx =>
    obtain ⟨e, he⟩ := hx.readExpr
    exact ⟨.eq (ReadExpr.binop _ h e (.lit v)) (.var k), by
      change (Option.bind (Option.bind (ReadExpr.ofTerm? x) fun x' =>
        Option.bind (ReadExpr.ofTerm? (LTm.app0 (C := C) (.lit v))) fun y' =>
          some (ReadExpr.binop _ h x' y')) fun x =>
        Option.bind (ReadExpr.ofTerm? (LTm.var (C := C) k)) fun y => some (ReadFormula.eq x y)) = _
      rw [he, show ReadExpr.ofTerm? (LTm.app0 (C := C) (.lit v)) = some (.lit v) by
        first | rfl | (cases ‹PrimTy› <;> rfl)]
      rfl⟩
  | @defAddW _ h k x y hx hy | @defSubW _ h k x y hx hy =>
    obtain ⟨ea, hea⟩ := hx.readExpr
    obtain ⟨eb, heb⟩ := hy.readExpr
    exact ⟨.eq (ReadExpr.binop _ h ea eb) (.var k), by
      change (Option.bind (Option.bind (ReadExpr.ofTerm? x) fun x' =>
        Option.bind (ReadExpr.ofTerm? y) fun y' => some (ReadExpr.binop _ h x' y')) fun x =>
        Option.bind (ReadExpr.ofTerm? (LTm.var (C := C) k)) fun y => some (ReadFormula.eq x y)) = _
      rw [hea, heb]
      rfl⟩
  | @defToInt _ h k x hx | @defToUint _ h k x hx =>
    obtain ⟨e, he⟩ := hx.readExpr
    exact ⟨.eq (ReadExpr.unop _ h e) (.var k), by
      change (Option.bind ((ReadExpr.ofTerm? x).map (ReadExpr.unop _ h)) fun x =>
        Option.bind (ReadExpr.ofTerm? (LTm.var (C := C) k)) fun y => some (ReadFormula.eq x y)) = _
      rw [he]
      rfl⟩

/-! ## The layout's inputs -/

theorem LTm.Num.restrict {P : Parameter → Prop} {E : EnvKey → Prop} :
    ∀ {p : PrimTy} {t : LTm C (.val p)}, t.Num (fun _ => True) (fun _ => True) →
      (∀ q ∈ t.parameters, P q) → (∀ e ∈ Inputs.termKeys t, E e) → t.Num P E := by
  intro p t h
  induction h with
  | var k _ => intro hP _; exact .var k (hP _ List.mem_cons_self)
  | lit v => intro _ _; exact .lit v
  | env e _ => intro _ hE; exact .env e (hE e List.mem_cons_self)
  | err => intro _ _; exact .err
  | neg h _ ih => intro hP hE; exact .neg h (ih hP hE)
  | bnot h _ ih => intro hP hE; exact .bnot h (ih hP hE)
  | @add p h a b _ _ iha ihb =>
    intro hP hE
    exact .add h (iha (fun q hq => hP q (by simp only [LTm.parameters, List.mem_append]; exact Or.inl hq))
      (fun e he => hE e (by simp only [Inputs.termKeys, List.mem_append]; exact Or.inl he)))
      (ihb (fun q hq => hP q (by simp only [LTm.parameters, List.mem_append]; exact Or.inr hq))
      (fun e he => hE e (by simp only [Inputs.termKeys, List.mem_append]; exact Or.inr he)))
  | @sub p h a b _ _ iha ihb =>
    intro hP hE
    exact .sub h (iha (fun q hq => hP q (by simp only [LTm.parameters, List.mem_append]; exact Or.inl hq))
      (fun e he => hE e (by simp only [Inputs.termKeys, List.mem_append]; exact Or.inl he)))
      (ihb (fun q hq => hP q (by simp only [LTm.parameters, List.mem_append]; exact Or.inr hq))
      (fun e he => hE e (by simp only [Inputs.termKeys, List.mem_append]; exact Or.inr he)))
  | @mulL p h v b _ ihb =>
    intro hP hE
    exact .mulL h v (ihb (fun q hq => hP q (by simp only [LTm.parameters, List.mem_append]; exact Or.inr hq))
      (fun e he => hE e (by simp only [Inputs.termKeys, List.mem_append]; exact Or.inr he)))
  | @mulR p h a v _ iha =>
    intro hP hE
    exact .mulR h v (iha (fun q hq => hP q (by simp only [LTm.parameters, List.mem_append]; exact Or.inl hq))
      (fun e he => hE e (by simp only [Inputs.termKeys, List.mem_append]; exact Or.inl he)))
  | @seq q p a b _ _ iha ihb =>
    intro hP hE
    exact .seq (iha (fun q hq => hP q (by simp only [LTm.parameters, List.mem_append]; exact Or.inl hq))
      (fun e he => hE e (by simp only [Inputs.termKeys, List.mem_append]; exact Or.inl he)))
      (ihb (fun q hq => hP q (by simp only [LTm.parameters, List.mem_append]; exact Or.inr hq))
      (fun e he => hE e (by simp only [Inputs.termKeys, List.mem_append]; exact Or.inr he)))

theorem LTm.ZNum.restrict {P : Parameter → Prop} {E : EnvKey → Prop} {L : PrimTy.uint.Denote → Prop} :
    ∀ {t : LTm C .kint}, t.ZNum (fun _ => True) (fun _ => True) L →
      (∀ q ∈ t.parameters, P q) → (∀ e ∈ Inputs.termKeys t, E e) → t.ZNum P E L := by
  intro t h
  induction h with
  | zlit n => intro _ _; exact .zlit n
  | toInt ha => intro hP hE; exact .toInt (ha.restrict hP hE)
  | add h _ _ iha ihb =>
    intro hP hE
    exact .add h (iha (fun q hq => hP q (by simp only [LTm.parameters, List.mem_append]; exact Or.inl hq))
      (fun e he => hE e (by simp only [Inputs.termKeys, List.mem_append]; exact Or.inl he)))
      (ihb (fun q hq => hP q (by simp only [LTm.parameters, List.mem_append]; exact Or.inr hq))
      (fun e he => hE e (by simp only [Inputs.termKeys, List.mem_append]; exact Or.inr he)))
  | sub h _ _ iha ihb =>
    intro hP hE
    exact .sub h (iha (fun q hq => hP q (by simp only [LTm.parameters, List.mem_append]; exact Or.inl hq))
      (fun e he => hE e (by simp only [Inputs.termKeys, List.mem_append]; exact Or.inl he)))
      (ihb (fun q hq => hP q (by simp only [LTm.parameters, List.mem_append]; exact Or.inr hq))
      (fun e he => hE e (by simp only [Inputs.termKeys, List.mem_append]; exact Or.inr he)))
  | mulL h n _ ihb =>
    intro hP hE
    exact .mulL h n (ihb (fun q hq => hP q (by simp only [LTm.parameters, List.mem_append]; exact Or.inr hq))
      (fun e he => hE e (by simp only [Inputs.termKeys, List.mem_append]; exact Or.inr he)))
  | mulR h n _ iha =>
    intro hP hE
    exact .mulR h n (iha (fun q hq => hP q (by simp only [LTm.parameters, List.mem_append]; exact Or.inl hq))
      (fun e he => hE e (by simp only [Inputs.termKeys, List.mem_append]; exact Or.inl he)))
  | netLit v hv => intro _ _; exact .netLit v hv
  | zseq hd _ iha =>
    intro hP hE
    exact .zseq (hd.restrict (fun q hq => hP q (by simp only [LTm.parameters, List.mem_append]; exact Or.inl hq))
      (fun e he => hE e (by simp only [Inputs.termKeys, List.mem_append]; exact Or.inl he)))
      (iha (fun q hq => hP q (by simp only [LTm.parameters, List.mem_append]; exact Or.inr hq))
      (fun e he => hE e (by simp only [Inputs.termKeys, List.mem_append]; exact Or.inr he)))

theorem LTm.BoolV.restrict {P : Parameter → Prop} {E : EnvKey → Prop} {L : PrimTy.uint.Denote → Prop} :
    ∀ {t : LTm C (.val .bool)}, t.BoolV (fun _ => True) (fun _ => True) L →
      (∀ q ∈ t.parameters, P q) → (∀ e ∈ Inputs.termKeys t, E e) → t.BoolV P E L := by
  intro t h
  induction h with
  | var k _ => intro hP _; exact .var k (hP _ List.mem_cons_self)
  | lit v => intro _ _; exact .lit v
  | err => intro _ _; exact .err
  | not _ ih => intro hP hE; exact .not (ih hP hE)
  | and _ _ iha ihb =>
    intro hP hE
    exact .and (iha (fun q hq => hP q (by simp only [LTm.parameters, List.mem_append]; exact Or.inl hq))
      (fun e he => hE e (by simp only [Inputs.termKeys, List.mem_append]; exact Or.inl he)))
      (ihb (fun q hq => hP q (by simp only [LTm.parameters, List.mem_append]; exact Or.inr hq))
      (fun e he => hE e (by simp only [Inputs.termKeys, List.mem_append]; exact Or.inr he)))
  | or _ _ iha ihb =>
    intro hP hE
    exact .or (iha (fun q hq => hP q (by simp only [LTm.parameters, List.mem_append]; exact Or.inl hq))
      (fun e he => hE e (by simp only [Inputs.termKeys, List.mem_append]; exact Or.inl he)))
      (ihb (fun q hq => hP q (by simp only [LTm.parameters, List.mem_append]; exact Or.inr hq))
      (fun e he => hE e (by simp only [Inputs.termKeys, List.mem_append]; exact Or.inr he)))
  | eqB _ _ iha ihb =>
    intro hP hE
    exact .eqB (iha (fun q hq => hP q (by simp only [LTm.parameters, List.mem_append]; exact Or.inl hq))
      (fun e he => hE e (by simp only [Inputs.termKeys, List.mem_append]; exact Or.inl he)))
      (ihb (fun q hq => hP q (by simp only [LTm.parameters, List.mem_append]; exact Or.inr hq))
      (fun e he => hE e (by simp only [Inputs.termKeys, List.mem_append]; exact Or.inr he)))
  | neB _ _ iha ihb =>
    intro hP hE
    exact .neB (iha (fun q hq => hP q (by simp only [LTm.parameters, List.mem_append]; exact Or.inl hq))
      (fun e he => hE e (by simp only [Inputs.termKeys, List.mem_append]; exact Or.inl he)))
      (ihb (fun q hq => hP q (by simp only [LTm.parameters, List.mem_append]; exact Or.inr hq))
      (fun e he => hE e (by simp only [Inputs.termKeys, List.mem_append]; exact Or.inr he)))
  | eqN hp ha hb =>
    intro hP hE
    exact .eqN hp (ha.restrict (fun q hq => hP q (by simp only [LTm.parameters, List.mem_append]; exact Or.inl hq))
      (fun e he => hE e (by simp only [Inputs.termKeys, List.mem_append]; exact Or.inl he)))
      (hb.restrict (fun q hq => hP q (by simp only [LTm.parameters, List.mem_append]; exact Or.inr hq))
      (fun e he => hE e (by simp only [Inputs.termKeys, List.mem_append]; exact Or.inr he)))
  | neN hp ha hb =>
    intro hP hE
    exact .neN hp (ha.restrict (fun q hq => hP q (by simp only [LTm.parameters, List.mem_append]; exact Or.inl hq))
      (fun e he => hE e (by simp only [Inputs.termKeys, List.mem_append]; exact Or.inl he)))
      (hb.restrict (fun q hq => hP q (by simp only [LTm.parameters, List.mem_append]; exact Or.inr hq))
      (fun e he => hE e (by simp only [Inputs.termKeys, List.mem_append]; exact Or.inr he)))
  | lt h ha hb =>
    intro hP hE
    exact .lt h (ha.restrict (fun q hq => hP q (by simp only [LTm.parameters, List.mem_append]; exact Or.inl hq))
      (fun e he => hE e (by simp only [Inputs.termKeys, List.mem_append]; exact Or.inl he)))
      (hb.restrict (fun q hq => hP q (by simp only [LTm.parameters, List.mem_append]; exact Or.inr hq))
      (fun e he => hE e (by simp only [Inputs.termKeys, List.mem_append]; exact Or.inr he)))
  | gt h ha hb =>
    intro hP hE
    exact .gt h (ha.restrict (fun q hq => hP q (by simp only [LTm.parameters, List.mem_append]; exact Or.inl hq))
      (fun e he => hE e (by simp only [Inputs.termKeys, List.mem_append]; exact Or.inl he)))
      (hb.restrict (fun q hq => hP q (by simp only [LTm.parameters, List.mem_append]; exact Or.inr hq))
      (fun e he => hE e (by simp only [Inputs.termKeys, List.mem_append]; exact Or.inr he)))
  | le h ha hb =>
    intro hP hE
    exact .le h (ha.restrict (fun q hq => hP q (by simp only [LTm.parameters, List.mem_append]; exact Or.inl hq))
      (fun e he => hE e (by simp only [Inputs.termKeys, List.mem_append]; exact Or.inl he)))
      (hb.restrict (fun q hq => hP q (by simp only [LTm.parameters, List.mem_append]; exact Or.inr hq))
      (fun e he => hE e (by simp only [Inputs.termKeys, List.mem_append]; exact Or.inr he)))
  | ge h ha hb =>
    intro hP hE
    exact .ge h (ha.restrict (fun q hq => hP q (by simp only [LTm.parameters, List.mem_append]; exact Or.inl hq))
      (fun e he => hE e (by simp only [Inputs.termKeys, List.mem_append]; exact Or.inl he)))
      (hb.restrict (fun q hq => hP q (by simp only [LTm.parameters, List.mem_append]; exact Or.inr hq))
      (fun e he => hE e (by simp only [Inputs.termKeys, List.mem_append]; exact Or.inr he)))
  | seqB _ _ iha ihb =>
    intro hP hE
    exact .seqB (iha (fun q hq => hP q (by simp only [LTm.parameters, List.mem_append]; exact Or.inl hq))
      (fun e he => hE e (by simp only [Inputs.termKeys, List.mem_append]; exact Or.inl he)))
      (ihb (fun q hq => hP q (by simp only [LTm.parameters, List.mem_append]; exact Or.inr hq))
      (fun e he => hE e (by simp only [Inputs.termKeys, List.mem_append]; exact Or.inr he)))
  | seqN hq hd _ iha =>
    intro hP hE
    exact .seqN hq (hd.restrict (fun q hq => hP q (by simp only [LTm.parameters, List.mem_append]; exact Or.inl hq))
      (fun e he => hE e (by simp only [Inputs.termKeys, List.mem_append]; exact Or.inl he)))
      (iha (fun q hq => hP q (by simp only [LTm.parameters, List.mem_append]; exact Or.inr hq))
      (fun e he => hE e (by simp only [Inputs.termKeys, List.mem_append]; exact Or.inr he)))
  | zcmp op h ha hb =>
    intro hP hE
    exact .zcmp op h (ha.restrict (fun q hq => hP q (by simp only [LTm.parameters, List.mem_append]; exact Or.inl hq))
      (fun e he => hE e (by simp only [Inputs.termKeys, List.mem_append]; exact Or.inl he)))
      (hb.restrict (fun q hq => hP q (by simp only [LTm.parameters, List.mem_append]; exact Or.inr hq))
      (fun e he => hE e (by simp only [Inputs.termKeys, List.mem_append]; exact Or.inr he)))

theorem LFml.Arith.restrict {P : Parameter → Prop} {E : EnvKey → Prop} {L : PrimTy.uint.Denote → Prop} :
    ∀ {φ : LFml C}, φ.Arith (fun _ => True) (fun _ => True) L →
      (∀ q ∈ φ.parameters, P q) → (∀ e ∈ Inputs.formulaKeys φ, E e) → φ.Arith P E L := by
  intro φ h
  induction h with
  | tt => intro _ _; exact .tt
  | eqB ha hb hda hdb =>
    intro hP hE
    exact .eqB (ha.restrict (fun q hq => hP q (by simp only [LFml.parameters, List.mem_append]; exact Or.inl hq))
      (fun e he => hE e (by simp only [Inputs.formulaKeys, List.mem_append]; exact Or.inl he)))
      (hb.restrict (fun q hq => hP q (by simp only [LFml.parameters, List.mem_append]; exact Or.inr hq))
      (fun e he => hE e (by simp only [Inputs.formulaKeys, List.mem_append]; exact Or.inr he))) hda hdb
  | eqN hp ha hb hda hdb =>
    intro hP hE
    exact .eqN hp (ha.restrict (fun q hq => hP q (by simp only [LFml.parameters, List.mem_append]; exact Or.inl hq))
      (fun e he => hE e (by simp only [Inputs.formulaKeys, List.mem_append]; exact Or.inl he)))
      (hb.restrict (fun q hq => hP q (by simp only [LFml.parameters, List.mem_append]; exact Or.inr hq))
      (fun e he => hE e (by simp only [Inputs.formulaKeys, List.mem_append]; exact Or.inr he))) hda hdb
  | not _ ih => intro hP hE; exact .not (ih hP hE)
  | and _ _ ihφ ihψ | imp _ _ ihφ ihψ =>
    intro hP hE
    first
    | exact .and (ihφ (fun q hq => hP q (by simp only [LFml.parameters, List.mem_append]; exact Or.inl hq))
        (fun e he => hE e (by simp only [Inputs.formulaKeys, List.mem_append]; exact Or.inl he)))
        (ihψ (fun q hq => hP q (by simp only [LFml.parameters, List.mem_append]; exact Or.inr hq))
        (fun e he => hE e (by simp only [Inputs.formulaKeys, List.mem_append]; exact Or.inr he)))
    | exact .imp (ihφ (fun q hq => hP q (by simp only [LFml.parameters, List.mem_append]; exact Or.inl hq))
        (fun e he => hE e (by simp only [Inputs.formulaKeys, List.mem_append]; exact Or.inl he)))
        (ihψ (fun q hq => hP q (by simp only [LFml.parameters, List.mem_append]; exact Or.inr hq))
        (fun e he => hE e (by simp only [Inputs.formulaKeys, List.mem_append]; exact Or.inr he)))

  | defDiv h c hc k ha _ hd =>
    intro hP hE
    exact .defDiv h c hc k (ha.restrict (fun q hq => hP q (by
        simp only [LFml.parameters, LTm.parameters, List.mem_append]; exact Or.inl (Or.inl hq)))
      (fun e he => hE e (by
        simp only [Inputs.formulaKeys, Inputs.termKeys, List.mem_append]; exact Or.inl (Or.inl he))))
      (hP _ (by simp only [LFml.parameters, LTm.parameters, List.mem_append, List.mem_cons, List.mem_nil_iff, or_false, Parameter.mk.injEq, and_true]; exact Or.inr rfl)) hd
  | defDivI h c hc k ha _ hd =>
    intro hP hE
    exact .defDivI h c hc k (ha.restrict (fun q hq => hP q (by
        simp only [LFml.parameters, LTm.parameters, List.mem_append]; exact Or.inl (Or.inl hq)))
      (fun e he => hE e (by
        simp only [Inputs.formulaKeys, Inputs.termKeys, List.mem_append]; exact Or.inl (Or.inl he))))
      (hP _ (by simp only [LFml.parameters, LTm.parameters, List.mem_append, List.mem_cons, List.mem_nil_iff, or_false, Parameter.mk.injEq, and_true]; exact Or.inr rfl)) hd
  | defShr h v k ha _ hd =>
    intro hP hE
    exact .defShr h v k (ha.restrict (fun q hq => hP q (by
        simp only [LFml.parameters, LTm.parameters, List.mem_append]; exact Or.inl (Or.inl hq)))
      (fun e he => hE e (by
        simp only [Inputs.formulaKeys, Inputs.termKeys, List.mem_append]; exact Or.inl (Or.inl he))))
      (hP _ (by simp only [LFml.parameters, LTm.parameters, List.mem_append, List.mem_cons, List.mem_nil_iff, or_false, Parameter.mk.injEq, and_true]; exact Or.inr rfl)) hd
  | defAddW h k ha hb _ hda hdb =>
    intro hP hE
    exact .defAddW h k (ha.restrict (fun q hq => hP q (by
        simp only [LFml.parameters, LTm.parameters, List.mem_append]; exact Or.inl (Or.inl hq)))
      (fun e he => hE e (by
        simp only [Inputs.formulaKeys, Inputs.termKeys, List.mem_append]; exact Or.inl (Or.inl he))))
      (hb.restrict (fun q hq => hP q (by
        simp only [LFml.parameters, LTm.parameters, List.mem_append]; exact Or.inl (Or.inr hq)))
      (fun e he => hE e (by
        simp only [Inputs.formulaKeys, Inputs.termKeys, List.mem_append]; exact Or.inl (Or.inr he))))
      (hP _ (by simp only [LFml.parameters, LTm.parameters, List.mem_append, List.mem_cons, List.mem_nil_iff, or_false, Parameter.mk.injEq, and_true]; exact Or.inr rfl)) hda hdb
  | defSubW h k ha hb _ hda hdb =>
    intro hP hE
    exact .defSubW h k (ha.restrict (fun q hq => hP q (by
        simp only [LFml.parameters, LTm.parameters, List.mem_append]; exact Or.inl (Or.inl hq)))
      (fun e he => hE e (by
        simp only [Inputs.formulaKeys, Inputs.termKeys, List.mem_append]; exact Or.inl (Or.inl he))))
      (hb.restrict (fun q hq => hP q (by
        simp only [LFml.parameters, LTm.parameters, List.mem_append]; exact Or.inl (Or.inr hq)))
      (fun e he => hE e (by
        simp only [Inputs.formulaKeys, Inputs.termKeys, List.mem_append]; exact Or.inl (Or.inr he))))
      (hP _ (by simp only [LFml.parameters, LTm.parameters, List.mem_append, List.mem_cons, List.mem_nil_iff, or_false, Parameter.mk.injEq, and_true]; exact Or.inr rfl)) hda hdb
  | defToInt h k ha _ hd =>
    intro hP hE
    exact .defToInt h k (ha.restrict (fun q hq => hP q (by
        simp only [LFml.parameters, LTm.parameters, List.mem_append]; exact Or.inl hq))
      (fun e he => hE e (by
        simp only [Inputs.formulaKeys, Inputs.termKeys, List.mem_append]; exact Or.inl he)))
      (hP _ (by simp only [LFml.parameters, LTm.parameters, List.mem_append, List.mem_cons, List.mem_nil_iff, or_false, Parameter.mk.injEq, and_true]; exact Or.inr rfl)) hd
  | defToUint h k ha _ hd =>
    intro hP hE
    exact .defToUint h k (ha.restrict (fun q hq => hP q (by
        simp only [LFml.parameters, LTm.parameters, List.mem_append]; exact Or.inl hq))
      (fun e he => hE e (by
        simp only [Inputs.formulaKeys, Inputs.termKeys, List.mem_append]; exact Or.inl he)))
      (hP _ (by simp only [LFml.parameters, LTm.parameters, List.mem_append, List.mem_cons, List.mem_nil_iff, or_false, Parameter.mk.injEq, and_true]; exact Or.inr rfl)) hd

/-! ## The leaf decision -/

/-- **Flattening and compiling never refuse their fragment**: a cut leaf
(`LFml.Src false false`, the defining equations of its atoms included) with at
most 511 nodes and 45 storage reads. -/
theorem readFlatten?_arith (φ : LFml C) (h : φ.Src false false) (hn : φ.nodes ≤ 511) {B : Nat}
    (hB : 2048 ≤ B) (hw : φ.words * φ.words ≤ B) :
    ∃ r, readFlatten? B φ = some r ∧ r.flat.reads.length * r.flat.reads.length ≤ B ∧
      (leafArithmetic? r.formula).isSome = true := by
  have hd := LFml.depth_le_nodes φ
  obtain ⟨a, ha, aok, alen, alaid, aocc⟩ :=
    flattenFormulaFuel?_Src (l := .none) (by decide) h B B φ.atomBound (by omega) (by omega)
      (Nat.le_refl _) hn
  replace aok := aok.ledger_mono (L' := fun _ => False) (fun _ h => nomatch h)
  obtain ⟨src, hsrc⟩ := h.readFormula
  have hwl : φ.words ≤ B := Nat.le_trans (Nat.le_mul_self _) hw
  obtain ⟨L, hL⟩ := Option.isSome_iff_exists.mp (occurrenceLayout?_isSome B alaid (by omega))
  obtain ⟨rf, hrf, hrf0⟩ := aok.readFree
  have hflat : flattenFormula? B φ = some a := by
    show Option.map Prod.fst (flattenFormulaFuel? B B φ φ.atomBound) = _
    rw [ha]
    rfl
  have hRF : readFreeFormula? a.formula = some ⟨rf, hrf0⟩ := by
    simp only [readFreeFormula?, hrf, Option.bind_eq_bind, Option.bind_some, hrf0, dif_pos]
    rfl
  have hR : readFlatten? B φ = some ⟨a, src, Nat.le_refl _, L, ⟨rf, hrf0⟩⟩ := by
    simp only [readFlatten?, hflat, hsrc, hL, hRF, Option.bind_eq_bind, Option.bind_some]
    rfl
  have harith : (ReadFlattening.formula (⟨a, src, Nat.le_refl _, L, ⟨rf, hrf0⟩⟩ :
      ReadFlattening φ φ.atomBound)).Arith (fun _ => True) (fun _ => True) :=
    .imp (ReadOccurrence.constraints_arith aocc) aok
  have hsq : a.reads.length * a.reads.length ≤ B := by rw [alen]; exact hw
  exact ⟨_, hR, hsq, leafArithmetic?_isSome _ (harith.restrict
    (fun q hq => (List.mem_eraseDups' _ q).mpr hq)
    (fun e he => ((Inputs.unique_spec _).2 e).mpr he))⟩

end Solidity.Decide
