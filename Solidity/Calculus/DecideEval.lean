import Solidity.Calculus.Decide
import Solidity.Theory.Typed.Mem

/-!
# The elimination keeps what a term reads

`LTm.elim` (`Calculus/Decide.lean`) is the typed Theory read symbolically;
here each of its parts is shown to read what the Theory's operation reads
(`Theory/Typed/Obs.lean`), and the elimination of a term to read what the
term reads (`LTm.elim_eval`, an equality).  The proofs follow the
definitions: a symbolic path names the reference its keys evaluate to
(`SPath.eval`), `relSegs` is `Path.strip?` (`relSegs_sound`), each reader
reads the observations of the value it stands for (`VRd.Rep`), and each
storage operation's reader those of the storage it leaves (`SRd.Rep`,
through the bridges `Storage.obs_write`, `obs_delete`, `obs_push`, …).
-/

namespace Solidity

namespace Decide

open Semantics

variable {C : Contract} (g : State C []) (ν : AEnv)

/-! ## Paths -/

namespace TSegs

theorem eval_nil {T : Ty} : (TSegs.nil : TSegs C T T).eval g ν = some .nil := rfl
theorem eval_field {s f : Name} {T U : Ty} (h : lookupBy f (structDef s) = some T)
    (r : TSegs C T U) : (TSegs.field h r).eval g ν = (r.eval g ν).map (.field h) := rfl
theorem eval_at {E U : Ty} (i : LTm C (.val .uint)) (r : TSegs C E U) :
    (TSegs.at i r).eval g ν =
      (i.eval g ν : Option PrimTy.uint.Denote).bind fun k => (r.eval g ν).map (.at k) := rfl
theorem eval_atF {E U : Ty} {n : Nat} (i : LTm C (.val .uint)) (r : TSegs C E U) :
    (TSegs.atF (n := n) i r).eval g ν =
      (i.eval g ν : Option PrimTy.uint.Denote).bind fun k => (r.eval g ν).map (.atF k) := rfl
theorem eval_key {k : PrimTy} {V U : Ty} (i : LTm C (.val k)) (r : TSegs C V U) :
    (TSegs.key i r).eval g ν =
      (i.eval g ν : Option k.Denote).bind fun j => (r.eval g ν).map (.key j) :=
  rfl

theorem append_nil' {U W : Ty} (q : TSegs C U W) : (TSegs.nil : TSegs C U U).append q = q := rfl

theorem eval_append {S U W : Ty} (p : TSegs C S U) (q : TSegs C U W) :
    (p.append q).eval g ν = (p.eval g ν).bind fun a => (q.eval g ν).map (a.append ·) := by
  induction p with
  | nil => cases h : q.eval g ν <;> simp only [append_nil', eval_nil, Option.bind_some, h,
      Option.map_none, Option.map_some, Path.append_nil]
  | field h r ih =>
    show ((r.append q).eval g ν).map _ = _
    rw [ih, eval_field]
    cases r.eval g ν <;> cases q.eval g ν <;> simp only [Option.bind_none, Option.map_none,
      Option.bind_some, Option.map_some, Path.append_field]
  | «at» i r ih =>
    show (i.eval g ν : Option PrimTy.uint.Denote).bind (fun k => ((r.append q).eval g ν).map _) = _
    rw [ih, eval_at]
    cases (i.eval g ν : Option PrimTy.uint.Denote) <;> cases r.eval g ν <;> cases q.eval g ν <;>
      simp only [Option.bind_none, Option.map_none, Option.bind_some, Option.map_some,
        Path.append_at]
  | atF i r ih =>
    show (i.eval g ν : Option PrimTy.uint.Denote).bind (fun k => ((r.append q).eval g ν).map _) = _
    rw [ih, eval_atF]
    cases (i.eval g ν : Option PrimTy.uint.Denote) <;> cases r.eval g ν <;> cases q.eval g ν <;>
      simp only [Option.bind_none, Option.map_none, Option.bind_some, Option.map_some,
        Path.append_atF]
  | key i r ih =>
    show (i.eval g ν : Option _).bind (fun k => ((r.append q).eval g ν).map _) = _
    rw [ih, eval_key]
    cases (i.eval g ν : Option _) <;> cases r.eval g ν <;> cases q.eval g ν <;>
      simp only [Option.bind_none, Option.map_none, Option.bind_some, Option.map_some,
        Path.append_key]

theorem eval_ofIndex {R : RefTy} {k : PrimTy} {V : Ty} (it : IndexTy R k V)
    (i : LTm C (.val k)) :
    (TSegs.ofIndex it i).eval g ν =
      (i.eval g ν : Option k.Denote).map fun j => Path.index it j := by
  cases it with
  | map => cases h : (i.eval g ν : Option _) <;> simp only [ofIndex, eval_key, h, eval_nil,
      Option.bind_none, Option.map_none, Option.bind_some, Option.map_some, Path.index_map]
  | arr a =>
    cases a <;> cases h : (i.eval g ν : Option _) <;> first
      | rfl
      | simp only [ofIndex, eval_at, eval_atF, h, eval_nil, Option.bind_some, Option.map_some,
          Path.index_dyn, Path.index_fixed] <;> rfl

end TSegs

theorem LTm.eval_field {s f : Name} {T : Ty} (h : C.fieldType s f = some T)
    (q : LTm C (.path (.ref (.struct s)))) :
    ((LTm.app1 (.field h) q).eval g ν : Option (SRef C T)) =
      (q.eval g ν : Option (SRef C _)).map fun r => r.append (.field h .nil) := rfl

theorem TSegs.eval_toLTm {S T : Ty} (p : TSegs C S T) (acc : LTm C (.path S)) :
    ((p.toLTm acc).eval g ν : Option (SRef C T)) =
      (acc.eval g ν : Option (SRef C S)).bind fun r => (p.eval g ν).map fun q => r.append q := by
  induction p with
  | nil =>
    show (acc.eval g ν : Option (SRef C _)) = _
    cases (acc.eval g ν : Option (SRef C _)) <;> simp only [eval_nil, Option.bind_none,
      Option.bind_some, Option.map_some, SRef.append, Path.append_nil_right]
  | field h r ih =>
    show ((r.toLTm _).eval g ν : Option (SRef C _)) = _
    rw [ih, LTm.eval_field, eval_field]
    cases (acc.eval g ν : Option (SRef C _)) <;> cases r.eval g ν <;>
      simp only [Option.map_none, Option.bind_none, Option.map_some, Option.bind_some,
        SRef.append_append, Path.append_field, Path.append_nil]
  | «at» i r ih =>
    show ((r.toLTm _).eval g ν : Option (SRef C _)) = _
    rw [ih, LTm.eval_index, eval_at]
    cases (acc.eval g ν : Option (SRef C _)) <;> cases (i.eval g ν : Option _) <;>
      cases r.eval g ν <;>
      simp only [Option.map_none, Option.bind_none, Option.map_some, Option.bind_some,
        SRef.index, SRef.append_append, Path.index_dyn, Path.append_at, Path.append_nil] <;> rfl
  | atF i r ih =>
    show ((r.toLTm _).eval g ν : Option (SRef C _)) = _
    rw [ih, LTm.eval_index, eval_atF]
    cases (acc.eval g ν : Option (SRef C _)) <;> cases (i.eval g ν : Option _) <;>
      cases r.eval g ν <;>
      simp only [Option.map_none, Option.bind_none, Option.map_some, Option.bind_some,
        SRef.index, SRef.append_append, Path.index_fixed, Path.append_atF, Path.append_nil] <;> rfl
  | key i r ih =>
    show ((r.toLTm _).eval g ν : Option (SRef C _)) = _
    rw [ih, LTm.eval_index, eval_key]
    cases (acc.eval g ν : Option (SRef C _)) <;> cases (i.eval g ν : Option _) <;>
      cases r.eval g ν <;>
      simp only [Option.map_none, Option.bind_none, Option.map_some, Option.bind_some,
        SRef.index, SRef.append_append, Path.index_map, Path.append_key, Path.append_nil] <;> rfl

namespace SPath

theorem eval_toLTm {T : Ty} (P : SPath C T) :
    (P.toLTm.eval g ν : Option (SRef C T)) = P.eval g ν := by
  rw [toLTm, TSegs.eval_toLTm]
  show (P.segs.eval g ν).map (fun q => (SRef.ofRoot P.r P.hr).append q) = _
  unfold eval
  cases P.segs.eval g ν <;> simp only [Option.map_none, Option.map_some, SRef.ofRoot,
    SRef.append, Path.append_nil]

theorem eval_snoc {T U : Ty} (P : SPath C T) (s : TSegs C T U) :
    (P.snoc s).eval g ν = (P.eval g ν).bind fun r => (s.eval g ν).map r.append := by
  simp only [snoc, eval, TSegs.eval_append]
  cases P.segs.eval g ν <;> cases s.eval g ν <;> rfl

end SPath

/-! ## Case trees and the comparison -/


namespace CTree

variable {α : Type}

/-- The leaf the keys select. -/
noncomputable def sel : CTree C α → α
  | .leaf a => a
  | .node a b t e => if a.eval g ν = b.eval g ν then t.sel else e.sel

/-- Every test of the tree compares keys that return. -/
def TestsOk : CTree C α → Prop
  | .leaf _ => True
  | .node a b t e => (a.eval g ν).isSome ∧ (b.eval g ν).isSome ∧ t.TestsOk ∧ e.TestsOk

theorem toTerm_eval {q : PrimTy} (f : α → LTm C (.val q)) :
    (t : CTree C α) → t.TestsOk g ν → (t.toTerm f).eval g ν = (f (t.sel g ν)).eval g ν
  | .leaf _, _ => rfl
  | .node a b t e, ⟨ha, hb, ht, he⟩ => by
    obtain ⟨x, hx⟩ := Option.isSome_iff_exists.1 ha
    obtain ⟨y, hy⟩ := Option.isSome_iff_exists.1 hb
    simp only [toTerm, LTm.eval_kite, hx, hy, Option.bind_some, sel, Option.some.injEq]
    split
    · exact toTerm_eval f t ht
    · exact toTerm_eval f e he

end CTree

theorem LTm.keyView_var {p : PrimTy} {t : LTm C (.val p)} {k : Nat} (h : t.keyView = .var k) :
    t = .var k := by
  cases t <;> simp only [LTm.keyView, reduceCtorEq, KV.var.injEq] at h
  · subst h; rfl
  · rename_i o; cases o <;> simp only [reduceCtorEq] at h

theorem LTm.keyView_env {p : PrimTy} {t : LTm C (.val p)} {k : EnvKey} (h : t.keyView = .env k) :
    ∃ e : p = .uint, e ▸ t = .app0 (.env k) := by
  cases t <;> simp only [LTm.keyView, reduceCtorEq] at h
  rename_i o; cases o <;> simp only [reduceCtorEq, KV.env.injEq] at h
  subst h; exact ⟨rfl, rfl⟩

theorem LTm.keyView_lit {p : PrimTy} {t : LTm C (.val p)} {v : Int} (h : t.keyView = .lit v) :
    ∃ w : p.Denote, t = .app0 (.lit w) ∧ PrimTy.key w = v := by
  cases t <;> simp only [LTm.keyView, reduceCtorEq] at h
  rename_i o; cases o <;> simp only [reduceCtorEq, KV.lit.injEq] at h
  exact ⟨_, rfl, h⟩

theorem keyCmp_sound {p : PrimTy} {a b : LTm C (.val p)} {c : Bool} (h : keyCmp a b = some c)
    {x y : p.Denote} (hx : (a.eval g ν : Option p.Denote) = some x)
    (hy : (b.eval g ν : Option p.Denote) = some y) : decide (x = y) = c := by
  unfold keyCmp at h
  split at h
  · rename_i x' y' ha hb
    split at h
    · cases h; subst_vars
      rw [LTm.keyView_var ha] at hx; rw [LTm.keyView_var hb] at hy
      rw [hx] at hy; cases hy; simp only [decide_true]
    · cases h
  · rename_i x' y' ha hb
    split at h
    · cases h; subst_vars
      obtain ⟨e, he⟩ := LTm.keyView_env ha
      obtain ⟨e', he'⟩ := LTm.keyView_env hb
      subst e; cases he; cases he'
      rw [hx] at hy; cases hy; simp only [decide_true]
    · cases h
  · rename_i x' y' ha hb
    cases h
    obtain ⟨w, rfl, hw⟩ := LTm.keyView_lit ha
    obtain ⟨w', rfl, hw'⟩ := LTm.keyView_lit hb
    simp only [LTm.eval_app0, Op0.eval, Option.some.injEq] at hx hy
    subst hx hy hw hw'
    by_cases e : w = w'
    · subst e; simp only [decide_true]
    · simp only [e, decide_false, Bool.false_eq, decide_eq_false_iff_not]
      exact fun h' => e (PrimTy.key_inj h')
  · cases h

/-- A key the terms compare returns. -/
theorem LTm.keyView_eval {p : PrimTy} {t : LTm C (.val p)} (h : t.keyView ≠ .other) :
    ∃ x, (t.eval g ν : Option p.Denote) = some x := by
  cases hv : t.keyView with
  | var k => rw [LTm.keyView_var hv]; exact ⟨_, rfl⟩
  | env k =>
    obtain ⟨e, he⟩ := LTm.keyView_env hv
    subst e; cases he; exact ⟨_, rfl⟩
  | lit v => obtain ⟨w, rfl, -⟩ := LTm.keyView_lit hv; exact ⟨w, rfl⟩
  | other => exact absurd hv h

theorem keyCmp_isSome {p : PrimTy} {a b : LTm C (.val p)} {c : Bool} (h : keyCmp a b = some c) :
    a.keyView ≠ .other ∧ b.keyView ≠ .other := by
  unfold keyCmp at h
  split at h
  · rename_i x y ha hb; rw [ha, hb]; exact ⟨nofun, nofun⟩
  · rename_i x y ha hb; rw [ha, hb]; exact ⟨nofun, nofun⟩
  · rename_i x y ha hb; rw [ha, hb]; exact ⟨nofun, nofun⟩
  · cases h

/-- `kiteK` reads as `kite`. -/
theorem LTm.eval_kiteK {p : PrimTy} {s : Srt} (a b : LTm C (.val p)) (t e : LTm C s) :
    (LTm.kiteK a b t e).eval g ν = (LTm.kite a b t e).eval g ν := by
  unfold LTm.kiteK
  split
  · rename_i hc
    obtain ⟨ha, hb⟩ := keyCmp_isSome hc
    obtain ⟨x, hx⟩ := LTm.keyView_eval g ν ha
    obtain ⟨y, hy⟩ := LTm.keyView_eval g ν hb
    have hxy := keyCmp_sound g ν hc hx hy
    rw [LTm.eval_kite, hx, hy]
    simp only [Option.bind_some, of_decide_eq_true hxy, if_true]
  · rename_i hc
    obtain ⟨ha, hb⟩ := keyCmp_isSome hc
    obtain ⟨x, hx⟩ := LTm.keyView_eval g ν ha
    obtain ⟨y, hy⟩ := LTm.keyView_eval g ν hb
    have hxy := keyCmp_sound g ν hc hx hy
    rw [LTm.eval_kite, hx, hy]
    simp only [Option.bind_some, of_decide_eq_false hxy, if_false]
  · rfl

theorem keyTree_sel {α : Type} {p : PrimTy} (a b : LTm C (.val p)) (t e : CTree C α)
    {x y : p.Denote} (hx : (a.eval g ν : Option p.Denote) = some x)
    (hy : (b.eval g ν : Option p.Denote) = some y) :
    (keyTree a b t e).sel g ν = if x = y then t.sel g ν else e.sel g ν := by
  unfold keyTree
  split
  · rename_i h
    have := keyCmp_sound g ν h hx hy
    simp only [decide_eq_true_eq] at this; simp only [this, if_true]
  · rename_i h
    have := keyCmp_sound g ν h hx hy
    simp only [decide_eq_false_iff_not] at this; simp only [this, if_false]
  · simp only [CTree.sel, hx, hy, Option.some.injEq]

theorem keyTree_testsOk {α : Type} {p : PrimTy} (a b : LTm C (.val p)) {t e : CTree C α}
    (ha : (a.eval g ν).isSome) (hb : (b.eval g ν).isSome) (ht : t.TestsOk g ν)
    (he : e.TestsOk g ν) : (keyTree a b t e).TestsOk g ν := by
  unfold keyTree
  split
  · exact ht
  · exact he
  · exact ⟨ha, hb, ht, he⟩

/-- What a leaf of the comparison says of the two paths: the rest, where
the read goes through the write. -/
def RelOk {T U : Ty} : Option (TSegs C T U) → Option (Path T U) → Prop
  | some rest, some r => rest.eval g ν = some r
  | none, none => True
  | _, _ => False


theorem relSegs_nil {S U : Ty} (q : TSegs C S U) : relSegs (.nil : TSegs C S S) q = .leaf (some q) :=
  rfl

theorem relSegs_field_field {s f f' : Name} {T T' U U' : Ty} (h : lookupBy f (structDef s) = some T)
    (h' : lookupBy f' (structDef s) = some T') (p : TSegs C T U) (q : TSegs C T' U') :
    relSegs (.field h p) (.field h' q) =
      if ef : f = f' then relSegs p (field_ty_eq h h' rfl ef ▸ q) else .leaf none := rfl

theorem relSegs_at_at {E U U' : Ty} (i j : LTm C (.val .uint)) (p : TSegs C E U) (q : TSegs C E U') :
    relSegs (.at i p) (.at j q) = keyTree i j (relSegs p q) (.leaf none) := rfl

theorem relSegs_atF_atF {E U U' : Ty} {n : Nat} (i j : LTm C (.val .uint)) (p : TSegs C E U)
    (q : TSegs C E U') :
    relSegs (.atF (n := n) i p) (.atF j q) = keyTree i j (relSegs p q) (.leaf none) := rfl

theorem relSegs_key_key {k : PrimTy} {V U U' : Ty} (i j : LTm C (.val k)) (p : TSegs C V U)
    (q : TSegs C V U') :
    relSegs (.key i p) (.key j q) = keyTree i j (relSegs p q) (.leaf none) := rfl

theorem eval_field_some {s f : Name} {T U : Ty} {h : lookupBy f (structDef s) = some T}
    {r : TSegs C T U} {pp : Path (.ref (.struct s)) U} (hp : (TSegs.field h r).eval g ν = some pp) :
    ∃ pp', r.eval g ν = some pp' ∧ pp = .field h pp' := by
  rw [TSegs.eval_field, Option.map_eq_some_iff] at hp
  obtain ⟨pp', h1, rfl⟩ := hp
  exact ⟨pp', h1, rfl⟩

theorem eval_at_some {E U : Ty} {i : LTm C (.val .uint)} {r : TSegs C E U} {pp : Path _ U}
    (hp : (TSegs.at i r).eval g ν = some pp) :
    ∃ k pp', (i.eval g ν : Option PrimTy.uint.Denote) = some k ∧ r.eval g ν = some pp' ∧
      pp = .at k pp' := by
  rw [TSegs.eval_at, Option.bind_eq_some_iff] at hp
  obtain ⟨k, hk, hp⟩ := hp
  rw [Option.map_eq_some_iff] at hp
  obtain ⟨pp', h1, rfl⟩ := hp
  exact ⟨k, pp', hk, h1, rfl⟩

theorem eval_atF_some {E U : Ty} {n : Nat} {i : LTm C (.val .uint)} {r : TSegs C E U}
    {pp : Path (.ref (.fixed E n)) U} (hp : (TSegs.atF i r).eval g ν = some pp) :
    ∃ k pp', (i.eval g ν : Option PrimTy.uint.Denote) = some k ∧ r.eval g ν = some pp' ∧
      pp = .atF k pp' := by
  rw [TSegs.eval_atF, Option.bind_eq_some_iff] at hp
  obtain ⟨k, hk, hp⟩ := hp
  rw [Option.map_eq_some_iff] at hp
  obtain ⟨pp', h1, rfl⟩ := hp
  exact ⟨k, pp', hk, h1, rfl⟩

theorem eval_key_some {k : PrimTy} {V U : Ty} {i : LTm C (.val k)} {r : TSegs C V U}
    {pp : Path _ U} (hp : (TSegs.key i r).eval g ν = some pp) :
    ∃ j pp', (i.eval g ν : Option k.Denote) = some j ∧ r.eval g ν = some pp' ∧
      pp = .key j pp' := by
  rw [TSegs.eval_key, Option.bind_eq_some_iff] at hp
  obtain ⟨j, hj, hp⟩ := hp
  rw [Option.map_eq_some_iff] at hp
  obtain ⟨pp', h1, rfl⟩ := hp
  exact ⟨j, pp', hj, h1, rfl⟩

/-- **The comparison is `Path.strip?`**: where both paths evaluate, its
tests compare keys that return, and the leaf they select is the rest of the
read past the write, or `none` where the read does not go through it. -/
theorem relSegs_sound : ∀ {S T U : Ty} (p : TSegs C S T) (q : TSegs C S U) {pp : Path S T}
    {qp : Path S U}, p.eval g ν = some pp → q.eval g ν = some qp →
    (relSegs p q).TestsOk g ν ∧ RelOk g ν ((relSegs p q).sel g ν) (Path.strip? pp qp)
  | _, _, _, .nil, q, pp, qp, hp, hq => by
    cases hp
    rw [relSegs_nil]
    exact ⟨trivial, hq⟩
  | _, _, _, .field h p, .nil, pp, qp, hp, hq => by
    obtain ⟨pp', -, rfl⟩ := eval_field_some g ν hp
    cases hq
    exact ⟨trivial, trivial⟩
  | _, _, _, @TSegs.field _ _ f _ _ h p, @TSegs.field _ _ f' _ _ h' q, pp, qp, hp, hq => by
    obtain ⟨pp', hp', rfl⟩ := eval_field_some g ν hp
    obtain ⟨qp', hq', rfl⟩ := eval_field_some g ν hq
    rw [relSegs_field_field]
    by_cases ef : f = f'
    · subst ef
      obtain rfl := field_ty_eq h h' rfl rfl
      simp only [dif_pos rfl, Path.strip?]
      exact relSegs_sound p q hp' hq'
    · simp only [ef, dif_neg, not_false_eq_true, Path.strip?]
      exact ⟨trivial, trivial⟩
  | _, _, _, .at i p, .nil, pp, qp, hp, hq => by
    obtain ⟨k, pp', -, -, rfl⟩ := eval_at_some g ν hp
    cases hq
    exact ⟨trivial, trivial⟩
  | _, _, _, .at i p, .at j q, pp, qp, hp, hq => by
    obtain ⟨k, pp', hk, hp', rfl⟩ := eval_at_some g ν hp
    obtain ⟨k', qp', hk', hq', rfl⟩ := eval_at_some g ν hq
    obtain ⟨ht, hr⟩ := relSegs_sound p q hp' hq'
    rw [relSegs_at_at]
    refine ⟨keyTree_testsOk g ν i j (by rw [hk]; rfl) (by rw [hk']; rfl) ht trivial, ?_⟩
    rw [keyTree_sel g ν i j _ _ hk hk']
    simp only [Path.strip?]
    by_cases e : k = k'
    · subst e; simp only [if_true]; exact hr
    · have e' : k.1 ≠ k'.1 := fun h => e (Subtype.ext h)
      simp only [e, if_false, e']
      exact trivial
  | _, _, _, .atF i p, .nil, pp, qp, hp, hq => by
    obtain ⟨k, pp', -, -, rfl⟩ := eval_atF_some g ν hp
    cases hq
    exact ⟨trivial, trivial⟩
  | _, _, _, .atF i p, .atF j q, pp, qp, hp, hq => by
    obtain ⟨k, pp', hk, hp', rfl⟩ := eval_atF_some g ν hp
    obtain ⟨k', qp', hk', hq', rfl⟩ := eval_atF_some g ν hq
    obtain ⟨ht, hr⟩ := relSegs_sound p q hp' hq'
    rw [relSegs_atF_atF]
    refine ⟨keyTree_testsOk g ν i j (by rw [hk]; rfl) (by rw [hk']; rfl) ht trivial, ?_⟩
    rw [keyTree_sel g ν i j _ _ hk hk']
    simp only [Path.strip?]
    by_cases e : k = k'
    · subst e; simp only [if_true]; exact hr
    · have e' : k.1 ≠ k'.1 := fun h => e (Subtype.ext h)
      simp only [e, if_false, e']
      exact trivial
  | _, _, _, .key i p, .nil, pp, qp, hp, hq => by
    obtain ⟨k, pp', -, -, rfl⟩ := eval_key_some g ν hp
    cases hq
    exact ⟨trivial, trivial⟩
  | _, _, _, .key i p, .key j q, pp, qp, hp, hq => by
    obtain ⟨k, pp', hk, hp', rfl⟩ := eval_key_some g ν hp
    obtain ⟨k', qp', hk', hq', rfl⟩ := eval_key_some g ν hq
    obtain ⟨ht, hr⟩ := relSegs_sound p q hp' hq'
    rw [relSegs_key_key]
    refine ⟨keyTree_testsOk g ν i j (by rw [hk]; rfl) (by rw [hk']; rfl) ht trivial, ?_⟩
    rw [keyTree_sel g ν i j _ _ hk hk']
    simp only [Path.strip?]
    by_cases e : k = k'
    · subst e; simp only [if_true]; exact hr
    · have e' : PrimTy.key k ≠ PrimTy.key k' := fun h => e (PrimTy.key_inj h)
      simp only [e, if_false, e']
      exact trivial


/-! ## Readers -/

/-- An observation of a value, read by a component (`Comp`) of the Theory:
the word, the length as a `uint`, whether it is there. -/
def CK.obsC {V : Ty} (c : CK V) (f : {α : Type} → Comp V α → α) : c.out.Denote :=
  match V, c with
  | _, .word P => (f (Comp.word P) : P.Denote)
  | _, .len E => uintOfNat (f (Comp.len E))
  | _, .has V => (f (Comp.has V) : Bool)

/-- What `c` observes of the value `t` at `p`. -/
def CK.obsV {V U : Ty} (c : CK V) (t : TVal U) (p : Path U V) : c.out.Denote :=
  c.obsC fun cc => cc.read t p

theorem CK.obsC_congr {V : Ty} (c : CK V) {f f' : {α : Type} → Comp V α → α}
    (h : ∀ {α : Type} (cc : Comp V α), f cc = f' cc) : c.obsC f = c.obsC f' := by
  cases c <;> simp only [CK.obsC, h]

theorem CK.obsC_ite {V : Ty} (c : CK V) (b : Prop) [Decidable b]
    (f f' : {α : Type} → Comp V α → α) :
    c.obsC (fun cc => if b then f cc else f' cc) = if b then c.obsC f else c.obsC f' := by
  by_cases h : b <;> simp only [h, if_true, if_false]

/-- **A reader reads the value `t`**: at segments that evaluate, the
observation of `t` at the path they name. -/
def VRd.Rep {T : Ty} (x : VRd C T) (t : TVal T) : Prop :=
  ∀ (V : Ty) (c : CK V) (r : TSegs C T V) (p : Path T V), r.eval g ν = some p →
    ((x c r).eval g ν : Option c.out.Denote) = some (c.obsV t p)

/-- The lengths of a value are `uint`s, as every stored array's is. -/
def Bnd {T : Ty} (t : TVal T) : Prop := ∀ {E : Ty} (p : Path T (.ref (.array E))), t.len p < 2 ^ 256

theorem Bnd.find {T U : Ty} {t : TVal T} (h : Bnd t) (p : Path T U) :
    Bnd (t.find p) := fun _ => h _

theorem VRd.Rep.find {T U : Ty} {x : VRd C T} {t : TVal T} (h : VRd.Rep g ν x t) {s : TSegs C T U}
    {ps : Path T U} (hs : s.eval g ν = some ps) : VRd.Rep g ν (x.find s) (t.find ps) := by
  intro V c r p hr
  have e : (s.append r).eval g ν = some (ps.append p) := by
    rw [TSegs.eval_append, hs, Option.bind_some, hr, Option.map_some]
  exact (h _ c _ _ e).trans (by cases c <;> rfl)

theorem LTm.eval_nat (n : Nat) : ((LTm.nat n : LTm C (.val .uint)).eval g ν : Option _) =
    some (uintOfNat n) := rfl

theorem LTm.eval_lt (a b : LTm C (.val .uint)) :
    ((LTm.lt a b).eval g ν : Option Bool) =
      (a.eval g ν : Option PrimTy.uint.Denote).bind fun x =>
        (b.eval g ν : Option PrimTy.uint.Denote).map fun y => decide (x.1 < y.1) := by
  unfold LTm.lt
  split
  · rename_i x y ha hb
    obtain ⟨w, rfl, hw⟩ := LTm.keyView_lit ha
    obtain ⟨w', rfl, hw'⟩ := LTm.keyView_lit hb
    subst hw hw'
    rfl
  · rw [LTm.eval_app2]
    cases (a.eval g ν : Option PrimTy.uint.Denote) <;>
      cases (b.eval g ν : Option PrimTy.uint.Denote) <;> rfl

theorem LTm.eval_cond {p : PrimTy} (c : LTm C (.val .bool)) (a b : LTm C (.val p)) :
    ((LTm.cond c a b).eval g ν : Option p.Denote) =
      (c.eval g ν : Option Bool).bind fun x => if (x : Bool) = true then a.eval g ν else b.eval g ν := by
  unfold LTm.cond
  split
  · rename_i h
    rw [LTm.isTT_eval h]; rfl
  · split
    · rename_i h
      rw [LTm.isFF_eval h]; rfl
    · split
      · rename_i h
        cases LTm.eq_of_beqR h
        rw [seqL_eval]
        cases (c.eval g ν : Option Bool) with
        | none => rfl
        | some x => cases x <;> rfl
      · split
        · rename_i h
          simp only [Bool.and_eq_true] at h
          obtain ⟨hac, hb⟩ := h
          cases p with
          | bool =>
            obtain ⟨-, hac⟩ := Sigma.mk.inj (LTm.sigma_eq_of_beqR hac)
            cases eq_of_heq hac
            have hb' := LTm.isTT_eval (g := g) (ν := ν) hb
            rw [seqL_eval, hb']
            cases hc : (c.eval g ν : Option Bool) with
            | none => rfl
            | some x => cases x <;> rfl
          | uint | int => simp only [LTm.isTrue, Bool.false_eq_true] at hb
        · rw [LTm.eval_app3]
          cases (c.eval g ν : Option Bool) with
          | none => rfl
          | some x => cases x <;> rfl

theorem LTm.eval_lt_some {a b : LTm C (.val .uint)} {x y : PrimTy.uint.Denote}
    (ha : (a.eval g ν : Option _) = some x) (hb : (b.eval g ν : Option _) = some y) :
    ((LTm.lt a b).eval g ν : Option Bool) = some (decide (x.1 < y.1)) := by
  rw [LTm.eval_lt, ha, hb]; rfl

theorem LTm.eval_cond_some {p : PrimTy} {c : LTm C (.val .bool)} {x : Bool} (a b : LTm C (.val p))
    (hc : (c.eval g ν : Option Bool) = some x) :
    ((LTm.cond c a b).eval g ν : Option p.Denote) = if (x : Bool) = true then a.eval g ν else b.eval g ν := by
  rw [LTm.eval_cond, hc]; rfl

/-- An index below a length, as `Path`'s `at` reads it. -/
theorem idx_lt_iff {k : PrimTy.uint.Denote} {n : Nat} (hn : n < 2 ^ 256) :
    decide (k.1 < (uintOfNat n).1) = decide (k.1.toNat < n) := by
  rw [uintOfNat_val hn]
  have hk := k.2
  simp only [PrimTy.inRange, decide_eq_true_eq] at hk
  apply decide_eq_decide.2
  omega

theorem CK.absent_eval {V : Ty} (c : CK V) :
    ((c.absent : LTm C (.val c.out)).eval g ν : Option c.out.Denote) =
      some (c.obsC fun cc => cc.absent) := by
  cases c <;> rfl

theorem CK.reset_eval {V : Ty} (c : CK V) (h : LTm C (.val .bool)) (t : TVal V)
    (hh : (h.eval g ν : Option Bool) = some (t.has .nil)) :
    ((c.reset h : LTm C (.val c.out)).eval g ν : Option c.out.Denote) =
      some (c.obsC fun cc => cc.reset t) := by
  cases c
  · rfl
  · rfl
  · exact hh

/-- **A delete, read, is `TVal.delR`.** -/
theorem delRS_rep : ∀ {U V : Ty} (r : TSegs C U V) (c : CK V) {x : VRd C U} {t : TVal U}
    {p : Path U V}, VRd.Rep g ν x t → Bnd t → r.eval g ν = some p →
    ((delRS x r c).eval g ν : Option c.out.Denote) = some (c.obsC fun cc => TVal.delR cc t p)
  | _, _, .nil, c, x, t, p, hx, _, hr => by
    cases hr
    rw [show delRS x .nil c = c.reset (x (.has _) .nil) from rfl,
      CK.reset_eval g ν c _ t (hx _ (.has _) .nil .nil rfl)]
    rfl
  | _, _, .field h r, c, x, t, p, hx, hb, hr => by
    obtain ⟨p', hp', rfl⟩ := eval_field_some g ν hr
    rw [show delRS x (.field h r) c = delRS (x.find (.field h .nil)) r c from rfl,
      delRS_rep r c (hx.find g ν (s := .field h .nil) rfl) (hb.find _) hp']
    rfl
  | _, _, .at i r, c, x, t, p, hx, hb, hr => by
    obtain ⟨k, p', hk, hp', rfl⟩ := eval_at_some g ν hr
    rw [show delRS x (.at i r) c = .cond (.lt i (x (.len _) .nil)) (delRS (x.find (.at i .nil)) r c)
        (x c (.at i r)) from rfl,
      LTm.eval_cond_some g ν _ _ (LTm.eval_lt_some g ν hk (hx _ (.len _) .nil .nil rfl)),
      show (CK.obsV (CK.len _) t .nil : PrimTy.uint.Denote) = uintOfNat (t.len .nil) from rfl,
      idx_lt_iff (hb .nil)]
    have e : CK.obsC c (fun cc => TVal.delR cc t (.at k p')) =
        if k.1.toNat < t.len .nil then c.obsC (fun cc => TVal.delR cc (t.find (.at k .nil)) p')
        else c.obsC (fun cc => cc.read t (.at k p')) := by
      rw [← CK.obsC_ite]; exact CK.obsC_congr c fun cc => by simp only [TVal.delR]
    rw [e]
    by_cases hc : k.1.toNat < t.len .nil
    · simp only [hc, decide_true, if_true]
      exact delRS_rep r c (hx.find g ν (s := .at i .nil) (by rw [TSegs.eval_at, hk]; rfl))
        (hb.find _) hp'
    · simp only [hc, decide_false, if_false, Bool.false_eq_true]
      exact hx _ c _ _ (by rw [TSegs.eval_at, hk, Option.bind_some, hp']; rfl)
  | _, _, .atF i r, c, x, t, p, hx, hb, hr => by
    obtain ⟨k, p', hk, hp', rfl⟩ := eval_atF_some g ν hr
    rw [show delRS x (.atF i r) c = delRS (x.find (.atF i .nil)) r c from rfl,
      delRS_rep r c (hx.find g ν (s := .atF i .nil) (by rw [TSegs.eval_atF, hk]; rfl))
        (hb.find _) hp']
    rfl
  | _, _, .key i r, c, x, t, p, hx, _, hr => by
    obtain ⟨j, p', hj, hp', rfl⟩ := eval_key_some g ν hr
    rw [show delRS x (.key i r) c = x c (.key i r) from rfl, hx _ c _ _ hr]
    rfl


theorem hasNil_eval {T : Ty} {x : VRd C T} {t : TVal T} (hx : VRd.Rep g ν x t) :
    ((x (.has _) .nil).eval g ν : Option Bool) = some (t.has .nil) := hx _ (.has _) .nil .nil rfl

theorem lenNil_eval {E : Ty} {x : VRd C (.ref (.array E))} {t : TVal (.ref (.array E))}
    (hx : VRd.Rep g ν x t) :
    ((x (.len _) .nil).eval g ν : Option PrimTy.uint.Denote) = some (uintOfNat (t.len .nil)) :=
  hx _ (.len _) .nil .nil rfl

/-- **A value written to fresh slots, read, is `TVal.stripR`.** -/
theorem stripRS_rep : ∀ {U V : Ty} (r : TSegs C U V) (c : CK V) {x : VRd C U} {t : TVal U}
    {p : Path U V}, VRd.Rep g ν x t → Bnd t → r.eval g ν = some p →
    ((stripRS x r c).eval g ν : Option c.out.Denote) = some (c.obsC fun cc => TVal.stripR cc t p)
  | _, _, .nil, c, x, t, p, hx, _, hr => by
    cases hr
    exact hx _ c .nil .nil rfl
  | _, _, .field h r, c, x, t, p, hx, hb, hr => by
    obtain ⟨p', hp', rfl⟩ := eval_field_some g ν hr
    rw [show stripRS x (.field h r) c = stripRS (x.find (.field h .nil)) r c from rfl,
      stripRS_rep r c (hx.find g ν (s := .field h .nil) rfl) (hb.find _) hp']
    rfl
  | _, _, .at i r, c, x, t, p, hx, hb, hr => by
    obtain ⟨k, p', hk, hp', rfl⟩ := eval_at_some g ν hr
    rw [show stripRS x (.at i r) c = .cond (.lt i (x (.len _) .nil))
        (stripRS (x.find (.at i .nil)) r c) c.absent from rfl,
      LTm.eval_cond_some g ν _ _ (LTm.eval_lt_some g ν hk (lenNil_eval g ν hx)),
      idx_lt_iff (hb .nil)]
    have e : CK.obsC c (fun cc => TVal.stripR cc t (.at k p')) =
        if k.1.toNat < t.len .nil then
          c.obsC (fun cc => TVal.stripR cc (t.find (.at k .nil)) p')
        else c.obsC (fun cc => cc.absent) := by
      rw [← CK.obsC_ite]; exact CK.obsC_congr c fun cc => by simp only [TVal.stripR]
    rw [e]
    by_cases hc : k.1.toNat < t.len .nil
    · simp only [hc, decide_true, if_true]
      exact stripRS_rep r c (hx.find g ν (s := .at i .nil) (by rw [TSegs.eval_at, hk]; rfl))
        (hb.find _) hp'
    · simp only [hc, decide_false, if_false, Bool.false_eq_true]
      exact CK.absent_eval g ν c
  | _, _, .atF i r, c, x, t, p, hx, hb, hr => by
    obtain ⟨k, p', hk, hp', rfl⟩ := eval_atF_some g ν hr
    rw [show stripRS x (.atF i r) c = stripRS (x.find (.atF i .nil)) r c from rfl,
      stripRS_rep r c (hx.find g ν (s := .atF i .nil) (by rw [TSegs.eval_atF, hk]; rfl))
        (hb.find _) hp']
    rfl
  | _, _, .key i r, c, x, t, p, hx, _, hr => by
    obtain ⟨j, p', hj, hp', rfl⟩ := eval_key_some g ν hr
    rw [show stripRS x (.key i r) c = x c (.key i r) from rfl, hx _ c _ _ hr]
    rfl

/-- **A copy laid over a value, read, is `TVal.ovR`.** -/
theorem ovRS_rep : ∀ {U V : Ty} (r : TSegs C U V) (c : CK V) {o n : VRd C U} {to tn : TVal U}
    {p : Path U V}, VRd.Rep g ν o to → VRd.Rep g ν n tn → Bnd to → Bnd tn →
    r.eval g ν = some p →
    ((ovRS o n r c).eval g ν : Option c.out.Denote) = some (c.obsC fun cc => TVal.ovR cc to tn p)
  | _, _, .nil, c, o, n, to, tn, p, _, hn, _, _, hr => by
    cases hr
    exact hn _ c .nil .nil rfl
  | _, _, .field h r, c, o, n, to, tn, p, ho, hn, hbo, hbn, hr => by
    obtain ⟨p', hp', rfl⟩ := eval_field_some g ν hr
    rw [show ovRS o n (.field h r) c = ovRS (o.find (.field h .nil)) (n.find (.field h .nil)) r c
        from rfl,
      ovRS_rep r c (ho.find g ν (s := .field h .nil) rfl) (hn.find g ν (s := .field h .nil) rfl)
        (hbo.find _) (hbn.find _) hp']
    rfl
  | _, _, .at i r, c, o, n, to, tn, p, ho, hn, hbo, hbn, hr => by
    obtain ⟨k, p', hk, hp', rfl⟩ := eval_at_some g ν hr
    rw [show ovRS o n (.at i r) c =
        .cond (n (.has _) .nil)
          (.cond (.lt i (n (.len _) .nil))
            (ovRS (o.find (.at i .nil)) (n.find (.at i .nil)) r c)
            (.cond (.lt i (o (.len _) .nil)) (delRS (o.find (.at i .nil)) r c) (o c (.at i r))))
          c.absent from rfl,
      LTm.eval_cond_some g ν _ _ (hasNil_eval g ν hn)]
    have e : CK.obsC c (fun cc => TVal.ovR cc to tn (.at k p')) =
        if tn.has .nil = true then
          (if k.1.toNat < tn.len .nil then
            c.obsC (fun cc => TVal.ovR cc (to.find (.at k .nil)) (tn.find (.at k .nil)) p')
          else if k.1.toNat < to.len .nil then
            c.obsC (fun cc => TVal.delR cc (to.find (.at k .nil)) p')
          else c.obsC (fun cc => cc.read to (.at k p')))
        else c.obsC (fun cc => cc.absent) := by
      rw [← CK.obsC_ite, ← CK.obsC_ite, ← CK.obsC_ite]
      exact CK.obsC_congr c fun cc => by simp only [TVal.ovR]
    rw [e]
    by_cases h1 : tn.has .nil = true
    · simp only [h1, if_true]
      rw [LTm.eval_cond_some g ν _ _ (LTm.eval_lt_some g ν hk (lenNil_eval g ν hn)),
        idx_lt_iff (hbn .nil)]
      by_cases h2 : k.1.toNat < tn.len .nil
      · simp only [h2, decide_true, if_true]
        exact ovRS_rep r c (ho.find g ν (s := .at i .nil) (by rw [TSegs.eval_at, hk]; rfl)) (hn.find g ν (s := .at i .nil) (by rw [TSegs.eval_at, hk]; rfl)) (hbo.find _) (hbn.find _) hp'
      · simp only [h2, decide_false, if_false, Bool.false_eq_true]
        rw [LTm.eval_cond_some g ν _ _ (LTm.eval_lt_some g ν hk (lenNil_eval g ν ho)),
          idx_lt_iff (hbo .nil)]
        by_cases h3 : k.1.toNat < to.len .nil
        · simp only [h3, decide_true, if_true]
          exact delRS_rep g ν r c (ho.find g ν (s := .at i .nil) (by rw [TSegs.eval_at, hk]; rfl)) (hbo.find _) hp'
        · simp only [h3, decide_false, if_false, Bool.false_eq_true]
          exact ho _ c _ _ hr
    · simp only [h1, if_false, Bool.false_eq_true]
      exact CK.absent_eval g ν c
  | _, _, .atF i r, c, o, n, to, tn, p, ho, hn, hbo, hbn, hr => by
    obtain ⟨k, p', hk, hp', rfl⟩ := eval_atF_some g ν hr
    rw [show ovRS o n (.atF i r) c = ovRS (o.find (.atF i .nil)) (n.find (.atF i .nil)) r c
        from rfl,
      ovRS_rep r c (ho.find g ν (s := .atF i .nil) (by rw [TSegs.eval_atF, hk]; rfl)) (hn.find g ν (s := .atF i .nil) (by rw [TSegs.eval_atF, hk]; rfl)) (hbo.find _) (hbn.find _) hp']
    rfl
  | _, _, .key i r, c, o, n, to, tn, p, ho, hn, _, _, hr => by
    obtain ⟨j, p', hj, hp', rfl⟩ := eval_key_some g ν hr
    rw [show ovRS o n (.key i r) c =
        .cond (n (.has _) .nil) (.cond (o (.has _) .nil) (o c (.key i r)) (n c (.key i r))) c.absent
        from rfl,
      LTm.eval_cond_some g ν _ _ (hasNil_eval g ν hn), LTm.eval_cond_some g ν _ _ (hasNil_eval g ν ho)]
    have e : CK.obsC c (fun cc => TVal.ovR cc to tn (.key j p')) =
        if tn.has .nil = true then
          (if to.has .nil = true then c.obsC (fun cc => cc.read to (.key j p'))
          else c.obsC (fun cc => cc.read tn (.key j p')))
        else c.obsC (fun cc => cc.absent) := by
      rw [← CK.obsC_ite, ← CK.obsC_ite]
      exact CK.obsC_congr c fun cc => by simp only [TVal.ovR]
    rw [e]
    by_cases h1 : tn.has .nil = true <;> by_cases h2 : to.has .nil = true <;>
      simp only [h1, h2, if_true, if_false, Bool.false_eq_true]
    · exact ho _ c _ _ hr
    · exact hn _ c _ _ hr
    · exact CK.absent_eval g ν c
    · exact CK.absent_eval g ν c


/-! ### Arrays -/

theorem uintOfNat_one : (uintOfNat 1).1 = 1 := uintOfNat_val (by decide)

theorem ofInt?_uint {m : Int} (h : PrimTy.uint.inRange m = true) :
    PrimTy.uint.ofInt? m = some (⟨m, h⟩ : {n : Int // PrimTy.uint.inRange n = true}) := by
  simp only [PrimTy.ofInt?, dif_pos h]

theorem LTm.eval_succ {L : LTm C (.val .uint)} {n : Nat}
    (hL : (L.eval g ν : Option PrimTy.uint.Denote) = some (uintOfNat n)) (h : n + 1 < 2 ^ 256) :
    ((LTm.succ L).eval g ν : Option PrimTy.uint.Denote) = some (uintOfNat (n + 1)) := by
  rw [LTm.succ, LTm.eval_app2, LTm.eval_nat, hL]
  show binopT .add rfl (uintOfNat n) (some (uintOfNat 1)) = _
  rw [binopT_some]
  show ((some ((uintOfNat n).1 + (uintOfNat 1).1)).bind PrimTy.uint.ofInt? :
    Option PrimTy.uint.Denote) = _
  rw [uintOfNat_val (by omega), uintOfNat_one, Option.bind_some,
    show (n : Int) + 1 = ((n + 1 : Nat) : Int) by push_cast; rfl, ofInt?_uint (lenU_inRange h)]
  exact congrArg some (Subtype.ext (uintOfNat_val h).symm)

theorem LTm.eval_pred {L : LTm C (.val .uint)} {n : Nat}
    (hL : (L.eval g ν : Option PrimTy.uint.Denote) = some (uintOfNat n)) (h0 : 0 < n)
    (h : n < 2 ^ 256) :
    ((LTm.pred L).eval g ν : Option PrimTy.uint.Denote) = some (uintOfNat (n - 1)) := by
  rw [LTm.pred, LTm.eval_app2, LTm.eval_nat, hL]
  show binopT .sub rfl (uintOfNat n) (some (uintOfNat 1)) = _
  rw [binopT_some]
  show ((some ((uintOfNat n).1 - (uintOfNat 1).1)).bind PrimTy.uint.ofInt? :
    Option PrimTy.uint.Denote) = _
  have h' : n - 1 < 2 ^ 256 := by omega
  rw [uintOfNat_val h, uintOfNat_one, Option.bind_some,
    show (n : Int) - 1 = ((n - 1 : Nat) : Int) by omega, ofInt?_uint (lenU_inRange h')]
  exact congrArg some (Subtype.ext (uintOfNat_val h').symm)

theorem LTm.eval_succK {L : LTm C (.val .uint)} {n : Nat}
    (hL : (L.eval g ν : Option PrimTy.uint.Denote) = some (uintOfNat n)) (h : n + 1 < 2 ^ 256) :
    ((LTm.succK L).eval g ν : Option PrimTy.uint.Denote) = some (uintOfNat (n + 1)) := by
  unfold LTm.succK
  split
  · rename_i m hm
    split
    · obtain ⟨w, rfl, hw⟩ := LTm.keyView_lit hm
      have hw' : (w : PrimTy.uint.Denote) = uintOfNat n := Option.some.inj hL
      have hn : (uintOfNat n).1 = n := uintOfNat_val (by omega)
      have hm' : m = n := by rw [← hw, hw']; exact hn
      subst hm'
      rw [LTm.eval_nat]
      congr 2
    · exact LTm.eval_succ g ν hL h
  · exact LTm.eval_succ g ν hL h

theorem LTm.eval_predK {L : LTm C (.val .uint)} {n : Nat}
    (hL : (L.eval g ν : Option PrimTy.uint.Denote) = some (uintOfNat n)) (h0 : 0 < n)
    (h : n < 2 ^ 256) :
    ((LTm.predK L).eval g ν : Option PrimTy.uint.Denote) = some (uintOfNat (n - 1)) := by
  unfold LTm.predK
  split
  · rename_i m hm
    split
    · obtain ⟨w, rfl, hw⟩ := LTm.keyView_lit hm
      have hw' : (w : PrimTy.uint.Denote) = uintOfNat n := Option.some.inj hL
      have hn : (uintOfNat n).1 = n := uintOfNat_val h
      have hm' : m = n := by rw [← hw, hw']; exact hn
      subst hm'
      rw [LTm.eval_nat]
      congr 2
      omega
    · exact LTm.eval_pred g ν hL h0 h
  · exact LTm.eval_pred g ν hL h0 h

theorem obsV_setLen_at {E V : Ty} (c : CK V) (a : TVal (.ref (.array E))) (n : Nat) (k : PrimTy.uint.Denote)
    (p : Path E V) : c.obsV (TVal.setLen a n) (.at k p) = c.obsV a (.at k p) := by
  cases c <;> rfl

theorem obsV_save_at {E V : Ty} (c : CK V) (a : TVal (.ref (.array E))) (x : TVal E) (m k : PrimTy.uint.Denote)
    (p : Path E V) :
    c.obsV (a.save (.at m .nil) x) (.at k p) = if k = m then c.obsV x p else c.obsV a (.at k p) := by
  by_cases e : k = m
  · subst e
    cases c <;> simp only [CK.obsV, CK.obsC, Comp.word, Comp.len, Comp.has, Obs.save,
      ObsLoc.strip?_path, Path.strip?, if_true]
  · have e' : ¬ m = k := fun h => e h.symm
    cases c <;> simp only [CK.obsV, CK.obsC, Comp.word, Comp.len, Comp.has, Obs.save,
      ObsLoc.strip?_path, Path.strip?, e, e', if_false]

theorem obsV_save_nil_has {E : Ty} (a : TVal (.ref (.array E))) (x : TVal E) (m : PrimTy.uint.Denote) :
    (a.save (.at m .nil) x).has .nil = a.has .nil := by
  simp only [Obs.save, ObsLoc.strip?_path, Path.strip?]

/-- **A reader at an array** reads `t` when it reads its length and
presence at the array, and each element below. -/
theorem arrRd_rep {E : Ty} {len' : LTm C (.val .uint)} {has : LTm C (.val .bool)}
    {below : LTm C (.val .uint) → VRd C E} {t : TVal (.ref (.array E))}
    (hl : (len'.eval g ν : Option PrimTy.uint.Denote) = some (uintOfNat (t.len .nil)))
    (hh : (has.eval g ν : Option Bool) = some (t.has .nil))
    (hb : ∀ (i : LTm C (.val .uint)) (k : PrimTy.uint.Denote),
      (i.eval g ν : Option PrimTy.uint.Denote) = some k → ∀ {V : Ty} (c : CK V) (r : TSegs C E V)
      (p : Path E V), r.eval g ν = some p →
      ((below i c r).eval g ν : Option c.out.Denote) = some (c.obsV t (.at k p))) :
    VRd.Rep g ν (arrRd len' has below) t := by
  intro V c r p hr
  cases r with
  | nil =>
    cases hr
    cases c
    · exact hl
    · exact hh
  | «at» i r =>
    obtain ⟨k, p', hk, hp', rfl⟩ := eval_at_some g ν hr
    exact hb i k hk c r p' hp'

/-- **A push, read, is `TVal.pushA`.** -/
theorem pushRd_rep {E : Ty} {a : VRd C (.ref (.array E))} {x : VRd C E}
    {L : LTm C (.val .uint)} {t : TVal (.ref (.array E))} {tx : TVal E}
    (ha : VRd.Rep g ν a t) (hx : VRd.Rep g ν x tx)
    (hL : (L.eval g ν : Option PrimTy.uint.Denote) = some (uintOfNat (t.len .nil)))
    (hn : t.len .nil + 1 < 2 ^ 256) : VRd.Rep g ν (pushRd a x L) (TVal.pushA t tx) := by
  apply arrRd_rep
  · exact LTm.eval_succK g ν hL hn
  · rw [hasNil_eval g ν ha]
    simp only [TVal.pushA, TVal.setLen, obsV_save_nil_has]
  · intro i k hk V c r p hr
    rw [LTm.eval_kiteK, LTm.eval_kite, hk, hL]
    simp only [Option.bind_some]
    rw [show c.obsV (TVal.pushA t tx) (.at k p) = _ from obsV_setLen_at c _ _ k p,
      obsV_save_at]
    by_cases e' : k = uintOfNat (t.len .nil)
    · rw [if_pos e', if_pos e']; exact hx _ c r p hr
    · rw [if_neg e', if_neg e']
      exact ha _ c _ _ (by rw [TSegs.eval_at, hk, Option.bind_some, hr]; rfl)

/-- **A length set, read, is `TVal.setLen`.** -/
theorem setLenRd_rep {E : Ty} {a : VRd C (.ref (.array E))} {L' : LTm C (.val .uint)}
    {t : TVal (.ref (.array E))} {n : Nat} (ha : VRd.Rep g ν a t)
    (hL : (L'.eval g ν : Option PrimTy.uint.Denote) = some (uintOfNat n)) :
    VRd.Rep g ν (setLenRd a L') (TVal.setLen t n) := by
  apply arrRd_rep
  · exact hL
  · exact hasNil_eval g ν (t := t) ha
  · intro i k hk V c r p hr
    rw [obsV_setLen_at]
    exact ha _ c _ _ (by rw [TSegs.eval_at, hk, Option.bind_some, hr]; rfl)

/-- **A pop, read, is `TVal.popA`**, the array not empty. -/
theorem popRd_rep (keep : Bool) {E : Ty} {a : VRd C (.ref (.array E))} {L : LTm C (.val .uint)}
    {t : TVal (.ref (.array E))} (ha : VRd.Rep g ν a t) (hb : Bnd t)
    (hL : (L.eval g ν : Option PrimTy.uint.Denote) = some (uintOfNat (t.len .nil)))
    (h0 : 0 < t.len .nil) : VRd.Rep g ν (popRd keep a L) (TVal.popA keep t) := by
  have hp := LTm.eval_predK g ν hL h0 (hb .nil)
  have hne : t.len .nil ≠ 0 := by omega
  cases keep with
  | true =>
    simp only [popRd, if_true, TVal.popA, hne, if_false]
    exact setLenRd_rep g ν ha hp
  | false =>
    simp only [popRd, Bool.false_eq_true, if_false, TVal.popA, hne]
    apply arrRd_rep
    · exact hp
    · rw [hasNil_eval g ν ha]
      simp only [TVal.setLen, obsV_save_nil_has]
    · intro i k hk V c r p hr
      rw [LTm.eval_kiteK, LTm.eval_kite, hk, hp]
      simp only [Option.bind_some]
      rw [obsV_setLen_at, obsV_save_at]
      have hb' : t.len .nil - 1 < 2 ^ 256 := by have := hb .nil; omega
      by_cases e' : k = uintOfNat (t.len .nil - 1)
      · rw [if_pos e', if_pos e']
        have hs : (TSegs.at (LTm.predK L) TSegs.nil : TSegs C (.ref (.array E)) E).eval g ν =
            some (.at (uintOfNat (t.len .nil - 1)) .nil) := by
          rw [TSegs.eval_at, hp, Option.bind_some]
          rfl
        rw [delRS_rep g ν r c (ha.find g ν hs) (hb.find _) hr]
        cases c <;> rfl
      · rw [if_neg e', if_neg e']
        exact ha _ c _ _ (by rw [TSegs.eval_at, hk, Option.bind_some, hr]; rfl)

/-- **A word as a stored value, read.** -/
theorem svalRd_rep {p : PrimTy} {w : LTm C (.val p)} {v : p.Denote}
    (hw : (w.eval g ν : Option p.Denote) = some v) : VRd.Rep g ν (svalRd w) (SVal.prim v).obs := by
  intro V c r q hr
  cases r with
  | nil =>
    cases hr
    cases c with
    | word P => exact hw
    | has V => rfl


/-! ### Defaults -/

/-- A location is there in a default value: no dynamic array's index on the
way (it is empty), a fixed one's in range. -/
def _root_.Solidity.Path.dfltOk : {T U : Ty} → Path T U → Bool
  | _, _, .nil => true
  | _, _, .field _ p => p.dfltOk
  | _, _, .key _ p => p.dfltOk
  | _, _, .at _ _ => false
  | _, _, .atF (n := n) i p => decide (i.1.toNat < n) && p.dfltOk

theorem findM_dflt : {T U : Ty} → (p : Path T U) →
    (SVal.dflt T).findM p = if p.dfltOk then some (SVal.dflt U) else none
  | _, _, .nil => by simp only [Path.dfltOk, if_true, SVal.findM_nil']
  | _, _, .field h p => by
    rw [SVal.dflt_struct, SVal.findM_field', SFields.dflt_get, findM_dflt p]; rfl
  | _, _, .key k p => by
    rw [SVal.dflt_map]; simp only [SVal.findM, SMap.toList]; exact findM_dflt p
  | _, _, .at i p => by
    rw [SVal.dflt_array, SVal.findM_at']
    simp only [Path.dfltOk, Bool.false_eq_true, if_false, SVec.toList_nil, SList.toList_nil,
      List.append_nil, List.getElem?_nil, Option.bind_none, ite_self]
  | _, _, .atF (n := n) i p => by
    rw [SVal.dflt_fixed, SVal.findM_atF', SVec.toList_replicate]
    simp only [Path.dfltOk, Bool.and_eq_true, decide_eq_true_eq]
    by_cases h : i.1.toNat < n
    · rw [List.getElem?_replicate_of_lt h, Option.bind_some, findM_dflt p]
      simp only [h, true_and]
    · rw [List.getElem?_eq_none (by rw [List.length_replicate]; omega), Option.bind_none]
      simp only [h, false_and, if_false]

theorem LTm.eval_ltNat {a : LTm C (.val .uint)} {k : PrimTy.uint.Denote} (n : Nat)
    (ha : (a.eval g ν : Option _) = some k) :
    ((LTm.ltNat a n).eval g ν : Option Bool) = some (decide (k.1.toNat < n)) := by
  have hk := k.2
  simp only [PrimTy.inRange, decide_eq_true_eq] at hk
  unfold LTm.ltNat
  split
  · rename_i hn
    rw [LTm.eval_lt_some g ν ha (LTm.eval_nat g ν n), uintOfNat_val hn]
    exact congrArg some (decide_eq_decide.2 (by omega))
  · rename_i hn
    exact congrArg some (Eq.symm (decide_eq_true (by omega)))

theorem dfltHas_eval : ∀ {U V : Ty} (r : TSegs C U V) {p : Path U V}, r.eval g ν = some p →
    ((dfltHas r).eval g ν : Option Bool) = some p.dfltOk
  | _, _, .nil, p, hr => by cases hr; rfl
  | _, _, .field h r, p, hr => by
    obtain ⟨p', hp', rfl⟩ := eval_field_some g ν hr
    exact dfltHas_eval r hp'
  | _, _, .key i r, p, hr => by
    obtain ⟨j, p', -, hp', rfl⟩ := eval_key_some g ν hr
    exact dfltHas_eval r hp'
  | _, _, .at i r, p, hr => by
    obtain ⟨k, p', -, -, rfl⟩ := eval_at_some g ν hr
    rfl
  | _, _, .atF (n := n) i r, p, hr => by
    obtain ⟨k, p', hk, hp', rfl⟩ := eval_atF_some g ν hr
    rw [show dfltHas (.atF i r) = .cond (.ltNat i n) (dfltHas r) (.lit (p := .bool) false) from rfl,
      LTm.eval_cond_some g ν _ _ (LTm.eval_ltNat g ν n hk)]
    by_cases h : k.1.toNat < n
    · simp only [h, decide_true, if_true, Path.dfltOk, Bool.true_and]
      exact dfltHas_eval r hp'
    · simp only [h, decide_false, if_false, Path.dfltOk, Bool.false_and, Bool.false_eq_true]
      rfl

/-- **A default value, read.** -/
theorem dfltRd_rep (E : Ty) : VRd.Rep g ν (dfltRd E) (SVal.dflt E).obs := by
  intro V c r p hr
  cases c with
  | word P =>
    show some (PrimTy.dflt P) = some (SVal.wordOf ((SVal.dflt E).findM p))
    rw [findM_dflt]; split <;> rfl
  | len E' =>
    show some (uintOfNat 0) = some (uintOfNat (SVal.lenOf ((SVal.dflt E).findM p)))
    rw [findM_dflt]; split <;> rfl
  | has V =>
    show ((dfltHas r).eval g ν : Option Bool) = _
    rw [dfltHas_eval g ν r hr]
    show some p.dfltOk = some ((SVal.dflt E).findM p).isSome
    rw [findM_dflt]; split <;> simp_all only [Option.isSome_some, Option.isSome_none]

/-- The initialized reads of a newly allocated dynamic array. -/
theorem newArrRd_array_rep (E : Ty) (n : LTm C (.val .uint)) (v : PrimTy.uint.Denote)
    (h : (RefTy.array E).newArrOk = true) (hn : n.eval g ν = some v) :
    VRd.Rep g ν (newArrArrayRd E n) (newArrT (.array E) v h).obs := by
  apply arrRd_rep
  · simp only [newArrT, SVal.obs_len, SVal.findM_nil', SVal.lenOf, SVal.view,
      List.length_replicate]
    rw [hn]
    congr 1
    apply Subtype.ext
    have hv := v.2
    simp only [PrimTy.inRange, decide_eq_true_eq] at hv
    rw [uintOfNat_val (by omega), Int.toNat_of_nonneg hv.1]
  · rfl
  · intro i k hk V c r p hr
    rw [LTm.eval_cond_some g ν _ _ (LTm.eval_lt_some g ν hk hn)]
    have hv := v.2
    have hkv := k.2
    simp only [PrimTy.inRange, decide_eq_true_eq] at hv hkv
    have he : (k.1 < v.1) = (k.1.toNat < v.1.toNat) := propext (by omega)
    simp only [he]
    by_cases hkn : k.1.toNat < v.1.toNat
    · simp only [hkn, decide_true, if_true]
      have hd := dfltRd_rep g ν E V c r p hr
      cases c <;> simpa only [CK.obsV, CK.obsC, Comp.word, Comp.len, Comp.has,
        SVal.obs, SVal.obsOpt, Option.bind_some, newArrT_find_at, hkn, if_true] using hd
    · simp only [hkn, decide_false]
      cases c <;> simp only [Bool.false_eq_true, if_false, CK.obsV, CK.obsC,
        Comp.word, Comp.len, Comp.has, SVal.obs, SVal.obsOpt, Option.bind_some,
        newArrT_find_at, hkn, CK.absent] <;> rfl

theorem newArrRd_rep (R : RefTy) (h : R.newArrOk = true)
    (n : LTm C (.val .uint)) (v : PrimTy.uint.Denote) (hn : n.eval g ν = some v) :
    VRd.Rep g ν (newArrRd R h n) (newArrT R v h).obs := by
  cases R with
  | array E => exact newArrRd_array_rep g ν E n v h hn
  | struct | fixed | mapping => cases h

theorem bnd_obs {T : Ty} (v : SVal T) : Bnd v.obs := by
  intro E p
  show SVal.lenOf (v.findM p) < 2 ^ 256
  cases v.findM p with
  | none => exact SVal.zero_lt_bound
  | some w => cases w with | array e sh hn => exact hn

/-- Every lazy read below a converted fixed-array element matches the
source snapshot, padded default or absent destination slot. -/
theorem fixedCopyChildRd_rep {E : Ty} {n : Nat} {R : RefTy}
    (shape : FixedCopy E n R) (a : VRd C (.ref (.fixed E n)))
    (v : SVal (.ref (.fixed E n))) (ha : VRd.Rep g ν a v.obs)
    (i : LTm C (.val .uint)) (k : PrimTy.uint.Denote)
    (hi : i.eval g ν = some k) :
    VRd.Rep g ν (fixedCopyChildRd shape a i) (shape.child v.obs k) := by
  intro V c r p hr
  unfold fixedCopyChildRd
  rw [LTm.eval_cond_some g ν _ _ (LTm.eval_ltNat g ν shape.targetLength hi)]
  by_cases ht : k.1.toNat < shape.targetLength
  · simp only [ht, decide_true, if_true]
    rw [LTm.eval_cond_some g ν _ _ (LTm.eval_ltNat g ν n hi)]
    by_cases hs : k.1.toNat < n
    · simp only [hs, decide_true, if_true]
      have hp := ha.find g ν (s := .atF i .nil) (by rw [TSegs.eval_atF, hi]; rfl)
      have he := stripRS_rep g ν r c hp (Bnd.find (bnd_obs v) (.atF k .nil)) hr
      simp only [FixedCopy.child, ht, hs, if_true, TVal.strip_find_atF]
      cases c <;> simpa only [CK.obsV, CK.obsC, Comp.word, Comp.len, Comp.has,
        TVal.strip, TVal.ofComp] using he
    · simp only [hs, decide_false, Bool.false_eq_true, if_false]
      have he := stripRS_rep g ν r c (dfltRd_rep g ν E) (bnd_obs (SVal.dflt E)) hr
      cases c <;> simpa only [FixedCopy.child, ht, hs, if_true, if_false, SVal.obs_strip,
        CK.obsV, CK.obsC, Comp.word, Comp.len, Comp.has, TVal.strip, TVal.ofComp] using he
  · simp only [ht, decide_false, Bool.false_eq_true, if_false]
    cases c <;> simp only [FixedCopy.child, ht, if_false, CK.absent, CK.obsV, CK.obsC,
      Comp.word, Comp.len, Comp.has, SVal.obsOpt, Option.bind_none] <;> rfl

/-- The lazy fixed-array copy reader preserves all observations of a
successful snapshot, including padded fixed tails. -/
theorem fixedCopyRd_rep {E : Ty} {n : Nat} {R : RefTy}
    (shape : FixedCopy E n R) (a : VRd C (.ref (.fixed E n)))
    (v : SVal (.ref (.fixed E n))) (ha : VRd.Rep g ν a v.obs) :
    VRd.Rep g ν (fixedCopyRd shape a) (shape.observe v.obs) := by
  cases shape with
  | dynamic bound =>
    apply arrRd_rep
    · rfl
    · rfl
    · intro i k hi V c r p hr
      have he := fixedCopyChildRd_rep g ν (.dynamic bound) a v ha i k hi V c r p hr
      cases c <;> simpa only [FixedCopy.observe, CK.obsV, CK.obsC,
        Comp.word, Comp.len, Comp.has] using he
  | fixed m fits =>
    intro V c r p hr
    cases r with
    | nil => cases hr; cases c; rfl
    | atF i r =>
      obtain ⟨k, p', hk, hp, rfl⟩ := eval_atF_some g ν hr
      have he := fixedCopyChildRd_rep g ν (.fixed m fits) a v ha i k hk V c r p' hp
      cases c <;> simpa only [fixedCopyRd, fixedArrRd, FixedCopy.observe, CK.obsV,
        CK.obsC, Comp.word, Comp.len, Comp.has] using he

/-- **One more live element, read, is `TVal.extendA`.** -/
theorem extendRd_rep {E : Ty} {a : VRd C (.ref (.array E))} {L : LTm C (.val .uint)}
    {t : TVal (.ref (.array E))} (ha : VRd.Rep g ν a t)
    (hL : (L.eval g ν : Option PrimTy.uint.Denote) = some (uintOfNat (t.len .nil)))
    (hn : t.len .nil + 1 < 2 ^ 256) : VRd.Rep g ν (extendRd a L) (TVal.extendA t) := by
  unfold extendRd TVal.extendA
  by_cases hp : E.isPrimitive = true
  · simp only [hp, if_true, Bool.true_or]
    exact pushRd_rep g ν ha (dfltRd_rep g ν E) hL hn
  · simp only [hp, if_false, Bool.false_or, Bool.false_eq_true]
    have hh : ((a (.has _) (.at L .nil)).eval g ν : Option Bool) =
        some (t.has (.at (uintOfNat (t.len .nil)) .nil)) := by
      have := ha _ (.has _) (.at L .nil) (.at (uintOfNat (t.len .nil)) .nil)
        (by rw [TSegs.eval_at, hL]; rfl)
      rw [this]; rfl
    intro V c r p hr
    rw [LTm.eval_cond_some g ν _ _ hh]
    by_cases h : t.has (.at (uintOfNat (t.len .nil)) .nil) = true
    · simp only [h, if_true, Bool.not_true, Bool.false_eq_true, if_false]
      exact setLenRd_rep g ν ha (LTm.eval_succK g ν hL hn) V c r p hr
    · simp only [h, if_false, Bool.false_eq_true, Bool.not_false, if_true]
      exact pushRd_rep g ν ha (dfltRd_rep g ν E) hL hn V c r p hr


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
