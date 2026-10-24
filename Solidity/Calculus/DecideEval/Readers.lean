import Solidity.Calculus.Decide
import Solidity.Theory.Typed.Mem

/-!
# The reduction's evaluation: paths and readers

Paths, case trees and the comparison, and the readers (arrays, defaults).

A piece of `Calculus/DecideEval.lean`, whose docstring describes the whole.
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

end Decide

end Solidity
