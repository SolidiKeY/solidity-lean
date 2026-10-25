import Solidity.Calculus.DependentReduction

/-!
# The leaf decision never refuses its fragment

`flattenedArithmetic?` (`Calculus/LeafArithmetic.lean`) is complete given
its certificate; this module proves that the certificate exists on a
syntactic fragment of leaves, under size bounds.
-/

namespace Solidity.Linear

/-! ## Widths: the arithmetic variables a compiled formula mentions -/

theorem Lin.length_sub : ∀ (as bs : Lin), (Lin.sub as bs).length = max as.length bs.length
  | [], bs => by simp only [Lin.sub, List.length_map, List.length_nil, Nat.zero_max]
  | _ :: _, [] => by simp only [Lin.sub, List.length_nil, Nat.max_zero]
  | _ :: as, _ :: bs => by
    simp only [Lin.sub, List.length_cons, Lin.length_sub as bs, Nat.add_max_add_right]

theorem Lin.length_add (as bs : Lin) : (Lin.add as bs).length = max as.length bs.length := by
  simp only [Lin.add, Lin.length_sub, List.length_map]

theorem Lin.length_basis : ∀ k : Nat, (Lin.basis k).length = k + 1
  | 0 => rfl
  | k + 1 => by simp only [Lin.basis, List.length_cons, Lin.length_basis k]

/-- An affine form over the first `n` variables. -/
def Affine.W (n : Nat) (a : Affine) : Prop := a.coeff.length ≤ n

theorem Affine.W.literal (n : Nat) (c : Int) : (Affine.literal c).W n := Nat.zero_le n

theorem Affine.W.variable {n k : Nat} (h : k < n) : (Affine.variable k).W n := by
  simp only [Affine.W, Affine.variable, Lin.length_basis]
  omega

theorem Affine.W.add {n : Nat} {a b : Affine} (ha : a.W n) (hb : b.W n) : (a.add b).W n := by
  simp only [Affine.W, Affine.add, Lin.length_add] at *
  omega

theorem Affine.W.sub {n : Nat} {a b : Affine} (ha : a.W n) (hb : b.W n) : (a.sub b).W n := by
  simp only [Affine.W, Affine.sub, Lin.length_sub] at *
  omega

theorem Affine.W.offset {n : Nat} {a : Affine} (ha : a.W n) (c : Int) : (a.offset c).W n := ha

theorem Affine.width_eq {n : Nat} {a b : Affine} (ha : a.W n) (hb : b.W n) :
    (a.eq b).width ≤ n := by
  simp only [Affine.W, Affine.eq, AFml.width, Lin.length_sub] at *
  omega

theorem Affine.width_le {n : Nat} {a b : Affine} (ha : a.W n) (hb : b.W n) :
    (a.le b).width ≤ n := by
  simp only [Affine.W, Affine.le, AFml.width, Lin.length_sub] at *
  omega

theorem Affine.width_compare {n : Nat} (op : BinOp) {a b : Affine} (ha : a.W n) (hb : b.W n) :
    (a.compare op b).width ≤ n := by
  cases op <;> simp only [Affine.compare, AFml.width] <;>
    first
    | exact Affine.width_le ha hb
    | exact Affine.width_le hb ha
    | exact Affine.width_eq ha hb
    | exact Nat.zero_le n

theorem AFml.width_and {n : Nat} {φ ψ : AFml} (h : φ.width ≤ n) (k : ψ.width ≤ n) :
    (AFml.and φ ψ).width ≤ n := by
  simp only [AFml.width]
  omega

theorem AFml.width_imp {n : Nat} {φ ψ : AFml} (h : φ.width ≤ n) (k : ψ.width ≤ n) :
    (AFml.imp φ ψ).width ≤ n := by
  simp only [AFml.width]
  omega

theorem AFml.width_not {n : Nat} {φ : AFml} (h : φ.width ≤ n) : (AFml.not φ).width ≤ n := h

/-- A checked scalar over the first `n` variables. -/
def CheckedScalar.W {p : PrimTy} (n : Nat) (a : CheckedScalar p) : Prop :=
  a.code.W n ∧ a.defined.width ≤ n

theorem CheckedScalar.W.range {n : Nat} (p : PrimTy) {a : Affine} (ha : a.W n) :
    (CheckedScalar.range p a).width ≤ n :=
  AFml.width_and (Affine.width_le (Affine.W.literal n 0) ha) (Affine.width_le ha (Affine.W.literal n _))

theorem CheckedScalar.W.ofInt {n : Nat} (p : PrimTy) {a : Affine} (ha : a.W n) :
    (CheckedScalar.ofInt p a).W n := ⟨ha, CheckedScalar.W.range p ha⟩

theorem CheckedScalar.W.guard {n : Nat} {p : PrimTy} {g : AFml} {a : CheckedScalar p}
    (hg : g.width ≤ n) (ha : a.W n) : (a.guard g).W n := ⟨ha.1, AFml.width_and hg ha.2⟩

theorem CheckedScalar.W.arith {n : Nat} {p : PrimTy} (subtract : Bool) {a b : CheckedScalar p}
    (ha : a.W n) (hb : b.W n) : (CheckedScalar.arith subtract a b).W n := by
  apply CheckedScalar.W.guard (AFml.width_and ha.2 hb.2)
  apply CheckedScalar.W.ofInt
  unfold CheckedScalar.arithCode
  cases subtract
  · exact (ha.1.add hb.1).offset _
  · exact (ha.1.sub hb.1).offset _

theorem Affine.W.scale {n : Nat} {a : Affine} (ha : a.W n) (c : Int) : (a.scale c).W n := by
  simp only [Affine.W, Affine.scale, Lin.length_scale]
  exact ha

theorem CheckedScalar.W.scale {n : Nat} {p : PrimTy} (c : Int) {a : CheckedScalar p} (ha : a.W n) :
    (CheckedScalar.scale c a).W n :=
  CheckedScalar.W.guard ha.2 (CheckedScalar.W.ofInt p (((ha.1.offset _).scale c).offset _))

theorem CheckedScalar.W.compl {n : Nat} {a : CheckedScalar .uint} (ha : a.W n) :
    (CheckedScalar.compl a).W n :=
  CheckedScalar.W.guard ha.2 (CheckedScalar.W.ofInt .uint ((Affine.W.literal _ _).sub ha.1))

theorem CheckedScalar.W.eq {n : Nat} {p : PrimTy} {a b : CheckedScalar p} (ha : a.W n)
    (hb : b.W n) : (a.eq b).width ≤ n :=
  AFml.width_and ha.2 (AFml.width_and hb.2 (Affine.width_eq ha.1 hb.1))

/-- A checked Boolean over the first `n` variables. -/
def CheckedBool.W (n : Nat) (a : CheckedBool) : Prop := a.yes.width ≤ n ∧ a.no.width ≤ n

theorem CheckedBool.W.disj {n : Nat} {a b : AFml} (ha : a.width ≤ n) (hb : b.width ≤ n) :
    (CheckedBool.disj a b).width ≤ n := AFml.width_imp (AFml.width_not ha) hb

theorem CheckedBool.W.ofScalar {n : Nat} {a : CheckedScalar .bool} (ha : a.W n) :
    (CheckedBool.ofScalar a).W n :=
  ⟨AFml.width_and ha.2 (Affine.width_eq ha.1 (Affine.W.literal n _)),
    AFml.width_and ha.2 (Affine.width_eq ha.1 (Affine.W.literal n _))⟩

theorem CheckedBool.W.not {n : Nat} {a : CheckedBool} (ha : a.W n) : a.not.W n := ⟨ha.2, ha.1⟩

theorem CheckedBool.W.and {n : Nat} {a b : CheckedBool} (ha : a.W n) (hb : b.W n) :
    (a.and b).W n :=
  ⟨AFml.width_and ha.1 hb.1, CheckedBool.W.disj ha.2 (AFml.width_and ha.1 hb.2)⟩

theorem CheckedBool.W.or {n : Nat} {a b : CheckedBool} (ha : a.W n) (hb : b.W n) :
    (a.or b).W n :=
  ⟨CheckedBool.W.disj ha.1 (AFml.width_and ha.2 hb.1), AFml.width_and ha.2 hb.2⟩

theorem CheckedBool.W.eq {n : Nat} {a b : CheckedBool} (ha : a.W n) (hb : b.W n) :
    (a.eq b).W n :=
  ⟨CheckedBool.W.disj (AFml.width_and ha.1 hb.1) (AFml.width_and ha.2 hb.2),
    CheckedBool.W.disj (AFml.width_and ha.1 hb.2) (AFml.width_and ha.2 hb.1)⟩

theorem CheckedBool.W.comparison {n : Nat} {p : PrimTy} (op : BinOp) {a b : CheckedScalar p}
    (ha : a.W n) (hb : b.W n) : (CheckedBool.comparison op a b).W n :=
  ⟨AFml.width_and (AFml.width_and ha.2 hb.2) (Affine.width_compare op (ha.1.offset _) (hb.1.offset _)),
    AFml.width_and (AFml.width_and ha.2 hb.2)
      (AFml.width_not (Affine.width_compare op (ha.1.offset _) (hb.1.offset _)))⟩

end Solidity.Linear

namespace Solidity.Decide

open Semantics ReadRealization Linear ScalarCode

variable {C : Contract}

/-- The height of a term. -/
def LTm.depth : {s : Srt} → LTm C s → Nat
  | _, .var _ | _, .app0 _ | _, .err => 1
  | _, .app1 _ a | _, .obsW a | _, .obsL a | _, .obsH a => a.depth + 1
  | _, .app2 _ a b | _, .index _ a b | _, .seq a b | _, .orElse a b => max a.depth b.depth + 1
  | _, .app3 _ a b c => max a.depth (max b.depth c.depth) + 1
  | _, .kite a b t e => max (max a.depth b.depth) (max t.depth e.depth) + 1

/-! ## The arithmetic compiler's fragment

The terms after flattening: no storage read is left, a read is a guard
followed by its fresh atom. -/

/-- The scalar terms `CheckedValue` encodes, its atoms satisfying `ps` and
its transaction fields `es` (membership in the layout's lists, or nothing:
`LTm.NumS`). -/
inductive LTm.Num (ps : Parameter → Prop) (es : EnvKey → Prop) : {p : PrimTy} → LTm C (.val p) → Prop
  | var {p : PrimTy} (k : Nat) (h : ps ⟨p, k⟩) : LTm.Num ps es (.var (p := p) k)
  | lit {p : PrimTy} (v : p.Denote) : LTm.Num ps es (.app0 (.lit v))
  | env (e : EnvKey) (h : es e) : LTm.Num ps es (.app0 (.env e))
  | add {p : PrimTy} (h : BinOp.add.accepts p = true) {a b : LTm C (.val p)} :
      LTm.Num ps es a → LTm.Num ps es b → LTm.Num ps es (.app2 (.binop .add h) a b)
  | sub {p : PrimTy} (h : BinOp.sub.accepts p = true) {a b : LTm C (.val p)} :
      LTm.Num ps es a → LTm.Num ps es b → LTm.Num ps es (.app2 (.binop .sub h) a b)
  | mulL {p : PrimTy} (h : BinOp.mul.accepts p = true) (v : p.Denote) {b : LTm C (.val p)} :
      LTm.Num ps es b → LTm.Num ps es (.app2 (.binop .mul h) (.app0 (.lit v)) b)
  | mulR {p : PrimTy} (h : BinOp.mul.accepts p = true) {a : LTm C (.val p)} (v : p.Denote) :
      LTm.Num ps es a → LTm.Num ps es (.app2 (.binop .mul h) a (.app0 (.lit v)))
  | neg (h : UnOp.neg.accepts .int = true) {a : LTm C (.val .int)} :
      LTm.Num ps es a → LTm.Num ps es (.app1 (.unop .neg h) a)
  | bnot (h : UnOp.bnot.accepts .uint = true) {a : LTm C (.val .uint)} :
      LTm.Num ps es a → LTm.Num ps es (.app1 (.unop .bnot h) a)
  | seq {q p : PrimTy} {d : LTm C (.val q)} {a : LTm C (.val p)} :
      LTm.Num ps es d → LTm.Num ps es a → LTm.Num ps es (.seq d a)
  | err {p : PrimTy} : LTm.Num ps es (LTm.err (C := C) (s := .val p))

theorem LTm.depth_pos {s : Srt} (t : LTm C s) : 0 < t.depth := by
  cases t <;> simp only [LTm.depth] <;> omega

theorem Layout.index_lt {r : Ref C} : ∀ {rs : List (Ref C)}, r ∈ rs → Layout.index r rs < rs.length
  | [], h => nomatch h
  | q :: rs, h => by
    unfold Layout.index
    by_cases he : r = q
    · simp only [he, if_true, List.length_cons]; omega
    · simp only [he, if_false, List.length_cons]
      have := Layout.index_lt ((List.mem_cons.mp h).resolve_left he)
      omega

theorem Parameters.index_lt {q : Parameter} : ∀ {ps : List Parameter}, q ∈ ps →
    Parameters.index q ps < ps.length
  | [], h => nomatch h
  | x :: ps, h => by
    unfold Parameters.index
    by_cases he : q = x
    · simp only [he, if_true, List.length_cons]; omega
    · simp only [he, if_false, List.length_cons]
      have := Parameters.index_lt ((List.mem_cons.mp h).resolve_left he)
      omega

theorem Inputs.index_lt {e : EnvKey} : ∀ {es : List EnvKey}, e ∈ es → Inputs.index e es < es.length
  | [], h => nomatch h
  | x :: es, h => by
    unfold Inputs.index
    by_cases he : e = x
    · simp only [he, if_true, List.length_cons]; omega
    · simp only [he, if_false, List.length_cons]
      have := Inputs.index_lt ((List.mem_cons.mp h).resolve_left he)
      omega

/-- A compiled scalar mentions only the inputs of its layout. -/
def CheckedValue.Good {ps : List Parameter} {es : List EnvKey} {p : PrimTy} {t : LTm C (.val p)}
    (v : CheckedValue (ps := ps) (es := es) t) : Prop :=
  ∀ rs : List (Ref C), (∀ r ∈ v.refs, r ∈ rs) → (v.lower rs).W (es.length + (ps.length + rs.length))

/-- A compiled Boolean mentions only the inputs of its layout. -/
def BooleanValue.Good {ps : List Parameter} {es : List EnvKey} {t : LTm C (.val .bool)}
    (v : BooleanValue (ps := ps) (es := es) t) : Prop :=
  ∀ rs : List (Ref C), (∀ r ∈ v.refs, r ∈ rs) → (v.lower rs).W (es.length + (ps.length + rs.length))

/-- A compiled formula mentions only the inputs of its layout. -/
def StorageEncoding.Good {ps : List Parameter} {es : List EnvKey} {φ : LFml C}
    (v : StorageEncoding (ps := ps) (es := es) φ) : Prop :=
  ∀ rs : List (Ref C), (∀ r ∈ v.refs, r ∈ rs) → (v.lower rs).width ≤ es.length + (ps.length + rs.length)

theorem CheckedValue.good_ofStatic {ps : List Parameter} {es : List EnvKey} {p : PrimTy}
    {t : LTm C (.val p)} (v : StaticValue t) :
    (CheckedValue.ofStatic (ps := ps) (es := es) v).Good := by
  intro rs hr
  refine ⟨?_, Nat.zero_le _⟩
  cases v with
  | lit v => exact Affine.W.literal _ _
  | constant v _ => exact Affine.W.literal _ _
  | read r =>
    apply Affine.W.variable
    have := Layout.index_lt (hr _ List.mem_cons_self)
    omega

theorem CheckedValue.ofTermFuel?_good (ps : List Parameter) (es : List EnvKey) :
    ∀ {p : PrimTy} {t : LTm C (.val p)}, t.Num (· ∈ ps) (· ∈ es) → ∀ (n : Nat), t.depth < n →
      ∃ v, CheckedValue.ofTermFuel? (C := C) (es := es) ps n t = some v ∧ v.Good := by
  intro p t h
  induction h with
  | @var p k hk =>
    intro n hn
    obtain ⟨n, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by simp only [LTm.depth] at hn; omega⟩
    cases hs : StaticValue.ofTerm? (LTm.var (C := C) (p := p) k) with
    | some w =>
      refine ⟨_, ?_, CheckedValue.good_ofStatic w⟩
      change (match StaticValue.ofTerm? (LTm.var (C := C) (p := p) k) with
        | some v => some (CheckedValue.ofStatic v)
        | none => if h : Parameter.mk p k ∈ ps then some (CheckedValue.parameter k h) else none) = _
      rw [hs]
    | none =>
      refine ⟨CheckedValue.parameter k hk, ?_, ?_⟩
      · change (match StaticValue.ofTerm? (LTm.var (C := C) (p := p) k) with
          | some v => some (CheckedValue.ofStatic v)
          | none => if h : Parameter.mk p k ∈ ps then some (CheckedValue.parameter k h) else none) = _
        rw [hs, dif_pos hk]
      · intro rs _
        refine ⟨Affine.W.variable ?_, Nat.zero_le _⟩
        have := Parameters.index_lt hk
        omega
  | @lit p v =>
    intro n hn
    obtain ⟨n, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by simp only [LTm.depth] at hn; omega⟩
    exact ⟨_, rfl, CheckedValue.good_ofStatic _⟩
  | env e he =>
    intro n hn
    obtain ⟨n, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by simp only [LTm.depth] at hn; omega⟩
    cases hs : StaticValue.ofTerm? (LTm.app0 (C := C) (.env e)) with
    | some w =>
      refine ⟨_, ?_, CheckedValue.good_ofStatic w⟩
      change (match StaticValue.ofTerm? (LTm.app0 (C := C) (.env e)) with
        | some v => some (CheckedValue.ofStatic v)
        | none => if h : e ∈ es then some (CheckedValue.environment e h) else none) = _
      rw [hs]
    | none =>
      refine ⟨CheckedValue.environment e he, ?_, ?_⟩
      · change (match StaticValue.ofTerm? (LTm.app0 (C := C) (.env e)) with
          | some v => some (CheckedValue.ofStatic v)
          | none => if h : e ∈ es then some (CheckedValue.environment e h) else none) = _
        rw [hs, dif_pos he]
      · intro rs _
        refine ⟨Affine.W.variable ?_, Nat.zero_le _⟩
        have := Inputs.index_lt he
        omega
  | @add p hp a b _ _ iha ihb =>
    intro n hn
    obtain ⟨n, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by simp only [LTm.depth] at hn; omega⟩
    simp only [LTm.depth] at hn
    obtain ⟨va, hva, ga⟩ := iha n (by omega)
    obtain ⟨vb, hvb, gb⟩ := ihb n (by omega)
    cases hs : StaticValue.ofTerm? (LTm.app2 (.binop .add hp) a b) with
    | some w => exact ⟨_, by simp only [CheckedValue.ofTermFuel?, hs], CheckedValue.good_ofStatic w⟩
    | none =>
      refine ⟨CheckedValue.add hp va vb, by simp only [CheckedValue.ofTermFuel?, hs, hva, hvb]; rfl, ?_⟩
      intro rs hr
      exact CheckedScalar.W.arith false (ga rs (fun r hm => hr r (List.mem_append_left _ hm))) (gb rs (fun r hm => hr r (List.mem_append_right _ hm)))
  | @sub p hp a b _ _ iha ihb =>
    intro n hn
    obtain ⟨n, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by simp only [LTm.depth] at hn; omega⟩
    simp only [LTm.depth] at hn
    obtain ⟨va, hva, ga⟩ := iha n (by omega)
    obtain ⟨vb, hvb, gb⟩ := ihb n (by omega)
    cases hs : StaticValue.ofTerm? (LTm.app2 (.binop .sub hp) a b) with
    | some w => exact ⟨_, by simp only [CheckedValue.ofTermFuel?, hs], CheckedValue.good_ofStatic w⟩
    | none =>
      refine ⟨CheckedValue.sub hp va vb, by simp only [CheckedValue.ofTermFuel?, hs, hva, hvb]; rfl, ?_⟩
      intro rs hr
      exact CheckedScalar.W.arith true (ga rs (fun r hm => hr r (List.mem_append_left _ hm))) (gb rs (fun r hm => hr r (List.mem_append_right _ hm)))
  | @neg hp a _ iha =>
    intro n hn
    obtain ⟨n, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by simp only [LTm.depth] at hn; omega⟩
    simp only [LTm.depth] at hn
    obtain ⟨va, hva, ga⟩ := iha n (by omega)
    cases hs : StaticValue.ofTerm? (LTm.app1 (C := C) (.unop .neg hp) a) with
    | some w => exact ⟨_, by simp only [CheckedValue.ofTermFuel?, hs], CheckedValue.good_ofStatic w⟩
    | none =>
      refine ⟨CheckedValue.neg hp va, by simp only [CheckedValue.ofTermFuel?, hs, hva]; rfl, ?_⟩
      intro rs hr
      exact CheckedScalar.W.scale _ (ga rs hr)
  | @bnot hp a _ iha =>
    intro n hn
    obtain ⟨n, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by simp only [LTm.depth] at hn; omega⟩
    simp only [LTm.depth] at hn
    obtain ⟨va, hva, ga⟩ := iha n (by omega)
    cases hs : StaticValue.ofTerm? (LTm.app1 (C := C) (.unop .bnot hp) a) with
    | some w => exact ⟨_, by simp only [CheckedValue.ofTermFuel?, hs], CheckedValue.good_ofStatic w⟩
    | none =>
      refine ⟨CheckedValue.bnot hp va, by simp only [CheckedValue.ofTermFuel?, hs, hva]; rfl, ?_⟩
      intro rs hr
      exact CheckedScalar.W.compl (ga rs hr)
  | @mulL p hp v b _ ihb =>
    intro n hn
    obtain ⟨n, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by simp only [LTm.depth] at hn; omega⟩
    simp only [LTm.depth] at hn
    obtain ⟨vb, hvb, gb⟩ := ihb n (by omega)
    cases hs : StaticValue.ofTerm? (LTm.app2 (.binop .mul hp) (.app0 (.lit v)) b) with
    | some w => exact ⟨_, by simp only [CheckedValue.ofTermFuel?, hs], CheckedValue.good_ofStatic w⟩
    | none =>
      refine ⟨CheckedValue.mulLit hp v rfl vb,
        by simp only [CheckedValue.ofTermFuel?, hs, LTm.lit?, hvb]; rfl, ?_⟩
      intro rs hr
      exact CheckedScalar.W.scale _ (gb rs hr)
  | @mulR p hp a v _ iha =>
    intro n hn
    obtain ⟨n, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by simp only [LTm.depth] at hn; omega⟩
    simp only [LTm.depth] at hn
    obtain ⟨va, hva, ga⟩ := iha n (by omega)
    cases hs : StaticValue.ofTerm? (LTm.app2 (.binop .mul hp) a (.app0 (.lit v))) with
    | some w => exact ⟨_, by simp only [CheckedValue.ofTermFuel?, hs], CheckedValue.good_ofStatic w⟩
    | none =>
      cases hl : a.lit? with
      | some r =>
        obtain ⟨w, hw⟩ := r
        obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by omega⟩
        refine ⟨CheckedValue.mulLit hp w hw (CheckedValue.ofStatic (.lit v)),
          by simp only [CheckedValue.ofTermFuel?, hs, hl]; rfl, ?_⟩
        intro rs hr
        exact CheckedScalar.W.scale _ (CheckedValue.good_ofStatic (.lit v) rs hr)
      | none =>
        refine ⟨CheckedValue.litMul hp v rfl va,
          by simp only [CheckedValue.ofTermFuel?, hs, hl, hva]; rfl, ?_⟩
        intro rs hr
        exact CheckedScalar.W.scale _ (ga rs hr)
  | @seq q p d a _ _ ihd iha =>
    intro n hn
    obtain ⟨n, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by simp only [LTm.depth] at hn; omega⟩
    simp only [LTm.depth] at hn
    obtain ⟨vd, hvd, gd⟩ := ihd n (by omega)
    obtain ⟨va, hva, ga⟩ := iha n (by omega)
    cases hs : StaticValue.ofTerm? (LTm.seq d a) with
    | some w => exact ⟨_, by simp only [CheckedValue.ofTermFuel?, hs], CheckedValue.good_ofStatic w⟩
    | none =>
      refine ⟨CheckedValue.seq vd va, by simp only [CheckedValue.ofTermFuel?, hs, hvd, hva]; rfl, ?_⟩
      intro rs hr
      exact CheckedScalar.W.guard (gd rs (fun r hm => hr r (List.mem_append_left _ hm))).2 (ga rs (fun r hm => hr r (List.mem_append_right _ hm)))
  | @err p =>
    intro n hn
    obtain ⟨n, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by simp only [LTm.depth] at hn; omega⟩
    cases hs : StaticValue.ofTerm? (LTm.err (C := C) (s := .val p)) with
    | some w =>
      refine ⟨_, ?_, CheckedValue.good_ofStatic w⟩
      change (match StaticValue.ofTerm? (LTm.err (C := C) (s := .val p)) with
        | some v => some (CheckedValue.ofStatic v)
        | none => some CheckedValue.failed) = _
      rw [hs]
    | none =>
      refine ⟨CheckedValue.failed, ?_, fun _ _ => ⟨Affine.W.literal _ _, Nat.zero_le _⟩⟩
      change (match StaticValue.ofTerm? (LTm.err (C := C) (s := .val p)) with
        | some v => some (CheckedValue.ofStatic v)
        | none => some CheckedValue.failed) = _
      rw [hs]

theorem CheckedValue.ofTermIn?_good {ps : List Parameter} {es : List EnvKey} {p : PrimTy}
    {t : LTm C (.val p)} (h : t.Num (· ∈ ps) (· ∈ es)) (hd : t.depth ≤ 1023) :
    ∃ v, CheckedValue.ofTermIn? (C := C) (es := es) ps t = some v ∧ v.Good :=
  CheckedValue.ofTermFuel?_good ps es h 1024 (by omega)

/-- The Boolean terms `BooleanValue` encodes. -/
inductive LTm.BoolV (ps : Parameter → Prop) (es : EnvKey → Prop) : LTm C (.val .bool) → Prop
  | var (k : Nat) (h : ps ⟨.bool, k⟩) : LTm.BoolV ps es (.var (p := .bool) k)
  | lit (v : Bool) : LTm.BoolV ps es (.app0 (.lit (p := .bool) v))
  | err : LTm.BoolV ps es (LTm.err (C := C) (s := .val .bool))
  | not {a : LTm C (.val .bool)} : LTm.BoolV ps es a → LTm.BoolV ps es (.app1 (.unop .not rfl) a)
  | and {a b : LTm C (.val .bool)} : LTm.BoolV ps es a → LTm.BoolV ps es b →
      LTm.BoolV ps es (.app2 (.binop .and rfl) a b)
  | or {a b : LTm C (.val .bool)} : LTm.BoolV ps es a → LTm.BoolV ps es b →
      LTm.BoolV ps es (.app2 (.binop .or rfl) a b)
  | eqB {a b : LTm C (.val .bool)} : LTm.BoolV ps es a → LTm.BoolV ps es b →
      LTm.BoolV ps es (.app2 (.binop .eqB rfl) a b)
  | neB {a b : LTm C (.val .bool)} : LTm.BoolV ps es a → LTm.BoolV ps es b →
      LTm.BoolV ps es (.app2 (.binop .neB rfl) a b)
  | eqN {p : PrimTy} (hp : p.isNumeric = true) {a b : LTm C (.val p)} :
      LTm.Num ps es a → LTm.Num ps es b → LTm.BoolV ps es (.app2 (.binop .eqB rfl) a b)
  | neN {p : PrimTy} (hp : p.isNumeric = true) {a b : LTm C (.val p)} :
      LTm.Num ps es a → LTm.Num ps es b → LTm.BoolV ps es (.app2 (.binop .neB rfl) a b)
  | lt {p : PrimTy} (h : BinOp.lt.accepts p = true) {a b : LTm C (.val p)} :
      LTm.Num ps es a → LTm.Num ps es b → LTm.BoolV ps es (.app2 (.binop .lt h) a b)
  | gt {p : PrimTy} (h : BinOp.gt.accepts p = true) {a b : LTm C (.val p)} :
      LTm.Num ps es a → LTm.Num ps es b → LTm.BoolV ps es (.app2 (.binop .gt h) a b)
  | le {p : PrimTy} (h : BinOp.le.accepts p = true) {a b : LTm C (.val p)} :
      LTm.Num ps es a → LTm.Num ps es b → LTm.BoolV ps es (.app2 (.binop .le h) a b)
  | ge {p : PrimTy} (h : BinOp.ge.accepts p = true) {a b : LTm C (.val p)} :
      LTm.Num ps es a → LTm.Num ps es b → LTm.BoolV ps es (.app2 (.binop .ge h) a b)
  | seqB {d a : LTm C (.val .bool)} : LTm.BoolV ps es d → LTm.BoolV ps es a →
      LTm.BoolV ps es (.seq d a)
  | seqN {q : PrimTy} (hq : q.isNumeric = true) {d : LTm C (.val q)} {a : LTm C (.val .bool)} :
      LTm.Num ps es d → LTm.BoolV ps es a → LTm.BoolV ps es (.seq d a)

theorem LTm.Num.toBoolV {ps : Parameter → Prop} {es : EnvKey → Prop} :
    ∀ {p : PrimTy} {t : LTm C (.val p)}, t.Num ps es → (h : p = .bool) →
      (h ▸ t : LTm C (.val .bool)).BoolV ps es := by
  intro p t ht
  induction ht with
  | var k hk => intro h; subst h; exact .var k hk
  | lit v => intro h; subst h; exact .lit v
  | env e _ => intro h; cases h
  | @add p hp a b _ _ _ _ =>
    intro h
    have hb : p = .bool := by simpa only [BinOp.ret, BinOp.isArith, if_true] using h
    subst hb
    cases hp
  | @sub p hp a b _ _ _ _ =>
    intro h
    have hb : p = .bool := by simpa only [BinOp.ret, BinOp.isArith, if_true] using h
    subst hb
    cases hp
  | neg _ _ _ | bnot _ _ _ => intro h; exact absurd h (by decide)
  | @mulL p hp v b _ _ | @mulR p hp b v _ _ =>
    intro h
    have hb : p = .bool := by simpa only [BinOp.ret, BinOp.isArith, if_true] using h
    subst hb
    cases hp
  | @seq q p d a hd _ ihd iha =>
    intro h
    subst h
    cases q with
    | bool => exact .seqB (ihd rfl) (iha rfl)
    | uint => exact .seqN rfl hd (iha rfl)
    | int => exact .seqN rfl hd (iha rfl)
  | err => intro h; subst h; exact .err

theorem BooleanValue.ofTermFuel?_good (ps : List Parameter) (es : List EnvKey) :
    ∀ {t : LTm C (.val .bool)}, t.BoolV (· ∈ ps) (· ∈ es) → ∀ (n : Nat), t.depth < n → t.depth ≤ 1023 →
      ∃ v, BooleanValue.ofTermFuel? (C := C) (es := es) ps n t = some v ∧ v.Good := by
  intro t h
  induction h with
  | var k hk =>
    intro n hn hd
    obtain ⟨n, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by simp only [LTm.depth] at hn; omega⟩
    obtain ⟨w, hw, gw⟩ := CheckedValue.ofTermIn?_good (es := es) (LTm.Num.var (C := C) (es := (· ∈ es)) (p := .bool) k hk) hd
    refine ⟨BooleanValue.ofScalar w, ?_, fun rs hr => CheckedBool.W.ofScalar (gw rs hr)⟩
    change (CheckedValue.ofTermIn? (C := C) (es := es) ps (LTm.var (p := .bool) k)).map BooleanValue.ofScalar = _
    rw [hw]
    rfl
  | lit v =>
    intro n hn hd
    obtain ⟨n, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by simp only [LTm.depth] at hn; omega⟩
    obtain ⟨w, hw, gw⟩ := CheckedValue.ofTermIn?_good (es := es) (LTm.Num.lit (C := C) (ps := (· ∈ ps)) (es := (· ∈ es)) (p := .bool) v) hd
    refine ⟨BooleanValue.ofScalar w, ?_, fun rs hr => CheckedBool.W.ofScalar (gw rs hr)⟩
    change (CheckedValue.ofTermIn? (C := C) (es := es) ps (LTm.app0 (.lit (p := .bool) v))).map BooleanValue.ofScalar = _
    rw [hw]
    rfl
  | err =>
    intro n hn hd
    obtain ⟨n, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by simp only [LTm.depth] at hn; omega⟩
    obtain ⟨w, hw, gw⟩ := CheckedValue.ofTermIn?_good (es := es) (LTm.Num.err (C := C) (ps := (· ∈ ps)) (es := (· ∈ es)) (p := .bool)) hd
    refine ⟨BooleanValue.ofScalar w, ?_, fun rs hr => CheckedBool.W.ofScalar (gw rs hr)⟩
    change (CheckedValue.ofTermIn? (C := C) (es := es) ps (LTm.err (C := C) (s := .val .bool))).map BooleanValue.ofScalar = _
    rw [hw]
    rfl
  | @not a _ ih =>
    intro n hn hd
    obtain ⟨n, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by simp only [LTm.depth] at hn; omega⟩
    simp only [LTm.depth] at hn hd
    obtain ⟨v, hv, gv⟩ := ih n (by omega) (by omega)
    refine ⟨BooleanValue.not v, ?_, fun rs hr => CheckedBool.W.not (gv rs hr)⟩
    change (BooleanValue.ofTermFuel? (C := C) (es := es) ps n a).map BooleanValue.not = _
    rw [hv]
    rfl
  | @and a b _ _ iha ihb =>
    intro n hn hd
    obtain ⟨n, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by simp only [LTm.depth] at hn; omega⟩
    simp only [LTm.depth] at hn hd
    obtain ⟨va, hva, ga⟩ := iha n (by omega) (by omega)
    obtain ⟨vb, hvb, gb⟩ := ihb n (by omega) (by omega)
    refine ⟨BooleanValue.and va vb, ?_, fun rs hr => CheckedBool.W.and (ga rs (fun r hm => hr r (List.mem_append_left _ hm))) (gb rs (fun r hm => hr r (List.mem_append_right _ hm)))⟩
    change (Option.bind (BooleanValue.ofTermFuel? (C := C) (es := es) ps n a) fun x => Option.bind (BooleanValue.ofTermFuel? (C := C) (es := es) ps n b) fun y => some (BooleanValue.and x y)) = _
    rw [hva, hvb]
    rfl
  | @or a b _ _ iha ihb =>
    intro n hn hd
    obtain ⟨n, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by simp only [LTm.depth] at hn; omega⟩
    simp only [LTm.depth] at hn hd
    obtain ⟨va, hva, ga⟩ := iha n (by omega) (by omega)
    obtain ⟨vb, hvb, gb⟩ := ihb n (by omega) (by omega)
    refine ⟨BooleanValue.or va vb, ?_, fun rs hr => CheckedBool.W.or (ga rs (fun r hm => hr r (List.mem_append_left _ hm))) (gb rs (fun r hm => hr r (List.mem_append_right _ hm)))⟩
    change (Option.bind (BooleanValue.ofTermFuel? (C := C) (es := es) ps n a) fun x => Option.bind (BooleanValue.ofTermFuel? (C := C) (es := es) ps n b) fun y => some (BooleanValue.or x y)) = _
    rw [hva, hvb]
    rfl
  | @eqB a b _ _ iha ihb =>
    intro n hn hd
    obtain ⟨n, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by simp only [LTm.depth] at hn; omega⟩
    simp only [LTm.depth] at hn hd
    obtain ⟨va, hva, ga⟩ := iha n (by omega) (by omega)
    obtain ⟨vb, hvb, gb⟩ := ihb n (by omega) (by omega)
    refine ⟨BooleanValue.eq va vb, ?_, fun rs hr => CheckedBool.W.eq (ga rs (fun r hm => hr r (List.mem_append_left _ hm))) (gb rs (fun r hm => hr r (List.mem_append_right _ hm)))⟩
    change (Option.bind (BooleanValue.ofTermFuel? (C := C) (es := es) ps n a) fun x => Option.bind (BooleanValue.ofTermFuel? (C := C) (es := es) ps n b) fun y => some (BooleanValue.eq x y)) = _
    rw [hva, hvb]
    rfl
  | @neB a b _ _ iha ihb =>
    intro n hn hd
    obtain ⟨n, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by simp only [LTm.depth] at hn; omega⟩
    simp only [LTm.depth] at hn hd
    obtain ⟨va, hva, ga⟩ := iha n (by omega) (by omega)
    obtain ⟨vb, hvb, gb⟩ := ihb n (by omega) (by omega)
    refine ⟨BooleanValue.ne va vb, ?_, fun rs hr => CheckedBool.W.not (CheckedBool.W.eq (ga rs (fun r hm => hr r (List.mem_append_left _ hm))) (gb rs (fun r hm => hr r (List.mem_append_right _ hm))))⟩
    change (Option.bind (BooleanValue.ofTermFuel? (C := C) (es := es) ps n a) fun x => Option.bind (BooleanValue.ofTermFuel? (C := C) (es := es) ps n b) fun y => some (BooleanValue.ne x y)) = _
    rw [hva, hvb]
    rfl
  | @eqN p hp a b ha hb =>
    intro n hn hd
    obtain ⟨n, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by simp only [LTm.depth] at hn; omega⟩
    simp only [LTm.depth] at hn hd
    obtain ⟨va, hva, ga⟩ := CheckedValue.ofTermIn?_good ha (by omega)
    obtain ⟨vb, hvb, gb⟩ := CheckedValue.ofTermIn?_good hb (by omega)
    cases p with
    | bool => cases hp
    | uint | int =>
      refine ⟨BooleanValue.comparison .eqB rfl rfl rfl va vb, ?_,
        fun rs hr => CheckedBool.W.comparison _ (ga rs (fun r hm => hr r (List.mem_append_left _ hm))) (gb rs (fun r hm => hr r (List.mem_append_right _ hm)))⟩
      change (Option.bind (CheckedValue.ofTermIn? (C := C) (es := es) ps a) fun x => Option.bind (CheckedValue.ofTermIn? (C := C) (es := es) ps b) fun y => some (BooleanValue.comparison .eqB rfl rfl rfl x y)) = _
      rw [hva, hvb]
      rfl
  | @neN p hp a b ha hb =>
    intro n hn hd
    obtain ⟨n, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by simp only [LTm.depth] at hn; omega⟩
    simp only [LTm.depth] at hn hd
    obtain ⟨va, hva, ga⟩ := CheckedValue.ofTermIn?_good ha (by omega)
    obtain ⟨vb, hvb, gb⟩ := CheckedValue.ofTermIn?_good hb (by omega)
    cases p with
    | bool => cases hp
    | uint | int =>
      refine ⟨BooleanValue.comparison .neB rfl rfl rfl va vb, ?_,
        fun rs hr => CheckedBool.W.comparison _ (ga rs (fun r hm => hr r (List.mem_append_left _ hm))) (gb rs (fun r hm => hr r (List.mem_append_right _ hm)))⟩
      change (Option.bind (CheckedValue.ofTermIn? (C := C) (es := es) ps a) fun x => Option.bind (CheckedValue.ofTermIn? (C := C) (es := es) ps b) fun y => some (BooleanValue.comparison .neB rfl rfl rfl x y)) = _
      rw [hva, hvb]
      rfl
  | @lt p h a b ha hb =>
    intro n hn hd
    obtain ⟨n, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by simp only [LTm.depth] at hn; omega⟩
    simp only [LTm.depth] at hn hd
    obtain ⟨va, hva, ga⟩ := CheckedValue.ofTermIn?_good ha (by omega)
    obtain ⟨vb, hvb, gb⟩ := CheckedValue.ofTermIn?_good hb (by omega)
    refine ⟨BooleanValue.comparison .lt rfl h rfl va vb, ?_,
      fun rs hr => CheckedBool.W.comparison _ (ga rs (fun r hm => hr r (List.mem_append_left _ hm))) (gb rs (fun r hm => hr r (List.mem_append_right _ hm)))⟩
    change (Option.bind (CheckedValue.ofTermIn? (C := C) (es := es) ps a) fun x => Option.bind (CheckedValue.ofTermIn? (C := C) (es := es) ps b) fun y => some (BooleanValue.comparison .lt rfl h rfl x y)) = _
    rw [hva, hvb]
    rfl
  | @gt p h a b ha hb =>
    intro n hn hd
    obtain ⟨n, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by simp only [LTm.depth] at hn; omega⟩
    simp only [LTm.depth] at hn hd
    obtain ⟨va, hva, ga⟩ := CheckedValue.ofTermIn?_good ha (by omega)
    obtain ⟨vb, hvb, gb⟩ := CheckedValue.ofTermIn?_good hb (by omega)
    refine ⟨BooleanValue.comparison .gt rfl h rfl va vb, ?_,
      fun rs hr => CheckedBool.W.comparison _ (ga rs (fun r hm => hr r (List.mem_append_left _ hm))) (gb rs (fun r hm => hr r (List.mem_append_right _ hm)))⟩
    change (Option.bind (CheckedValue.ofTermIn? (C := C) (es := es) ps a) fun x => Option.bind (CheckedValue.ofTermIn? (C := C) (es := es) ps b) fun y => some (BooleanValue.comparison .gt rfl h rfl x y)) = _
    rw [hva, hvb]
    rfl
  | @le p h a b ha hb =>
    intro n hn hd
    obtain ⟨n, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by simp only [LTm.depth] at hn; omega⟩
    simp only [LTm.depth] at hn hd
    obtain ⟨va, hva, ga⟩ := CheckedValue.ofTermIn?_good ha (by omega)
    obtain ⟨vb, hvb, gb⟩ := CheckedValue.ofTermIn?_good hb (by omega)
    refine ⟨BooleanValue.comparison .le rfl h rfl va vb, ?_,
      fun rs hr => CheckedBool.W.comparison _ (ga rs (fun r hm => hr r (List.mem_append_left _ hm))) (gb rs (fun r hm => hr r (List.mem_append_right _ hm)))⟩
    change (Option.bind (CheckedValue.ofTermIn? (C := C) (es := es) ps a) fun x => Option.bind (CheckedValue.ofTermIn? (C := C) (es := es) ps b) fun y => some (BooleanValue.comparison .le rfl h rfl x y)) = _
    rw [hva, hvb]
    rfl
  | @ge p h a b ha hb =>
    intro n hn hd
    obtain ⟨n, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by simp only [LTm.depth] at hn; omega⟩
    simp only [LTm.depth] at hn hd
    obtain ⟨va, hva, ga⟩ := CheckedValue.ofTermIn?_good ha (by omega)
    obtain ⟨vb, hvb, gb⟩ := CheckedValue.ofTermIn?_good hb (by omega)
    refine ⟨BooleanValue.comparison .ge rfl h rfl va vb, ?_,
      fun rs hr => CheckedBool.W.comparison _ (ga rs (fun r hm => hr r (List.mem_append_left _ hm))) (gb rs (fun r hm => hr r (List.mem_append_right _ hm)))⟩
    change (Option.bind (CheckedValue.ofTermIn? (C := C) (es := es) ps a) fun x => Option.bind (CheckedValue.ofTermIn? (C := C) (es := es) ps b) fun y => some (BooleanValue.comparison .ge rfl h rfl x y)) = _
    rw [hva, hvb]
    rfl
  | @seqB d a _ _ ihd iha =>
    intro n hn hd
    obtain ⟨n, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by simp only [LTm.depth] at hn; omega⟩
    simp only [LTm.depth] at hn hd
    obtain ⟨vd, hvd, gd⟩ := ihd n (by omega) (by omega)
    obtain ⟨va, hva, ga⟩ := iha n (by omega) (by omega)
    refine ⟨BooleanValue.seq vd.defined va, ?_, fun rs hr =>
      ⟨AFml.width_and (CheckedBool.W.disj (gd rs (fun r hm => hr r (List.mem_append_left _ hm))).1 (gd rs (fun r hm => hr r (List.mem_append_left _ hm))).2) (ga rs (fun r hm => hr r (List.mem_append_right _ hm))).1,
        AFml.width_and (CheckedBool.W.disj (gd rs (fun r hm => hr r (List.mem_append_left _ hm))).1 (gd rs (fun r hm => hr r (List.mem_append_left _ hm))).2) (ga rs (fun r hm => hr r (List.mem_append_right _ hm))).2⟩⟩
    change (Option.bind (BooleanValue.ofTermFuel? (C := C) (es := es) ps n d) fun x => Option.bind (BooleanValue.ofTermFuel? (C := C) (es := es) ps n a) fun y => some (BooleanValue.seq (BooleanValue.defined x) y)) = _
    rw [hvd, hva]
    rfl
  | @seqN q hq d a hdn _ iha =>
    intro n hn hd
    obtain ⟨n, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by simp only [LTm.depth] at hn; omega⟩
    simp only [LTm.depth] at hn hd
    obtain ⟨vd, hvd, gd⟩ := CheckedValue.ofTermIn?_good hdn (by omega)
    obtain ⟨va, hva, ga⟩ := iha n (by omega) (by omega)
    cases q with
    | bool => cases hq
    | uint | int =>
      refine ⟨BooleanValue.seq vd.defined va, ?_, fun rs hr =>
        ⟨AFml.width_and (gd rs (fun r hm => hr r (List.mem_append_left _ hm))).2 (ga rs (fun r hm => hr r (List.mem_append_right _ hm))).1, AFml.width_and (gd rs (fun r hm => hr r (List.mem_append_left _ hm))).2 (ga rs (fun r hm => hr r (List.mem_append_right _ hm))).2⟩⟩
      change (Option.bind (CheckedValue.ofTermIn? (C := C) (es := es) ps d) fun x => Option.bind (BooleanValue.ofTermFuel? (C := C) (es := es) ps n a) fun y => some (BooleanValue.seq (CheckedValue.defined x) y)) = _
      rw [hvd, hva]
      rfl

theorem BooleanValue.ofTermIn?_good {ps : List Parameter} {es : List EnvKey}
    {t : LTm C (.val .bool)} (h : t.BoolV (· ∈ ps) (· ∈ es)) (hd : t.depth ≤ 1023) :
    ∃ v, BooleanValue.ofTermIn? (C := C) (es := es) ps t = some v ∧ v.Good :=
  BooleanValue.ofTermFuel?_good ps es h 1024 (by omega) hd

/-- The formulas `StorageEncoding` encodes: Boolean equations of Boolean
terms, numeric equations of scalar terms, under `¬`, `∧`, `→`. -/
inductive LFml.Arith (ps : Parameter → Prop) (es : EnvKey → Prop) : LFml C → Prop
  | tt : LFml.Arith ps es .tt
  | eqB {a b : LTm C (.val .bool)} : a.BoolV ps es → b.BoolV ps es → a.depth ≤ 1023 →
      b.depth ≤ 1023 → LFml.Arith ps es (.eq a b)
  | eqN {p : PrimTy} (hp : p.isNumeric = true) {a b : LTm C (.val p)} : a.Num ps es →
      b.Num ps es → a.depth ≤ 1023 → b.depth ≤ 1023 → LFml.Arith ps es (.eq a b)
  | not {φ : LFml C} : LFml.Arith ps es φ → LFml.Arith ps es (.not φ)
  | and {φ ψ : LFml C} : LFml.Arith ps es φ → LFml.Arith ps es ψ → LFml.Arith ps es (.and φ ψ)
  | imp {φ ψ : LFml C} : LFml.Arith ps es φ → LFml.Arith ps es ψ → LFml.Arith ps es (.imp φ ψ)
  /-- The defining equations of cut atoms (`Calculus/QuotientCut.lean`). -/
  | defDiv (h : BinOp.div.accepts .uint = true) (c : PrimTy.uint.Denote) (hc : c.val ≠ 0) (k : Nat)
      {a : LTm C (.val .uint)} : a.Num ps es → ps ⟨.uint, k⟩ → a.depth ≤ 1023 →
      LFml.Arith ps es (.eq (.app2 (.binop .div h) a (.app0 (.lit c))) (.var k))
  | defShr {p : PrimTy} (h : BinOp.shr.accepts p = true) (v : p.Denote) (k : Nat)
      {a : LTm C (.val p)} : a.Num ps es → ps ⟨p, k⟩ → a.depth ≤ 1023 →
      LFml.Arith ps es (.eq (.app2 (.binop .shr h) a (.app0 (.lit v))) (.var k))
  | defAddW (h : BinOp.addW.accepts .uint = true) (k : Nat) {a b : LTm C (.val .uint)} :
      a.Num ps es → b.Num ps es → ps ⟨.uint, k⟩ → a.depth ≤ 1023 → b.depth ≤ 1023 →
      LFml.Arith ps es (.eq (.app2 (.binop .addW h) a b) (.var k))
  | defSubW (h : BinOp.subW.accepts .uint = true) (k : Nat) {a b : LTm C (.val .uint)} :
      a.Num ps es → b.Num ps es → ps ⟨.uint, k⟩ → a.depth ≤ 1023 → b.depth ≤ 1023 →
      LFml.Arith ps es (.eq (.app2 (.binop .subW h) a b) (.var k))
  | defToInt (h : UnOp.toInt.accepts .uint = true) (k : Nat) {a : LTm C (.val .uint)} :
      a.Num ps es → ps ⟨.int, k⟩ → a.depth ≤ 1023 →
      LFml.Arith ps es (.eq (.app1 (.unop .toInt h) a) (.var k))
  | defToUint (h : UnOp.toUint.accepts .int = true) (k : Nat) {a : LTm C (.val .int)} :
      a.Num ps es → ps ⟨.uint, k⟩ → a.depth ≤ 1023 →
      LFml.Arith ps es (.eq (.app1 (.unop .toUint h) a) (.var k))

theorem StorageEncoding.specialVar?_num {ps : List Parameter} {es : List EnvKey}
    {P : Parameter → Prop} {E : EnvKey → Prop} :
    ∀ {p : PrimTy} {a : LTm C (.val p)}, a.Num P E → ∀ k (hk : Parameter.mk p k ∈ ps),
      StorageEncoding.specialVar? (ps := ps) (es := es) a k hk = none := by
  intro p a ha
  cases ha <;> intro k hk <;> rfl

theorem StorageEncoding.specialVar?_bool {ps : List Parameter} {es : List EnvKey}
    {P : Parameter → Prop} {E : EnvKey → Prop} :
    ∀ {a : LTm C (.val .bool)}, a.BoolV P E → ∀ k (hk : Parameter.mk .bool k ∈ ps),
      StorageEncoding.specialVar? (ps := ps) (es := es) a k hk = none := by
  intro a ha
  cases ha <;> intro k hk <;> rfl

theorem StorageEncoding.special?_none {ps : List Parameter} {es : List EnvKey} {p : PrimTy}
    {a : LTm C (.val p)} (ha : ∀ k (hk : Parameter.mk p k ∈ ps),
      StorageEncoding.specialVar? (ps := ps) (es := es) a k hk = none) (b : LTm C (.val p)) :
    StorageEncoding.special? (ps := ps) (es := es) a b = none := by
  unfold StorageEncoding.special?
  split
  · split
    · exact ha _ _
    · rfl
  · rfl

theorem StorageEncoding.equality?_plain {ps : List Parameter} {es : List EnvKey} {p : PrimTy}
    {a : LTm C (.val p)} (ha : ∀ k (hk : Parameter.mk p k ∈ ps),
      StorageEncoding.specialVar? (ps := ps) (es := es) a k hk = none) (b : LTm C (.val p)) :
    StorageEncoding.equality? (ps := ps) (es := es) a b =
      StorageEncoding.equalityPlain? (ps := ps) (es := es) a b := by
  unfold StorageEncoding.equality?
  rw [StorageEncoding.special?_none ha b]

theorem StorageEncoding.equality?_var {ps : List Parameter} {es : List EnvKey} {p : PrimTy}
    (a : LTm C (.val p)) (k : Nat) (hk : Parameter.mk p k ∈ ps)
    (e : StorageEncoding (ps := ps) (es := es) (.eq a (.var k)))
    (he : StorageEncoding.specialVar? (ps := ps) (es := es) a k hk = some e) :
    StorageEncoding.equality? (ps := ps) (es := es) a (.var k) = some e := by
  have hs : StorageEncoding.special? (ps := ps) (es := es) a (.var k) =
      StorageEncoding.specialVar? (ps := ps) (es := es) a k hk := by
    show (if hk' : Parameter.mk p k ∈ ps then _ else none) = _
    rw [dif_pos hk]
  unfold StorageEncoding.equality?
  rw [hs, he]

theorem Affine.W.var_index {ps : List Parameter} {es : List EnvKey} {rs : List (Ref C)} {r : PrimTy}
    {k : Nat} (hk : Parameter.mk r k ∈ ps) :
    (Affine.variable (es.length + Parameters.index ⟨r, k⟩ ps)).W (es.length + (ps.length + rs.length)) := by
  apply Affine.W.variable
  have := Parameters.index_lt hk
  omega

theorem floorRel_width {n : Nat} {A B : Affine} (hA : A.W n) (hB : B.W n) (off d M : Int) :
    (floorRel off d M A B).width ≤ n :=
  AFml.width_and (AFml.width_and (Affine.width_le ((hB.offset _).scale _) (hA.offset _))
    (Affine.width_le (hA.offset _) (((hB.offset _).scale _).offset _)))
    (Affine.width_le (hB.offset _) (Affine.W.literal _ _))

theorem wrapRel_width {n : Nat} {A B Y : Affine} (hA : A.W n) (hB : B.W n) (hY : Y.W n) (sub : Bool) :
    (wrapRel sub A B Y).width ≤ n := by
  cases sub
  · exact AFml.width_imp (AFml.width_not (Affine.width_eq hY (hA.add hB)))
      (Affine.width_eq (hY.offset _) (hA.add hB))
  · exact AFml.width_imp (AFml.width_not (Affine.width_eq hY (hA.sub hB)))
      (Affine.width_eq hY ((hA.sub hB).offset _))

theorem convRel_width {n : Nat} {A Y : Affine} (hA : A.W n) (hY : Y.W n) :
    (convRel A Y).width ≤ n :=
  AFml.width_imp (AFml.width_not (Affine.width_eq hY (hA.offset _))) (Affine.width_eq (hY.offset _) hA)

theorem StorageEncoding.ofFormula?_good {ps : List Parameter} {es : List EnvKey} :
    ∀ {φ : LFml C}, φ.Arith (· ∈ ps) (· ∈ es) → ∃ v, StorageEncoding.ofFormula? (C := C) (ps := ps) (es := es) φ = some v ∧ v.Good := by
  intro φ h
  induction h with
  | tt => exact ⟨_, rfl, fun _ _ => Nat.zero_le _⟩
  | @eqB a b ha hb hda hdb =>
    obtain ⟨va, hva, ga⟩ := BooleanValue.ofTermIn?_good (es := es) ha hda
    obtain ⟨vb, hvb, gb⟩ := BooleanValue.ofTermIn?_good (es := es) hb hdb
    refine ⟨StorageEncoding.boolEq va vb, ?_, fun rs hr => (CheckedBool.W.eq (ga rs (fun r hm => hr r (List.mem_append_left _ hm))) (gb rs (fun r hm => hr r (List.mem_append_right _ hm)))).1⟩
    show StorageEncoding.equality? a b = _
    rw [StorageEncoding.equality?_plain (StorageEncoding.specialVar?_bool ha) b]
    change (Option.bind (BooleanValue.ofTermIn? (C := C) (es := es) ps a) fun x => Option.bind (BooleanValue.ofTermIn? (C := C) (es := es) ps b) fun y => some (StorageEncoding.boolEq x y)) = _
    rw [hva, hvb]
    rfl
  | @eqN p hp a b ha hb hda hdb =>
    obtain ⟨va, hva, ga⟩ := CheckedValue.ofTermIn?_good (es := es) ha hda
    obtain ⟨vb, hvb, gb⟩ := CheckedValue.ofTermIn?_good (es := es) hb hdb
    cases p with
    | bool => cases hp
    | uint | int =>
      refine ⟨StorageEncoding.eq va vb, ?_, fun rs hr => CheckedScalar.W.eq (ga rs (fun r hm => hr r (List.mem_append_left _ hm))) (gb rs (fun r hm => hr r (List.mem_append_right _ hm)))⟩
      show StorageEncoding.equality? a b = _
      rw [StorageEncoding.equality?_plain (StorageEncoding.specialVar?_num ha) b]
      change (Option.bind (CheckedValue.ofTermIn? (C := C) (es := es) ps a) fun x => Option.bind (CheckedValue.ofTermIn? (C := C) (es := es) ps b) fun y => some (StorageEncoding.eq x y)) = _
      rw [hva, hvb]
      rfl
  | @not φ _ ih =>
    obtain ⟨v, hv, gv⟩ := ih
    refine ⟨StorageEncoding.not v, ?_, fun rs hr => AFml.width_not (gv rs hr)⟩
    change (StorageEncoding.ofFormula? (C := C) (ps := ps) (es := es) φ).map StorageEncoding.not = _
    rw [hv]
    rfl
  | @and φ ψ _ _ ihφ ihψ =>
    obtain ⟨v, hv, gv⟩ := ihφ
    obtain ⟨w, hw, gw⟩ := ihψ
    refine ⟨StorageEncoding.and v w, ?_, fun rs hr => AFml.width_and (gv rs (fun r hm => hr r (List.mem_append_left _ hm))) (gw rs (fun r hm => hr r (List.mem_append_right _ hm)))⟩
    change (Option.bind (StorageEncoding.ofFormula? (C := C) (ps := ps) (es := es) φ) fun x => Option.bind (StorageEncoding.ofFormula? (C := C) (ps := ps) (es := es) ψ) fun y => some (StorageEncoding.and x y)) = _
    rw [hv, hw]
    rfl
  | @imp φ ψ _ _ ihφ ihψ =>
    obtain ⟨v, hv, gv⟩ := ihφ
    obtain ⟨w, hw, gw⟩ := ihψ
    refine ⟨StorageEncoding.imp v w, ?_, fun rs hr => AFml.width_imp (gv rs (fun r hm => hr r (List.mem_append_left _ hm))) (gw rs (fun r hm => hr r (List.mem_append_right _ hm)))⟩
    change (Option.bind (StorageEncoding.ofFormula? (C := C) (ps := ps) (es := es) φ) fun x => Option.bind (StorageEncoding.ofFormula? (C := C) (ps := ps) (es := es) ψ) fun y => some (StorageEncoding.imp x y)) = _
    rw [hv, hw]
    rfl

  | @defDiv h c hc k a ha hk hd =>
    obtain ⟨va, hva, ga⟩ := CheckedValue.ofTermIn?_good (es := es) ha hd
    refine ⟨StorageEncoding.defDiv h c hc k hk va, StorageEncoding.equality?_var _ k hk _ ?_,
      fun rs hr => AFml.width_and (ga rs hr).2 (floorRel_width (ga rs hr).1 (Affine.W.var_index hk) _ _ _)⟩
    show (if hc' : c.val = 0 then none else _) = _
    rw [dif_neg hc, hva]
    rfl
  | @defShr p h v k a ha hk hd =>
    obtain ⟨va, hva, ga⟩ := CheckedValue.ofTermIn?_good (es := es) ha hd
    refine ⟨StorageEncoding.defShr h v k hk va, StorageEncoding.equality?_var _ k hk _ ?_,
      fun rs hr => AFml.width_and (ga rs hr).2 (floorRel_width (ga rs hr).1 (Affine.W.var_index hk) _ _ _)⟩
    cases p with
    | bool => cases h
    | uint | int =>
      show (CheckedValue.ofTermIn? ps a).map _ = _
      rw [hva]
      rfl
  | @defAddW h k a b ha hb hk hda hdb =>
    obtain ⟨va, hva, ga⟩ := CheckedValue.ofTermIn?_good (es := es) ha hda
    obtain ⟨vb, hvb, gb⟩ := CheckedValue.ofTermIn?_good (es := es) hb hdb
    refine ⟨StorageEncoding.defAddW h k hk va vb, StorageEncoding.equality?_var _ k hk _ ?_,
      fun rs hr => ?_⟩
    · show (Option.bind (CheckedValue.ofTermIn? ps a) fun x =>
        Option.bind (CheckedValue.ofTermIn? ps b) fun y => some _) = _
      rw [hva, hvb]
      rfl
    · have ha' := ga rs (fun r hm => hr r (List.mem_append_left _ hm))
      have hb' := gb rs (fun r hm => hr r (List.mem_append_right _ hm))
      exact AFml.width_and ha'.2 (AFml.width_and hb'.2
        (wrapRel_width ha'.1 hb'.1 (Affine.W.var_index hk) false))
  | @defSubW h k a b ha hb hk hda hdb =>
    obtain ⟨va, hva, ga⟩ := CheckedValue.ofTermIn?_good (es := es) ha hda
    obtain ⟨vb, hvb, gb⟩ := CheckedValue.ofTermIn?_good (es := es) hb hdb
    refine ⟨StorageEncoding.defSubW h k hk va vb, StorageEncoding.equality?_var _ k hk _ ?_,
      fun rs hr => ?_⟩
    · show (Option.bind (CheckedValue.ofTermIn? ps a) fun x =>
        Option.bind (CheckedValue.ofTermIn? ps b) fun y => some _) = _
      rw [hva, hvb]
      rfl
    · have ha' := ga rs (fun r hm => hr r (List.mem_append_left _ hm))
      have hb' := gb rs (fun r hm => hr r (List.mem_append_right _ hm))
      exact AFml.width_and ha'.2 (AFml.width_and hb'.2
        (wrapRel_width ha'.1 hb'.1 (Affine.W.var_index hk) true))
  | @defToInt h k a ha hk hd =>
    obtain ⟨va, hva, ga⟩ := CheckedValue.ofTermIn?_good (es := es) ha hd
    refine ⟨StorageEncoding.defToInt h k hk va, StorageEncoding.equality?_var _ k hk _ ?_,
      fun rs hr => AFml.width_and (ga rs hr).2 (convRel_width (ga rs hr).1 (Affine.W.var_index hk))⟩
    show (CheckedValue.ofTermIn? ps a).map _ = _
    rw [hva]
    rfl
  | @defToUint h k a ha hk hd =>
    obtain ⟨va, hva, ga⟩ := CheckedValue.ofTermIn?_good (es := es) ha hd
    refine ⟨StorageEncoding.defToUint h k hk va, StorageEncoding.equality?_var _ k hk _ ?_,
      fun rs hr => AFml.width_and (ga rs hr).2 (convRel_width (Affine.W.var_index hk) (ga rs hr).1)⟩
    show (CheckedValue.ofTermIn? ps a).map _ = _
    rw [hva]
    rfl

/-! ## The leaf arithmetic: layouts -/

theorem List.eraseDups_spec {α : Type} [BEq α] [LawfulBEq α] :
    ∀ (n : Nat) (l : List α), l.length ≤ n → l.eraseDups.Nodup ∧ ∀ x, x ∈ l.eraseDups ↔ x ∈ l
  | _, [], _ => ⟨List.nodup_nil, fun x => by simp only [List.eraseDups_nil]⟩
  | 0, _ :: _, h => by simp only [List.length_cons] at h; omega
  | n + 1, a :: as, h => by
    have hl : (as.filter fun b => !b == a).length ≤ n := by
      have := List.length_filter_le (fun b => !b == a) as
      simp only [List.length_cons] at h
      omega
    obtain ⟨hn, hm⟩ := List.eraseDups_spec n _ hl
    rw [List.eraseDups_cons]
    refine ⟨List.nodup_cons.mpr ⟨fun ha => ?_, hn⟩, fun x => ?_⟩
    · have := (hm a).mp ha
      simp only [List.mem_filter, beq_self_eq_true, Bool.not_true, Bool.false_eq_true, and_false] at this
    · rw [List.mem_cons, hm x, List.mem_filter, List.mem_cons]
      by_cases hx : x = a
      · subst hx; simp only [true_or]
      · simp only [hx, false_or, Bool.not_eq_true', beq_eq_false_iff_ne, ne_eq,
          not_false_eq_true, and_true]

theorem List.nodup_eraseDups' {α : Type} [BEq α] [LawfulBEq α] (l : List α) : l.eraseDups.Nodup :=
  (List.eraseDups_spec l.length l (Nat.le_refl _)).1

theorem List.mem_eraseDups' {α : Type} [BEq α] [LawfulBEq α] (l : List α) (x : α) :
    x ∈ l.eraseDups ↔ x ∈ l :=
  (List.eraseDups_spec l.length l (Nat.le_refl _)).2 x

theorem Inputs.unique_spec : ∀ (es : List EnvKey),
    (Inputs.unique es).Nodup ∧ ∀ e, e ∈ Inputs.unique es ↔ e ∈ es
  | [] => ⟨List.nodup_nil, fun _ => Iff.rfl⟩
  | e :: es => by
    obtain ⟨hn, hm⟩ := Inputs.unique_spec es
    unfold Inputs.unique
    by_cases he : e ∈ Inputs.unique es
    · simp only [he, if_true]
      exact ⟨hn, fun x => (hm x).trans ⟨fun h => List.mem_cons_of_mem e h, fun h =>
        (List.mem_cons.mp h).elim (fun hx => hx ▸ (hm e).mp he) id⟩⟩
    · simp only [he, if_false]
      exact ⟨List.nodup_cons.mpr ⟨he, hn⟩, fun x => by rw [List.mem_cons, List.mem_cons, hm x]⟩

theorem Layout.unique_spec : ∀ (rs : List (Ref C)),
    (Layout.unique rs).Nodup ∧ ∀ r, r ∈ Layout.unique rs ↔ r ∈ rs
  | [] => ⟨List.nodup_nil, fun _ => Iff.rfl⟩
  | r :: rs => by
    obtain ⟨hn, hm⟩ := Layout.unique_spec rs
    unfold Layout.unique
    by_cases he : r ∈ Layout.unique rs
    · simp only [he, if_true]
      exact ⟨hn, fun x => (hm x).trans ⟨fun h => List.mem_cons_of_mem r h, fun h =>
        (List.mem_cons.mp h).elim (fun hx => hx ▸ (hm r).mp he) id⟩⟩
    · simp only [he, if_false]
      exact ⟨List.nodup_cons.mpr ⟨he, hn⟩, fun x => by rw [List.mem_cons, List.mem_cons, hm x]⟩

theorem Inputs.length_types (ps : List Parameter) (rs : List (Ref C)) :
    ∀ es : List EnvKey, (Inputs.types es ps rs).length = es.length + (ps.length + rs.length)
  | [] => by
    simp only [Inputs.types, Parameters.types, Layout.types, List.length_append, List.length_map,
      List.length_nil, Nat.zero_add]
  | _ :: es => by
    simp only [Inputs.types, List.length_cons, Inputs.length_types ps rs es]
    omega

/-- **The leaf arithmetic never refuses its fragment.** -/
theorem leafArithmetic?_isSome (φ : LFml C)
    (h : φ.Arith (· ∈ φ.parameters.eraseDups) (· ∈ Inputs.unique (Inputs.formulaKeys φ))) :
    (leafArithmetic? φ).isSome = true := by
  obtain ⟨enc, henc, good⟩ := StorageEncoding.ofFormula?_good h
  have he : (Inputs.unique (Inputs.formulaKeys φ)).Nodup := (Inputs.unique_spec _).1
  have hp : φ.parameters.eraseDups.Nodup := List.nodup_eraseDups' _
  have hr : (Layout.unique enc.refs).Nodup := (Layout.unique_spec _).1
  have hc : ∀ q ∈ enc.refs, q ∈ Layout.unique enc.refs := fun q hq => ((Layout.unique_spec _).2 q).mpr hq
  have hw : (enc.lower (Layout.unique enc.refs)).width ≤
      (Inputs.types (Inputs.unique (Inputs.formulaKeys φ)) φ.parameters.eraseDups
        (Layout.unique enc.refs)).length := by
    rw [Inputs.length_types]
    exact good _ hc
  simp only [leafArithmetic?, henc, Option.bind_eq_bind, Option.bind_some, he, hp, hr, hw, dif_pos]
  rw [dif_pos hc]
  rfl

end Solidity.Decide
