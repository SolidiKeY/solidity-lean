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

theorem Affine.W.mono {n m : Nat} {a : Affine} (ha : a.W n) (h : n ≤ m) : a.W m :=
  Nat.le_trans ha h

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

theorem CheckedScalar.W.mono {n m : Nat} {p : PrimTy} {a : CheckedScalar p} (ha : a.W n)
    (h : n ≤ m) : a.W m := ⟨ha.1.mono h, Nat.le_trans ha.2 h⟩

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

/-- A checked KeY `int` over the first `n` variables. -/
def CheckedInt.W (n : Nat) (a : CheckedInt) : Prop := a.code.W n ∧ a.defined.width ≤ n

theorem CheckedInt.W.lit (n : Nat) (c : Int) : (CheckedInt.lit c).W n :=
  ⟨Affine.W.literal n c, Nat.zero_le n⟩

theorem CheckedInt.W.ofUint {n : Nat} {a : CheckedScalar .uint} (ha : a.W n) :
    (CheckedInt.ofUint a).W n := ha

theorem CheckedInt.W.arith {n : Nat} (subtract : Bool) {a b : CheckedInt} (ha : a.W n)
    (hb : b.W n) : (CheckedInt.arith subtract a b).W n := by
  refine ⟨?_, AFml.width_and ha.2 hb.2⟩
  cases subtract
  · exact ha.1.add hb.1
  · exact ha.1.sub hb.1

theorem CheckedInt.W.scale {n : Nat} (c : Int) {a : CheckedInt} (ha : a.W n) :
    (CheckedInt.scale c a).W n := ⟨ha.1.scale c, ha.2⟩

theorem CheckedInt.W.comparison {n : Nat} (op : BinOp) {a b : CheckedInt} (ha : a.W n)
    (hb : b.W n) : (CheckedInt.comparison op a b).W n :=
  ⟨AFml.width_and (AFml.width_and ha.2 hb.2) (Affine.width_compare op ha.1 hb.1),
    AFml.width_and (AFml.width_and ha.2 hb.2) (AFml.width_not (Affine.width_compare op ha.1 hb.1))⟩

end Solidity.Linear

namespace Solidity.Decide

open Semantics ReadRealization Linear ScalarCode

variable {C : Contract} {ls : List PrimTy.uint.Denote}

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

/-- A compiled scalar mentions only the inputs of its layout. -/
def CheckedValue.Good {ps : List Parameter} {es : List EnvKey} {p : PrimTy} {t : LTm C (.val p)}
    (v : CheckedValue (ps := ps) (es := es) t) : Prop :=
  ∀ rs : List (Ref C), (∀ r ∈ v.refs, r ∈ rs) → (v.lower rs).W (es.length + (ps.length + rs.length))

/-- A compiled scalar's width, past the ledger's codes too. -/
theorem CheckedValue.Good.lift {ps : List Parameter} {es : List EnvKey} {p : PrimTy}
    {t : LTm C (.val p)} {v : CheckedValue (ps := ps) (es := es) t} (h : v.Good)
    (ls : List PrimTy.uint.Denote) : ∀ rs : List (Ref C), (∀ r ∈ v.refs, r ∈ rs) →
      (v.lower rs).W (es.length + (ps.length + rs.length) + 2 * ls.length) :=
  fun rs hr => (h rs hr).mono (Nat.le_add_right _ _)

/-- A compiled Boolean mentions only the inputs of its layout. -/
def BooleanValue.Good {ps : List Parameter} {es : List EnvKey} {ls : List PrimTy.uint.Denote}
    {t : LTm C (.val .bool)} (v : BooleanValue (ps := ps) (es := es) (ls := ls) t) : Prop :=
  ∀ rs : List (Ref C), (∀ r ∈ v.refs, r ∈ rs) →
    (v.lower rs).W (es.length + (ps.length + rs.length) + 2 * ls.length)

/-- A compiled formula mentions only the inputs of its layout. -/
def StorageEncoding.Good {ps : List Parameter} {es : List EnvKey} {ls : List PrimTy.uint.Denote}
    {φ : LFml C} (v : StorageEncoding (ps := ps) (es := es) (ls := ls) φ) : Prop :=
  ∀ rs : List (Ref C), (∀ r ∈ v.refs, r ∈ rs) →
    (v.lower rs).width ≤ es.length + (ps.length + rs.length) + 2 * ls.length

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

/-- The KeY `int` terms `KIntValue` encodes: literals, a `uint` widened,
`+`, `-` and products by a literal. -/
inductive LTm.ZNum (ps : Parameter → Prop) (es : EnvKey → Prop)
    (L : PrimTy.uint.Denote → Prop := fun _ => False) : LTm C .kint → Prop
  | zlit (n : Int) : LTm.ZNum ps es L (.app0 (.zlit n))
  | toInt {a : LTm C (.val .uint)} : a.Num ps es → LTm.ZNum ps es L (.app1 .toInt a)
  | add (h : BinOp.add.zArith = true) {a b : LTm C .kint} :
      LTm.ZNum ps es L a → LTm.ZNum ps es L b → LTm.ZNum ps es L (.app2 (.zbin .add h) a b)
  | sub (h : BinOp.sub.zArith = true) {a b : LTm C .kint} :
      LTm.ZNum ps es L a → LTm.ZNum ps es L b → LTm.ZNum ps es L (.app2 (.zbin .sub h) a b)
  | mulL (h : BinOp.mul.zArith = true) (n : Int) {b : LTm C .kint} :
      LTm.ZNum ps es L b → LTm.ZNum ps es L (.app2 (.zbin .mul h) (.app0 (.zlit n)) b)
  | mulR (h : BinOp.mul.zArith = true) {a : LTm C .kint} (n : Int) :
      LTm.ZNum ps es L a → LTm.ZNum ps es L (.app2 (.zbin .mul h) a (.app0 (.zlit n)))
  /-- A ledger read at a constant of the layout's ledger (`L`). -/
  | netLit (v : PrimTy.uint.Denote) (h : L v) : LTm.ZNum ps es L (.app1 .net (.app0 (.lit v)))
  /-- A scalar guard before a KeY `int` (the ledger cut's address). -/
  | zseq {q : PrimTy} {d : LTm C (.val q)} {a : LTm C .kint} :
      d.Num ps es → LTm.ZNum ps es L a → LTm.ZNum ps es L (.seq d a)

/-- A compiled KeY `int` mentions only the inputs of its layout. -/
def KIntValue.Good {ps : List Parameter} {es : List EnvKey} {ls : List PrimTy.uint.Denote}
    {t : LTm C .kint} (v : KIntValue (ps := ps) (es := es) (ls := ls) t) : Prop :=
  ∀ rs : List (Ref C), (∀ r ∈ v.refs, r ∈ rs) →
    (v.lower rs).W (es.length + (ps.length + rs.length) + 2 * ls.length)

theorem KIntValue.ofTermFuel?_good (ps : List Parameter) (es : List EnvKey) :
    ∀ {t : LTm C .kint}, t.ZNum (· ∈ ps) (· ∈ es) (· ∈ ls) → ∀ (n : Nat), t.depth < n → t.depth ≤ 1023 →
      ∃ v, KIntValue.ofTermFuel? (C := C) (es := es) (ls := ls) ps n t = some v ∧ v.Good := by
  intro t h
  induction h with
  | zlit c =>
    intro n hn _
    obtain ⟨n, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by simp only [LTm.depth] at hn; omega⟩
    exact ⟨KIntValue.zlit c, rfl, fun _ _ => CheckedInt.W.lit _ c⟩
  | @toInt a ha =>
    intro n hn hd
    obtain ⟨n, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by simp only [LTm.depth] at hn; omega⟩
    simp only [LTm.depth] at hd
    obtain ⟨w, hw, gw⟩ := CheckedValue.ofTermIn?_good (es := es) ha (by omega)
    replace gw := gw.lift ls
    refine ⟨KIntValue.toInt w, ?_, fun rs hr => CheckedInt.W.ofUint (gw rs hr)⟩
    change (CheckedValue.ofTermIn? (C := C) (es := es) ps a).map KIntValue.toInt = _
    rw [hw]
    rfl
  | @add h a b _ _ iha ihb =>
    intro n hn hd
    obtain ⟨n, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by simp only [LTm.depth] at hn; omega⟩
    simp only [LTm.depth] at hn hd
    obtain ⟨va, hva, ga⟩ := iha n (by omega) (by omega)
    obtain ⟨vb, hvb, gb⟩ := ihb n (by omega) (by omega)
    refine ⟨KIntValue.arith false .add h rfl va vb, ?_, fun rs hr => CheckedInt.W.arith false
      (ga rs (fun r hm => hr r (List.mem_append_left _ hm)))
      (gb rs (fun r hm => hr r (List.mem_append_right _ hm)))⟩
    change (Option.bind (KIntValue.ofTermFuel? (C := C) (es := es) (ls := ls) ps n a) fun x =>
      Option.bind (KIntValue.ofTermFuel? (C := C) (es := es) (ls := ls) ps n b) fun y =>
        some (KIntValue.arith false .add h rfl x y)) = _
    rw [hva, hvb]
    rfl
  | @sub h a b _ _ iha ihb =>
    intro n hn hd
    obtain ⟨n, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by simp only [LTm.depth] at hn; omega⟩
    simp only [LTm.depth] at hn hd
    obtain ⟨va, hva, ga⟩ := iha n (by omega) (by omega)
    obtain ⟨vb, hvb, gb⟩ := ihb n (by omega) (by omega)
    refine ⟨KIntValue.arith true .sub h rfl va vb, ?_, fun rs hr => CheckedInt.W.arith true
      (ga rs (fun r hm => hr r (List.mem_append_left _ hm)))
      (gb rs (fun r hm => hr r (List.mem_append_right _ hm)))⟩
    change (Option.bind (KIntValue.ofTermFuel? (C := C) (es := es) (ls := ls) ps n a) fun x =>
      Option.bind (KIntValue.ofTermFuel? (C := C) (es := es) (ls := ls) ps n b) fun y =>
        some (KIntValue.arith true .sub h rfl x y)) = _
    rw [hva, hvb]
    rfl
  | @mulL h c b _ ihb =>
    intro n hn hd
    obtain ⟨n, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by simp only [LTm.depth] at hn; omega⟩
    simp only [LTm.depth] at hn hd
    obtain ⟨vb, hvb, gb⟩ := ihb n (by omega) (by omega)
    refine ⟨KIntValue.mulLit h c rfl vb, ?_, fun rs hr => CheckedInt.W.scale c (gb rs hr)⟩
    change (Option.bind (KIntValue.ofTermFuel? (C := C) (es := es) (ls := ls) ps n b) fun y =>
      some (KIntValue.mulLit h c rfl y)) = _
    rw [hvb]
    rfl
  | @mulR h a c _ iha =>
    intro n hn hd
    obtain ⟨n, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by simp only [LTm.depth] at hn; omega⟩
    simp only [LTm.depth] at hn hd
    obtain ⟨va, hva, ga⟩ := iha n (by omega) (by omega)
    cases hz : a.zlit? with
    | some r =>
      obtain ⟨m, rfl⟩ := r
      have hn1 : 0 < n := by simp only [LTm.depth] at hn; omega
      obtain ⟨n', rfl⟩ : ∃ k, n = k + 1 := ⟨n - 1, by omega⟩
      refine ⟨KIntValue.mulLit h m rfl (KIntValue.zlit c), ?_, fun _ _ => CheckedInt.W.scale m
        (CheckedInt.W.lit _ c)⟩
      rfl
    | none =>
      refine ⟨KIntValue.litMul h c rfl va, ?_, fun rs hr => CheckedInt.W.scale c (ga rs hr)⟩
      simp only [KIntValue.ofTermFuel?, hz, hva]
      rfl
  | netLit v hv =>
    intro n hn _
    obtain ⟨n, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by simp only [LTm.depth] at hn; omega⟩
    refine ⟨KIntValue.netLit v hv, ?_, fun rs _ => ⟨?_, Nat.zero_le _⟩⟩
    · show (if hc : v ∈ ls then some (KIntValue.netLit v hc) else none) = _
      rw [dif_pos hv]
    · have hi := ledgerIndex_lt hv
      exact (Affine.W.variable (by simp only [Inputs.width]; omega)).sub
        (Affine.W.variable (by simp only [Inputs.width]; omega))
  | @zseq q d a hd _ iha =>
    intro n hn hdep
    obtain ⟨n, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by simp only [LTm.depth] at hn; omega⟩
    simp only [LTm.depth] at hn hdep
    obtain ⟨vd, hvd, gd⟩ := CheckedValue.ofTermIn?_good (es := es) hd (by omega)
    replace gd := gd.lift ls
    obtain ⟨va, hva, ga⟩ := iha n (by omega) (by omega)
    refine ⟨KIntValue.seq vd va, ?_, fun rs hr => ⟨(ga rs (fun r hm => hr r (List.mem_append_right _ hm))).1,
      AFml.width_and (gd rs (fun r hm => hr r (List.mem_append_left _ hm))).2
        (ga rs (fun r hm => hr r (List.mem_append_right _ hm))).2⟩⟩
    change (Option.bind (CheckedValue.ofTermIn? (C := C) (es := es) ps d) fun x =>
      Option.bind (KIntValue.ofTermFuel? (C := C) (es := es) (ls := ls) ps n a) fun y =>
        some (KIntValue.seq x y)) = _
    rw [hvd, hva]
    rfl

theorem KIntValue.ofTermIn?_good {ps : List Parameter} {es : List EnvKey}
    {t : LTm C .kint} (h : t.ZNum (· ∈ ps) (· ∈ es) (· ∈ ls)) (hd : t.depth ≤ 1023) :
    ∃ v, KIntValue.ofTermIn? (C := C) (es := es) (ls := ls) ps t = some v ∧ v.Good :=
  KIntValue.ofTermFuel?_good ps es h 1024 (by omega) hd

/-- The Boolean terms `BooleanValue` encodes. -/
inductive LTm.BoolV (ps : Parameter → Prop) (es : EnvKey → Prop)
    (L : PrimTy.uint.Denote → Prop := fun _ => False) : LTm C (.val .bool) → Prop
  | var (k : Nat) (h : ps ⟨.bool, k⟩) : LTm.BoolV ps es L (.var (p := .bool) k)
  | lit (v : Bool) : LTm.BoolV ps es L (.app0 (.lit (p := .bool) v))
  | err : LTm.BoolV ps es L (LTm.err (C := C) (s := .val .bool))
  | not {a : LTm C (.val .bool)} : LTm.BoolV ps es L a → LTm.BoolV ps es L (.app1 (.unop .not rfl) a)
  | and {a b : LTm C (.val .bool)} : LTm.BoolV ps es L a → LTm.BoolV ps es L b →
      LTm.BoolV ps es L (.app2 (.binop .and rfl) a b)
  | or {a b : LTm C (.val .bool)} : LTm.BoolV ps es L a → LTm.BoolV ps es L b →
      LTm.BoolV ps es L (.app2 (.binop .or rfl) a b)
  | eqB {a b : LTm C (.val .bool)} : LTm.BoolV ps es L a → LTm.BoolV ps es L b →
      LTm.BoolV ps es L (.app2 (.binop .eqB rfl) a b)
  | neB {a b : LTm C (.val .bool)} : LTm.BoolV ps es L a → LTm.BoolV ps es L b →
      LTm.BoolV ps es L (.app2 (.binop .neB rfl) a b)
  | eqN {p : PrimTy} (hp : p.isNumeric = true) {a b : LTm C (.val p)} :
      LTm.Num ps es a → LTm.Num ps es b → LTm.BoolV ps es L (.app2 (.binop .eqB rfl) a b)
  | neN {p : PrimTy} (hp : p.isNumeric = true) {a b : LTm C (.val p)} :
      LTm.Num ps es a → LTm.Num ps es b → LTm.BoolV ps es L (.app2 (.binop .neB rfl) a b)
  | lt {p : PrimTy} (h : BinOp.lt.accepts p = true) {a b : LTm C (.val p)} :
      LTm.Num ps es a → LTm.Num ps es b → LTm.BoolV ps es L (.app2 (.binop .lt h) a b)
  | gt {p : PrimTy} (h : BinOp.gt.accepts p = true) {a b : LTm C (.val p)} :
      LTm.Num ps es a → LTm.Num ps es b → LTm.BoolV ps es L (.app2 (.binop .gt h) a b)
  | le {p : PrimTy} (h : BinOp.le.accepts p = true) {a b : LTm C (.val p)} :
      LTm.Num ps es a → LTm.Num ps es b → LTm.BoolV ps es L (.app2 (.binop .le h) a b)
  | ge {p : PrimTy} (h : BinOp.ge.accepts p = true) {a b : LTm C (.val p)} :
      LTm.Num ps es a → LTm.Num ps es b → LTm.BoolV ps es L (.app2 (.binop .ge h) a b)
  | seqB {d a : LTm C (.val .bool)} : LTm.BoolV ps es L d → LTm.BoolV ps es L a →
      LTm.BoolV ps es L (.seq d a)
  | seqN {q : PrimTy} (hq : q.isNumeric = true) {d : LTm C (.val q)} {a : LTm C (.val .bool)} :
      LTm.Num ps es d → LTm.BoolV ps es L a → LTm.BoolV ps es L (.seq d a)
  /-- A comparison of KeY `int`s. -/
  | zcmp (op : BinOp) (h : op.zCmp = true) {a b : LTm C .kint} :
      LTm.ZNum ps es L a → LTm.ZNum ps es L b → LTm.BoolV ps es L (.app2 (.zcmp op h) a b)

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
    ∀ {t : LTm C (.val .bool)}, t.BoolV (· ∈ ps) (· ∈ es) (· ∈ ls) → ∀ (n : Nat), t.depth < n → t.depth ≤ 1023 →
      ∃ v, BooleanValue.ofTermFuel? (C := C) (es := es) (ls := ls) ps n t = some v ∧ v.Good := by
  intro t h
  induction h with
  | var k hk =>
    intro n hn hd
    obtain ⟨n, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by simp only [LTm.depth] at hn; omega⟩
    obtain ⟨w, hw, gw⟩ := CheckedValue.ofTermIn?_good (es := es) (LTm.Num.var (C := C) (es := (· ∈ es)) (p := .bool) k hk) hd
    replace gw := gw.lift ls
    refine ⟨BooleanValue.ofScalar w, ?_, fun rs hr => CheckedBool.W.ofScalar (gw rs hr)⟩
    change (CheckedValue.ofTermIn? (C := C) (es := es) ps (LTm.var (p := .bool) k)).map BooleanValue.ofScalar = _
    rw [hw]
    rfl
  | lit v =>
    intro n hn hd
    obtain ⟨n, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by simp only [LTm.depth] at hn; omega⟩
    obtain ⟨w, hw, gw⟩ := CheckedValue.ofTermIn?_good (es := es) (LTm.Num.lit (C := C) (ps := (· ∈ ps)) (es := (· ∈ es)) (p := .bool) v) hd
    replace gw := gw.lift ls
    refine ⟨BooleanValue.ofScalar w, ?_, fun rs hr => CheckedBool.W.ofScalar (gw rs hr)⟩
    change (CheckedValue.ofTermIn? (C := C) (es := es) ps (LTm.app0 (.lit (p := .bool) v))).map BooleanValue.ofScalar = _
    rw [hw]
    rfl
  | err =>
    intro n hn hd
    obtain ⟨n, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by simp only [LTm.depth] at hn; omega⟩
    obtain ⟨w, hw, gw⟩ := CheckedValue.ofTermIn?_good (es := es) (LTm.Num.err (C := C) (ps := (· ∈ ps)) (es := (· ∈ es)) (p := .bool)) hd
    replace gw := gw.lift ls
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
    change (BooleanValue.ofTermFuel? (C := C) (es := es) (ls := ls) ps n a).map BooleanValue.not = _
    rw [hv]
    rfl
  | @and a b _ _ iha ihb =>
    intro n hn hd
    obtain ⟨n, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by simp only [LTm.depth] at hn; omega⟩
    simp only [LTm.depth] at hn hd
    obtain ⟨va, hva, ga⟩ := iha n (by omega) (by omega)
    obtain ⟨vb, hvb, gb⟩ := ihb n (by omega) (by omega)
    refine ⟨BooleanValue.and va vb, ?_, fun rs hr => CheckedBool.W.and (ga rs (fun r hm => hr r (List.mem_append_left _ hm))) (gb rs (fun r hm => hr r (List.mem_append_right _ hm)))⟩
    change (Option.bind (BooleanValue.ofTermFuel? (C := C) (es := es) (ls := ls) ps n a) fun x => Option.bind (BooleanValue.ofTermFuel? (C := C) (es := es) (ls := ls) ps n b) fun y => some (BooleanValue.and x y)) = _
    rw [hva, hvb]
    rfl
  | @or a b _ _ iha ihb =>
    intro n hn hd
    obtain ⟨n, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by simp only [LTm.depth] at hn; omega⟩
    simp only [LTm.depth] at hn hd
    obtain ⟨va, hva, ga⟩ := iha n (by omega) (by omega)
    obtain ⟨vb, hvb, gb⟩ := ihb n (by omega) (by omega)
    refine ⟨BooleanValue.or va vb, ?_, fun rs hr => CheckedBool.W.or (ga rs (fun r hm => hr r (List.mem_append_left _ hm))) (gb rs (fun r hm => hr r (List.mem_append_right _ hm)))⟩
    change (Option.bind (BooleanValue.ofTermFuel? (C := C) (es := es) (ls := ls) ps n a) fun x => Option.bind (BooleanValue.ofTermFuel? (C := C) (es := es) (ls := ls) ps n b) fun y => some (BooleanValue.or x y)) = _
    rw [hva, hvb]
    rfl
  | @eqB a b _ _ iha ihb =>
    intro n hn hd
    obtain ⟨n, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by simp only [LTm.depth] at hn; omega⟩
    simp only [LTm.depth] at hn hd
    obtain ⟨va, hva, ga⟩ := iha n (by omega) (by omega)
    obtain ⟨vb, hvb, gb⟩ := ihb n (by omega) (by omega)
    refine ⟨BooleanValue.eq va vb, ?_, fun rs hr => CheckedBool.W.eq (ga rs (fun r hm => hr r (List.mem_append_left _ hm))) (gb rs (fun r hm => hr r (List.mem_append_right _ hm)))⟩
    change (Option.bind (BooleanValue.ofTermFuel? (C := C) (es := es) (ls := ls) ps n a) fun x => Option.bind (BooleanValue.ofTermFuel? (C := C) (es := es) (ls := ls) ps n b) fun y => some (BooleanValue.eq x y)) = _
    rw [hva, hvb]
    rfl
  | @neB a b _ _ iha ihb =>
    intro n hn hd
    obtain ⟨n, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by simp only [LTm.depth] at hn; omega⟩
    simp only [LTm.depth] at hn hd
    obtain ⟨va, hva, ga⟩ := iha n (by omega) (by omega)
    obtain ⟨vb, hvb, gb⟩ := ihb n (by omega) (by omega)
    refine ⟨BooleanValue.ne va vb, ?_, fun rs hr => CheckedBool.W.not (CheckedBool.W.eq (ga rs (fun r hm => hr r (List.mem_append_left _ hm))) (gb rs (fun r hm => hr r (List.mem_append_right _ hm))))⟩
    change (Option.bind (BooleanValue.ofTermFuel? (C := C) (es := es) (ls := ls) ps n a) fun x => Option.bind (BooleanValue.ofTermFuel? (C := C) (es := es) (ls := ls) ps n b) fun y => some (BooleanValue.ne x y)) = _
    rw [hva, hvb]
    rfl
  | @eqN p hp a b ha hb =>
    intro n hn hd
    obtain ⟨n, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by simp only [LTm.depth] at hn; omega⟩
    simp only [LTm.depth] at hn hd
    obtain ⟨va, hva, ga⟩ := CheckedValue.ofTermIn?_good ha (by omega)
    replace ga := ga.lift ls
    obtain ⟨vb, hvb, gb⟩ := CheckedValue.ofTermIn?_good hb (by omega)
    replace gb := gb.lift ls
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
    replace ga := ga.lift ls
    obtain ⟨vb, hvb, gb⟩ := CheckedValue.ofTermIn?_good hb (by omega)
    replace gb := gb.lift ls
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
    replace ga := ga.lift ls
    obtain ⟨vb, hvb, gb⟩ := CheckedValue.ofTermIn?_good hb (by omega)
    replace gb := gb.lift ls
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
    replace ga := ga.lift ls
    obtain ⟨vb, hvb, gb⟩ := CheckedValue.ofTermIn?_good hb (by omega)
    replace gb := gb.lift ls
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
    replace ga := ga.lift ls
    obtain ⟨vb, hvb, gb⟩ := CheckedValue.ofTermIn?_good hb (by omega)
    replace gb := gb.lift ls
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
    replace ga := ga.lift ls
    obtain ⟨vb, hvb, gb⟩ := CheckedValue.ofTermIn?_good hb (by omega)
    replace gb := gb.lift ls
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
    change (Option.bind (BooleanValue.ofTermFuel? (C := C) (es := es) (ls := ls) ps n d) fun x => Option.bind (BooleanValue.ofTermFuel? (C := C) (es := es) (ls := ls) ps n a) fun y => some (BooleanValue.seq (BooleanValue.defined x) y)) = _
    rw [hvd, hva]
    rfl
  | @seqN q hq d a hdn _ iha =>
    intro n hn hd
    obtain ⟨n, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by simp only [LTm.depth] at hn; omega⟩
    simp only [LTm.depth] at hn hd
    obtain ⟨vd, hvd, gd⟩ := CheckedValue.ofTermIn?_good hdn (by omega)
    replace gd := gd.lift ls
    obtain ⟨va, hva, ga⟩ := iha n (by omega) (by omega)
    cases q with
    | bool => cases hq
    | uint | int =>
      refine ⟨BooleanValue.seq vd.defined va, ?_, fun rs hr =>
        ⟨AFml.width_and (gd rs (fun r hm => hr r (List.mem_append_left _ hm))).2 (ga rs (fun r hm => hr r (List.mem_append_right _ hm))).1, AFml.width_and (gd rs (fun r hm => hr r (List.mem_append_left _ hm))).2 (ga rs (fun r hm => hr r (List.mem_append_right _ hm))).2⟩⟩
      change (Option.bind (CheckedValue.ofTermIn? (C := C) (es := es) ps d) fun x => Option.bind (BooleanValue.ofTermFuel? (C := C) (es := es) (ls := ls) ps n a) fun y => some (BooleanValue.seq (CheckedValue.defined x) y)) = _
      rw [hvd, hva]
      rfl
  | @zcmp op h a b ha hb =>
    intro n hn hd
    obtain ⟨n, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by simp only [LTm.depth] at hn; omega⟩
    simp only [LTm.depth] at hn hd
    obtain ⟨va, hva, ga⟩ := KIntValue.ofTermIn?_good ha (by omega)
    obtain ⟨vb, hvb, gb⟩ := KIntValue.ofTermIn?_good hb (by omega)
    refine ⟨BooleanValue.zcmp op h va vb, ?_, fun rs hr => CheckedInt.W.comparison op
      (ga rs (fun r hm => hr r (List.mem_append_left _ hm)))
      (gb rs (fun r hm => hr r (List.mem_append_right _ hm)))⟩
    change (Option.bind (KIntValue.ofTermIn? (C := C) (es := es) (ls := ls) ps a) fun x =>
      Option.bind (KIntValue.ofTermIn? (C := C) (es := es) (ls := ls) ps b) fun y =>
        some (BooleanValue.zcmp op h x y)) = _
    rw [hva, hvb]
    rfl

theorem BooleanValue.ofTermIn?_good {ps : List Parameter} {es : List EnvKey}
    {t : LTm C (.val .bool)} (h : t.BoolV (· ∈ ps) (· ∈ es) (· ∈ ls)) (hd : t.depth ≤ 1023) :
    ∃ v, BooleanValue.ofTermIn? (C := C) (es := es) (ls := ls) ps t = some v ∧ v.Good :=
  BooleanValue.ofTermFuel?_good ps es h 1024 (by omega) hd

/-- The formulas `StorageEncoding` encodes: Boolean equations of Boolean
terms, numeric equations of scalar terms, under `¬`, `∧`, `→`. -/
inductive LFml.Arith (ps : Parameter → Prop) (es : EnvKey → Prop)
    (L : PrimTy.uint.Denote → Prop := fun _ => False) : LFml C → Prop
  | tt : LFml.Arith ps es L .tt
  | eqB {a b : LTm C (.val .bool)} : a.BoolV ps es L → b.BoolV ps es L → a.depth ≤ 1023 →
      b.depth ≤ 1023 → LFml.Arith ps es L (.eq a b)
  | eqN {p : PrimTy} (hp : p.isNumeric = true) {a b : LTm C (.val p)} : a.Num ps es →
      b.Num ps es → a.depth ≤ 1023 → b.depth ≤ 1023 → LFml.Arith ps es L (.eq a b)
  | not {φ : LFml C} : LFml.Arith ps es L φ → LFml.Arith ps es L (.not φ)
  | and {φ ψ : LFml C} : LFml.Arith ps es L φ → LFml.Arith ps es L ψ → LFml.Arith ps es L (.and φ ψ)
  | imp {φ ψ : LFml C} : LFml.Arith ps es L φ → LFml.Arith ps es L ψ → LFml.Arith ps es L (.imp φ ψ)
  /-- The defining equations of cut atoms (`Calculus/QuotientCut.lean`). -/
  | defDiv (h : BinOp.div.accepts .uint = true) (c : PrimTy.uint.Denote) (hc : c.val ≠ 0) (k : Nat)
      {a : LTm C (.val .uint)} : a.Num ps es → ps ⟨.uint, k⟩ → a.depth ≤ 1023 →
      LFml.Arith ps es L (.eq (.app2 (.binop .div h) a (.app0 (.lit c))) (.var k))
  | defShr {p : PrimTy} (h : BinOp.shr.accepts p = true) (v : p.Denote) (k : Nat)
      {a : LTm C (.val p)} : a.Num ps es → ps ⟨p, k⟩ → a.depth ≤ 1023 →
      LFml.Arith ps es L (.eq (.app2 (.binop .shr h) a (.app0 (.lit v))) (.var k))
  | defAddW (h : BinOp.addW.accepts .uint = true) (k : Nat) {a b : LTm C (.val .uint)} :
      a.Num ps es → b.Num ps es → ps ⟨.uint, k⟩ → a.depth ≤ 1023 → b.depth ≤ 1023 →
      LFml.Arith ps es L (.eq (.app2 (.binop .addW h) a b) (.var k))
  | defSubW (h : BinOp.subW.accepts .uint = true) (k : Nat) {a b : LTm C (.val .uint)} :
      a.Num ps es → b.Num ps es → ps ⟨.uint, k⟩ → a.depth ≤ 1023 → b.depth ≤ 1023 →
      LFml.Arith ps es L (.eq (.app2 (.binop .subW h) a b) (.var k))
  | defToInt (h : UnOp.toInt.accepts .uint = true) (k : Nat) {a : LTm C (.val .uint)} :
      a.Num ps es → ps ⟨.int, k⟩ → a.depth ≤ 1023 →
      LFml.Arith ps es L (.eq (.app1 (.unop .toInt h) a) (.var k))
  | defToUint (h : UnOp.toUint.accepts .int = true) (k : Nat) {a : LTm C (.val .int)} :
      a.Num ps es → ps ⟨.uint, k⟩ → a.depth ≤ 1023 →
      LFml.Arith ps es L (.eq (.app1 (.unop .toUint h) a) (.var k))

theorem StorageEncoding.specialVar?_num {ps : List Parameter} {es : List EnvKey}
    {P : Parameter → Prop} {E : EnvKey → Prop} :
    ∀ {p : PrimTy} {a : LTm C (.val p)}, a.Num P E → ∀ k (hk : Parameter.mk p k ∈ ps),
      StorageEncoding.specialVar? (ps := ps) (es := es) (ls := ls) a k hk = none := by
  intro p a ha
  cases ha <;> intro k hk <;> rfl

theorem StorageEncoding.specialVar?_bool {ps : List Parameter} {es : List EnvKey}
    {P : Parameter → Prop} {E : EnvKey → Prop} {L : PrimTy.uint.Denote → Prop} :
    ∀ {a : LTm C (.val .bool)}, a.BoolV P E L → ∀ k (hk : Parameter.mk .bool k ∈ ps),
      StorageEncoding.specialVar? (ps := ps) (es := es) (ls := ls) a k hk = none := by
  intro a ha
  cases ha <;> intro k hk <;> rfl

theorem StorageEncoding.special?_none {ps : List Parameter} {es : List EnvKey} {p : PrimTy}
    {a : LTm C (.val p)} (ha : ∀ k (hk : Parameter.mk p k ∈ ps),
      StorageEncoding.specialVar? (ps := ps) (es := es) (ls := ls) a k hk = none) (b : LTm C (.val p)) :
    StorageEncoding.special? (ps := ps) (es := es) (ls := ls) a b = none := by
  unfold StorageEncoding.special?
  split
  · split
    · exact ha _ _
    · rfl
  · rfl

theorem StorageEncoding.equality?_plain {ps : List Parameter} {es : List EnvKey} {p : PrimTy}
    {a : LTm C (.val p)} (ha : ∀ k (hk : Parameter.mk p k ∈ ps),
      StorageEncoding.specialVar? (ps := ps) (es := es) (ls := ls) a k hk = none) (b : LTm C (.val p)) :
    StorageEncoding.equality? (ps := ps) (es := es) (ls := ls) a b =
      StorageEncoding.equalityPlain? (ps := ps) (es := es) (ls := ls) a b := by
  unfold StorageEncoding.equality?
  rw [StorageEncoding.special?_none ha b]

theorem StorageEncoding.equality?_var {ps : List Parameter} {es : List EnvKey} {p : PrimTy}
    (a : LTm C (.val p)) (k : Nat) (hk : Parameter.mk p k ∈ ps)
    (e : StorageEncoding (ps := ps) (es := es) (ls := ls) (.eq a (.var k)))
    (he : StorageEncoding.specialVar? (ps := ps) (es := es) (ls := ls) a k hk = some e) :
    StorageEncoding.equality? (ps := ps) (es := es) (ls := ls) a (.var k) = some e := by
  have hs : StorageEncoding.special? (ps := ps) (es := es) (ls := ls) a (.var k) =
      StorageEncoding.specialVar? (ps := ps) (es := es) (ls := ls) a k hk := by
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

theorem StorageEncoding.ofFormulaL?_good {ps : List Parameter} {es : List EnvKey} :
    ∀ {φ : LFml C}, φ.Arith (· ∈ ps) (· ∈ es) (· ∈ ls) → ∃ v, StorageEncoding.ofFormulaL? (C := C) (ps := ps) (es := es) (ls := ls) φ = some v ∧ v.Good := by
  intro φ h
  induction h with
  | tt => exact ⟨_, rfl, fun _ _ => Nat.zero_le _⟩
  | @eqB a b ha hb hda hdb =>
    obtain ⟨va, hva, ga⟩ := BooleanValue.ofTermIn?_good (es := es) (ls := ls) ha hda
    obtain ⟨vb, hvb, gb⟩ := BooleanValue.ofTermIn?_good (es := es) (ls := ls) hb hdb
    refine ⟨StorageEncoding.boolEq va vb, ?_, fun rs hr => (CheckedBool.W.eq (ga rs (fun r hm => hr r (List.mem_append_left _ hm))) (gb rs (fun r hm => hr r (List.mem_append_right _ hm)))).1⟩
    show StorageEncoding.equality? a b = _
    rw [StorageEncoding.equality?_plain (StorageEncoding.specialVar?_bool ha) b]
    change (Option.bind (BooleanValue.ofTermIn? (C := C) (es := es) (ls := ls) ps a) fun x => Option.bind (BooleanValue.ofTermIn? (C := C) (es := es) (ls := ls) ps b) fun y => some (StorageEncoding.boolEq x y)) = _
    rw [hva, hvb]
    rfl
  | @eqN p hp a b ha hb hda hdb =>
    obtain ⟨va, hva, ga⟩ := CheckedValue.ofTermIn?_good (es := es) ha hda
    replace ga := ga.lift ls
    obtain ⟨vb, hvb, gb⟩ := CheckedValue.ofTermIn?_good (es := es) hb hdb
    replace gb := gb.lift ls
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
    change (StorageEncoding.ofFormulaL? (C := C) (ps := ps) (es := es) (ls := ls) φ).map StorageEncoding.not = _
    rw [hv]
    rfl
  | @and φ ψ _ _ ihφ ihψ =>
    obtain ⟨v, hv, gv⟩ := ihφ
    obtain ⟨w, hw, gw⟩ := ihψ
    refine ⟨StorageEncoding.and v w, ?_, fun rs hr => AFml.width_and (gv rs (fun r hm => hr r (List.mem_append_left _ hm))) (gw rs (fun r hm => hr r (List.mem_append_right _ hm)))⟩
    change (Option.bind (StorageEncoding.ofFormulaL? (C := C) (ps := ps) (es := es) (ls := ls) φ) fun x => Option.bind (StorageEncoding.ofFormulaL? (C := C) (ps := ps) (es := es) (ls := ls) ψ) fun y => some (StorageEncoding.and x y)) = _
    rw [hv, hw]
    rfl
  | @imp φ ψ _ _ ihφ ihψ =>
    obtain ⟨v, hv, gv⟩ := ihφ
    obtain ⟨w, hw, gw⟩ := ihψ
    refine ⟨StorageEncoding.imp v w, ?_, fun rs hr => AFml.width_imp (gv rs (fun r hm => hr r (List.mem_append_left _ hm))) (gw rs (fun r hm => hr r (List.mem_append_right _ hm)))⟩
    change (Option.bind (StorageEncoding.ofFormulaL? (C := C) (ps := ps) (es := es) (ls := ls) φ) fun x => Option.bind (StorageEncoding.ofFormulaL? (C := C) (ps := ps) (es := es) (ls := ls) ψ) fun y => some (StorageEncoding.imp x y)) = _
    rw [hv, hw]
    rfl

  | @defDiv h c hc k a ha hk hd =>
    obtain ⟨va, hva, ga⟩ := CheckedValue.ofTermIn?_good (es := es) ha hd
    replace ga := ga.lift ls
    refine ⟨StorageEncoding.defDiv h c hc k hk va, StorageEncoding.equality?_var _ k hk _ ?_,
      fun rs hr => AFml.width_and (ga rs hr).2 (floorRel_width (ga rs hr).1 ((Affine.W.var_index hk).mono (Nat.le_add_right _ _)) _ _ _)⟩
    show (if hc' : c.val = 0 then none else _) = _
    rw [dif_neg hc, hva]
    rfl
  | @defShr p h v k a ha hk hd =>
    obtain ⟨va, hva, ga⟩ := CheckedValue.ofTermIn?_good (es := es) ha hd
    replace ga := ga.lift ls
    refine ⟨StorageEncoding.defShr h v k hk va, StorageEncoding.equality?_var _ k hk _ ?_,
      fun rs hr => AFml.width_and (ga rs hr).2 (floorRel_width (ga rs hr).1 ((Affine.W.var_index hk).mono (Nat.le_add_right _ _)) _ _ _)⟩
    cases p with
    | bool => cases h
    | uint | int =>
      show (CheckedValue.ofTermIn? ps a).map _ = _
      rw [hva]
      rfl
  | @defAddW h k a b ha hb hk hda hdb =>
    obtain ⟨va, hva, ga⟩ := CheckedValue.ofTermIn?_good (es := es) ha hda
    replace ga := ga.lift ls
    obtain ⟨vb, hvb, gb⟩ := CheckedValue.ofTermIn?_good (es := es) hb hdb
    replace gb := gb.lift ls
    refine ⟨StorageEncoding.defAddW h k hk va vb, StorageEncoding.equality?_var _ k hk _ ?_,
      fun rs hr => ?_⟩
    · show (Option.bind (CheckedValue.ofTermIn? ps a) fun x =>
        Option.bind (CheckedValue.ofTermIn? ps b) fun y => some _) = _
      rw [hva, hvb]
      rfl
    · have ha' := ga rs (fun r hm => hr r (List.mem_append_left _ hm))
      have hb' := gb rs (fun r hm => hr r (List.mem_append_right _ hm))
      exact AFml.width_and ha'.2 (AFml.width_and hb'.2
        (wrapRel_width ha'.1 hb'.1 ((Affine.W.var_index hk).mono (Nat.le_add_right _ _)) false))
  | @defSubW h k a b ha hb hk hda hdb =>
    obtain ⟨va, hva, ga⟩ := CheckedValue.ofTermIn?_good (es := es) ha hda
    replace ga := ga.lift ls
    obtain ⟨vb, hvb, gb⟩ := CheckedValue.ofTermIn?_good (es := es) hb hdb
    replace gb := gb.lift ls
    refine ⟨StorageEncoding.defSubW h k hk va vb, StorageEncoding.equality?_var _ k hk _ ?_,
      fun rs hr => ?_⟩
    · show (Option.bind (CheckedValue.ofTermIn? ps a) fun x =>
        Option.bind (CheckedValue.ofTermIn? ps b) fun y => some _) = _
      rw [hva, hvb]
      rfl
    · have ha' := ga rs (fun r hm => hr r (List.mem_append_left _ hm))
      have hb' := gb rs (fun r hm => hr r (List.mem_append_right _ hm))
      exact AFml.width_and ha'.2 (AFml.width_and hb'.2
        (wrapRel_width ha'.1 hb'.1 ((Affine.W.var_index hk).mono (Nat.le_add_right _ _)) true))
  | @defToInt h k a ha hk hd =>
    obtain ⟨va, hva, ga⟩ := CheckedValue.ofTermIn?_good (es := es) ha hd
    replace ga := ga.lift ls
    refine ⟨StorageEncoding.defToInt h k hk va, StorageEncoding.equality?_var _ k hk _ ?_,
      fun rs hr => AFml.width_and (ga rs hr).2 (convRel_width (ga rs hr).1 ((Affine.W.var_index hk).mono (Nat.le_add_right _ _)))⟩
    show (CheckedValue.ofTermIn? ps a).map _ = _
    rw [hva]
    rfl
  | @defToUint h k a ha hk hd =>
    obtain ⟨va, hva, ga⟩ := CheckedValue.ofTermIn?_good (es := es) ha hd
    replace ga := ga.lift ls
    refine ⟨StorageEncoding.defToUint h k hk va, StorageEncoding.equality?_var _ k hk _ ?_,
      fun rs hr => AFml.width_and (ga rs hr).2 (convRel_width ((Affine.W.var_index hk).mono (Nat.le_add_right _ _)) (ga rs hr).1)⟩
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

theorem LTm.ZNum.ledger_mono {P : Parameter → Prop} {E : EnvKey → Prop}
    {L L' : PrimTy.uint.Denote → Prop} (hL : ∀ v, L v → L' v) :
    ∀ {t : LTm C .kint}, t.ZNum P E L → t.ZNum P E L' := by
  intro t h
  induction h with
  | zlit n => exact .zlit n
  | toInt ha => exact .toInt ha
  | add h _ _ iha ihb => exact .add h iha ihb
  | sub h _ _ iha ihb => exact .sub h iha ihb
  | mulL h n _ ih => exact .mulL h n ih
  | mulR h n _ ih => exact .mulR h n ih
  | netLit v hv => exact .netLit v (hL v hv)
  | zseq hd _ ih => exact .zseq hd ih

theorem LTm.BoolV.ledger_mono {P : Parameter → Prop} {E : EnvKey → Prop}
    {L L' : PrimTy.uint.Denote → Prop} (hL : ∀ v, L v → L' v) :
    ∀ {t : LTm C (.val .bool)}, t.BoolV P E L → t.BoolV P E L' := by
  intro t h
  induction h with
  | var k hk => exact .var k hk
  | lit v => exact .lit v
  | err => exact .err
  | not _ ih => exact .not ih
  | and _ _ iha ihb => exact .and iha ihb
  | or _ _ iha ihb => exact .or iha ihb
  | eqB _ _ iha ihb => exact .eqB iha ihb
  | neB _ _ iha ihb => exact .neB iha ihb
  | eqN hp ha hb => exact .eqN hp ha hb
  | neN hp ha hb => exact .neN hp ha hb
  | lt h ha hb => exact .lt h ha hb
  | gt h ha hb => exact .gt h ha hb
  | le h ha hb => exact .le h ha hb
  | ge h ha hb => exact .ge h ha hb
  | seqB _ _ ihd iha => exact .seqB ihd iha
  | seqN hq hd _ iha => exact .seqN hq hd iha
  | zcmp op h ha hb => exact .zcmp op h (ha.ledger_mono hL) (hb.ledger_mono hL)

theorem LFml.Arith.ledger_mono {P : Parameter → Prop} {E : EnvKey → Prop}
    {L L' : PrimTy.uint.Denote → Prop} (hL : ∀ v, L v → L' v) :
    ∀ {φ : LFml C}, φ.Arith P E L → φ.Arith P E L' := by
  intro φ h
  induction h with
  | tt => exact .tt
  | eqB ha hb hda hdb => exact .eqB (ha.ledger_mono hL) (hb.ledger_mono hL) hda hdb
  | eqN hp ha hb hda hdb => exact .eqN hp ha hb hda hdb
  | not _ ih => exact .not ih
  | and _ _ ih1 ih2 => exact .and ih1 ih2
  | imp _ _ ih1 ih2 => exact .imp ih1 ih2
  | defDiv h c hc k ha hk hd => exact .defDiv h c hc k ha hk hd
  | defShr h v k ha hk hd => exact .defShr h v k ha hk hd
  | defAddW h k ha hb hk hda hdb => exact .defAddW h k ha hb hk hda hdb
  | defSubW h k ha hb hk hda hdb => exact .defSubW h k ha hb hk hda hdb
  | defToInt h k ha hk hd => exact .defToInt h k ha hk hd
  | defToUint h k ha hk hd => exact .defToUint h k ha hk hd

/-- **The compiler never refuses its fragment**, with no ledger. -/
theorem StorageEncoding.ofFormula?_good {ps : List Parameter} {es : List EnvKey} :
    ∀ {φ : LFml C}, φ.Arith (· ∈ ps) (· ∈ es) → ∃ v, StorageEncoding.ofFormula? (C := C) (ps := ps) (es := es) φ = some v ∧
      ∀ rs : List (Ref C), (∀ r ∈ v.refs, r ∈ rs) → (v.lower rs).width ≤ es.length + (ps.length + rs.length) := by
  intro φ h
  obtain ⟨v, hv, gv⟩ := StorageEncoding.ofFormulaL?_good (ls := [])
    (h.ledger_mono (L' := (· ∈ ([] : List PrimTy.uint.Denote))) (fun _ h => h.elim))
  refine ⟨v, hv, fun rs hr => ?_⟩
  simpa only [List.length_nil, Nat.mul_zero, Nat.add_zero] using gv rs hr

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
