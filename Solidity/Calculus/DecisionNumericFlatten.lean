import Solidity.Calculus.DecisionNumericLogic

/-! # Formula-derived read-free numeric flattening resources
These proofs concern the existing flattener, independently of the later
arithmetic compiler and unchanged global admission/runtime bounds.
-/
namespace Solidity.Decide

private def PureFuel {C : Contract} {s : Srt} (t : LTm C s) : Prop :=
  ∀ d r start : Nat, t.depth ≤ d → t.nodes ≤ r →
    flattenFuel? d r t start = some (Flattened.pure t start, r - t.nodes)

private theorem pureFuel_var {C : Contract} {p : PrimTy} (k : Nat) :
    PureFuel (LTm.var (C := C) (p := p) k) := by
  intro d r start hd hr
  cases d with
  | zero => simp only [LTm.depth] at hd; omega
  | succ d =>
    cases r with
    | zero => simp only [LTm.nodes] at hr; omega
    | succ r => simp only [LTm.nodes, Nat.add_sub_cancel]; rfl

private theorem pureFuel_lit {C : Contract} {p : PrimTy} (v : p.Denote) :
    PureFuel (LTm.app0 (C := C) (.lit v)) := by
  intro d r start hd hr
  cases d with
  | zero => simp only [LTm.depth] at hd; omega
  | succ d =>
    cases r with
    | zero => simp only [LTm.nodes] at hr; omega
    | succ r =>
      simpa only [LTm.nodes, Nat.add_sub_cancel] using flattenFuel?_lit v d r start

private theorem pureFuel_env {C : Contract} (e : EnvKey) :
    PureFuel (LTm.app0 (C := C) (.env e)) := by
  intro d r start hd hr
  cases d with
  | zero => simp only [LTm.depth] at hd; omega
  | succ d =>
    cases r with
    | zero => simp only [LTm.nodes] at hr; omega
    | succ r => simp only [LTm.nodes, Nat.add_sub_cancel]; rfl

private theorem pureFuel_err {C : Contract} {p : PrimTy} :
    PureFuel (LTm.err (C := C) (s := .val p)) := by
  intro d r start hd hr
  cases d with
  | zero => simp only [LTm.depth] at hd; omega
  | succ d =>
    cases r with
    | zero => simp only [LTm.nodes] at hr; omega
    | succ r => simp only [LTm.nodes, Nat.add_sub_cancel]; rfl

private theorem pureFuel_unop {C : Contract} {p : PrimTy} (op : UnOp)
    (hop : op.accepts p = true) {a : LTm C (.val p)} (ha : PureFuel a) :
    PureFuel (LTm.app1 (.unop op hop) a) := by
  intro d r start hd hr
  cases d with
  | zero => simp only [LTm.depth] at hd; omega
  | succ d =>
    cases r with
    | zero => simp only [LTm.nodes] at hr; omega
    | succ r =>
      have hda : a.depth ≤ d := by simp only [LTm.depth] at hd; omega
      have hra : a.nodes ≤ r := by simp only [LTm.nodes] at hr; omega
      change (flattenFuel? d r a start).bind (fun u =>
        some (Flattened.app1 (.unop op hop) u.1, u.2)) = _
      rw [ha d r start hda hra]
      simp only [Option.bind_some, Flattened.app1, Flattened.pure, LTm.nodes,
        Nat.add_sub_add_right]

private theorem pureFuel_binop {C : Contract} {p : PrimTy} (op : BinOp)
    (hop : op.accepts p = true) {a b : LTm C (.val p)}
    (ha : PureFuel a) (hb : PureFuel b) :
    PureFuel (LTm.app2 (.binop op hop) a b) := by
  intro d r start hd hr
  cases d with
  | zero => simp only [LTm.depth] at hd; omega
  | succ d =>
    cases r with
    | zero => simp only [LTm.nodes] at hr; omega
    | succ r =>
      have hda : a.depth ≤ d := by simp only [LTm.depth] at hd; omega
      have hdb : b.depth ≤ d := by simp only [LTm.depth] at hd; omega
      have hra : a.nodes ≤ r := by simp only [LTm.nodes] at hr; omega
      have hrb : b.nodes ≤ r - a.nodes := by simp only [LTm.nodes] at hr; omega
      change (flattenFuel? d r a start).bind (fun u =>
        (flattenFuel? d u.2 b u.1.next).bind (fun v =>
          some (Flattened.app2 (.binop op hop) u.1 v.1, v.2))) = _
      rw [ha d r start hda hra]
      change (flattenFuel? d (r - a.nodes) b start).bind (fun v =>
        some (Flattened.app2 (.binop op hop) (Flattened.pure a start) v.1, v.2)) = _
      rw [hb d (r - a.nodes) start hdb hrb]
      simp only [Option.bind_some, Flattened.app2, Flattened.pure, List.nil_append,
        LTm.nodes, Nat.add_sub_add_right, Nat.sub_sub]

private theorem pureFuel_seq {C : Contract} {p q : PrimTy}
    {a : LTm C (.val p)} {b : LTm C (.val q)} (ha : PureFuel a) (hb : PureFuel b) :
    PureFuel (LTm.seq a b) := by
  intro d r start hd hr
  cases d with
  | zero => simp only [LTm.depth] at hd; omega
  | succ d =>
    cases r with
    | zero => simp only [LTm.nodes] at hr; omega
    | succ r =>
      have hda : a.depth ≤ d := by simp only [LTm.depth] at hd; omega
      have hdb : b.depth ≤ d := by simp only [LTm.depth] at hd; omega
      have hra : a.nodes ≤ r := by simp only [LTm.nodes] at hr; omega
      have hrb : b.nodes ≤ r - a.nodes := by simp only [LTm.nodes] at hr; omega
      change (flattenFuel? d r a start).bind (fun u =>
        (flattenFuel? d u.2 b u.1.next).bind (fun v =>
          some (Flattened.seq u.1 v.1, v.2))) = _
      rw [ha d r start hda hra]
      change (flattenFuel? d (r - a.nodes) b start).bind (fun v =>
        some (Flattened.seq (Flattened.pure a start) v.1, v.2)) = _
      rw [hb d (r - a.nodes) start hdb hrb]
      simp only [Option.bind_some, Flattened.seq, Flattened.pure, List.nil_append,
        LTm.nodes, Nat.add_sub_add_right, Nat.sub_sub]

/-- Actual numeric flattening consumes exactly its structural nodes, without
any 511-node premise, and returns the original term with no storage observations. -/
theorem numeric_flattenFuel {C : Contract} {P : Parameter → Prop} {E : EnvKey → Prop}
    {p : PrimTy} {t : LTm C (.val p)} (h : t.Num P E) (d r start : Nat)
    (hd : t.depth ≤ d) (hr : t.nodes ≤ r) :
    flattenFuel? d r t start = some (Flattened.pure t start, r - t.nodes) := by
  have hp : PureFuel t := by
    clear hd hr
    induction h with
    | var k hk => exact pureFuel_var k
    | lit v => exact pureFuel_lit v
    | env e he => exact pureFuel_env e
    | add hop ha hb iha ihb => exact pureFuel_binop .add hop iha ihb
    | sub hop ha hb iha ihb => exact pureFuel_binop .sub hop iha ihb
    | mulL hop v hb ihb => exact pureFuel_binop .mul hop (pureFuel_lit v) ihb
    | mulR hop v ha iha => exact pureFuel_binop .mul hop iha (pureFuel_lit v)
    | neg hop ha iha => exact pureFuel_unop .neg hop iha
    | bnot hop ha iha => exact pureFuel_unop .bnot hop iha
    | seq ha hb iha ihb => exact pureFuel_seq iha ihb
    | err => exact pureFuel_err
  exact hp d r start hd hr

/-- Structural nodes alone suffice for this real term traversal. -/
theorem numeric_flattenTermAt_nodes {C : Contract} {P : Parameter → Prop} {E : EnvKey → Prop}
    {p : PrimTy} {t : LTm C (.val p)} (h : t.Num P E) (start : Nat) :
    flattenTermAt? t.nodes start t = some (Flattened.pure t start) := by
  have hf : flattenFuel? t.nodes t.nodes t start =
      some (Flattened.pure t start, t.nodes - t.nodes) :=
    numeric_flattenFuel h t.nodes t.nodes start (LTm.depth_le_nodes t) (Nat.le_refl _)
  simp only [flattenTermAt?, hf, Option.map_some]

private def pureFormula {C : Contract} (φ : LFml C) (start : Nat) : FlattenedFormula φ start :=
  ⟨φ, [], fun _ _ _ => Iff.rfl⟩

private def PureFormulaFuel {C : Contract} (φ : LFml C) : Prop :=
  ∀ d r start : Nat, φ.depth ≤ d → φ.nodes ≤ r →
    flattenFormulaFuel? d r φ start = some (pureFormula φ start, r - φ.nodes)

private theorem pureFormulaFuel_tt {C : Contract} : PureFormulaFuel (LFml.tt (C := C)) := by
  intro d r start hd hr
  cases d with
  | zero => simp only [LFml.depth] at hd; omega
  | succ d =>
    cases r with
    | zero => simp only [LFml.nodes] at hr; omega
    | succ r => simp only [LFml.nodes, Nat.add_sub_cancel]; rfl

private theorem pureFormulaFuel_eq {C : Contract} {P : Parameter → Prop} {E : EnvKey → Prop}
    {p : PrimTy} {a b : LTm C (.val p)} (ha : a.Num P E) (hb : b.Num P E) :
    PureFormulaFuel (LFml.eq a b) := by
  intro d r start hd hr
  cases d with
  | zero => simp only [LFml.depth] at hd; omega
  | succ d =>
    cases r with
    | zero => simp only [LFml.nodes] at hr; omega
    | succ r =>
      have hda : a.depth ≤ d := by simp only [LFml.depth] at hd; omega
      have hdb : b.depth ≤ d := by simp only [LFml.depth] at hd; omega
      have hra : a.nodes ≤ r := by simp only [LFml.nodes] at hr; omega
      have hrb : b.nodes ≤ r - a.nodes := by simp only [LFml.nodes] at hr; omega
      change (flattenFuel? d r a start).bind (fun u =>
        (flattenFuel? d u.2 b u.1.next).bind (fun v =>
          some (FlattenedFormula.eq u.1 v.1, v.2))) = _
      rw [numeric_flattenFuel ha d r start hda hra]
      change (flattenFuel? d (r - a.nodes) b start).bind (fun v =>
        some (FlattenedFormula.eq (Flattened.pure a start) v.1, v.2)) = _
      rw [numeric_flattenFuel hb d (r - a.nodes) start hdb hrb]
      simp only [Option.bind_some, FlattenedFormula.eq, Flattened.pure, pureFormula,
        List.nil_append, LFml.nodes, Nat.add_sub_add_right, Nat.sub_sub]

private theorem pureFormulaFuel_not {C : Contract} {φ : LFml C} (h : PureFormulaFuel φ) :
    PureFormulaFuel (.not φ) := by
  intro d r start hd hr
  cases d with
  | zero => simp only [LFml.depth] at hd; omega
  | succ d =>
    cases r with
    | zero => simp only [LFml.nodes] at hr; omega
    | succ r =>
      have hda : φ.depth ≤ d := by simp only [LFml.depth] at hd; omega
      have hra : φ.nodes ≤ r := by simp only [LFml.nodes] at hr; omega
      change (flattenFormulaFuel? d r φ start).bind (fun u =>
        some (FlattenedFormula.not u.1, u.2)) = _
      rw [h d r start hda hra]
      simp only [Option.bind_some, FlattenedFormula.not, pureFormula, LFml.nodes,
        Nat.add_sub_add_right]

private theorem pureFormulaFuel_and {C : Contract} {φ ψ : LFml C}
    (hφ : PureFormulaFuel φ) (hψ : PureFormulaFuel ψ) : PureFormulaFuel (.and φ ψ) := by
  intro d r start hd hr
  cases d with
  | zero => simp only [LFml.depth] at hd; omega
  | succ d =>
    cases r with
    | zero => simp only [LFml.nodes] at hr; omega
    | succ r =>
      have hdφ : φ.depth ≤ d := by simp only [LFml.depth] at hd; omega
      have hdψ : ψ.depth ≤ d := by simp only [LFml.depth] at hd; omega
      have hrφ : φ.nodes ≤ r := by simp only [LFml.nodes] at hr; omega
      have hrψ : ψ.nodes ≤ r - φ.nodes := by simp only [LFml.nodes] at hr; omega
      change (flattenFormulaFuel? d r φ start).bind (fun u =>
        (flattenFormulaFuel? d u.2 ψ u.1.next).bind (fun v =>
          some (FlattenedFormula.and u.1 v.1, v.2))) = _
      rw [hφ d r start hdφ hrφ]
      change (flattenFormulaFuel? d (r - φ.nodes) ψ start).bind (fun v =>
        some (FlattenedFormula.and (pureFormula φ start) v.1, v.2)) = _
      rw [hψ d (r - φ.nodes) start hdψ hrψ]
      simp only [Option.bind_some, FlattenedFormula.and, pureFormula, List.nil_append,
        LFml.nodes, Nat.add_sub_add_right, Nat.sub_sub]

private theorem pureFormulaFuel_imp {C : Contract} {φ ψ : LFml C}
    (hφ : PureFormulaFuel φ) (hψ : PureFormulaFuel ψ) : PureFormulaFuel (.imp φ ψ) := by
  intro d r start hd hr
  cases d with
  | zero => simp only [LFml.depth] at hd; omega
  | succ d =>
    cases r with
    | zero => simp only [LFml.nodes] at hr; omega
    | succ r =>
      have hdφ : φ.depth ≤ d := by simp only [LFml.depth] at hd; omega
      have hdψ : ψ.depth ≤ d := by simp only [LFml.depth] at hd; omega
      have hrφ : φ.nodes ≤ r := by simp only [LFml.nodes] at hr; omega
      have hrψ : ψ.nodes ≤ r - φ.nodes := by simp only [LFml.nodes] at hr; omega
      change (flattenFormulaFuel? d r φ start).bind (fun u =>
        (flattenFormulaFuel? d u.2 ψ u.1.next).bind (fun v =>
          some (FlattenedFormula.imp u.1 v.1, v.2))) = _
      rw [hφ d r start hdφ hrφ]
      change (flattenFormulaFuel? d (r - φ.nodes) ψ start).bind (fun v =>
        some (FlattenedFormula.imp (pureFormula φ start) v.1, v.2)) = _
      rw [hψ d (r - φ.nodes) start hdψ hrψ]
      simp only [Option.bind_some, FlattenedFormula.imp, pureFormula, List.nil_append,
        LFml.nodes, Nat.add_sub_add_right, Nat.sub_sub]

/-- Actual formula traversal consumes its structural nodes without a 511-node
assumption. Neither later arithmetic compilation nor global admission is asserted. -/
theorem numeric_formula_flattenFuel {C : Contract} {P : Parameter → Prop} {E : EnvKey → Prop}
    {φ : LFml C} (h : φ.UIntQF P E) (d r start : Nat)
    (hd : φ.depth ≤ d) (hr : φ.nodes ≤ r) :
    ∃ a : FlattenedFormula φ start,
      flattenFormulaFuel? d r φ start = some (a, r - φ.nodes) ∧
      a.formula = φ ∧ a.reads = [] := by
  have hp : PureFormulaFuel φ := by
    clear hd hr
    induction h with
    | tt => exact pureFormulaFuel_tt
    | eq ha hb => exact pureFormulaFuel_eq ha hb
    | not h ih => exact pureFormulaFuel_not ih
    | and hφ hψ ihφ ihψ => exact pureFormulaFuel_and ihφ ihψ
    | imp hφ hψ ihφ ihψ => exact pureFormulaFuel_imp ihφ ihψ
  exact ⟨pureFormula φ start, hp d r start hd hr, rfl, rfl⟩

/-- Structural depth and nodes leave exactly zero shared fuel after traversal. -/
theorem numeric_formula_flatten_zero {C : Contract} {P : Parameter → Prop} {E : EnvKey → Prop}
    {φ : LFml C} (h : φ.UIntQF P E) (start : Nat) :
    ∃ a : FlattenedFormula φ start,
      flattenFormulaFuel? φ.depth φ.nodes φ start = some (a, 0) ∧
      a.formula = φ ∧ a.reads = [] := by
  obtain ⟨a, ha, hf, hr⟩ := numeric_formula_flattenFuel h φ.depth φ.nodes start
    (Nat.le_refl _) (Nat.le_refl _)
  exact ⟨a, by simpa only [Nat.sub_self] using ha, hf, hr⟩

/-- Formula-derived nodes suffice for the public flattener wrapper itself. -/
theorem numeric_formula_flattenAt_nodes {C : Contract} {P : Parameter → Prop} {E : EnvKey → Prop}
    {φ : LFml C} (h : φ.UIntQF P E) (start : Nat) :
    ∃ a : FlattenedFormula φ start, flattenFormulaAt? φ.nodes start φ = some a ∧
      a.formula = φ ∧ a.reads = [] := by
  obtain ⟨a, ha, hf, hr⟩ := numeric_formula_flattenFuel h φ.nodes φ.nodes start
    (LFml.depth_le_nodes φ) (Nat.le_refl _)
  exact ⟨a, by simp only [flattenFormulaAt?, ha, Option.map_some], hf, hr⟩

end Solidity.Decide
