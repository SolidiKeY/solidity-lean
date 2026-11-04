import Solidity.Calculus.DecisionNumericFlatten

/-! # Necessary shared fuel for numeric flattening
Converse resource proofs for the existing intrinsic flattener. The algorithms,
source predicates and public limits are unchanged. Formula nodes characterize
this numeric traversal stage, not the complete decision pipeline.
-/
namespace Solidity.Decide

private def TermConsumes {C : Contract} {s : Srt} (t : LTm C s) : Prop :=
  ∀ (d r start : Nat) (a : Flattened t start) (rest : Nat),
    flattenFuel? d r t start = some (a, rest) → rest + t.nodes = r

private theorem consumes_var {C : Contract} {p : PrimTy} (k : Nat) :
    TermConsumes (LTm.var (C := C) (p := p) k) := by
  intro d r start a rest he
  cases d with
  | zero => cases he
  | succ d =>
    cases r with
    | zero => cases he
    | succ r =>
      have hr : r = rest := congrArg Prod.snd (Option.some.inj he)
      simp only [LTm.nodes]
      omega

private theorem consumes_lit {C : Contract} {p : PrimTy} (v : p.Denote) :
    TermConsumes (LTm.app0 (C := C) (.lit v)) := by
  intro d r start a rest he
  cases d with
  | zero => cases he
  | succ d =>
    cases r with
    | zero => cases he
    | succ r =>
      rw [flattenFuel?_lit] at he
      have hr : r = rest := congrArg Prod.snd (Option.some.inj he)
      simpa only [LTm.nodes] using congrArg Nat.succ hr.symm

private theorem consumes_env {C : Contract} (e : EnvKey) :
    TermConsumes (LTm.app0 (C := C) (.env e)) := by
  intro d r start a rest he
  cases d with
  | zero => cases he
  | succ d =>
    cases r with
    | zero => cases he
    | succ r =>
      have hr : r = rest := congrArg Prod.snd (Option.some.inj he)
      simp only [LTm.nodes]
      omega

private theorem consumes_err {C : Contract} {p : PrimTy} :
    TermConsumes (LTm.err (C := C) (s := .val p)) := by
  intro d r start a rest he
  cases d with
  | zero => cases he
  | succ d =>
    cases r with
    | zero => cases he
    | succ r =>
      have hr : r = rest := congrArg Prod.snd (Option.some.inj he)
      simp only [LTm.nodes]
      omega

private theorem consumes_unop {C : Contract} {p : PrimTy} (op : UnOp)
    (hop : op.accepts p = true) {a : LTm C (.val p)} (ha : TermConsumes a) :
    TermConsumes (LTm.app1 (.unop op hop) a) := by
  intro d r start result rest he
  cases d with
  | zero => cases he
  | succ d =>
    cases r with
    | zero => cases he
    | succ r =>
      change (flattenFuel? d r a start).bind
        (fun u => some (Flattened.app1 (.unop op hop) u.1, u.2)) = some (result, rest) at he
      cases hx : flattenFuel? d r a start with
      | none => rw [hx] at he; cases he
      | some u =>
        rcases u with ⟨fa, ra⟩
        rw [hx] at he
        have hrest : ra = rest := congrArg Prod.snd (Option.some.inj he)
        have hc : ra + a.nodes = r := ha d r start fa ra hx
        simp only [LTm.nodes]
        omega

private theorem consumes_binop {C : Contract} {p : PrimTy} (op : BinOp)
    (hop : op.accepts p = true) {a b : LTm C (.val p)}
    (ha : TermConsumes a) (hb : TermConsumes b) :
    TermConsumes (LTm.app2 (.binop op hop) a b) := by
  intro d r start result rest he
  cases d with
  | zero => cases he
  | succ d =>
    cases r with
    | zero => cases he
    | succ r =>
      change (flattenFuel? d r a start).bind (fun u =>
        (flattenFuel? d u.2 b u.1.next).bind (fun v =>
          some (Flattened.app2 (.binop op hop) u.1 v.1, v.2))) = some (result, rest) at he
      cases hx : flattenFuel? d r a start with
      | none => rw [hx] at he; cases he
      | some u =>
        rcases u with ⟨fa, ra⟩
        rw [hx] at he
        change (flattenFuel? d ra b fa.next).bind
          (fun v => some (Flattened.app2 (.binop op hop) fa v.1, v.2)) = some (result, rest) at he
        cases hy : flattenFuel? d ra b fa.next with
        | none => rw [hy] at he; cases he
        | some v =>
          rcases v with ⟨fb, rb⟩
          rw [hy] at he
          have hrest : rb = rest := congrArg Prod.snd (Option.some.inj he)
          have hca : ra + a.nodes = r := ha d r start fa ra hx
          have hcb : rb + b.nodes = ra := hb d ra fa.next fb rb hy
          simp only [LTm.nodes]
          omega

private theorem consumes_seq {C : Contract} {p q : PrimTy}
    {a : LTm C (.val p)} {b : LTm C (.val q)}
    (ha : TermConsumes a) (hb : TermConsumes b) : TermConsumes (LTm.seq a b) := by
  intro d r start result rest he
  cases d with
  | zero => cases he
  | succ d =>
    cases r with
    | zero => cases he
    | succ r =>
      change (flattenFuel? d r a start).bind (fun u =>
        (flattenFuel? d u.2 b u.1.next).bind (fun v =>
          some (Flattened.seq u.1 v.1, v.2))) = some (result, rest) at he
      cases hx : flattenFuel? d r a start with
      | none => rw [hx] at he; cases he
      | some u =>
        rcases u with ⟨fa, ra⟩
        rw [hx] at he
        change (flattenFuel? d ra b fa.next).bind
          (fun v => some (Flattened.seq fa v.1, v.2)) = some (result, rest) at he
        cases hy : flattenFuel? d ra b fa.next with
        | none => rw [hy] at he; cases he
        | some v =>
          rcases v with ⟨fb, rb⟩
          rw [hy] at he
          have hrest : rb = rest := congrArg Prod.snd (Option.some.inj he)
          have hca : ra + a.nodes = r := ha d r start fa ra hx
          have hcb : rb + b.nodes = ra := hb d ra fa.next fb rb hy
          simp only [LTm.nodes]
          omega

/-- Success itself forces exact consumption, without an adequate-fuel premise. -/
theorem numeric_flattenFuel_consumption {C : Contract}
    {P : Parameter → Prop} {E : EnvKey → Prop} {p : PrimTy} {t : LTm C (.val p)}
    (h : t.Num P E) (d r start : Nat) (a : Flattened t start) (rest : Nat)
    (he : flattenFuel? d r t start = some (a, rest)) : rest + t.nodes = r := by
  suffices hc : TermConsumes t from hc d r start a rest he
  clear d r start a rest he
  induction h <;> solve_by_elim [consumes_var, consumes_lit, consumes_env, consumes_err,
    consumes_unop, consumes_binop, consumes_seq]

private def FormulaConsumes {C : Contract} (φ : LFml C) : Prop :=
  ∀ (d r start : Nat) (a : FlattenedFormula φ start) (rest : Nat),
    flattenFormulaFuel? d r φ start = some (a, rest) → rest + φ.nodes = r

private theorem consumes_formula_tt {C : Contract} : FormulaConsumes (LFml.tt (C := C)) := by
  intro d r start result rest he
  cases d with
  | zero => cases he
  | succ d =>
    cases r with
    | zero => cases he
    | succ r =>
      have hr : r = rest := congrArg Prod.snd (Option.some.inj he)
      simp only [LFml.nodes]
      omega

private theorem consumes_formula_eq {C : Contract} {p : PrimTy}
    {a b : LTm C (.val p)} (ha : TermConsumes a) (hb : TermConsumes b) :
    FormulaConsumes (.eq a b) := by
  intro d r start result rest he
  cases d with
  | zero => cases he
  | succ d =>
    cases r with
    | zero => cases he
    | succ r =>
      change (flattenFuel? d r a start).bind (fun u =>
        (flattenFuel? d u.2 b u.1.next).bind (fun v =>
          some (FlattenedFormula.eq u.1 v.1, v.2))) = some (result, rest) at he
      cases hx : flattenFuel? d r a start with
      | none => rw [hx] at he; cases he
      | some u =>
        rcases u with ⟨fa, ra⟩
        rw [hx] at he
        change (flattenFuel? d ra b fa.next).bind
          (fun v => some (FlattenedFormula.eq fa v.1, v.2)) = some (result, rest) at he
        cases hy : flattenFuel? d ra b fa.next with
        | none => rw [hy] at he; cases he
        | some v =>
          rcases v with ⟨fb, rb⟩
          rw [hy] at he
          have hrest : rb = rest := congrArg Prod.snd (Option.some.inj he)
          have hca : ra + a.nodes = r := ha d r start fa ra hx
          have hcb : rb + b.nodes = ra := hb d ra fa.next fb rb hy
          simp only [LFml.nodes]
          omega

private theorem consumes_formula_not {C : Contract} {φ : LFml C}
    (hφ : FormulaConsumes φ) : FormulaConsumes (.not φ) := by
  intro d r start result rest he
  cases d with
  | zero => cases he
  | succ d =>
    cases r with
    | zero => cases he
    | succ r =>
      change (flattenFormulaFuel? d r φ start).bind
        (fun u => some (FlattenedFormula.not u.1, u.2)) = some (result, rest) at he
      cases hx : flattenFormulaFuel? d r φ start with
      | none => rw [hx] at he; cases he
      | some u =>
        rcases u with ⟨fa, ra⟩
        rw [hx] at he
        have hrest : ra = rest := congrArg Prod.snd (Option.some.inj he)
        have hc : ra + φ.nodes = r := hφ d r start fa ra hx
        simp only [LFml.nodes]
        omega

private theorem consumes_formula_and {C : Contract} {φ ψ : LFml C}
    (hφ : FormulaConsumes φ) (hψ : FormulaConsumes ψ) : FormulaConsumes (.and φ ψ) := by
  intro d r start result rest he
  cases d with
  | zero => cases he
  | succ d =>
    cases r with
    | zero => cases he
    | succ r =>
      change (flattenFormulaFuel? d r φ start).bind (fun u =>
        (flattenFormulaFuel? d u.2 ψ u.1.next).bind (fun v =>
          some (FlattenedFormula.and u.1 v.1, v.2))) = some (result, rest) at he
      cases hx : flattenFormulaFuel? d r φ start with
      | none => rw [hx] at he; cases he
      | some u =>
        rcases u with ⟨fa, ra⟩
        rw [hx] at he
        change (flattenFormulaFuel? d ra ψ fa.next).bind
          (fun v => some (FlattenedFormula.and fa v.1, v.2)) = some (result, rest) at he
        cases hy : flattenFormulaFuel? d ra ψ fa.next with
        | none => rw [hy] at he; cases he
        | some v =>
          rcases v with ⟨fb, rb⟩
          rw [hy] at he
          have hrest : rb = rest := congrArg Prod.snd (Option.some.inj he)
          have hca : ra + φ.nodes = r := hφ d r start fa ra hx
          have hcb : rb + ψ.nodes = ra := hψ d ra fa.next fb rb hy
          simp only [LFml.nodes]
          omega

private theorem consumes_formula_imp {C : Contract} {φ ψ : LFml C}
    (hφ : FormulaConsumes φ) (hψ : FormulaConsumes ψ) : FormulaConsumes (.imp φ ψ) := by
  intro d r start result rest he
  cases d with
  | zero => cases he
  | succ d =>
    cases r with
    | zero => cases he
    | succ r =>
      change (flattenFormulaFuel? d r φ start).bind (fun u =>
        (flattenFormulaFuel? d u.2 ψ u.1.next).bind (fun v =>
          some (FlattenedFormula.imp u.1 v.1, v.2))) = some (result, rest) at he
      cases hx : flattenFormulaFuel? d r φ start with
      | none => rw [hx] at he; cases he
      | some u =>
        rcases u with ⟨fa, ra⟩
        rw [hx] at he
        change (flattenFormulaFuel? d ra ψ fa.next).bind
          (fun v => some (FlattenedFormula.imp fa v.1, v.2)) = some (result, rest) at he
        cases hy : flattenFormulaFuel? d ra ψ fa.next with
        | none => rw [hy] at he; cases he
        | some v =>
          rcases v with ⟨fb, rb⟩
          rw [hy] at he
          have hrest : rb = rest := congrArg Prod.snd (Option.some.inj he)
          have hca : ra + φ.nodes = r := hφ d r start fa ra hx
          have hcb : rb + ψ.nodes = ra := hψ d ra fa.next fb rb hy
          simp only [LFml.nodes]
          omega

/-- A successful numeric formula traversal consumes exactly its structural nodes. -/
theorem numeric_formula_flattenFuel_consumption {C : Contract}
    {P : Parameter → Prop} {E : EnvKey → Prop} {φ : LFml C} (h : φ.UIntQF P E)
    (d r start : Nat) (a : FlattenedFormula φ start) (rest : Nat)
    (he : flattenFormulaFuel? d r φ start = some (a, rest)) : rest + φ.nodes = r := by
  suffices hc : FormulaConsumes φ from hc d r start a rest he
  clear d r start a rest he
  induction h <;> solve_by_elim [consumes_formula_tt, consumes_formula_eq,
    consumes_formula_not, consumes_formula_and, consumes_formula_imp, numeric_flattenFuel_consumption]

/-- The real public numeric flattener succeeds exactly when its formula nodes fit.
Depth is discharged from those same nodes, not an extra fixed fuel premise. -/
theorem numeric_formula_flattenAt_iff_nodes {C : Contract}
    {P : Parameter → Prop} {E : EnvKey → Prop} {φ : LFml C} (h : φ.UIntQF P E)
    (budget start : Nat) :
    (flattenFormulaAt? budget start φ).isSome = true ↔ φ.nodes ≤ budget := by
  constructor
  · intro hs
    change ((flattenFormulaFuel? budget budget φ start).map Prod.fst).isSome = true at hs
    cases he : flattenFormulaFuel? budget budget φ start with
    | none => rw [he] at hs; cases hs
    | some pair =>
      rcases pair with ⟨a, rest⟩
      have hc : rest + φ.nodes = budget :=
        numeric_formula_flattenFuel_consumption h budget budget start a rest he
      omega
  · intro hn
    obtain ⟨a, ha, _, _⟩ := numeric_formula_flattenFuel h budget budget start
      (Nat.le_trans (LFml.depth_le_nodes φ) hn) hn
    simp only [flattenFormulaAt?, ha, Option.map_some, Option.isSome_some]

/-- Strictly insufficient formula-derived node fuel forces actual refusal. -/
theorem numeric_formula_flattenAt_below_nodes {C : Contract}
    {P : Parameter → Prop} {E : EnvKey → Prop} {φ : LFml C} (h : φ.UIntQF P E)
    (budget start : Nat) (hb : budget < φ.nodes) : flattenFormulaAt? budget start φ = none := by
  cases he : flattenFormulaAt? budget start φ with
  | none => rfl
  | some a =>
    have hs : (flattenFormulaAt? budget start φ).isSome = true := by
      rw [he]
      rfl
    have hn : φ.nodes ≤ budget := (numeric_formula_flattenAt_iff_nodes h budget start).mp hs
    omega

#print axioms numeric_flattenFuel_consumption
#print axioms numeric_formula_flattenFuel_consumption
#print axioms numeric_formula_flattenAt_iff_nodes
#print axioms numeric_formula_flattenAt_below_nodes

end Solidity.Decide
