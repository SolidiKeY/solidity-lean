import Solidity.Calculus.DecisionUIntPrefix

/-!
# Numeric grammar through the existing leaf preparation

Closure lemmas for the existing intrinsic Num grammar, independent of coverage
or a verdict. No preparation function or budget is changed.
-/
namespace Solidity.Decide

theorem seqL_numeric {C : Contract} {P : Parameter → Prop} {E : EnvKey → Prop}
    {p q : PrimTy} {d : LTm C (.val q)} {a : LTm C (.val p)}
    (hd : d.Num P E) (ha : a.Num P E) : (seqL d a).Num P E := by
  unfold seqL
  split
  · exact ha
  · exact .seq hd ha

/-- Actual storage-read elimination preserves the read-free numeric grammar. -/
theorem numeric_elim {C : Contract} {P : Parameter → Prop} {E : EnvKey → Prop}
    {p : PrimTy} {t : LTm C (.val p)} (h : t.Num P E) :
    (t.elim : LTm C (.val p)).Num P E := by
  induction h with
  | var k hk => exact .var k hk
  | lit v => exact .lit v
  | env e he => exact .env e he
  | add h ha hb iha ihb => exact .add h iha ihb
  | sub h ha hb iha ihb => exact .sub h iha ihb
  | mulL h v hb ihb => exact .mulL h v ihb
  | mulR h v ha iha => exact .mulR h v iha
  | neg h ha iha => exact .neg h iha
  | bnot h ha iha => exact .bnot h iha
  | seq hd ha ihd iha => exact seqL_numeric (seqL_numeric ihd (.lit (p := .bool) true)) iha
  | err => exact .err

/-- Trivial-conditional simplification preserves the same numeric grammar. -/
theorem numeric_condSimp {C : Contract} {P : Parameter → Prop} {E : EnvKey → Prop}
    {p : PrimTy} {t : LTm C (.val p)} (h : t.Num P E) : t.condSimp.Num P E := by
  induction h with
  | var k hk => exact .var k hk
  | lit v => exact .lit v
  | env e he => exact .env e he
  | add h ha hb iha ihb => exact .add h iha ihb
  | sub h ha hb iha ihb => exact .sub h iha ihb
  | mulL h v hb ihb => exact .mulL h v ihb
  | mulR h v ha iha => exact .mulR h v iha
  | neg h ha iha => exact .neg h iha
  | bnot h ha iha => exact .bnot h iha
  | seq hd ha ihd iha => exact .seq ihd iha
  | err => exact .err

/-- Numeric evidence supplies the existing source grammar at either conditional/cut setting. -/
theorem numeric_source {C : Contract} {P : Parameter → Prop} {E : EnvKey → Prop}
    {p : PrimTy} {t : LTm C (.val p)} (h : t.Num P E) (c w : Bool) :
    t.Src c w .num := by
  induction h with
  | var k hk => exact .var k
  | lit v => exact .lit v
  | env e he => exact .env e
  | add h ha hb iha ihb => exact .add h iha ihb
  | sub h ha hb iha ihb => exact .sub h iha ihb
  | mulL h v hb ihb => exact .mulL h v ihb
  | mulR h v ha iha => exact .mulR h v iha
  | neg h ha iha => exact .neg h iha
  | bnot h ha iha => exact .bnot h iha
  | seq hd ha ihd iha => exact .seq ihd iha
  | err => exact .err

/-- Numeric terms contain no conditional to split; sequencing may still halt. -/
theorem numeric_no_conds {C : Contract} {P : Parameter → Prop} {E : EnvKey → Prop}
    {p : PrimTy} {t : LTm C (.val p)} (h : t.Num P E) : t.conds = 0 := by
  induction h <;> simp_all only [LTm.conds, Nat.add_zero]

/-- Actual elimination and simplification preserve the original parameter/environment predicates. -/
theorem numeric_prepared {C : Contract} {P : Parameter → Prop} {E : EnvKey → Prop}
    {p : PrimTy} {t : LTm C (.val p)} (h : t.Num P E) :
    (t.elim : LTm C (.val p)).condSimp.Num P E :=
  numeric_condSimp (numeric_elim h)

/-- Literal folding preserves the existing numeric grammar, including failure. -/
theorem fold2_preserves_numeric {C : Contract} {p : PrimTy} {P : Parameter → Prop} {E : EnvKey → Prop}
    (op : BinOp) (h : op.accepts p = true) {x y : LTm C (.val p)}
    (hxy : (LTm.app2 (.binop op h) x y).Num P E) :
    (fold2 (.binop op h) x y).Num P E := by
  unfold fold2
  simp only
  split
  · split
    · exact .lit _
    · split
      · split
        · exact hxy
        · split
          · exact .lit _
          · exact .err
      · exact hxy
  · exact hxy

/-- Construct actual numeric outputs from intrinsic uint syntax and numeric local bindings. -/
theorem uintLinear_toL_numeric {C : Contract} {Γ : Ctx} {t : Tm C Γ (.val .uint)}
    (h : t.UIntLinear) (ρ : SymS C Γ) {P : Parameter → Prop} {E : EnvKey → Prop}
    (hρ : ∀ i : Idx Γ (.val .uint), ∃ l : LTm C (.val .uint),
      ρ.loc.get i = some l ∧ l.Num P E) :
    ∃ l : LTm C (.val .uint), t.toL ρ = some l ∧ l.Num P E := by
  induction h with
  | «local» i => exact hρ i
  | lit v => exact ⟨.app0 (.lit v), rfl, .lit v⟩
  | @add a b ha hb iha ihb =>
    obtain ⟨u, hu, hsu⟩ := iha
    obtain ⟨v, hv, hsv⟩ := ihb
    refine ⟨fold2 (.binop .add rfl) u v, ?_, fold2_preserves_numeric .add rfl (.add rfl hsu hsv)⟩
    change (a.toL ρ).bind (fun u => (b.toL ρ).bind (fun v => some (fold2 (.binop .add rfl) u v))) = _
    rw [hu, hv]
    rfl
  | @sub a b ha hb iha ihb =>
    obtain ⟨u, hu, hsu⟩ := iha
    obtain ⟨v, hv, hsv⟩ := ihb
    refine ⟨fold2 (.binop .sub rfl) u v, ?_, fold2_preserves_numeric .sub rfl (.sub rfl hsu hsv)⟩
    change (a.toL ρ).bind (fun u => (b.toL ρ).bind (fun v => some (fold2 (.binop .sub rfl) u v))) = _
    rw [hu, hv]
    rfl
  | @mulL v b hb ihb =>
    obtain ⟨u, hu, hsu⟩ := ihb
    refine ⟨fold2 (.binop .mul rfl) (.app0 (.lit v)) u, ?_,
      fold2_preserves_numeric .mul rfl (.mulL rfl v hsu)⟩
    change (b.toL ρ).bind (fun u => some (fold2 (.binop .mul rfl) (.app0 (.lit v)) u)) = _
    rw [hu]
    rfl
  | @mulR a v ha iha =>
    obtain ⟨u, hu, hsu⟩ := iha
    refine ⟨fold2 (.binop .mul rfl) u (.app0 (.lit v)), ?_,
      fold2_preserves_numeric .mul rfl (.mulR rfl v hsu)⟩
    change (a.toL ρ).bind (fun u => some (fold2 (.binop .mul rfl) u (.app0 (.lit v)))) = _
    rw [hu]
    rfl

/-- A real initial uint prefix permits only its bound atom, with no environment input. -/
theorem uintLinear_prefix_numeric {C : Contract}
    {t : Tm C [.val .uint] (.val .uint)} (h : t.UIntLinear) :
    ∃ l : LTm C (.val .uint), t.toLT ((SymS.init (C := C)).pushQ .uint) = some l ∧
      l.Num (fun q => q = ⟨.uint, 0⟩) (fun _ => False) := by
  rw [toLT_eq_toL_of_agree t _ (uintLinear_agrees h)]
  apply uintLinear_toL_numeric h
  intro i
  cases i with
  | here => exact ⟨.var 0, rfl, .var 0 rfl⟩
  | there i => cases i

/-- Actual prefix outputs remain numeric after the existing preparation stages. -/
theorem uintLinear_prefix_prepared_numeric {C : Contract}
    {t : Tm C [.val .uint] (.val .uint)} (h : t.UIntLinear) :
    ∃ l : LTm C (.val .uint), t.toLT ((SymS.init (C := C)).pushQ .uint) = some l ∧
      (l.elim : LTm C (.val .uint)).condSimp.Num
        (fun q => q = ⟨.uint, 0⟩) (fun _ => False) := by
  obtain ⟨l, hl, hn⟩ := uintLinear_prefix_numeric h
  exact ⟨l, hl, numeric_prepared hn⟩

end Solidity.Decide
