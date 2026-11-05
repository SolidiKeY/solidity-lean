import Solidity.Calculus.DecisionNumericFormula
import Solidity.Calculus.SyntaxSize

/-!
# Source-derived numeric leaf bounds

Reuse the existing intrinsic source node count and unchanged preparation.
These proofs do not change any runtime fuel, node or proof budget.
-/
namespace Solidity.Decide

/-- A binary operation on elimination-fixed operands remains fixed. -/
theorem binop_elim_fixed {C : Contract} {p : PrimTy} (op : BinOp) (h : op.accepts p = true)
    {x y : LTm C (.val p)} (hx : (x.elim : LTm C (.val p)) = x)
    (hy : (y.elim : LTm C (.val p)) = y) :
    ((LTm.app2 (.binop op h) x y).elim : LTm C (.val (op.ret p))) = .app2 (.binop op h) x y := by
  change LTm.app2 (.binop op h) (x.elim : LTm C (.val p)) (y.elim : LTm C (.val p)) = _
  rw [hx, hy]

/-- Literal folding cannot enlarge its original binary node. -/
theorem fold2_nodes_le {C : Contract} {p : PrimTy} (op : BinOp) (h : op.accepts p = true)
    (x y : LTm C (.val p)) :
    (fold2 (.binop op h) x y).nodes ≤ x.nodes + y.nodes + 1 := by
  unfold fold2
  simp only
  split
  · split
    · change 1 ≤ x.nodes + y.nodes + 1
      omega
    · split
      · split
        · simp only [LTm.nodes, Nat.le_refl]
        · split
          · change 1 ≤ x.nodes + y.nodes + 1
            omega
          · change 1 ≤ x.nodes + y.nodes + 1
            omega
      · simp only [LTm.nodes, Nat.le_refl]
  · simp only [LTm.nodes, Nat.le_refl]

/-- Folding elimination-fixed operands does not introduce storage-read structure. -/
theorem fold2_elim_fixed {C : Contract} {p : PrimTy} (op : BinOp) (h : op.accepts p = true)
    {x y : LTm C (.val p)} (hx : (x.elim : LTm C (.val p)) = x)
    (hy : (y.elim : LTm C (.val p)) = y) :
    ((fold2 (.binop op h) x y).elim : LTm C (.val (op.ret p))) = fold2 (.binop op h) x y := by
  unfold fold2
  simp only
  split
  · split
    · rfl
    · split
      · split
        · exact binop_elim_fixed op h hx hy
        · split
          · rfl
          · rfl
      · exact binop_elim_fixed op h hx hy
  · exact binop_elim_fixed op h hx hy

/-- Actual numeric source translation is bounded by the existing intrinsic source size.
The local facts are discharged by the real fresh prefix in the family theorem. -/
theorem uintLinear_toL_sourceBound {C : Contract} {Γ : Ctx}
    {t : Tm C Γ (.val .uint)} (h : t.UIntLinear) (ρ : SymS C Γ)
    {P : Parameter → Prop} {E : EnvKey → Prop}
    (hρ : ∀ i : Idx Γ (.val .uint), ∃ l : LTm C (.val .uint),
      ρ.loc.get i = some l ∧ l.Num P E ∧ (l.elim : LTm C (.val .uint)) = l ∧ l.nodes ≤ 1) :
    ∃ l : LTm C (.val .uint), t.toL ρ = some l ∧ l.Num P E ∧
      (l.elim : LTm C (.val .uint)) = l ∧ l.nodes ≤ t.size := by
  induction h with
  | «local» i => exact hρ i
  | lit v => exact ⟨.app0 (.lit v), rfl, .lit v, rfl, Nat.le_refl 1⟩
  | @add a b ha hb iha ihb =>
    obtain ⟨u, hu, hNu, hEu, hsu⟩ := iha
    obtain ⟨v, hv, hNv, hEv, hsv⟩ := ihb
    refine ⟨fold2 (.binop .add rfl) u v, ?_,
      fold2_preserves_numeric .add rfl (.add rfl hNu hNv),
      fold2_elim_fixed .add rfl hEu hEv, ?_⟩
    · change (a.toL ρ).bind (fun u => (b.toL ρ).bind (fun v => some (fold2 (.binop .add rfl) u v))) = _
      rw [hu, hv]
      rfl
    · have hf : (fold2 (.binop .add rfl) u v).nodes ≤ u.nodes + v.nodes + 1 := fold2_nodes_le .add rfl u v
      change _ ≤ 1 + a.size + b.size
      omega
  | @sub a b ha hb iha ihb =>
    obtain ⟨u, hu, hNu, hEu, hsu⟩ := iha
    obtain ⟨v, hv, hNv, hEv, hsv⟩ := ihb
    refine ⟨fold2 (.binop .sub rfl) u v, ?_,
      fold2_preserves_numeric .sub rfl (.sub rfl hNu hNv),
      fold2_elim_fixed .sub rfl hEu hEv, ?_⟩
    · change (a.toL ρ).bind (fun u => (b.toL ρ).bind (fun v => some (fold2 (.binop .sub rfl) u v))) = _
      rw [hu, hv]
      rfl
    · have hf : (fold2 (.binop .sub rfl) u v).nodes ≤ u.nodes + v.nodes + 1 := fold2_nodes_le .sub rfl u v
      change _ ≤ 1 + a.size + b.size
      omega
  | @mulL v b hb ihb =>
    obtain ⟨u, hu, hNu, hEu, hsu⟩ := ihb
    refine ⟨fold2 (.binop .mul rfl) (.app0 (.lit v)) u, ?_,
      fold2_preserves_numeric .mul rfl (.mulL rfl v hNu),
      fold2_elim_fixed .mul rfl rfl hEu, ?_⟩
    · change (b.toL ρ).bind (fun u => some (fold2 (.binop .mul rfl) (.app0 (.lit v)) u)) = _
      rw [hu]
      rfl
    · have hf : (fold2 (.binop .mul rfl) (.app0 (.lit v)) u).nodes ≤
          (LTm.app0 (.lit v) : LTm C (.val .uint)).nodes + u.nodes + 1 :=
        fold2_nodes_le .mul rfl (.app0 (.lit v)) u
      simp only [LTm.nodes] at hf
      change _ ≤ 1 + 1 + b.size
      omega
  | @mulR a v ha iha =>
    obtain ⟨u, hu, hNu, hEu, hsu⟩ := iha
    refine ⟨fold2 (.binop .mul rfl) u (.app0 (.lit v)), ?_,
      fold2_preserves_numeric .mul rfl (.mulR rfl v hNu),
      fold2_elim_fixed .mul rfl hEu rfl, ?_⟩
    · change (a.toL ρ).bind (fun u => some (fold2 (.binop .mul rfl) u (.app0 (.lit v)))) = _
      rw [hu]
      rfl
    · have hf : (fold2 (.binop .mul rfl) u (.app0 (.lit v))).nodes ≤
          u.nodes + (LTm.app0 (.lit v) : LTm C (.val .uint)).nodes + 1 :=
        fold2_nodes_le .mul rfl u (.app0 (.lit v))
      simp only [LTm.nodes] at hf
      change _ ≤ 1 + a.size + 1
      omega

/-- A real fresh uint prefix discharges every local shape/size premise. -/
theorem uintLinear_prefix_sourceBound {C : Contract}
    {t : Tm C [.val .uint] (.val .uint)} (h : t.UIntLinear) :
    ∃ l : LTm C (.val .uint), t.toLT ((SymS.init (C := C)).pushQ .uint) = some l ∧
      l.Num (fun q => q = ⟨.uint, 0⟩) (fun _ => False) ∧
      (l.elim : LTm C (.val .uint)) = l ∧ l.condSimp = l ∧ l.nodes ≤ t.size := by
  rw [toLT_eq_toL_of_agree t _ (uintLinear_agrees h)]
  have hρ : ∀ i : Idx [.val .uint] (.val .uint), ∃ l : LTm C (.val .uint),
      ((SymS.init (C := C)).pushQ .uint).loc.get i = some l ∧
      l.Num (fun q => q = ⟨.uint, 0⟩) (fun _ => False) ∧
      (l.elim : LTm C (.val .uint)) = l ∧ l.nodes ≤ 1 := by
    intro i
    cases i with
    | here => exact ⟨.var 0, rfl, .var 0 rfl, rfl, Nat.le_refl 1⟩
    | there i => cases i
  obtain ⟨l, hl, hn, he, hs⟩ := uintLinear_toL_sourceBound h _ hρ
  exact ⟨l, hl, hn, he, LTm.condSimp_of_conds l (numeric_no_conds hn), hs⟩

/-- Optional equality repeats each operand seven times and adds thirteen nodes. -/
theorem optEq_nodes {C : Contract} {p : PrimTy} (x y : LTm C (.val p)) :
    (LFml.optEq x y).nodes = 7 * x.nodes + 7 * y.nodes + 13 := by
  simp only [LFml.optEq, LFml.nodes]
  omega

/-- Exact operand identities give a structural bound on the actual prepared equality. -/
theorem uintEq_prepared_nodes_le {C : Contract} {Γ : Ctx}
    {a b : Tm C Γ (.val .uint)} (ha : a.UIntLinear) (hb : b.UIntLinear)
    {x y : LTm C (.val .uint)}
    (hEx : (x.elim : LTm C (.val .uint)) = x) (hEy : (y.elim : LTm C (.val .uint)) = y)
    (hCx : x.condSimp = x) (hCy : y.condSimp = y) :
    (Fml.eqAt true a b x y).elim.condSimp.prenex.nodes ≤ 7 * x.nodes + 7 * y.nodes + 13 := by
  unfold Fml.eqAt
  rw [uintLinear_agrees ha, uintLinear_agrees hb]
  simp only [Bool.true_and, if_true]
  split <;> simp only [LFml.elim, LFml.condSimp, LFml.prenex, LFml.optEq,
    hEx, hEy, hCx, hCy, LFml.nodes] <;> omega

/-- The actual prepared body is bounded by raw source syntax, including all optional-equality copies. -/
theorem uintPrefix_prepared_sourceBound {C : Contract} (name : Var)
    {a b : Tm C [.val .uint] (.val .uint)} (ha : a.UIntLinear) (hb : b.UIntLinear) :
    ∃ ψ : LFml C, leafOf? (primitivePrefixEq name a b) = some (.all 0 .uint ψ) ∧
      (∀ c : Bool, ψ.Src c true) ∧ (∀ q ∈ ψ.parameters, q = ⟨.uint, 0⟩) ∧
      ψ.condMax = 2 ∧ ψ.nodes ≤ 7 * (a.size + b.size) + 13 := by
  obtain ⟨x, hx, hNx, hEx, hCx, hSx⟩ := uintLinear_prefix_sourceBound ha
  obtain ⟨y, hy, hNy, hEy, hCy, hSy⟩ := uintLinear_prefix_sourceBound hb
  rw [toLT_eq_toL_of_agree a _ (uintLinear_agrees ha)] at hx
  rw [toLT_eq_toL_of_agree b _ (uintLinear_agrees hb)] at hy
  let θ : LFml C := Fml.eqAt true a b x y
  have hp : (Fml.eq a b).toLS true ((SymS.init (C := C)).pushQ .uint) = some θ := by
    change (a.toL ((SymS.init (C := C)).pushQ .uint)).bind
      (fun u => (b.toL ((SymS.init (C := C)).pushQ .uint)).map
        (fun v => Fml.eqAt true a b u v)) = some θ
    rw [hx, hy]
    rfl
  have hn : (Fml.eq a b).toLS false ((SymS.init (C := C)).pushQ .uint) = some θ := by
    change (a.toL ((SymS.init (C := C)).pushQ .uint)).bind
      (fun u => (b.toL ((SymS.init (C := C)).pushQ .uint)).map
        (fun v => Fml.eqAt false a b u v)) = some θ
    rw [hx, hy]
    exact congrArg some (uintLinear_eqAt_polarity ha hb x y false)
  have hs : (sourceReduction? (primitivePrefixEq name a b)).map (·.leaf) =
      some (.all 0 .uint θ) := uintPrefix_source_from_polarities name θ hp hn
  refine ⟨θ.elim.condSimp.prenex, ?_, ?_, ?_, ?_, ?_⟩
  · exact leafOf_of_normalized_source (primitivePrefixEq name a b) (.all 0 .uint θ)
      (primitivePrefixEq_normalizes name a b) hs
  · intro c
    exact uintEq_prepared_source ha hb hNx hNy c true
  · exact uintEq_prepared_parameters ha hb hNx hNy
  · exact uintEq_prepared_condMax ha hb hNx hNy
  · have hn : θ.elim.condSimp.prenex.nodes ≤ 7 * x.nodes + 7 * y.nodes + 13 :=
      uintEq_prepared_nodes_le ha hb hEx hEy hCx hCy
    omega

/-- A sufficient raw-source size criterion for the existing body-node cap.
This is not necessary, a new runtime limit, a cut bound or a Covered theorem. -/
theorem uintPrefix_sourceBound_sufficient {C : Contract} (name : Var)
    {a b : Tm C [.val .uint] (.val .uint)} (ha : a.UIntLinear) (hb : b.UIntLinear)
    (hs : a.size + b.size ≤ 71) :
    ∃ ψ : LFml C, leafOf? (primitivePrefixEq name a b) = some (.all 0 .uint ψ) ∧ ψ.nodes ≤ 511 := by
  obtain ⟨ψ, hl, hsrc, hp, hc, hn⟩ := uintPrefix_prepared_sourceBound name ha hb
  exact ⟨ψ, hl, by omega⟩

end Solidity.Decide
