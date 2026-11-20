import Solidity.Goals.ElabTotal
import Solidity.Syntax.Elab.Measure

/-! Structural expression closure for the elaborator totality proof. -/
namespace Solidity.ElabHoist
open Semantics
variable [FreshNames]
private theorem field_congr (C : Contract) (rc rc' : ElabRec C)
    (H K : RawExpr → ElabM (SProg C × RawExpr))
    (e a : RawExpr) (f : String) (hf : e.foldConst = .ok (.field a f))
    (ha : H a = K a) :
    hoistWith C {rc with hoist := H} e = hoistWith C {rc' with hoist := K} e := by
  have hfold : (liftM e.foldConst : ElabM RawExpr) = pure (.field a f) := by rw [hf]; rfl
  unfold hoistWith
  extract_lets
  rw [hfold]
  simp -zeta only [pure_bind]
  dsimp +zetaDelta only
  rw [ha]
private theorem index_congr (C : Contract) (rc rc' : ElabRec C)
    (H K : RawExpr → ElabM (SProg C × RawExpr))
    (e a b : RawExpr) (hf : e.foldConst = .ok (.index a b))
    (ha : H a = K a) (hb : H b = K b) :
    hoistWith C {rc with hoist := H} e = hoistWith C {rc' with hoist := K} e := by
  have hfold : (liftM e.foldConst : ElabM RawExpr) = pure (.index a b) := by rw [hf]; rfl
  unfold hoistWith
  extract_lets
  rw [hfold]
  simp -zeta only [pure_bind]
  dsimp +zetaDelta only
  rw [ha, hb]
private theorem unop_congr (C : Contract) (rc rc' : ElabRec C)
    (H K : RawExpr → ElabM (SProg C × RawExpr))
    (e a : RawExpr) (op : UnOp) (hf : e.foldConst = .ok (.unop op a))
    (ha : H a = K a) :
    hoistWith C {rc with hoist := H} e = hoistWith C {rc' with hoist := K} e := by
  have hfold : (liftM e.foldConst : ElabM RawExpr) = pure (.unop op a) := by rw [hf]; rfl
  unfold hoistWith
  extract_lets
  rw [hfold]
  simp -zeta only [pure_bind]
  dsimp +zetaDelta only
  rw [ha]
private theorem incDec_congr (C : Contract) (rc rc' : ElabRec C)
    (H K : RawExpr → ElabM (SProg C × RawExpr))
    (e a : RawExpr) (op : IncDec) (hf : e.foldConst = .ok (.incDec op a))
    (ha : H a = K a) :
    hoistWith C {rc with hoist := H} e = hoistWith C {rc' with hoist := K} e := by
  have hfold : (liftM e.foldConst : ElabM RawExpr) = pure (.incDec op a) := by rw [hf]; rfl
  unfold hoistWith
  extract_lets
  rw [hfold]
  simp -zeta only [pure_bind]
  dsimp +zetaDelta only
  rw [ha]
private theorem newArr_congr (C : Contract) (rc rc' : ElabRec C)
    (H K : RawExpr → ElabM (SProg C × RawExpr))
    (e a : RawExpr) (op : RawTy) (hf : e.foldConst = .ok (.newArr op a))
    (ha : H a = K a) :
    hoistWith C {rc with hoist := H} e = hoistWith C {rc' with hoist := K} e := by
  have hfold : (liftM e.foldConst : ElabM RawExpr) = pure (.newArr op a) := by rw [hf]; rfl
  unfold hoistWith
  extract_lets
  rw [hfold]
  simp -zeta only [pure_bind]
  dsimp +zetaDelta only
  rw [ha]

omit [FreshNames] in
theorem foldConst_same_or_lit (e out : RawExpr) (h : e.foldConst = .ok out) :
    out = e ∨ out.isLit = true := by
  unfold RawExpr.foldConst at h
  split at h
  · cases h; exact Or.inl rfl
  · split at h
    · cases h
    · dsimp only at h
      split at h
      · cases h; exact Or.inr rfl
      · cases h; exact Or.inr rfl


omit [FreshNames] in
theorem RawExpr.nodes_pos (e : RawExpr) : 0 < e.nodes := by
  cases e <;> simp only [RawExpr.nodes] <;> omega

omit [FreshNames] in
private theorem lit_nodes_le (e : RawExpr) (h : e.isLit = true) : e.nodes ≤ 2 := by
  cases e <;> simp only [RawExpr.isLit, Bool.false_eq_true] at h
  · simp [RawExpr.nodes]
  · rename_i op a
    cases op <;> cases a <;> simp_all [RawExpr.nodes]

omit [FreshNames] in
/-- Folding does not increase the existing node count, which ignores literal values. -/
theorem foldConst_nodes_le (e out : RawExpr) (h : e.foldConst = .ok out) :
    out.nodes ≤ e.nodes := by
  have hbound : out.nodes ≤ e.nodes ∨ out.nodes ≤ 2 := by
    rcases foldConst_same_or_lit e out h with he | hl
    · exact Or.inl (he ▸ Nat.le_refl _)
    · exact Or.inr (lit_nodes_le out hl)
  cases e with
  | unop op a =>
    have := RawExpr.nodes_pos a
    simp only [RawExpr.nodes] at *
    omega
  | binop op a b =>
    have := RawExpr.nodes_pos a
    simp only [RawExpr.nodes] at *
    omega
  | num n =>
    simp [RawExpr.foldConst, RawExpr.constRat?] at h
    cases h
    exact Nat.le_refl _
  | _ =>
    simp [RawExpr.foldConst, RawExpr.constRat?] at h
    cases h
    exact Nat.le_refl _


private theorem assign_congr (C : Contract) (rc rc' : ElabRec C)
    (H K : RawExpr → ElabM (SProg C × RawExpr)) (stmts : List RawStmt → ElabM (SProg C))
    (e l r : RawExpr) (hf : e.foldConst = .ok (.assign l r))
    (hr : H r = K r) :
    hoistWith C {rc with hoist := H, elabStmtsP := stmts} e =
      hoistWith C {rc' with hoist := K, elabStmtsP := stmts} e := by
  have hfold : (liftM e.foldConst : ElabM RawExpr) = pure (.assign l r) := by rw [hf]; rfl
  unfold hoistWith
  extract_lets
  rw [hfold]
  simp -zeta only [pure_bind]
  dsimp +zetaDelta only
  rw [hr]

private theorem ternary_congr (C : Contract) (rc rc' : ElabRec C)
    (H K : RawExpr → ElabM (SProg C × RawExpr)) (stmts : List RawStmt → ElabM (SProg C))
    (e c a b : RawExpr) (hf : e.foldConst = .ok (.ternary c a b))
    (hc : H c = K c) (ha : H a = K a) (hb : H b = K b) :
    hoistWith C {rc with hoist := H, elabStmtsP := stmts} e =
      hoistWith C {rc' with hoist := K, elabStmtsP := stmts} e := by
  have hfold : (liftM e.foldConst : ElabM RawExpr) = pure (.ternary c a b) := by rw [hf]; rfl
  have ht : H (if a.isLit then b else a) = K (if a.isLit then b else a) := by
    split <;> assumption
  unfold hoistWith
  extract_lets
  rw [hfold]
  simp -zeta only [pure_bind]
  dsimp +zetaDelta only
  rw [hc, ht, ha, hb]
private theorem terminal_congr (C : Contract) (rc rc' : ElabRec C)
    (H K : RawExpr → ElabM (SProg C × RawExpr)) (stmts : List RawStmt → ElabM (SProg C))
    (e s : RawExpr) (hf : e.foldConst = .ok s)
    (hs : (match s with
      | .num _ | .name _ | .bool _ | .env _ | .tuple _ | .opAssign .. => true
      | _ => false) = true) :
    hoistWith C {rc with hoist := H, elabStmtsP := stmts} e =
      hoistWith C {rc' with hoist := K, elabStmtsP := stmts} e := by
  have hfold : (liftM e.foldConst : ElabM RawExpr) = pure s := by rw [hf]; rfl
  unfold hoistWith
  extract_lets
  rw [hfold]
  simp -zeta only [pure_bind]
  cases s <;> simp only [Bool.false_eq_true] at hs
  all_goals rfl

/-- Argument hoisting consults its callback only on members of the original list. -/
theorem hoistArgsWith_congr (C : Contract)
    (H K : RawExpr → ElabM (SProg C × RawExpr)) (xs : List RawExpr)
    (h : ∀ a ∈ xs, H a = K a) : hoistArgsWith C H xs = hoistArgsWith C K xs := by
  induction xs with
  | nil => rfl
  | cons a as ih =>
    simp only [hoistArgsWith]
    rw [h a (by simp)]
    rw [ih (fun x hx => h x (by simp [hx]))]

private theorem modular_congr (C : Contract) (rc rc' : ElabRec C)
    (H K : RawExpr → ElabM (SProg C × RawExpr))
    (e a b k : RawExpr) (op : ModOp) (hf : e.foldConst = .ok (.modular op a b k))
    (ha : H a = K a) (hb : H b = K b) (hk : H k = K k) :
    hoistWith C {rc with hoist := H, hoistArgs := hoistArgsWith C H} e =
      hoistWith C {rc' with hoist := K, hoistArgs := hoistArgsWith C K} e := by
  have hfold : (liftM e.foldConst : ElabM RawExpr) = pure (.modular op a b k) := by rw [hf]; rfl
  have h3 := hoistArgsWith_congr C H K [a, b, k] (by
    intro x hx; simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
    rcases hx with rfl | rfl | rfl <;> assumption)
  have h2 := hoistArgsWith_congr C H K [b, a] (by
    intro x hx; simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
    rcases hx with rfl | rfl <;> assumption)
  unfold hoistWith
  extract_lets
  rw [hfold]
  simp -zeta only [pure_bind]
  dsimp +zetaDelta only
  rw [h3, h2, hk]

private theorem pair_congr (C : Contract)
    (H K : RawExpr → ElabM (SProg C × RawExpr)) (a b : RawExpr)
    (ha : H a = K a) (hb : H b = K b) :
    hoistPairWith C H a b = hoistPairWith C K a b := by
  unfold hoistPairWith
  rw [ha, hb]
private theorem binop_helper_congr (C : Contract)
    (H K : RawExpr → ElabM (SProg C × RawExpr)) (op : BinOp) (a b : RawExpr)
    (ha : H a = K a) (hb : H b = K b) :
    hoistBinopWith C H op a b = hoistBinopWith C K op a b := by
  unfold hoistBinopWith
  rw [pair_congr C H K a b ha hb, pair_congr C H K b a hb ha]
private theorem eager_pair_congr (C : Contract)
    (H K : RawExpr → ElabM (SProg C × RawExpr)) (a b : RawExpr)
    (discard : Bool) (expected : List (Option PrimTy))
    (ha : H a = K a) (hb : H b = K b) :
    eagerArgsWith C H [a,b] discard expected = eagerArgsWith C K [a,b] discard expected := by
  unfold eagerArgsWith
  simp only [List.zipIdx_cons, List.zipIdx_nil, List.forIn_cons, List.forIn_nil, ha, hb]

private theorem binary_congr (C : Contract) (rc rc' : ElabRec C)
    (H K : RawExpr → ElabM (SProg C × RawExpr)) (stmts : List RawStmt → ElabM (SProg C))
    (e a b : RawExpr) (op : BinOp) (hf : e.foldConst = .ok (.binop op a b))
    (ha : H a = K a) (hb : H b = K b) :
    hoistWith C {rc with hoist := H, elabStmtsP := stmts, hoistBinop := hoistBinopWith C H} e =
      hoistWith C {rc' with hoist := K, elabStmtsP := stmts, hoistBinop := hoistBinopWith C K} e := by
  have hfold : (liftM e.foldConst : ElabM RawExpr) = pure (.binop op a b) := by rw [hf]; rfl
  have he :
      eagerArgsWith C H (if C.evalOrder.binaryLeftToRight then [a,b] else [b,a]) false [some .uint, some .uint] =
      eagerArgsWith C K (if C.evalOrder.binaryLeftToRight then [a,b] else [b,a]) false [some .uint, some .uint] := by
    split
    · exact eager_pair_congr C H K a b _ _ ha hb
    · exact eager_pair_congr C H K b a _ _ hb ha
  have hp := binop_helper_congr C H K op a b ha hb
  unfold hoistWith
  extract_lets
  rw [hfold]
  simp -zeta only [pure_bind]
  dsimp +zetaDelta only
  rw [he, ha, hp]

omit [FreshNames] in
private theorem foldConst_structural (e s : RawExpr) (hf : e.foldConst = .ok s)
    (hs : structural e = true) : structural s = true := by
  rcases foldConst_same_or_lit e s hf with he | hl
  · subst s; exact hs
  · cases s <;> simp_all only [structural, RawExpr.isLit, Bool.false_eq_true]

private theorem error_congr (C : Contract) (rc rc' : ElabRec C)
    (e : RawExpr) (err : String) (hf : e.foldConst = .error err) :
    hoistWith C rc e = hoistWith C rc' e := by
  have hfold : (liftM e.foldConst : ElabM RawExpr) = throw err := by rw [hf]; rfl
  unfold hoistWith
  extract_lets
  rw [hfold]
  rfl

private theorem structural_congr (C : Contract) (rc rc' : ElabRec C)
    (H K : RawExpr → ElabM (SProg C × RawExpr)) (stmts : List RawStmt → ElabM (SProg C))
    (e : RawExpr) (hs : structural e = true)
    (h : ∀ a, a.nodes < e.nodes → H a = K a) :
    hoistWith C {rc with hoist := H, elabStmtsP := stmts, hoistArgs := hoistArgsWith C H, hoistBinop := hoistBinopWith C H} e =
      hoistWith C {rc' with hoist := K, elabStmtsP := stmts, hoistArgs := hoistArgsWith C K, hoistBinop := hoistBinopWith C K} e := by
  cases hf : e.foldConst with
  | error err => exact error_congr C _ _ e err hf
  | ok s =>
    have hsout := foldConst_structural e s hf hs
    have hb := foldConst_nodes_le e s hf
    cases s <;> simp only [structural, Bool.false_eq_true] at hsout
    all_goals try exact terminal_congr C {rc with hoistArgs := hoistArgsWith C H, hoistBinop := hoistBinopWith C H} {rc' with hoistArgs := hoistArgsWith C K, hoistBinop := hoistBinopWith C K} H K stmts e _ hf rfl
    case field a f =>
      apply field_congr C {rc with elabStmtsP := stmts, hoistArgs := hoistArgsWith C H, hoistBinop := hoistBinopWith C H} {rc' with elabStmtsP := stmts, hoistArgs := hoistArgsWith C K, hoistBinop := hoistBinopWith C K} H K e a f hf
      all_goals apply h
      all_goals simp only [RawExpr.nodes] at hb
      all_goals omega
    case index a b =>
      apply index_congr C {rc with elabStmtsP := stmts, hoistArgs := hoistArgsWith C H, hoistBinop := hoistBinopWith C H} {rc' with elabStmtsP := stmts, hoistArgs := hoistArgsWith C K, hoistBinop := hoistBinopWith C K} H K e a b hf
      all_goals apply h
      all_goals simp only [RawExpr.nodes] at hb
      all_goals omega
    case unop op a =>
      apply unop_congr C {rc with elabStmtsP := stmts, hoistArgs := hoistArgsWith C H, hoistBinop := hoistBinopWith C H} {rc' with elabStmtsP := stmts, hoistArgs := hoistArgsWith C K, hoistBinop := hoistBinopWith C K} H K e a op hf
      all_goals apply h
      all_goals simp only [RawExpr.nodes] at hb
      all_goals omega
    case incDec op a =>
      apply incDec_congr C {rc with elabStmtsP := stmts, hoistArgs := hoistArgsWith C H, hoistBinop := hoistBinopWith C H} {rc' with elabStmtsP := stmts, hoistArgs := hoistArgsWith C K, hoistBinop := hoistBinopWith C K} H K e a op hf
      all_goals apply h
      all_goals simp only [RawExpr.nodes] at hb
      all_goals omega
    case newArr op a =>
      apply newArr_congr C {rc with elabStmtsP := stmts, hoistArgs := hoistArgsWith C H, hoistBinop := hoistBinopWith C H} {rc' with elabStmtsP := stmts, hoistArgs := hoistArgsWith C K, hoistBinop := hoistBinopWith C K} H K e a op hf
      all_goals apply h
      all_goals simp only [RawExpr.nodes] at hb
      all_goals omega
    case assign l r =>
      apply assign_congr C {rc with hoistArgs := hoistArgsWith C H, hoistBinop := hoistBinopWith C H} {rc' with hoistArgs := hoistArgsWith C K, hoistBinop := hoistBinopWith C K} H K stmts e l r hf
      all_goals apply h
      all_goals simp only [RawExpr.nodes] at hb
      all_goals omega
    case ternary c a b =>
      apply ternary_congr C {rc with hoistArgs := hoistArgsWith C H, hoistBinop := hoistBinopWith C H} {rc' with hoistArgs := hoistArgsWith C K, hoistBinop := hoistBinopWith C K} H K stmts e c a b hf
      all_goals apply h
      all_goals simp only [RawExpr.nodes] at hb
      all_goals omega

    case modular op a b k =>
      apply modular_congr C {rc with elabStmtsP := stmts, hoistBinop := hoistBinopWith C H} {rc' with elabStmtsP := stmts, hoistBinop := hoistBinopWith C K} H K e a b k op hf
      all_goals apply h
      all_goals simp only [RawExpr.nodes] at hb
      all_goals omega

    case binop op a b =>
      apply binary_congr C {rc with hoistArgs := hoistArgsWith C H} {rc' with hoistArgs := hoistArgsWith C K} H K stmts e a b op hf
      all_goals apply h
      all_goals simp only [RawExpr.nodes] at hb
      all_goals omega

theorem hoistFuel_stable (C : Contract)
    (record : (RawExpr → ElabM (SProg C × RawExpr)) → ElabRec C)
    (stmts : List RawStmt → ElabM (SProg C))
    (fallback : RawExpr → ElabM (SProg C × RawExpr))
    (e : RawExpr) (n m : Nat) (hn : e.nodes ≤ n) (hm : e.nodes ≤ m) :
    hoistFuel C record stmts fallback n e = hoistFuel C record stmts fallback m e := by
  cases n with
  | zero => have hp := RawExpr.nodes_pos e; exfalso; omega
  | succ n =>
    cases m with
    | zero => have hp := RawExpr.nodes_pos e; exfalso; omega
    | succ m =>
      simp only [hoistFuel]
      split
      next hs =>
        apply structural_congr C _ _ _ _ stmts e hs
        intro a ha
        exact hoistFuel_stable C record stmts fallback a n m (by omega) (by omega)
      next => rfl
termination_by e.nodes

theorem hoistStructural_eq (C : Contract)
    (record : (RawExpr → ElabM (SProg C × RawExpr)) → ElabRec C)
    (stmts : List RawStmt → ElabM (SProg C))
    (fallback : RawExpr → ElabM (SProg C × RawExpr)) (e : RawExpr) :
    hoistStructural C record stmts fallback e =
      if structural e then
        hoistWith C {record (hoistStructural C record stmts fallback) with
          hoist := hoistStructural C record stmts fallback, elabStmtsP := stmts,
          hoistArgs := hoistArgsWith C (hoistStructural C record stmts fallback),
          hoistBinop := hoistBinopWith C (hoistStructural C record stmts fallback)} e
      else fallback e := by
  unfold hoistStructural
  cases hn : e.nodes with
  | zero => have hp := RawExpr.nodes_pos e; exfalso; omega
  | succ n =>
    rw [hoistFuel]
    split
    next hs =>
      apply structural_congr C _ _ _ _ stmts e hs
      intro a ha
      exact hoistFuel_stable C record stmts fallback a n a.nodes (by omega) (Nat.le_refl _)
    next => rfl

theorem hoistStructural_unique (C : Contract)
    (record : (RawExpr → ElabM (SProg C × RawExpr)) → ElabRec C)
    (stmts : List RawStmt → ElabM (SProg C))
    (fallback g : RawExpr → ElabM (SProg C × RawExpr))
    (hg : ∀ e, g e = if structural e then
      hoistWith C {record g with
        hoist := g, elabStmtsP := stmts,
        hoistArgs := hoistArgsWith C g, hoistBinop := hoistBinopWith C g} e else fallback e)
    (e : RawExpr) : g e = hoistStructural C record stmts fallback e := by
  rw [hg e, hoistStructural_eq]
  split
  next hs =>
    apply structural_congr C _ _ _ _ stmts e hs
    intro a ha
    exact hoistStructural_unique C record stmts fallback g hg a
  next => rfl
termination_by e.nodes
/-- The public hoister's arm equation for every constructor other than calls. -/
theorem hoist_structural_eq (C : Contract) (e : RawExpr) (hs : structural e = true) :
    hoist C e = hoistWith C (elabRec C ()) e := by
  have hupdate (H : RawExpr → ElabM (SProg C × RawExpr)) :
      let rc := elabRecWithProducers C
        (elabRecWithCallbacks C H (elabStmtP C) (@elabCallRet C _))
        (panicProducerWithCallbacks C (elabStmtP C) (@elabCallRet C _))
      {rc with
        hoist := H, elabStmtsP := elabStmtsPWith C (elabStmtP C),
        hoistArgs := hoistArgsWith C H, hoistBinop := hoistBinopWith C H} = rc := by
    let rc := elabRecWithProducers C
      (elabRecWithCallbacks C H (elabStmtP C) (@elabCallRet C _))
      (panicProducerWithCallbacks C (elabStmtP C) (@elabCallRet C _))
    have hh : rc.hoist = H := rfl
    have hs' : rc.elabStmtsP = elabStmtsPWith C (elabStmtP C) := rfl
    have ha : rc.hoistArgs = hoistArgsWith C H := rfl
    have hb : rc.hoistBinop = hoistBinopWith C H := rfl
    change {rc with
      hoist := H, elabStmtsP := elabStmtsPWith C (elabStmtP C),
      hoistArgs := hoistArgsWith C H, hoistBinop := hoistBinopWith C H} = rc
    rw [← ha, ← hb, ← hh, ← hs']
  unfold hoist hoistWithCallbacks
  rw [hoistStructural_eq, if_pos hs]
  apply congrArg (fun rc : ElabRec C => hoistWith C rc e)
  conv => rhs; unfold elabRec elabRecCore panicProducerRec hoist hoistWithCallbacks
  exact hupdate _

end Solidity.ElabHoist
