import Solidity.Syntax.Elab.CallMeasure

/-! Output-height bounds for structural expression arms and capture helpers. -/

namespace Solidity.ElabCallHeight
open Semantics ElabControlProof
variable (C : Contract) [FreshNames]

/-- Narrow-value capture keeps its operand or returns a captured name. -/
theorem narrowCapture_height_bound (e : RawExpr) :
    Obs (narrowCapture C e) (fun out => height out.2 ≤ height e) := by
  unfold narrowCapture
  repeat' first
    | (apply obs_pure; exact Nat.le_refl _)
    | (apply obs_pure; exact height_pos e)
    | exact obs_throw
    | (with_reducible apply obs_any; intro x)
    | split

/-- Forced argument capture never increases weighted expression height,
including the unannotated fallback through ordinary capture. -/
theorem forceArg_height_bound (e : RawExpr) (expected : Option PrimTy) :
    Obs (forceArg C e expected) (fun out => height out.2 ≤ height e) := by
  simp only [forceArg]
  change Obs (if (e.isLit || e.bytesLit?.isSome || (e matches .bool _)) = true
    then _ else _) _
  by_cases he : (e.isLit || e.bytesLit?.isSome || (e matches .bool _)) = true
  · rw [if_pos he]
    apply obs_pure
    exact Nat.le_refl _
  · rw [if_neg he]
    simp only [pure_bind]
    apply obs_any
    intro ⟨Γ, t⟩
    cases t <;> try (rename_i T _; cases T)
    all_goals
      repeat' first
      | exact captureExpr_height_bound C e
      | (apply obs_pure; exact height_pos e)
      | (with_reducible apply obs_any; intro value)
      | split

/-- Unary hoisting composes its operand bound with narrow capture. -/
theorem unop_output_height (rc : ElabRec C) (e a : RawExpr) (op : UnOp)
    (hf : e.foldConst = .ok (.unop op a))
    (ha : Obs (rc.hoist a) (fun out => height out.2 ≤ height a)) :
    Obs (hoistWith C rc e) (fun out => height out.2 ≤ height (.unop op a)) := by
  have hfold : (liftM e.foldConst : ElabM RawExpr) = pure (.unop op a) := by rw [hf]; rfl
  unfold hoistWith
  extract_lets
  rw [hfold]
  simp -zeta only [pure_bind]
  dsimp +zetaDelta only
  with_reducible apply obs_bind ha
  rintro ⟨P, a'⟩ ha'
  with_reducible apply obs_bind (narrowCapture_height_bound C (.unop op a'))
  rintro ⟨Q, out⟩ hout
  apply obs_pure
  simp only [height] at hout ⊢
  exact Nat.le_trans hout (Nat.add_le_add_left ha' 1)

/-- Field access preserves the operand bound, including fixed-array base capture. -/
theorem field_output_height (rc : ElabRec C) (e a : RawExpr) (f : String)
    (hf : e.foldConst = .ok (.field a f))
    (ha : Obs (rc.hoist a) (fun out => height out.2 ≤ height a)) :
    Obs (hoistWith C rc e) (fun out => height out.2 ≤ height (.field a f)) := by
  have hfold : (liftM e.foldConst : ElabM RawExpr) = pure (.field a f) := by rw [hf]; rfl
  unfold hoistWith
  extract_lets
  rw [hfold]
  simp -zeta only [pure_bind]
  dsimp +zetaDelta only
  with_reducible apply obs_bind ha
  rintro ⟨P, a'⟩ ha'
  repeat' first
    | (with_reducible apply obs_bind (captureExpr_height_bound C a'); rintro ⟨Pc, a''⟩ hcap)
    | (with_reducible apply obs_pure; simp only [height] at *; omega)
    | (with_reducible apply obs_any; intro value)
    | split

/-- Index access composes base/index bounds across capture and evaluation paths. -/
theorem index_output_height (rc : ElabRec C) (e a b : RawExpr)
    (hf : e.foldConst = .ok (.index a b))
    (ha : Obs (rc.hoist a) (fun out => height out.2 ≤ height a))
    (hb : Obs (rc.hoist b) (fun out => height out.2 ≤ height b)) :
    Obs (hoistWith C rc e) (fun out => height out.2 ≤ height (.index a b)) := by
  have hfold : (liftM e.foldConst : ElabM RawExpr) = pure (.index a b) := by rw [hf]; rfl
  unfold hoistWith
  extract_lets
  rw [hfold]
  simp -zeta only [pure_bind]
  dsimp +zetaDelta only
  with_reducible apply obs_bind ha
  rintro ⟨P, a'⟩ ha'
  repeat' first
    | (with_reducible apply obs_bind (captureExpr_height_bound C a'); rintro ⟨Pc, a''⟩ hcap)
    | (with_reducible apply obs_bind (forceArg_height_bound C a' none); rintro ⟨Pc, a''⟩ hcap)
    | (with_reducible apply obs_bind hb; rintro ⟨Q, b'⟩ hb')
    | (with_reducible apply obs_pure; simp only [height] at *; omega)
    | (with_reducible apply obs_any; intro value)
    | split

/-- Successful incDec hoisting returns a captured expression of height one. -/
theorem incDec_output_height (rc : ElabRec C) (e a : RawExpr) (op : IncDec)
    (hf : e.foldConst = .ok (.incDec op a)) :
    Obs (hoistWith C rc e) (fun out => height out.2 = 1) := by
  have hfold : (liftM e.foldConst : ElabM RawExpr) = pure (.incDec op a) := by rw [hf]; rfl
  unfold hoistWith
  extract_lets
  rw [hfold]
  simp -zeta only [pure_bind]
  dsimp +zetaDelta only
  repeat' first
    | (with_reducible apply obs_pure; simp only [height])
    | exact obs_throw
    | (with_reducible apply obs_any; intro value)
    | split


/-- Successful newArr hoisting returns a captured expression of height one. -/
theorem newArr_output_height (rc : ElabRec C) (e a : RawExpr) (op : RawTy)
    (hf : e.foldConst = .ok (.newArr op a)) :
    Obs (hoistWith C rc e) (fun out => height out.2 = 1) := by
  have hfold : (liftM e.foldConst : ElabM RawExpr) = pure (.newArr op a) := by rw [hf]; rfl
  unfold hoistWith
  extract_lets
  rw [hfold]
  simp -zeta only [pure_bind]
  dsimp +zetaDelta only
  repeat' first
    | (with_reducible apply obs_pure; simp only [height])
    | exact obs_throw
    | (with_reducible apply obs_any; intro value)
    | split


/-- Conditional hoisting either preserves its guarded condition or captures the join. -/
theorem ternary_output_height (rc : ElabRec C) (e c a b : RawExpr)
    (hf : e.foldConst = .ok (.ternary c a b))
    (hc : Obs (rc.hoist c) (fun out => height out.2 ≤ height c)) :
    Obs (hoistWith C rc e) (fun out => height out.2 ≤ height (.ternary c a b)) := by
  have hfold : (liftM e.foldConst : ElabM RawExpr) = pure (.ternary c a b) := by rw [hf]; rfl
  unfold hoistWith
  rw [hfold]
  simp -zeta only [pure_bind]
  dsimp +zetaDelta only
  with_reducible apply obs_bind hc
  rintro ⟨P, c'⟩ hc'
  have hname (Q : SProg C) (x : String) :
      Obs (pure (Q, RawExpr.name x) : ElabM (SProg C × RawExpr))
        (fun out => height out.2 ≤ height (.ternary c a b)) :=
    obs_pure (height_pos (.ternary c a b))
  have hkeep (Q : SProg C) :
      Obs (pure (Q, RawExpr.ternary c' a b) : ElabM (SProg C × RawExpr))
        (fun out => height out.2 ≤ height (.ternary c a b)) := by
    apply obs_pure
    simp only [height]
    simp only at hc'
    omega
  repeat' first
    | (with_reducible exact hname _ _)
    | (with_reducible exact hkeep _)
    | (with_reducible exact obs_throw)
    | (with_reducible apply obs_any; intro value)
    | split


/-- Binary hoisting composes operand and ordinary binary-helper bounds. -/
theorem binary_output_height (rc : ElabRec C) (e a b : RawExpr) (op : BinOp)
    (hf : e.foldConst = .ok (.binop op a b))
    (ha : Obs (rc.hoist a) (fun out => height out.2 ≤ height a))
    (hbin : Obs (rc.hoistBinop op a b)
      (fun out => height out.2 ≤ height (.binop op a b))) :
    Obs (hoistWith C rc e) (fun out => height out.2 ≤ height (.binop op a b)) := by
  have hfold : (liftM e.foldConst : ElabM RawExpr) = pure (.binop op a b) := by rw [hf]; rfl
  unfold hoistWith
  rw [hfold]
  simp -zeta only [pure_bind]
  dsimp +zetaDelta only
  repeat' first
    | (with_reducible apply obs_bind ha; rintro ⟨P, a'⟩ ha')
    | (with_reducible apply obs_bind hbin; rintro ⟨P, e'⟩ he')
    | (with_reducible apply obs_bind (narrowCapture_height_bound C e'); rintro ⟨Q, out⟩ hout)
    | (with_reducible apply obs_pure; simp only [height] at *; omega)
    | (with_reducible exact obs_throw)
    | (with_reducible apply obs_any; intro value)
    | split




end Solidity.ElabCallHeight

namespace Solidity.ElabCallHeight
open Semantics ElabControlProof
variable (C : Contract) [FreshNames]

/-- Both modular evaluation schedules preserve the maximum source operand height. -/
theorem modular_output_height (rc : ElabRec C) (e a b k : RawExpr) (op : ModOp)
    (hf : e.foldConst = .ok (.modular op a b k))
    (hk : Obs (rc.hoist k) (fun out => height out.2 ≤ height k))
    (hleft : Obs (rc.hoistArgs [a, b, k]) (fun out => heights out.2 ≤ heights [a, b, k]))
    (hright : Obs (rc.hoistArgs [b, a]) (fun out => heights out.2 ≤ heights [b, a])) :
    Obs (hoistWith C rc e) (fun out => height out.2 ≤ height (.modular op a b k)) := by
  have hfold : (liftM e.foldConst : ElabM RawExpr) = pure (.modular op a b k) := by rw [hf]; rfl
  unfold hoistWith
  rw [hfold]
  simp -zeta only [pure_bind]
  dsimp +zetaDelta only
  repeat' first
    | (with_reducible apply obs_bind hk; rintro ⟨P, k'⟩ hk')
    | (with_reducible apply obs_bind hleft; rintro ⟨P, args⟩ hargs)
    | (with_reducible apply obs_bind hright; rintro ⟨Q, args⟩ hargs)
    | (with_reducible apply obs_bind (captureExpr_height_bound C k'); rintro ⟨Pc, k''⟩ hcap)
    | (with_reducible apply obs_pure; simp_all only [height, heights]; omega)
    | (with_reducible exact obs_throw)
    | (with_reducible apply obs_any; intro value)
    | split

end Solidity.ElabCallHeight

namespace Solidity.ElabCallHeight
open Semantics ElabControlProof
variable (C : Contract) [FreshNames]

/-- Assignment expressions return the captured right-hand side without increasing its height. -/
theorem assignment_output_height (rc : ElabRec C) (e l r : RawExpr)
    (hf : e.foldConst = .ok (.assign l r))
    (hr : Obs (rc.hoist r) (fun out => height out.2 ≤ height r)) :
    Obs (hoistWith C rc e) (fun out => height out.2 ≤ height r) := by
  have hfold : (liftM e.foldConst : ElabM RawExpr) = pure (.assign l r) := by rw [hf]; rfl
  unfold hoistWith
  rw [hfold]
  simp -zeta only [pure_bind]
  dsimp +zetaDelta only
  with_reducible apply obs_bind hr
  rintro ⟨P, r'⟩ hr'
  repeat' first
    | (with_reducible apply obs_bind (captureExpr_height_bound C r'); rintro ⟨Pc, r''⟩ hcap)
    | (with_reducible apply obs_bind (forceArg_height_bound C r' none); rintro ⟨Pc, r''⟩ hcap)
    | (with_reducible apply obs_pure; exact Nat.le_trans hcap hr')
    | (with_reducible apply obs_any; intro value)
    | split

/-- Compound assignments return their original target expression. -/
theorem compound_assignment_output (rc : ElabRec C) (e l r : RawExpr) (op : BinOp)
    (hf : e.foldConst = .ok (.opAssign op l r)) :
    Obs (hoistWith C rc e) (fun out => out.2 = l) := by
  have hfold : (liftM e.foldConst : ElabM RawExpr) = pure (.opAssign op l r) := by rw [hf]; rfl
  unfold hoistWith
  rw [hfold]
  simp -zeta only [pure_bind]
  dsimp +zetaDelta only
  repeat' first
    | (with_reducible apply obs_pure; rfl)
    | (with_reducible exact obs_throw)
    | (with_reducible apply obs_any; intro value)
    | split

end Solidity.ElabCallHeight

namespace Solidity.ElabCallHeight
open Semantics ElabControlProof
variable (C : Contract) [FreshNames]

/-- Named-argument rewriting inherits the bound of its smaller ordinary call. -/
theorem named_output_height (rc : ElabRec C) (e : RawExpr) (f : String)
    (ns : List String) (args : List RawExpr)
    (hf : e.foldConst = .ok (.named f ns args))
    (hr : let request := RawExpr.call f ((C.structFields f).map fun p =>
        (lookupBy p.1 (ns.zip args)).getD (.num 0))
      Obs (rc.hoist request) (fun out => height out.2 ≤ height request)) :
    Obs (hoistWith C rc e) (fun out => height out.2 ≤ height (.named f ns args)) := by
  have hrequest : Obs (rc.hoist (.call f ((C.structFields f).map fun p =>
      (lookupBy p.1 (ns.zip args)).getD (.num 0))))
      (fun out => height out.2 ≤ height (.named f ns args)) := by
    intro sc st m out st' m' hrun
    exact Nat.le_trans (hr sc st m out st' m' hrun)
      (Nat.le_of_lt (named_request_lt C f ns args))
  have hfold : (liftM e.foldConst : ElabM RawExpr) = pure (.named f ns args) := by rw [hf]; rfl
  unfold hoistWith
  rw [hfold]
  simp -zeta only [pure_bind]
  dsimp +zetaDelta only
  simp only [List.map_map, Function.comp_def]
  repeat' first
    | (with_reducible exact hrequest)
    | (with_reducible exact obs_throw)
    | (with_reducible apply obs_any; intro value)
    | split

end Solidity.ElabCallHeight

namespace Solidity.ElabCallHeight
open Semantics ElabControlProof
variable (C : Contract) [FreshNames]

/-- Address conversion keeps its operand or captures a name. -/
theorem addressCapture_height_bound (e : RawExpr) :
    Obs (addressCapture C e) (fun out => height out.2 ≤ height e) := by
  simp only [addressCapture, pure_bind]
  repeat' first
    | (apply obs_pure; exact Nat.le_refl _)
    | (apply obs_pure; exact height_pos e)
    | (with_reducible apply obs_any; intro value)
    | split

/-- Enum conversion returns a captured name after its membership check. -/
theorem enumCapture_output_height (n : Nat) (e : RawExpr) :
    Obs (enumCapture C n e) (fun out => height out.2 = 1) := by
  unfold enumCapture
  repeat' first
    | (with_reducible apply obs_pure; simp only [height])
    | (with_reducible apply obs_any; intro value)
    | split

/-- Numeric casts return a captured name on success. -/
theorem castCapture_output_height (f : String) (e : RawExpr) :
    Obs (castCapture C f e) (fun out => height out.2 = 1) := by
  unfold castCapture
  repeat' first
    | (with_reducible apply obs_pure; simp only [height])
    | (with_reducible exact obs_throw)
    | (with_reducible apply obs_any; intro value)
    | split

end Solidity.ElabCallHeight
