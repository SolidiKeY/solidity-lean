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

namespace Solidity.ElabCallHeight
open Semantics ElabControlProof
variable (C : Contract) [FreshNames]

private theorem tuple_folded_output_height (rc : ElabRec C) (e : RawExpr) (n : List RawExpr)
    (hf : e.foldConst = .ok (.tuple n)) :
    Obs (hoistWith C rc e) (fun out => height out.2 ≤ height (.tuple n)) := by
  have hfold : (liftM e.foldConst : ElabM RawExpr) = pure (.tuple n) := by rw [hf]; rfl
  unfold hoistWith
  extract_lets
  rw [hfold]
  simp -zeta only [pure_bind]
  exact obs_throw

private theorem num_folded_output_height (rc : ElabRec C) (e : RawExpr) (n : Nat)
    (hf : e.foldConst = .ok (.num n)) :
    Obs (hoistWith C rc e) (fun out => height out.2 ≤ height (.num n)) := by
  have hfold : (liftM e.foldConst : ElabM RawExpr) = pure (.num n) := by rw [hf]; rfl
  unfold hoistWith
  extract_lets
  rw [hfold]
  simp -zeta only [pure_bind]
  exact obs_pure (Nat.le_refl _)

private theorem name_folded_output_height (rc : ElabRec C) (e : RawExpr) (n : String)
    (hf : e.foldConst = .ok (.name n)) :
    Obs (hoistWith C rc e) (fun out => height out.2 ≤ height (.name n)) := by
  have hfold : (liftM e.foldConst : ElabM RawExpr) = pure (.name n) := by rw [hf]; rfl
  unfold hoistWith
  extract_lets
  rw [hfold]
  simp -zeta only [pure_bind]
  exact obs_pure (Nat.le_refl _)

private theorem bool_folded_output_height (rc : ElabRec C) (e : RawExpr) (n : Bool)
    (hf : e.foldConst = .ok (.bool n)) :
    Obs (hoistWith C rc e) (fun out => height out.2 ≤ height (.bool n)) := by
  have hfold : (liftM e.foldConst : ElabM RawExpr) = pure (.bool n) := by rw [hf]; rfl
  unfold hoistWith
  extract_lets
  rw [hfold]
  simp -zeta only [pure_bind]
  exact obs_pure (Nat.le_refl _)

private theorem env_folded_output_height (rc : ElabRec C) (e : RawExpr) (n : EnvKey)
    (hf : e.foldConst = .ok (.env n)) :
    Obs (hoistWith C rc e) (fun out => height out.2 ≤ height (.env n)) := by
  have hfold : (liftM e.foldConst : ElabM RawExpr) = pure (.env n) := by rw [hf]; rfl
  unfold hoistWith
  extract_lets
  rw [hfold]
  simp -zeta only [pure_bind]
  exact obs_pure (Nat.le_refl _)

/-- Structural arms preserve height when smaller expression callbacks and the
binary helper preserve their bounds. Ordinary and named calls remain separate obligations. -/
theorem structural_folded_output_height (rc : ElabRec C) (e s : RawExpr)
    (hf : e.foldConst = .ok s) (hs : ElabHoist.structural s = true)
    (hh : ∀ a, height a < height s → Obs (rc.hoist a) (fun out => height out.2 ≤ height a))
    (hb : rc.hoistBinop = hoistBinopWith C rc.hoist)
    (hargs : rc.hoistArgs = hoistArgsWith C rc.hoist) :
    Obs (hoistWith C rc e) (fun out => height out.2 ≤ height s) := by
  cases s with
  | call f args => simp [ElabHoist.structural] at hs
  | named f ns args => simp [ElabHoist.structural] at hs
  | field a f =>
    apply field_output_height C rc e a f hf
    apply hh
    simp only [height]; omega
  | index a b =>
    apply index_output_height C rc e a b hf
    all_goals apply hh; simp only [height]; omega
  | unop op a =>
    apply unop_output_height C rc e a op hf
    apply hh
    simp only [height]; omega
  | binop op a b =>
    apply binary_output_height C rc e a b op hf
    · apply hh; simp only [height]; omega
    · rw [hb]
      apply binop_output_height_of_hoist C
      all_goals apply hh; simp only [height]; omega
  | ternary c a b =>
    apply ternary_output_height C rc e c a b hf
    apply hh
    simp only [height]; omega
  | modular op a b k =>
    apply modular_output_height C rc e a b k op hf
    · apply hh; simp only [height]; omega
    · rw [hargs]
      apply args_output_heights C
      intro x hx
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
      rcases hx with rfl | rfl | rfl
      all_goals apply hh; simp only [height]; omega
    · rw [hargs]
      apply args_output_heights C
      intro x hx
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
      rcases hx with rfl | rfl
      all_goals apply hh; simp only [height]; omega
  | assign l r =>
    have hr := hh r (by simp only [height]; omega)
    intro sc st m out st' m' h
    have he := assignment_output_height C rc e l r hf hr sc st m out st' m' h
    simp only [height]; omega
  | opAssign op l r =>
    intro sc st m out st' m' h
    have he := compound_assignment_output C rc e l r op hf sc st m out st' m' h
    simp only [he, height]; omega
  | incDec op a =>
    intro sc st m out st' m' h
    have he := incDec_output_height C rc e a op hf sc st m out st' m' h
    rw [he]
    exact height_pos (.incDec op a)
  | newArr op a =>
    intro sc st m out st' m' h
    have he := newArr_output_height C rc e a op hf sc st m out st' m' h
    rw [he]
    exact height_pos (.newArr op a)
  | tuple args => exact tuple_folded_output_height C rc e args hf
  | num n => exact num_folded_output_height C rc e n hf
  | name n => exact name_folded_output_height C rc e n hf
  | bool n => exact bool_folded_output_height C rc e n hf
  | env n => exact env_folded_output_height C rc e n hf

end Solidity.ElabCallHeight

namespace Solidity.ElabCallHeight
open Semantics ElabControlProof
variable (C : Contract) [FreshNames]

/-- Constant folding and the structural arm together preserve the original
input height. Only strictly smaller expression callbacks are assumed bounded. -/
theorem structural_output_height (rc : ElabRec C) (e : RawExpr)
    (hs : ElabHoist.structural e = true)
    (hh : ∀ a, height a < height e → Obs (rc.hoist a) (fun out => height out.2 ≤ height a))
    (hb : rc.hoistBinop = hoistBinopWith C rc.hoist)
    (hargs : rc.hoistArgs = hoistArgsWith C rc.hoist) :
    Obs (hoistWith C rc e) (fun out => height out.2 ≤ height e) := by
  cases hf : e.foldConst with
  | error err =>
    have hfold : (liftM e.foldConst : ElabM RawExpr) = throw err := by rw [hf]; rfl
    unfold hoistWith
    extract_lets
    rw [hfold]
    exact obs_throw
  | ok s =>
    have hse := foldConst_height_le e s hf
    have hs' : ElabHoist.structural s = true := by
      rcases ElabHoist.foldConst_same_or_lit e s hf with he | hl
      · subst s; exact hs
      · cases s <;> simp_all only [ElabHoist.structural, RawExpr.isLit, Bool.false_eq_true]
    have hsmall : ∀ a, height a < height s →
        Obs (rc.hoist a) (fun out => height out.2 ≤ height a) :=
      fun a ha => hh a (Nat.lt_of_lt_of_le ha hse)
    intro sc st m out st' m' h
    exact Nat.le_trans
      (structural_folded_output_height C rc e s hf hs' hsmall hb hargs sc st m out st' m' h) hse

end Solidity.ElabCallHeight

namespace Solidity.ElabCallHeight
open Semantics ElabControlProof ElabHoist
variable (C : Contract) [FreshNames]

/-- Structural fuel closure preserves output height on any proof region closed
under strictly smaller height. This does not impose a runtime input guard. -/
theorem hoistFuel_output_height_on
    (record : (RawExpr → ElabM (SProg C × RawExpr)) → ElabRec C)
    (stmts : List RawStmt → ElabM (SProg C))
    (fallback : RawExpr → ElabM (SProg C × RawExpr)) (Good : RawExpr → Prop)
    (hdown : ∀ e a, Good e → height a < height e → Good a)
    (hfb : ∀ e, Good e → Obs (fallback e) (fun out => height out.2 ≤ height e))
    (fuel : Nat) (e : RawExpr) (he : Good e) :
    Obs (hoistFuel C record stmts fallback fuel e) (fun out => height out.2 ≤ height e) := by
  induction fuel generalizing e with
  | zero => exact hfb e he
  | succ n ih =>
    simp only [hoistFuel]
    split
    next hs =>
      apply structural_output_height C _ e hs
      · intro a ha
        exact ih a (hdown e a he ha)
      · rfl
      · rfl
    next => exact hfb e he

/-- Named-call closure preserves the output-height invariant on the region, since its reordered
ordinary-call request is strictly smaller in weighted height. -/
theorem namedClosure_output_height_on (rc : ElabRec C)
    (fallback : RawExpr → ElabM (SProg C × RawExpr)) (Good : RawExpr → Prop)
    (hdown : ∀ e a, Good e → height a < height e → Good a)
    (hfb : ∀ e, Good e → Obs (fallback e) (fun out => height out.2 ≤ height e))
    (e : RawExpr) (he : Good e) :
    Obs (namedClosure C rc fallback e) (fun out => height out.2 ≤ height e) := by
  cases e <;> simp only [namedClosure] <;> try exact hfb _ he
  rename_i f ns args
  apply named_output_height C _ _ f ns args rfl
  exact hfb _ (hdown _ _ he (named_request_lt C f ns args))

/-- Closing structural and named recursion retains a fallback's output invariant
on a downward-closed proof region; fallback termination is not established. -/
theorem namedStructural_output_height_on
    (record : (RawExpr → ElabM (SProg C × RawExpr)) → ElabRec C)
    (stmts : List RawStmt → ElabM (SProg C))
    (fallback : RawExpr → ElabM (SProg C × RawExpr)) (Good : RawExpr → Prop)
    (hdown : ∀ e a, Good e → height a < height e → Good a)
    (hfb : ∀ e, Good e → Obs (fallback e) (fun out => height out.2 ≤ height e))
    (e : RawExpr) (he : Good e) :
    Obs (namedStructural C record stmts fallback e) (fun out => height out.2 ≤ height e) := by
  exact hoistFuel_output_height_on C record stmts _ Good hdown
    (namedClosure_output_height_on C (record fallback) fallback Good hdown hfb) e.nodes e he

theorem hoistFuel_output_height
    (record : (RawExpr → ElabM (SProg C × RawExpr)) → ElabRec C)
    (stmts : List RawStmt → ElabM (SProg C))
    (fallback : RawExpr → ElabM (SProg C × RawExpr)) (bound : Nat)
    (hfb : ∀ e, height e ≤ bound → Obs (fallback e) (fun out => height out.2 ≤ height e))
    (fuel : Nat) (e : RawExpr) (he : height e ≤ bound) :
    Obs (hoistFuel C record stmts fallback fuel e) (fun out => height out.2 ≤ height e) := by
  exact hoistFuel_output_height_on C record stmts fallback (fun a => height a ≤ bound)
    (fun _ _ h ha => Nat.le_trans (Nat.le_of_lt ha) h) hfb fuel e he


theorem namedClosure_output_height (rc : ElabRec C)
    (fallback : RawExpr → ElabM (SProg C × RawExpr)) (bound : Nat)
    (hfb : ∀ e, height e ≤ bound → Obs (fallback e) (fun out => height out.2 ≤ height e))
    (e : RawExpr) (he : height e ≤ bound) :
    Obs (namedClosure C rc fallback e) (fun out => height out.2 ≤ height e) := by
  exact namedClosure_output_height_on C rc fallback (fun a => height a ≤ bound)
    (fun _ _ h ha => Nat.le_trans (Nat.le_of_lt ha) h) hfb e he


theorem namedStructural_output_height
    (record : (RawExpr → ElabM (SProg C × RawExpr)) → ElabRec C)
    (stmts : List RawStmt → ElabM (SProg C))
    (fallback : RawExpr → ElabM (SProg C × RawExpr)) (bound : Nat)
    (hfb : ∀ e, height e ≤ bound → Obs (fallback e) (fun out => height out.2 ≤ height e))
    (e : RawExpr) (he : height e ≤ bound) :
    Obs (namedStructural C record stmts fallback e) (fun out => height out.2 ≤ height e) := by
  exact namedStructural_output_height_on C record stmts fallback (fun a => height a ≤ bound)
    (fun _ _ h ha => Nat.le_trans (Nat.le_of_lt ha) h) hfb e he


end Solidity.ElabCallHeight

namespace Solidity.ElabCallHeight
open Semantics ElabControlProof ElabHoist

/-- A strict height decrease stays inside the existing height/node prefix. -/
theorem height_nodes_before_down (root e a : RawExpr)
    (he : height e < height root ∨ (height e = height root ∧ e.nodes < root.nodes))
    (ha : height a < height e) :
    height a < height root ∨ (height a = height root ∧ a.nodes < root.nodes) := by
  left
  rcases he with he | ⟨he, _⟩
  · exact Nat.lt_trans ha he
  · exact Nat.lt_of_lt_of_le ha (Nat.le_of_eq he)

/-- The named-callee request lies before its caller even when heights tie. -/
theorem named_callee_before (g : String) (args : List RawExpr) :
    height (.call g args) < height (.call callValueName (.name g :: args)) ∨
      (height (.call g args) = height (.call callValueName (.name g :: args)) ∧
       RawExpr.nodes (.call g args) < RawExpr.nodes (.call callValueName (.name g :: args))) := by
  have h := named_callee_decreases g args
  rcases Nat.lt_or_eq_of_le h.1 with hl | he
  · exact Or.inl hl
  · exact Or.inr ⟨he, h.2⟩

variable (C : Contract) [FreshNames]

/-- The closure output invariant applies to the existing height/node prefix,
using only a fallback invariant on that strict prefix. -/
theorem namedStructural_output_height_before
    (record : (RawExpr → ElabM (SProg C × RawExpr)) → ElabRec C)
    (stmts : List RawStmt → ElabM (SProg C))
    (fallback : RawExpr → ElabM (SProg C × RawExpr)) (root : RawExpr)
    (hfb : ∀ a, (height a < height root ∨ (height a = height root ∧ a.nodes < root.nodes)) →
      Obs (fallback a) (fun out => height out.2 ≤ height a))
    (e : RawExpr)
    (he : height e < height root ∨ (height e = height root ∧ e.nodes < root.nodes)) :
    Obs (namedStructural C record stmts fallback e) (fun out => height out.2 ≤ height e) :=
  namedStructural_output_height_on C record stmts fallback _
    (height_nodes_before_down root) hfb e he

/-- Named-callee recursion can use the strict-prefix closure invariant without
assuming strict height decrease or bounds outside that prefix. -/
theorem named_callee_closure_output_height
    (record : (RawExpr → ElabM (SProg C × RawExpr)) → ElabRec C)
    (stmts : List RawStmt → ElabM (SProg C))
    (fallback : RawExpr → ElabM (SProg C × RawExpr)) (g : String) (args : List RawExpr)
    (hfb : ∀ a,
      (height a < height (.call callValueName (.name g :: args)) ∨
        (height a = height (.call callValueName (.name g :: args)) ∧
         a.nodes < RawExpr.nodes (.call callValueName (.name g :: args)))) →
      Obs (fallback a) (fun out => height out.2 ≤ height a)) :
    Obs (namedStructural C record stmts fallback (.call g args))
      (fun out => height out.2 ≤ height (.call g args)) :=
  namedStructural_output_height_before C record stmts fallback _ hfb _
    (named_callee_before g args)

end Solidity.ElabCallHeight

namespace Solidity.ElabCallHeight
open Semantics ElabControlProof

/-- Every successful inline opening came from a descriptor or raw slice. -/
theorem inlineSliceOpen_cases (t : String) (view : RawExpr) (v : SliceView) (pre : List RawStmt)
    (h : inlineSliceOpen t view = .ok (v, pre)) :
    (view = .call "#sliceDesc" [.name v.base, v.off, v.fin] ∧ pre = []) ∨
      ∃ b i j, view = .call "#sliceRaw" [b, i, j] := by
  unfold inlineSliceOpen at h
  split at h
  · exact Or.inr ⟨_, _, _, rfl⟩
  · dsimp only at h
    split at h
    · cases h
      exact Or.inl ⟨rfl, rfl⟩
    · cases h
/-- Opening an explicit descriptor only returns its recorded components. -/
theorem inlineSliceOpen_desc (t base : String) (off fin : RawExpr) :
    inlineSliceOpen t (.call "#sliceDesc" [.name base, off, fin]) =
      .ok (({ base, off, fin } : SliceView), []) := by rfl

/-- Folded subtraction adds at most one expression layer. -/
theorem sliceSub_height_le (e o : RawExpr) :
    height (sliceSub e o) ≤ 1 + max (height e) (height o) := by
  unfold sliceSub
  split <;> simp only [height] <;> omega

/-- A descriptor's computed length remains below its descriptor height. -/
theorem descriptor_len_le (base : String) (off fin : RawExpr) :
    height (({ base, off, fin } : SliceView).len) ≤
      height (.call "#sliceDesc" [.name base, off, fin]) := by
  have h := sliceSub_height_le fin off
  have hc : cost "#sliceDesc" = 1 := rfl
  simp only [SliceView.len, height, heights, hc]
  omega

/-- The exact indexing request from an opened descriptor decreases. -/
theorem descriptor_at_request_lt (base : String) (off fin k : RawExpr) :
    height (.index (.name base) (.call "#sliceIndex"
      [off, ({ base, off, fin } : SliceView).len, k, .field (.name base) "length"])) <
    height (.call "#sliceAt" [.call "#sliceDesc" [.name base, off, fin], k]) := by
  have h := descriptor_len_le base off fin
  have hc : cost "#sliceDesc" = 1 := rfl
  have hi : cost "#sliceIndex" = 3 := rfl
  have ha : cost "#sliceAt" = 6 := rfl
  simp only [height, heights, hc, hi, ha] at h ⊢
  omega

/-- Reading the length after opening a descriptor decreases. -/
theorem descriptor_length_request_lt (base : String) (off fin : RawExpr) :
    height (({ base, off, fin } : SliceView).len) <
      height (.call "#sliceLength" [.call "#sliceDesc" [.name base, off, fin]]) := by
  have h := descriptor_len_le base off fin
  have hc : cost "#sliceLength" = 2 := rfl
  simp only [height, heights, hc] at h ⊢
  omega

/-- The exact ABI decode request from an opened descriptor decreases. -/
theorem descriptor_decode_request_lt (base : String) (off fin : RawExpr)
    (rest : List RawExpr) :
    height (.call "abi.decode" (.call sliceViewName
      [.name base, off, ({ base, off, fin } : SliceView).len] :: rest)) <
    height (.call "#sliceDecode" (.call "#sliceDesc" [.name base, off, fin] :: rest)) := by
  have h := descriptor_len_le base off fin
  have hc : cost "#sliceDesc" = 1 := rfl
  have hv : cost sliceViewName = 1 := rfl
  have hd : cost "#sliceDecode" = 5 := rfl
  have hdecode : cost "abi.decode" = 2 := rfl
  simp only [height, heights, hc, hv, hd, hdecode] at h ⊢
  omega



theorem raw_at_request_lt (b i j k : RawExpr) (v : SliceView)
    (ho : height v.off ≤ 2) (hl : height v.len ≤ 3) :
    height (.index (.name v.base) (.call "#sliceIndex"
      [v.off, v.len, k, .field (.name v.base) "length"])) <
      height (.call "#sliceAt" [.call "#sliceRaw" [b, i, j], k]) := by
  have hb := height_pos b
  have hc : cost "#sliceRaw" = 1 := rfl
  have hi : cost "#sliceIndex" = 3 := rfl
  have ha : cost "#sliceAt" = 6 := rfl
  simp only [height, heights, hc, hi, ha]
  omega

theorem raw_length_request_lt (b i j : RawExpr) (v : SliceView)
    (hl : height v.len ≤ 3) :
    height v.len < height (.call "#sliceLength" [.call "#sliceRaw" [b, i, j]]) := by
  have hb := height_pos b
  have hc : cost "#sliceRaw" = 1 := rfl
  have hd : cost "#sliceLength" = 2 := rfl
  simp only [height, heights, hc, hd]
  omega

theorem raw_decode_request_lt (b i j : RawExpr) (v : SliceView) (rest : List RawExpr)
    (ho : height v.off ≤ 2) (hl : height v.len ≤ 3) :
    height (.call "abi.decode" (.call sliceViewName [.name v.base, v.off, v.len] :: rest)) <
    height (.call "#sliceDecode" (.call "#sliceRaw" [b, i, j] :: rest)) := by
  have hb := height_pos b
  have hc : cost "#sliceRaw" = 1 := rfl
  have hv : cost sliceViewName = 1 := rfl
  have hd : cost "#sliceDecode" = 5 := rfl
  have cost_decode : cost "abi.decode" = 2 := rfl
  simp only [height, heights, hc, hv, hd, cost_decode]
  omega


end Solidity.ElabCallHeight

namespace Solidity.ElabControlProof
/-- A successful checking step retains its result predicate when lifted. -/
theorem obs_lift {α : Type} {x : Except String α} {Q : α → Prop}
    (hx : ∀ a, x = .ok a → Q a) : Obs (ElabM.lift x) Q := by
  intro sc st m a st' m' h
  cases he : x with
  | error err => simp only [he] at h; cases h
  | ok v =>
    simp only [he] at h
    cases h
    exact hx _ he
end Solidity.ElabControlProof

namespace Solidity.ElabCallHeight
open Semantics ElabControlProof
variable (C : Contract) [FreshNames]

/-- Slice length preserves height when opening supplies a smaller request. -/
theorem slice_length_output_height_of_request (rc : ElabRec C) (e view : RawExpr)
    (hf : e.foldConst = .ok (.call "#sliceLength" [view]))
    (hreq : ∀ t v pre, inlineSliceOpen t view = .ok (v, pre) →
      height v.len < height (.call "#sliceLength" [view]))
    (hh : ∀ a, height a < height (.call "#sliceLength" [view]) →
      Obs (rc.hoist a) (fun out => height out.2 ≤ height a)) :
    Obs (hoistWith C rc e) (fun out => height out.2 ≤ height (.call "#sliceLength" [view])) := by
  have hfold : (liftM e.foldConst : ElabM RawExpr) = pure (.call "#sliceLength" [view]) := by rw [hf]; rfl
  unfold hoistWith
  rw [hfold]
  simp -zeta only [pure_bind]
  dsimp +zetaDelta only
  with_reducible apply obs_any
  intro fresh
  with_reducible apply obs_bind (obs_lift (fun out h => hreq (toString fresh) out.1 out.2 h))
  rintro ⟨v, pre⟩ hlt
  have hrequest := hh _ hlt
  repeat' first
    | (with_reducible apply obs_bind hrequest; rintro ⟨R, out⟩ hout)
    | (with_reducible apply obs_pure; exact Nat.le_trans hout (Nat.le_of_lt hlt))
    | (with_reducible apply obs_any; intro value)
    | split

/-- Slice at preserves height when opening supplies a smaller request. -/
theorem slice_at_output_height_of_request (rc : ElabRec C) (e view k : RawExpr)
    (hf : e.foldConst = .ok (.call "#sliceAt" [view, k]))
    (hreq : ∀ t v pre, inlineSliceOpen t view = .ok (v, pre) →
      height (.index (.name v.base) (.call "#sliceIndex" [v.off, v.len, k, .field (.name v.base) "length"])) < height (.call "#sliceAt" [view, k]))
    (hh : ∀ a, height a < height (.call "#sliceAt" [view, k]) →
      Obs (rc.hoist a) (fun out => height out.2 ≤ height a)) :
    Obs (hoistWith C rc e) (fun out => height out.2 ≤ height (.call "#sliceAt" [view, k])) := by
  have hfold : (liftM e.foldConst : ElabM RawExpr) = pure (.call "#sliceAt" [view, k]) := by rw [hf]; rfl
  unfold hoistWith
  rw [hfold]
  simp -zeta only [pure_bind]
  dsimp +zetaDelta only
  with_reducible apply obs_any
  intro fresh
  with_reducible apply obs_bind (obs_lift (fun out h => hreq (toString fresh) out.1 out.2 h))
  rintro ⟨v, pre⟩ hlt
  have hrequest := hh _ hlt
  repeat' first
    | (with_reducible apply obs_bind hrequest; rintro ⟨R, out⟩ hout)
    | (with_reducible apply obs_pure; exact Nat.le_trans hout (Nat.le_of_lt hlt))
    | (with_reducible apply obs_any; intro value)
    | split

/-- Slice decoding preserves height when opening supplies a smaller request. -/
theorem slice_decode_output_height_of_request (rc : ElabRec C) (e view : RawExpr)
    (rest : List RawExpr)
    (hf : e.foldConst = .ok (.call "#sliceDecode" (view :: rest)))
    (hreq : ∀ t v pre, inlineSliceOpen t view = .ok (v, pre) →
      height (.call "abi.decode" (.call sliceViewName [.name v.base, v.off, v.len] :: rest)) <
        height (.call "#sliceDecode" (view :: rest)))
    (hh : ∀ a, height a < height (.call "#sliceDecode" (view :: rest)) →
      Obs (rc.hoist a) (fun out => height out.2 ≤ height a)) :
    Obs (hoistWith C rc e) (fun out => height out.2 ≤ height (.call "#sliceDecode" (view :: rest))) := by
  have hfold : (liftM e.foldConst : ElabM RawExpr) =
      pure (.call "#sliceDecode" (view :: rest)) := by rw [hf]; rfl
  unfold hoistWith
  rw [hfold]
  simp -zeta only [pure_bind]
  dsimp +zetaDelta only
  split <;> try (exfalso; simp_all [RawExpr.call.injEq]; done)
  case h_14 =>
    rename_i heq
    obtain ⟨rfl, rfl⟩ := List.cons.inj (RawExpr.call.inj heq).2
    with_reducible apply obs_any
    intro fresh
    with_reducible apply obs_bind (obs_lift (fun out h => hreq (toString fresh) out.1 out.2 h))
    rintro ⟨v, pre⟩ hlt
    have hrequest := hh _ hlt
    repeat' first
      | (with_reducible apply obs_bind hrequest; rintro ⟨R, out⟩ hout)
      | (with_reducible apply obs_pure; exact Nat.le_trans hout (Nat.le_of_lt hlt))
      | (with_reducible apply obs_any; intro value)
  case h_17 =>
    rename_i hdecode hcopy harray heq
    obtain ⟨rfl, rfl⟩ := RawExpr.call.inj heq
    exact False.elim (hdecode view rest rfl rfl)

/-- Earlier specialized contract, derived from the shared arm proof. -/
theorem descriptor_length_output_height (rc : ElabRec C) (e : RawExpr)
    (base : String) (off fin : RawExpr)
    (hf : e.foldConst = .ok (.call "#sliceLength" [.call "#sliceDesc" [.name base, off, fin]]))
    (hh : ∀ a, height a < height (.call "#sliceLength" [.call "#sliceDesc" [.name base, off, fin]]) →
      Obs (rc.hoist a) (fun out => height out.2 ≤ height a)) :
    Obs (hoistWith C rc e) (fun out => height out.2 ≤
      height (.call "#sliceLength" [.call "#sliceDesc" [.name base, off, fin]])) := by
  refine slice_length_output_height_of_request C rc e _ hf ?_ hh
  intro t v pre h
  rw [inlineSliceOpen_desc] at h
  cases h
  exact descriptor_length_request_lt base off fin


/-- Earlier specialized contract, derived from the shared arm proof. -/
theorem descriptor_at_output_height (rc : ElabRec C) (e : RawExpr)
    (base : String) (off fin k : RawExpr)
    (hf : e.foldConst = .ok (.call "#sliceAt" [.call "#sliceDesc" [.name base, off, fin], k]))
    (hh : ∀ a, height a < height (.call "#sliceAt" [.call "#sliceDesc" [.name base, off, fin], k]) →
      Obs (rc.hoist a) (fun out => height out.2 ≤ height a)) :
    Obs (hoistWith C rc e) (fun out => height out.2 ≤
      height (.call "#sliceAt" [.call "#sliceDesc" [.name base, off, fin], k])) := by
  refine slice_at_output_height_of_request C rc e _ k hf ?_ hh
  intro t v pre h
  rw [inlineSliceOpen_desc] at h
  cases h
  exact descriptor_at_request_lt base off fin k


/-- Earlier specialized contract, derived from the shared arm proof. -/
theorem descriptor_decode_output_height (rc : ElabRec C) (e : RawExpr)
    (base : String) (off fin : RawExpr) (rest : List RawExpr)
    (hf : e.foldConst = .ok (.call "#sliceDecode" (.call "#sliceDesc" [.name base, off, fin] :: rest)))
    (hh : ∀ a, height a < height (.call "#sliceDecode" (.call "#sliceDesc" [.name base, off, fin] :: rest)) →
      Obs (rc.hoist a) (fun out => height out.2 ≤ height a)) :
    Obs (hoistWith C rc e) (fun out => height out.2 ≤
      height (.call "#sliceDecode" (.call "#sliceDesc" [.name base, off, fin] :: rest))) := by
  refine slice_decode_output_height_of_request C rc e _ rest hf ?_ hh
  intro t v pre h
  rw [inlineSliceOpen_desc] at h
  cases h
  exact descriptor_decode_request_lt base off fin rest


/-- Earlier specialized contract, derived from the shared arm proof. -/
theorem raw_length_output_height_of_bounds (rc : ElabRec C) (e b i j : RawExpr)
    (hf : e.foldConst = .ok (.call "#sliceLength" [.call "#sliceRaw" [b, i, j]]))
    (hopen : ∀ t v pre, inlineSliceOpen t (.call "#sliceRaw" [b, i, j]) = .ok (v, pre) →
      height v.off ≤ 2 ∧ height v.len ≤ 3)
    (hh : ∀ a, height a < height (.call "#sliceLength" [.call "#sliceRaw" [b, i, j]]) →
      Obs (rc.hoist a) (fun out => height out.2 ≤ height a)) :
    Obs (hoistWith C rc e) (fun out => height out.2 ≤ height (.call "#sliceLength" [.call "#sliceRaw" [b, i, j]])) := by
  refine slice_length_output_height_of_request C rc e _ hf ?_ hh
  intro t v pre h
  have hv := hopen t v pre h
  exact raw_length_request_lt b i j v hv.2


/-- Earlier specialized contract, derived from the shared arm proof. -/
theorem raw_at_output_height_of_bounds (rc : ElabRec C) (e b i j k : RawExpr)
    (hf : e.foldConst = .ok (.call "#sliceAt" [.call "#sliceRaw" [b, i, j], k]))
    (hopen : ∀ t v pre, inlineSliceOpen t (.call "#sliceRaw" [b, i, j]) = .ok (v, pre) →
      height v.off ≤ 2 ∧ height v.len ≤ 3)
    (hh : ∀ a, height a < height (.call "#sliceAt" [.call "#sliceRaw" [b, i, j], k]) →
      Obs (rc.hoist a) (fun out => height out.2 ≤ height a)) :
    Obs (hoistWith C rc e) (fun out => height out.2 ≤ height (.call "#sliceAt" [.call "#sliceRaw" [b, i, j], k])) := by
  refine slice_at_output_height_of_request C rc e _ k hf ?_ hh
  intro t v pre h
  have hv := hopen t v pre h
  exact raw_at_request_lt b i j k v hv.1 hv.2


/-- Earlier specialized contract, derived from the shared arm proof. -/
theorem raw_decode_output_height_of_bounds (rc : ElabRec C) (e b i j : RawExpr)
    (rest : List RawExpr)
    (hf : e.foldConst = .ok (.call "#sliceDecode" (.call "#sliceRaw" [b, i, j] :: rest)))
    (hopen : ∀ t v pre, inlineSliceOpen t (.call "#sliceRaw" [b, i, j]) = .ok (v, pre) →
      height v.off ≤ 2 ∧ height v.len ≤ 3)
    (hh : ∀ a, height a < height (.call "#sliceDecode" (.call "#sliceRaw" [b, i, j] :: rest)) →
      Obs (rc.hoist a) (fun out => height out.2 ≤ height a)) :
    Obs (hoistWith C rc e) (fun out => height out.2 ≤
      height (.call "#sliceDecode" (.call "#sliceRaw" [b, i, j] :: rest))) := by
  refine slice_decode_output_height_of_request C rc e _ rest hf ?_ hh
  intro t v pre h
  have hv := hopen t v pre h
  exact raw_decode_request_lt b i j v rest hv.1 hv.2


end Solidity.ElabCallHeight

namespace Solidity.ElabCallHeight
open Semantics ElabControlProof

/-- Successful opening yields a smaller length request, assuming raw opening bounds. -/
theorem slice_length_request_lt_of_raw_bounds (view : RawExpr) (t : String)
    (v : SliceView) (pre : List RawStmt)
    (hopen : ∀ t b i j v pre, inlineSliceOpen t (.call "#sliceRaw" [b, i, j]) = .ok (v, pre) →
      height v.off ≤ 2 ∧ height v.len ≤ 3)
    (h : inlineSliceOpen t view = .ok (v, pre)) :
    height v.len < height (.call "#sliceLength" [view]) := by
  rcases inlineSliceOpen_cases t view v pre h with ⟨rfl, _⟩ | ⟨b, i, j, rfl⟩
  · exact descriptor_length_request_lt v.base v.off v.fin
  · exact raw_length_request_lt b i j v (hopen t b i j v pre h).2

/-- Successful opening yields a smaller indexing request, assuming raw opening bounds. -/
theorem slice_at_request_lt_of_raw_bounds (view k : RawExpr) (t : String)
    (v : SliceView) (pre : List RawStmt)
    (hopen : ∀ t b i j v pre, inlineSliceOpen t (.call "#sliceRaw" [b, i, j]) = .ok (v, pre) →
      height v.off ≤ 2 ∧ height v.len ≤ 3)
    (h : inlineSliceOpen t view = .ok (v, pre)) :
    height (.index (.name v.base) (.call "#sliceIndex"
      [v.off, v.len, k, .field (.name v.base) "length"])) <
      height (.call "#sliceAt" [view, k]) := by
  rcases inlineSliceOpen_cases t view v pre h with ⟨rfl, _⟩ | ⟨b, i, j, rfl⟩
  · exact descriptor_at_request_lt v.base v.off v.fin k
  · have hv := hopen t b i j v pre h
    exact raw_at_request_lt b i j k v hv.1 hv.2

/-- Successful opening yields a smaller decode request, assuming raw opening bounds. -/
theorem slice_decode_request_lt_of_raw_bounds (view : RawExpr) (rest : List RawExpr)
    (t : String) (v : SliceView) (pre : List RawStmt)
    (hopen : ∀ t b i j v pre, inlineSliceOpen t (.call "#sliceRaw" [b, i, j]) = .ok (v, pre) →
      height v.off ≤ 2 ∧ height v.len ≤ 3)
    (h : inlineSliceOpen t view = .ok (v, pre)) :
    height (.call "abi.decode" (.call sliceViewName [.name v.base, v.off, v.len] :: rest)) <
      height (.call "#sliceDecode" (view :: rest)) := by
  rcases inlineSliceOpen_cases t view v pre h with ⟨rfl, _⟩ | ⟨b, i, j, rfl⟩
  · exact descriptor_decode_request_lt v.base v.off v.fin rest
  · have hv := hopen t b i j v pre h
    exact raw_decode_request_lt b i j v rest hv.1 hv.2

end Solidity.ElabCallHeight

namespace Solidity.ElabCallHeight
open Semantics ElabControlProof
variable (C : Contract) [FreshNames]

/-- All successful slice-length arms preserve height under raw opening bounds. -/
theorem slice_length_output_height_of_raw_bounds (rc : ElabRec C) (e view : RawExpr)
    (hf : e.foldConst = .ok (.call "#sliceLength" [view]))
    (hopen : ∀ t b i j v pre, inlineSliceOpen t (.call "#sliceRaw" [b, i, j]) = .ok (v, pre) →
      height v.off ≤ 2 ∧ height v.len ≤ 3)
    (hh : ∀ a, height a < height (.call "#sliceLength" [view]) →
      Obs (rc.hoist a) (fun out => height out.2 ≤ height a)) :
    Obs (hoistWith C rc e) (fun out => height out.2 ≤ height (.call "#sliceLength" [view])) :=
  slice_length_output_height_of_request C rc e view hf
    (fun t v pre h => slice_length_request_lt_of_raw_bounds view t v pre hopen h) hh

/-- All successful slice-at arms preserve height under raw opening bounds. -/
theorem slice_at_output_height_of_raw_bounds (rc : ElabRec C) (e view k : RawExpr)
    (hf : e.foldConst = .ok (.call "#sliceAt" [view, k]))
    (hopen : ∀ t b i j v pre, inlineSliceOpen t (.call "#sliceRaw" [b, i, j]) = .ok (v, pre) →
      height v.off ≤ 2 ∧ height v.len ≤ 3)
    (hh : ∀ a, height a < height (.call "#sliceAt" [view, k]) →
      Obs (rc.hoist a) (fun out => height out.2 ≤ height a)) :
    Obs (hoistWith C rc e) (fun out => height out.2 ≤ height (.call "#sliceAt" [view, k])) :=
  slice_at_output_height_of_request C rc e view k hf
    (fun t v pre h => slice_at_request_lt_of_raw_bounds view k t v pre hopen h) hh

/-- All successful slice-decode arms preserve height under raw opening bounds. -/
theorem slice_decode_output_height_of_raw_bounds (rc : ElabRec C) (e view : RawExpr)
    (rest : List RawExpr)
    (hf : e.foldConst = .ok (.call "#sliceDecode" (view :: rest)))
    (hopen : ∀ t b i j v pre, inlineSliceOpen t (.call "#sliceRaw" [b, i, j]) = .ok (v, pre) →
      height v.off ≤ 2 ∧ height v.len ≤ 3)
    (hh : ∀ a, height a < height (.call "#sliceDecode" (view :: rest)) →
      Obs (rc.hoist a) (fun out => height out.2 ≤ height a)) :
    Obs (hoistWith C rc e) (fun out => height out.2 ≤ height (.call "#sliceDecode" (view :: rest))) :=
  slice_decode_output_height_of_request C rc e view rest hf
    (fun t v pre h => slice_decode_request_lt_of_raw_bounds view rest t v pre hopen h) hh

end Solidity.ElabCallHeight

namespace Solidity.ElabCallHeight
open Semantics ElabControlProof


theorem call_output_height_of_raw_bounds (C : Contract) [FreshNames] (rc : ElabRec C) (f : String) (args : List RawExpr)
    (hh : ∀ a, (height a < height (.call f args) ∨
      height a = height (.call f args) ∧ a.nodes < (RawExpr.call f args).nodes) →
      Obs (rc.hoist a) (fun out => height out.2 ≤ height a))
    (henc : ∀ std strs xs marks sel, Obs (rc.abiEncode std strs xs marks sel)
      (fun out => height out.2 = 1))
    (hopen : ∀ t b i j v pre, inlineSliceOpen t (.call "#sliceRaw" [b, i, j]) = .ok (v, pre) →
      height v.off ≤ 2 ∧ height v.len ≤ 3)
    (hmem : ∀ h ty xs, Obs (rc.fnMemoryDispatch h ty xs) (fun out => height out.2 = 1)) :
    Obs (hoistWith C rc (.call f args)) (fun out => height out.2 ≤ height (.call f args)) := by
  have hhash : Obs (hoistHashWith C rc.hoist rc.abiMemBytes rc.elabStmtsP f args)
      (fun out => height out.2 = 1) := by
    intro sc st m out st' m' hr
    exact hash_output_height C rc.hoist rc.abiMemBytes rc.elabStmtsP f args sc st st' m m' out hr
  have hdecode : Obs (abiDecodeWith C rc.hoist rc.abiMemBytes rc.elabStmtsP rc.abiDecodeBytes f args)
      (fun out => height out.2 ≤ height (.call f args)) :=
    decode_output_height C rc.hoist rc.abiMemBytes rc.elabStmtsP rc.abiDecodeBytes f args
      (fun e he => hh e (Or.inl he))
  have herc : f = "erc7201" → Obs (hoistERC7201With C rc.hoist args)
      (fun out => height out.2 ≤ height (.call f args)) := by
    intro hf
    subst f
    exact erc_args_output_height C rc.hoist args (fun e he => hh e (Or.inl he))
  have hfold : (liftM (RawExpr.call f args).foldConst : ElabM RawExpr) =
      pure (.call f args) := rfl
  unfold hoistWith
  rw [hfold]
  simp -zeta only [pure_bind]
  extract_lets
  split
  case h_17 =>
    rename_i heq
    obtain ⟨rfl, rfl⟩ := RawExpr.call.inj heq
    extract_lets fields declared byName byValue structFinish structBuild structOrValue castTail enumTail markedArgs builtinTail
    have hname (P : SProg C) (x : String) :
        Obs (pure (P, RawExpr.name x) : ElabM (SProg C × RawExpr))
          (fun out => height out.2 = 1) := obs_pure rfl
    have hdecl : ∀ u, Obs (declared u) (fun out => height out.2 = 1) := by
      intro u
      simp -zeta only [declared]
      repeat' first
        | (with_reducible exact hname _ _)
        | (with_reducible exact obs_throw)
        | (with_reducible apply obs_any; intro value)
        | split
        | extract_lets
    clear_value declared
    have hkeep (P : SProg C) (a : RawExpr) (ha : height a = 1) :
        Obs (pure (P, a) : ElabM (SProg C × RawExpr))
          (fun out => height out.2 = 1) := obs_pure ha
    have hbyName : ∀ u, Obs (byName u) (fun out => height out.2 = 1) := by
      intro u
      simp -zeta only [byName]
      repeat' first
        | (with_reducible exact hdecl _)
        | (with_reducible exact hname _ _)
        | (with_reducible exact hkeep _ _ (by assumption))
        | (with_reducible apply obs_bind (hmem _ _ _); rintro ⟨Q, a⟩ ha)
        | (with_reducible exact obs_throw)
        | (with_reducible apply obs_any; intro value)
        | split
        | extract_lets
    clear_value byName
    have weaken {x : ElabM (SProg C × RawExpr)}
        (hx : Obs x (fun out => height out.2 = 1)) :
        Obs x (fun out => height out.2 ≤ height (.call f args)) := by
      intro sc st m out st' m' hr
      have := hx sc st m out st' m' hr
      have := height_pos (.call f args)
      omega
    have pureBound (P : SProg C) (a : RawExpr)
        (ha : height a ≤ height (.call f args)) :
        Obs (pure (P, a) : ElabM (SProg C × RawExpr))
          (fun out => height out.2 ≤ height (.call f args)) := obs_pure ha
    have named (g : String) (rest : List RawExpr)
        (hf : f = callValueName) (ha : args = .name g :: rest) :
        Obs (rc.hoist (.call g rest))
          (fun out => height out.2 ≤ height (.call f args)) := by
      subst f; subst args
      have hd := named_callee_decreases g rest
      have hp : height (.call g rest) < height (.call callValueName (.name g :: rest)) ∨
          height (.call g rest) = height (.call callValueName (.name g :: rest)) ∧
          (RawExpr.call g rest).nodes < (RawExpr.call callValueName (.name g :: rest)).nodes := by
        rcases Nat.lt_or_eq_of_le hd.1 with hlt | heq
        · exact Or.inl hlt
        · exact Or.inr ⟨heq, hd.2⟩
      intro sc st m out st' m' hr
      have := hh _ hp sc st m out st' m' hr
      omega
    have hvalue : ∀ u, Obs (byValue u)
        (fun out => height out.2 ≤ height (.call f args)) := by
      intro u
      simp -zeta only [byValue]
      repeat' first
        | (with_reducible exact weaken (hbyName _))
        | (with_reducible exact weaken (hname _ _))
        | (with_reducible exact pureBound _ _ (by assumption))
        | (with_reducible apply obs_bind (weaken (hmem _ _ _)); rintro ⟨Q, a⟩ ha)
        | (with_reducible apply obs_bind (named _ _ (by simpa only [beq_iff_eq] using ‹(f == callValueName) = true›) rfl); rintro ⟨Q, a⟩ ha)
        | (with_reducible exact obs_throw)
        | (with_reducible apply obs_any; intro value)
        | split
        | extract_lets
    clear_value byValue
    have hfinish : ∀ u, Obs (structFinish u) (fun out => height out.2 = 1) := by
      intro u
      simp -zeta only [structFinish]
      repeat' first
        | (with_reducible exact hname _ _)
        | (with_reducible exact obs_throw)
        | (with_reducible apply obs_any; intro value)
        | split
        | extract_lets
    clear_value structFinish
    have hbuild : ∀ u, Obs (structBuild u) (fun out => height out.2 = 1) := by
      intro u
      simp -zeta only [structBuild]
      repeat' first
        | (with_reducible exact hfinish _)
        | (with_reducible exact obs_throw)
        | (with_reducible apply obs_any; intro value)
        | split
        | extract_lets
    clear_value structBuild
    have hstructOrValue : ∀ u, Obs (structOrValue u)
        (fun out => height out.2 ≤ height (.call f args)) := by
      intro u
      simp -zeta only [structOrValue]
      repeat' first
        | (with_reducible exact weaken (hbuild _))
        | (with_reducible exact hvalue _)
        | (with_reducible exact obs_throw)
        | (with_reducible apply obs_any; intro value)
        | split
        | extract_lets
    clear_value structOrValue
    have hcast : ∀ u, Obs (castTail u)
        (fun out => height out.2 ≤ height (.call f args)) := by
      intro u
      simp -zeta only [castTail]
      repeat' first
        | (with_reducible exact hstructOrValue _)
        | (with_reducible exact weaken (hkeep _ _ (by assumption)))
        | (with_reducible apply obs_bind (castCapture_output_height C _ _); rintro ⟨Q, a⟩ ha)
        | (with_reducible exact obs_throw)
        | (with_reducible apply obs_any; intro value)
        | split
        | extract_lets
    clear_value castTail
    have henum : ∀ u, Obs (enumTail u)
        (fun out => height out.2 ≤ height (.call f args)) := by
      intro u
      simp -zeta only [enumTail]
      repeat' first
        | (with_reducible exact hcast _)
        | (with_reducible exact weaken (hkeep _ _ (by assumption)))
        | (with_reducible apply obs_bind (enumCapture_output_height C _ _); rintro ⟨Q, a⟩ ha)
        | (with_reducible exact obs_throw)
        | (with_reducible apply obs_any; intro value)
        | split
        | extract_lets
    clear_value enumTail
    have hH (a : RawExpr) (ha : height a < height (.call f args)) :
        Obs (rc.hoist a) (fun out => height out.2 ≤ height (.call f args)) := by
      intro sc st m out st' m' hr
      exact Nat.le_trans (hh a (Or.inl ha) sc st m out st' m' hr) (Nat.le_of_lt ha)
    have hbuiltin : ∀ u, Obs (builtinTail u)
        (fun out => height out.2 ≤ height (.call f args)) := by
      intro u
      simp -zeta only [builtinTail]
      apply obs_any
      intro scope
      extract_lets builtin addressTail decodeTail encodeTail selectorTail hashTail fallback
      have haddressTail : ∀ u, Obs (addressTail u)
          (fun out => height out.2 ≤ height (.call f args)) := by
        intro u
        simp -zeta only [addressTail]
        repeat' first
          | (with_reducible exact henum _)
          | (with_reducible exact pureBound _ _ (by omega))
          | (with_reducible apply obs_bind (addressCapture_height_bound C _); rintro ⟨Q, a⟩ ha)
          | (with_reducible apply obs_bind (hH _ (argument_lt_call f (by simp))); rintro ⟨Q, a⟩ ha)
          | (with_reducible exact obs_throw)
          | (with_reducible apply obs_any; intro value)
          | split
          | extract_lets
      clear_value addressTail
      have hdecodeTail : ∀ u, Obs (decodeTail u)
          (fun out => height out.2 ≤ height (.call f args)) := by
        intro u
        simp -zeta only [decodeTail]
        repeat' first
          | (with_reducible exact haddressTail _)
          | (with_reducible exact pureBound _ _ (by assumption))
          | (with_reducible apply obs_bind hdecode; rintro ⟨Q, a⟩ ha)
          | split
          | extract_lets
      clear_value decodeTail
      have hencodeTail : ∀ u, Obs (encodeTail u)
          (fun out => height out.2 ≤ height (.call f args)) := by
        intro u
        simp -zeta only [encodeTail]
        repeat' first
          | (with_reducible exact hdecodeTail _)
          | (with_reducible exact weaken (hkeep _ _ (by assumption)))
          | (with_reducible apply obs_bind (henc _ _ _ _ _); rintro ⟨Q, a⟩ ha)
          | (with_reducible apply obs_any; intro value)
          | split
          | extract_lets
      clear_value encodeTail
      have hselectorTail : ∀ u, Obs (selectorTail u)
          (fun out => height out.2 ≤ height (.call f args)) := by
        intro u
        simp -zeta only [selectorTail]
        repeat' first
          | (with_reducible exact hencodeTail _)
          | (with_reducible exact weaken (hkeep _ _ (by assumption)))
          | (with_reducible apply obs_bind (henc _ _ _ _ _); rintro ⟨Q, a⟩ ha)
          | (with_reducible exact obs_throw)
          | (with_reducible apply obs_any; intro value)
          | split
          | extract_lets
      clear_value selectorTail
      have hhashTail : ∀ u, Obs (hashTail u)
          (fun out => height out.2 ≤ height (.call f args)) := by
        intro u
        simp -zeta only [hashTail]
        repeat' first
          | (with_reducible exact hselectorTail _)
          | (with_reducible exact weaken (hkeep _ _ (by assumption)))
          | (with_reducible apply obs_bind hhash; rintro ⟨Q, a⟩ ha)
          | split
          | extract_lets
      clear_value hashTail
      have hfallback : ∀ u, Obs (fallback u)
          (fun out => height out.2 ≤ height (.call f args)) := by
        intro u
        simp -zeta only [fallback]
        split
        · rename_i hb
          have heq : f = "erc7201" := by
            simpa only [beq_iff_eq] using (Bool.and_eq_true_iff.mp hb).2
          exact obs_bind (herc heq) (fun out hout => obs_pure hout)
        · exact hhashTail _
      clear_value fallback
      split
      · rename_i hpref
        have hpref' : f.startsWith "#bytesPrefix" = true := (Bool.and_eq_true_iff.mp hpref).2
        split
        · rename_i n hnparse
          extract_lets prefixBody
          split
          · rename_i hn
            have hn' : n ≤ 32 := of_decide_eq_true (Bool.and_eq_true_iff.mp hn).2
            simp -zeta only [prefixBody]
            repeat' first
              | (with_reducible exact hfallback _)
              | (with_reducible exact pureBound _ _ (by assumption))
              | (with_reducible apply obs_bind (hH _ (prefix_cast_lt f _ n _ hpref' hn')); rintro ⟨Q, a⟩ ha)
              | (with_reducible exact obs_throw)
              | (with_reducible apply obs_any; intro value)
              | split
              | extract_lets
          · intro sc st m out st' m' hr
            cases hr
        · intro sc st m out st' m' hr
          cases hr
      · exact hfallback _
    clear_value builtinTail
    repeat' first
      | (with_reducible exact hbuiltin _)
      | (with_reducible exact weaken (hname _ _))
      | (with_reducible exact obs_throw)
      | (with_reducible apply obs_any; intro value)
      | split
      | extract_lets
  all_goals try (exfalso; contradiction)
  case h_10 =>
    rename_i b i n heq
    obtain ⟨rfl, rfl⟩ := RawExpr.call.inj heq
    exact bytes_index_output_height C rc (.call "#bytesIndex" [b, i, .num n]) b i n rfl
      (fun e he => hh e (Or.inl he))
  case h_11 =>
    rename_i off len k past heq
    obtain ⟨rfl, rfl⟩ := RawExpr.call.inj heq
    exact slice_index_output_height C rc (.call "#sliceIndex" [off, len, k, past]) off len k past rfl
      (fun e he => hh e (Or.inl he))
  case h_12 =>
    rename_i view k heq
    obtain ⟨rfl, rfl⟩ := RawExpr.call.inj heq
    exact slice_at_output_height_of_raw_bounds C rc (.call "#sliceAt" [view, k]) view k rfl hopen
      (fun e he => hh e (Or.inl he))
  case h_13 =>
    rename_i view heq
    obtain ⟨rfl, rfl⟩ := RawExpr.call.inj heq
    exact slice_length_output_height_of_raw_bounds C rc (.call "#sliceLength" [view]) view rfl hopen
      (fun e he => hh e (Or.inl he))
  case h_14 =>
    rename_i view rest h1 h2 h3 h4 heq
    obtain ⟨rfl, rfl⟩ := RawExpr.call.inj heq
    exact slice_decode_output_height_of_raw_bounds C rc (.call "#sliceDecode" (view :: rest)) view rest rfl hopen
      (fun e he => hh e (Or.inl he))
  case h_15 =>
    rename_i view h1 h2 heq
    obtain ⟨rfl, rfl⟩ := RawExpr.call.inj heq
    intro sc st m out st' m' hr
    have hn := sliceCopy_output_height C rc (.call "#sliceCopy" [view]) view rfl sc st m out st' m' hr
    have hp := height_pos (.call "#sliceCopy" [view])
    omega
  case h_16 =>
    rename_i xs h1 h2 h3 h4 h5 h6 heq
    obtain ⟨rfl, rfl⟩ := RawExpr.call.inj heq
    intro sc st m out st' m' hr
    have hn := array_output_height C rc (.call "#array" args) args rfl sc st m out st' m' hr
    have hp := height_pos (.call "#array" args)
    omega

  case h_21 => exact obs_pure (Nat.le_refl _)

end Solidity.ElabCallHeight

namespace Solidity.ElabCallHeight
open Semantics ElabSliceOpen
/-- The extracted producer's bound atoms have at most one field layer. -/
theorem boundAtom_height_le (e : RawExpr) (h : BoundAtom e) : height e ≤ 2 := by
  unfold BoundAtom at h
  split at h <;> simp_all only [height] <;> omega

/-- The H1280 extraction supplies the exact raw opening premise used by call bounds. -/
theorem inlineSliceOpen_raw_height
    (t : String) (b i j : RawExpr) (v : SliceView) (pre : List RawStmt)
    (h : inlineSliceOpen t (.call "#sliceRaw" [b, i, j]) = .ok (v, pre)) :
    height v.off ≤ 2 ∧ height v.len ≤ 3 := by
  obtain ⟨ho, hf⟩ := inlineSliceOpen_raw_atoms t b i j v pre h
  have ho := boundAtom_height_le v.off ho
  have hf := boundAtom_height_le v.fin hf
  have hl := sliceSub_height_le v.fin v.off
  exact ⟨ho, by simpa only [SliceView.len] using
    (show height (sliceSub v.fin v.off) ≤ 3 by omega)⟩

end Solidity.ElabCallHeight
