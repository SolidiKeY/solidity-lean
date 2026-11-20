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
