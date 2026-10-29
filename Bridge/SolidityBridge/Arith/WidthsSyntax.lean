import Solidity.Syntax.Elab

/-! Stable source-checker proof facts for the optional width adapter.
The monadic literal result stays abstract to avoid reducing its large bound. -/
namespace Solidity.Bridge.Arith.WidthsSyntax

theorem synth_head {C : Contract} (p : PrimTy) (name : String) (Γ : NCtx) :
    Solidity.synth C ((Var.ofName name, .val p) :: Γ) (.name name) =
      .ok (.val p (.simple (.local (.here : Idx (.val p :: Γ.ctx) (.val p))))) := by
  simp only [synth, NCtx.lookupTy, if_true, NCtx.idx, NCtx.find, Except.map,
    dite_true, pure, Except.pure, bind, Except.bind]

private theorem transport_ne {α β : Type} (f : α → β) {e n : α} {y : β}
    (h : f e = y) (hn : f n ≠ y) : e ≠ n :=
  fun he => hn ((congrArg f he).symm.trans h)

/-- Keep the result abstract: reducing a generic literal range check here
forces the large word bound during kernel conversion. -/
private theorem uint_source_not_int {C : Contract} {Γ : Ctx}
    (r : Except String (Simple C Γ .uint)) (v : Val C Γ .int) :
    (do pure (TExpr.val .uint (.simple (← r)))) ≠ .ok (.val .int v) := by
  intro h
  have ht := congrArg (fun res : Except String (TExpr C Γ) => res.toOption.map TExpr.ty) h
  cases r with
  | error err =>
    change (none : Option Ty) = some (Ty.prim .int) at ht
    cases ht
  | ok a =>
    change some (Ty.prim .uint) = some (Ty.prim .int) at ht
    cases ht

private theorem synth_num_not_int [FreshNames] {C : Contract} {Γ : NCtx}
    (n : Nat) (v : Val C Γ.ctx .int) :
    Solidity.synth C Γ (.num n) ≠ .ok (.val .int v) := by
  have heq : Solidity.synth C Γ (.num n) =
      (do pure (TExpr.val .uint (.simple (← litAt C Γ .uint (n : Int))))) := by
    rw [synth]
  intro h
  exact uint_source_not_int (litAt C Γ .uint (n : Int)) v (heq.symm.trans h)

private theorem unary_not_negative_literal [FreshNames] {C : Contract} {Γ : NCtx}
    (p : PrimTy) (e : RawExpr) (v : Val C Γ.ctx p) (op : UnOp)
    (ha : op.accepts p = true) (hs : Solidity.synth C Γ e = .ok (.val p v)) :
    ∀ n, op = .neg → e ≠ .num n := by
  intro n hop
  cases op with
  | neg =>
    cases p with
    | bool => cases ha
    | uint => cases ha
    | int => exact transport_ne (Solidity.synth C Γ) hs (synth_num_not_int n v)
  | not => cases hop
  | bnot => cases hop
  | toInt => cases hop
  | toUint => cases hop

theorem synth_unary {C : Contract} {Γ : NCtx} (p : PrimTy) (e : RawExpr)
    (v : Val C Γ.ctx p) (op : UnOp) (ha : op.accepts p = true)
    (hs : Solidity.synth C Γ e = .ok (.val p v)) :
    Solidity.synth C Γ (.unop op e) =
      .ok (.val (op.ret p) (.unop op ha rfl v)) := by
  have overlap := unary_not_negative_literal p e v op ha hs
  rw [synth, hs]
  simp only [bind, Except.bind, TExpr.toVal?]
  split
  · rfl
  · rename_i hf
    rw [ha] at hf
    cases hf
  · exact overlap

/-- info: 'Solidity.Bridge.Arith.WidthsSyntax.synth_head' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms synth_head
/-- info: 'Solidity.Bridge.Arith.WidthsSyntax.synth_unary' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms synth_unary
end Solidity.Bridge.Arith.WidthsSyntax
