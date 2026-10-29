import Solidity.Syntax.Splice
import Solidity.Syntax.Elab
import Solidity.Semantics.Run

/-! Concrete current-elaborator obstruction to the old generic Widths helper.
No theorem from the failing Widths module is imported. -/
namespace Solidity.Bridge.Arith.WidthsObstructions

abbrev shiftContext : NCtx :=
  [(Var.ofName "x", .val .int)]

def leftValue {C : Contract} : Val C shiftContext.ctx .int := .simple (.local .here)
def rightValue {C : Contract} : Val C shiftContext.ctx .int := .simple (.local .here)

/-- All premises of the existing generic synth_binary helper have inhabitants. -/
theorem signed_shift_premises (C : Contract) :
    BinOp.shr.accepts .int = true ∧
    (RawExpr.name "x").constRat? = none ∧
    (RawExpr.name "x").isLit = false ∧
    Solidity.synth C shiftContext (.name "x") = .ok (.val .int leftValue) ∧
    Solidity.check C shiftContext .int (.name "x") = .ok leftValue ∧
    Solidity.check C shiftContext .int (.name "x") = .ok rightValue := by
  have hs : Solidity.synth C shiftContext (.name "x") = .ok (.val .int leftValue) := by
    simp only [synth, shiftContext, NCtx.lookupTy, NCtx.idx, NCtx.find, Except.map,
      bind, Except.bind, pure, Except.pure, if_true, dite_true]
    rfl
  have hv : Solidity.check C shiftContext .int (.name "x") = .ok leftValue := by
    simp only [Solidity.check, checkVia, hs, TExpr.toVal?, bind, Except.bind,
      dite_true, pure, Except.pure]
  exact ⟨rfl, rfl, rfl, hs, hv, hv⟩


/-- Signed shifts check the right operand as uint; an int local is refused. -/
theorem actual_signed_shift_refusal (C : Contract) :
    (Solidity.synth C shiftContext (.binop .shr (.name "x") (.name "x"))).toOption = none := by
  simp only [synth, Solidity.check, checkVia, shiftContext, NCtx.lookupTy, NCtx.idx, NCtx.find,
    RawExpr.constRat?, RawExpr.isLit, TExpr.toVal?, List.map_cons, List.map_nil,
    bind, Except.bind, pure, Except.pure, Except.map, if_true, dite_true]
  rfl

/-- This is exactly the claimed conclusion of synth_binary at the inhabited
premises above, and the current evaluator disproves it. -/
theorem signed_shift_counterexample (C : Contract) :
    Solidity.synth C shiftContext (.binop .shr (.name "x") (.name "x")) ≠
      .ok (.val .int (.binop .shr rfl rfl leftValue rightValue)) := by
  intro h
  have he := congrArg Except.toOption h
  rw [actual_signed_shift_refusal] at he
  cases he

/-- info: 'Solidity.Bridge.Arith.WidthsObstructions.signed_shift_premises' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms signed_shift_premises
/-- info: 'Solidity.Bridge.Arith.WidthsObstructions.actual_signed_shift_refusal' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms actual_signed_shift_refusal
/-- info: 'Solidity.Bridge.Arith.WidthsObstructions.signed_shift_counterexample' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms signed_shift_counterexample

def literalShift {C : Contract} (n : Int) (h : PrimTy.int.inRange n = true) :
    TExpr C shiftContext.ctx :=
  .val .int (.binop .shr rfl rfl leftValue (.simple (.lit n h)))

theorem literal_shift_premises (C : Contract) :
    BinOp.shr.accepts .int = true ∧ PrimTy.int.inRange (257 : Int) = true ∧
    (RawExpr.name "x").constRat? = none ∧ (RawExpr.name "x").isLit = false ∧
    Solidity.synth C shiftContext (.name "x") = .ok (.val .int leftValue) ∧
    Solidity.check C shiftContext .int (.name "x") = .ok leftValue := by
  exact ⟨rfl, by decide, rfl, rfl, (signed_shift_premises C).2.2.2.1,
    (signed_shift_premises C).2.2.2.2.1⟩

theorem actual_literal_shift (C : Contract) :
    Solidity.synth C shiftContext (.binop .shr (.name "x") (.num 257)) =
      .ok (literalShift 256 (by decide)) := by
  have hs := (signed_shift_premises C).2.2.2.1
  have hv := (signed_shift_premises C).2.2.2.2.1
  simp only [synth, RawExpr.constRat?, RawExpr.isLit, hs, TExpr.toVal?,
    Solidity.check, hv, RawExpr.litVal?, bind, Except.bind, pure, Except.pure]
  rfl

theorem literal_shift_counterexample (C : Contract) :
    Solidity.synth C shiftContext (.binop .shr (.name "x") (.num 257)) ≠
      .ok (literalShift 257 (by decide)) := by
  rw [actual_literal_shift]
  intro h
  cases h

/-- info: 'Solidity.Bridge.Arith.WidthsObstructions.literal_shift_premises' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms literal_shift_premises
/-- info: 'Solidity.Bridge.Arith.WidthsObstructions.actual_literal_shift' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms actual_literal_shift
/-- info: 'Solidity.Bridge.Arith.WidthsObstructions.literal_shift_counterexample' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms literal_shift_counterexample

/-- The inputs are jointly inhabited in a concrete empty contract. -/
theorem inhabited_counterexample :
    ∃ C : Contract,
      BinOp.shr.accepts .int = true ∧
      (RawExpr.name "x").constRat? = none ∧
      (RawExpr.name "x").isLit = false ∧
      Solidity.synth C shiftContext (.name "x") = .ok (.val .int leftValue) ∧
      Solidity.check C shiftContext .int (.name "x") = .ok leftValue ∧
      Solidity.check C shiftContext .int (.name "x") = .ok rightValue ∧
      Solidity.synth C shiftContext (.binop .shr (.name "x") (.name "x")) ≠
        .ok (.val .int (.binop .shr rfl rfl leftValue rightValue)) := by
  let C : Contract := contract!{}
  rcases signed_shift_premises C with ⟨ha, hc, hl, hs, hv, hw⟩
  exact ⟨C, ha, hc, hl, hs, hv, hw, signed_shift_counterexample C⟩

/-- info: 'Solidity.Bridge.Arith.WidthsObstructions.inhabited_counterexample' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms inhabited_counterexample

/-- The original generic binary helper's exact contract, as a proposition. -/
def OldSynthBinary : Prop :=
  ∀ (C : Contract) (Γ : NCtx) (p : PrimTy) (e b : RawExpr)
    (v w : Val C Γ.ctx p) (op : BinOp) (ha : op.accepts p = true),
    e.constRat? = none → e.isLit = false →
    Solidity.synth C Γ e = .ok (.val p v) →
    Solidity.check C Γ p e = .ok v → Solidity.check C Γ p b = .ok w →
    Solidity.synth C Γ (.binop op e b) =
      .ok (.val (op.ret p) (.binop op ha rfl v w))

theorem not_old_synth_binary : ¬ OldSynthBinary := by
  intro claim
  let C : Contract := contract!{}
  rcases signed_shift_premises C with ⟨ha, hc, hl, hs, hv, hw⟩
  exact signed_shift_counterexample C
    (claim C shiftContext .int (.name "x") (.name "x") leftValue rightValue .shr
      ha hc hl hs hv hw)

/-- The original literal helper's exact contract, as a proposition. -/
def OldSynthBinLiteral : Prop :=
  ∀ (C : Contract) (Γ : NCtx) (p : PrimTy) (e : RawExpr)
    (v : Val C Γ.ctx p) (op : BinOp) (k : Nat) (ha : op.accepts p = true)
    (hk : p.inRange (k : Int) = true),
    e.constRat? = none → e.isLit = false →
    Solidity.synth C Γ e = .ok (.val p v) →
    Solidity.check C Γ p e = .ok v →
    Solidity.synth C Γ (.binop op e (.num k)) =
      .ok (.val (op.ret p) (.binop op ha rfl v (.simple (.lit k hk))))

theorem not_old_synth_bin_literal : ¬ OldSynthBinLiteral := by
  intro claim
  let C : Contract := contract!{}
  rcases literal_shift_premises C with ⟨ha, hk, hc, hl, hs, hv⟩
  exact literal_shift_counterexample C
    (claim C shiftContext .int (.name "x") leftValue .shr 257 ha hk hc hl hs hv)

/-- info: 'Solidity.Bridge.Arith.WidthsObstructions.not_old_synth_binary' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms not_old_synth_binary
/-- info: 'Solidity.Bridge.Arith.WidthsObstructions.not_old_synth_bin_literal' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms not_old_synth_bin_literal


abbrev uintContext : NCtx := [(Var.ofName "x", .val .uint)]
def uintValue {C : Contract} : Val C uintContext.ctx .uint := .simple (.local .here)

/-- The unsigned source path keeps its literal count, unlike signed SHR. -/
theorem unsigned_shift_257 (C : Contract) :
    Solidity.synth C uintContext (.binop .shr (.name "x") (.num 257)) =
      .ok (.val .uint (.binop .shr rfl rfl uintValue
        (.simple (.lit 257 (by decide))))) := by
  simp only [synth, Solidity.check, checkVia, uintContext, NCtx.lookupTy, NCtx.idx,
    NCtx.find, RawExpr.constRat?, RawExpr.isLit, TExpr.toVal?, Except.map,
    bind, Except.bind, pure, Except.pure, if_true, dite_true]
  rfl

/-- The narrow 8-bit reduction remains the ordinary uint modulo source path. -/
theorem narrow_modulo_control (C : Contract) :
    Solidity.synth C uintContext (.binop .mod (.name "x") (.num 256)) =
      .ok (.val .uint (.binop .mod rfl rfl uintValue
        (.simple (.lit 256 (by decide))))) := by
  simp only [synth, Solidity.check, checkVia, uintContext, NCtx.lookupTy, NCtx.idx,
    NCtx.find, RawExpr.constRat?, RawExpr.isLit, TExpr.toVal?, Except.map,
    bind, Except.bind, pure, Except.pure, if_true, dite_true]
  rfl

/-- Full-word signed-to-unsigned conversion still resolves the int local. -/
theorem signed_cast_control (C : Contract) :
    Solidity.synth C shiftContext (.unop .toUint (.name "x")) =
      .ok (.val .uint (.unop .toUint rfl rfl leftValue)) := by
  simp only [synth, shiftContext, NCtx.lookupTy, NCtx.idx, NCtx.find,
    TExpr.toVal?, Except.map, bind, Except.bind, pure, Except.pure, if_true, dite_true]
  rfl

/-- Negative numeric literals use the signed literal clause, not generic negation. -/
theorem negative_literal_control (C : Contract) :
    Solidity.synth C shiftContext (.unop .neg (.num 1)) =
      .ok (.val .int (.simple (.lit (-1) (by decide)))) := by
  simp only [synth]
  rfl

/-- info: 'Solidity.Bridge.Arith.WidthsObstructions.unsigned_shift_257' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms unsigned_shift_257
/-- info: 'Solidity.Bridge.Arith.WidthsObstructions.narrow_modulo_control' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms narrow_modulo_control
/-- info: 'Solidity.Bridge.Arith.WidthsObstructions.signed_cast_control' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms signed_cast_control
/-- info: 'Solidity.Bridge.Arith.WidthsObstructions.negative_literal_control' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms negative_literal_control

end Solidity.Bridge.Arith.WidthsObstructions
