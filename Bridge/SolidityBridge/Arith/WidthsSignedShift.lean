import SolidityBridge.Arith.Widths
import Solidity.Syntax.Splice

/-! The actual source checker's signed SHR branch, separate from the generic
homogeneous operator helpers. Counts are checked as uint before saturation. -/
namespace Solidity.Bridge.Arith.WidthsSignedShift

def boundedCount {C : Contract} {Γ : Ctx} (w : Val C Γ .uint)
    (limit : Simple C Γ .uint) : Val C Γ .int :=
  .unop .toInt rfl rfl (.ternary (.binop .lt rfl rfl w (.simple limit)) w (.simple limit))

theorem synth_literal {C : Contract} {Γ : NCtx} (e b : RawExpr)
    (v : Val C Γ.ctx .int) (w : Val C Γ.ctx .uint) (n : Int)
    (count : Simple C Γ.ctx .int)
    (hc : e.constRat? = none) (hl : e.isLit = false)
    (hs : Solidity.synth C Γ e = .ok (.val .int v))
    (hv : Solidity.check C Γ .int e = .ok v)
    (hw : Solidity.check C Γ .uint b = .ok w)
    (hb : b.litVal? = some n)
    (hcount : litAt C Γ .int (min n 256) = .ok count) :
    Solidity.synth C Γ (.binop .shr e b) =
      .ok (.val .int (.binop .shr rfl rfl v (.simple count))) := by
  unfold synth
  simp only [RawExpr.constRat?, hc, hl, Bool.false_and, Bool.false_eq_true,
    if_false, hs, TExpr.toVal?, bind, Except.bind, pure, Except.pure, hv, hw, hb, hcount]
  rfl

theorem synth_nonliteral {C : Contract} {Γ : NCtx} (e b : RawExpr)
    (v : Val C Γ.ctx .int) (w : Val C Γ.ctx .uint)
    (limit : Simple C Γ.ctx .uint)
    (hc : e.constRat? = none) (hl : e.isLit = false)
    (hs : Solidity.synth C Γ e = .ok (.val .int v))
    (hv : Solidity.check C Γ .int e = .ok v)
    (hw : Solidity.check C Γ .uint b = .ok w)
    (hb : b.litVal? = none)
    (hlimit : litAt C Γ .uint 256 = .ok limit) :
    Solidity.synth C Γ (.binop .shr e b) =
      .ok (.val .int (.binop .shr rfl rfl v (boundedCount w limit))) := by
  unfold synth
  simp only [RawExpr.constRat?, hc, hl, Bool.false_and, Bool.false_eq_true,
    if_false, hs, TExpr.toVal?, bind, Except.bind, pure, Except.pure, hv, hw, hb, hlimit]
  rfl

/-- Source checking at int goes through the same synthesized signed-SHR path. -/
theorem check_of_synth {C : Contract} {Γ : NCtx} (e b : RawExpr)
    (v : Val C Γ.ctx .int) (hc : e.constRat? = none) (hl : e.isLit = false)
    (hs : Solidity.synth C Γ (.binop .shr e b) = .ok (.val .int v)) :
    Solidity.check C Γ .int (.binop .shr e b) = .ok v := by
  unfold Solidity.check
  simp only [RawExpr.constRat?, hc, hl, Bool.false_and, Bool.false_eq_true,
    if_false, checkVia, hs, bind, Option.bind, Except.bind, TExpr.toVal?, dite_true, pure, Except.pure]

abbrev context : NCtx := [(Var.ofName "x", .val .int)]
def left {C : Contract} : Val C context.ctx .int := .simple (.local .here)
def castCount {C : Contract} : Val C context.ctx .uint := .unop .toUint rfl rfl left

/-- Inhabited nonliteral count setup: the source casts the int local to uint. -/
theorem nonliteral_control (C : Contract) :
    Solidity.synth C context (.binop .shr (.name "x") (.unop .toUint (.name "x"))) =
      .ok (.val .int (.binop .shr rfl rfl left
        (boundedCount castCount (.lit 256 (by decide))))) := by
  apply synth_nonliteral (.name "x") (.unop .toUint (.name "x")) left castCount
    (.lit 256 (by decide)) rfl rfl
  · exact WidthsSyntax.synth_head .int "x" []
  · exact Widths.check_head .int "x" []
  · exact Widths.check_unary .int (.name "x") left .toUint rfl rfl
      (WidthsSyntax.synth_head .int "x" [])
  · rfl
  · exact Widths.litAt_of_range .uint 256 (by decide)

/-- All boundary controls have an actual concrete contract and typed input. -/
theorem inhabited_controls :
    ∃ C : Contract,
      (∀ k ∈ [0, 255, 256, 257],
        ∃ v : Val C context.ctx .int,
          Solidity.check C context .int (.binop .shr (.name "x") (.num k)) = .ok v) ∧
      (∃ v : Val C context.ctx .int,
        Solidity.check C context .int
          (.binop .shr (.name "x") (.unop .toUint (.name "x"))) = .ok v) := by
  refine ⟨contract!{}, ?_, ?_⟩
  · intro k hk
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hk
    rcases hk with rfl | rfl | rfl | rfl
    · refine ⟨.binop .shr rfl rfl left (.simple (.lit 0 (by decide))), ?_⟩
      apply check_of_synth (.name "x") (.num 0) _ rfl rfl
      apply synth_literal (.name "x") (.num 0) left (.simple (.lit 0 (by decide))) 0
        (.lit 0 (by decide)) rfl rfl
      · exact WidthsSyntax.synth_head .int "x" []
      · exact Widths.check_head .int "x" []
      · simp only [Solidity.check]
        rfl
      · rfl
      · exact Widths.litAt_of_range .int _ (by decide)
    · refine ⟨.binop .shr rfl rfl left (.simple (.lit 255 (by decide))), ?_⟩
      apply check_of_synth (.name "x") (.num 255) _ rfl rfl
      apply synth_literal (.name "x") (.num 255) left (.simple (.lit 255 (by decide))) 255
        (.lit 255 (by decide)) rfl rfl
      · exact WidthsSyntax.synth_head .int "x" []
      · exact Widths.check_head .int "x" []
      · simp only [Solidity.check]
        rfl
      · rfl
      · exact Widths.litAt_of_range .int _ (by decide)
    · refine ⟨.binop .shr rfl rfl left (.simple (.lit 256 (by decide))), ?_⟩
      apply check_of_synth (.name "x") (.num 256) _ rfl rfl
      apply synth_literal (.name "x") (.num 256) left (.simple (.lit 256 (by decide))) 256
        (.lit 256 (by decide)) rfl rfl
      · exact WidthsSyntax.synth_head .int "x" []
      · exact Widths.check_head .int "x" []
      · simp only [Solidity.check]
        rfl
      · rfl
      · exact Widths.litAt_of_range .int _ (by decide)
    · refine ⟨.binop .shr rfl rfl left (.simple (.lit 256 (by decide))), ?_⟩
      apply check_of_synth (.name "x") (.num 257) _ rfl rfl
      apply synth_literal (.name "x") (.num 257) left (.simple (.lit 257 (by decide))) 257
        (.lit 256 (by decide)) rfl rfl
      · exact WidthsSyntax.synth_head .int "x" []
      · exact Widths.check_head .int "x" []
      · simp only [Solidity.check]
        rfl
      · rfl
      · exact Widths.litAt_of_range .int _ (by decide)
  · exact ⟨_, check_of_synth (.name "x") _ _ rfl rfl (nonliteral_control _)⟩

/-- info: 'Solidity.Bridge.Arith.WidthsSignedShift.synth_literal' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms synth_literal
/-- info: 'Solidity.Bridge.Arith.WidthsSignedShift.synth_nonliteral' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms synth_nonliteral
/-- info: 'Solidity.Bridge.Arith.WidthsSignedShift.check_of_synth' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms check_of_synth
/-- info: 'Solidity.Bridge.Arith.WidthsSignedShift.nonliteral_control' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms nonliteral_control
/-- info: 'Solidity.Bridge.Arith.WidthsSignedShift.inhabited_controls' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms inhabited_controls
end Solidity.Bridge.Arith.WidthsSignedShift
