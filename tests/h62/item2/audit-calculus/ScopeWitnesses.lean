import Solidity.Calculus.TermWk
import Solidity.Calculus.Shift
import tests.h62.item2.«audit-calculus».KernelCensus

/-! Joint fixtures for all source declarations in TermWk/Shift. The weakening
adds a real Boolean local, retains an existing uint local and uses actual
typed storage roots and memory-array paths. These are scoped syntax/semantic
transport witnesses, not source compilation or gas/fork adequacy. -/
namespace H62.AuditCalculus.Scope
open Solidity

private def C : Contract :=
  { vars := [("x", .prim .uint), ("a", .ref (.array (.prim .uint)))] }

private def word7 : PrimTy.uint.Denote := ⟨7, by decide⟩
private def t7 (Γ : Ctx) : Tm C Γ (.val .uint) := .app0 (.lit (p := .uint) word7)
private def t9 (Γ : Ctx) : Tm C Γ (.val .uint) := .app0 (.lit (p := .uint) ⟨9, by decide⟩)
private def baseState : State C [.val .uint] := (State.init C).push word7
private def shiftedState : State C [.val .bool, .val .uint] := baseState.push true
private def memoryPath : MPath C [.mem (.array (.prim .uint))] (.ref (.array (.prim .uint))) :=
  .var .here rfl
private def memoryLoc : MLoc C [.mem (.array (.prim .uint))] (.prim .uint) :=
  .index .dyn memoryPath (.simple (.lit 0 rfl))

#joint_premises Solidity.Tm.wk_pvV as case_1_premises
/-- One closed dependent witness for the exact original telescope. -/
theorem case_1_joint : case_1_premises := ⟨C, [.val .uint], [.val .bool, .val .uint], Thin.drop .refl, .uint, .here, True.intro⟩

#joint_premises Solidity.Tm.wk_pvP as case_2_premises
/-- One closed dependent witness for the exact original telescope. -/
theorem case_2_joint : case_2_premises := ⟨C, [.alias (.array (.prim .uint))], [.val .bool, .alias (.array (.prim .uint))], Thin.drop .refl, (.array (.prim .uint)), .here, True.intro⟩

#joint_premises Solidity.Tm.wk_pvS as case_3_premises
/-- One closed dependent witness for the exact original telescope. -/
theorem case_3_joint : case_3_premises := ⟨C, [.old], [.val .bool, .old], Thin.drop .refl, .here, True.intro⟩

#joint_premises Solidity.Tm.wk_pvI as case_4_premises
/-- One closed dependent witness for the exact original telescope. -/
theorem case_4_joint : case_4_premises := ⟨C, [.mem (.array (.prim .uint))], [.val .bool, .mem (.array (.prim .uint))], Thin.drop .refl, (.array (.prim .uint)), .here, True.intro⟩

#joint_premises Solidity.Tm.wk_netOf as case_5_premises
/-- One closed dependent witness for the exact original telescope. -/
theorem case_5_joint : case_5_premises := ⟨C, [.oldNet], [.val .bool, .oldNet], Thin.drop .refl, .here, t7 _, True.intro⟩

#joint_premises Solidity.Tm.wk_app0 as case_6_premises
/-- One closed dependent witness for the exact original telescope. -/
theorem case_6_joint : case_6_premises := ⟨C, [.val .uint], [.val .bool, .val .uint], Thin.drop .refl, .val .uint, .lit (p := .uint) word7, True.intro⟩

#joint_premises Solidity.Tm.wk_app1 as case_7_premises
/-- One closed dependent witness for the exact original telescope. -/
theorem case_7_joint : case_7_premises := ⟨C, [.val .uint], [.val .bool, .val .uint], Thin.drop .refl, .val .uint, .val .uint, .delValue, t7 _, True.intro⟩

#joint_premises Solidity.Tm.wk_app2 as case_8_premises
/-- One closed dependent witness for the exact original telescope. -/
theorem case_8_joint : case_8_premises := ⟨C, [.val .uint], [.val .bool, .val .uint], Thin.drop .refl, .kint, .kint, .kint, .zbin .add rfl, .app0 (.zlit 1), .app0 (.zlit 2), True.intro⟩

#joint_premises Solidity.Tm.wk_app3 as case_9_premises
/-- One closed dependent witness for the exact original telescope. -/
theorem case_9_joint : case_9_premises := ⟨C, [.val .uint], [.val .bool, .val .uint], Thin.drop .refl, .val .bool, .val .uint, .val .uint, .val .uint, .ite, .app0 (.lit (p := .bool) true), t7 _, t9 _, True.intro⟩

#joint_premises Solidity.Tm.wk_pvZ as case_10_premises
/-- One closed dependent witness for the exact original telescope. -/
theorem case_10_joint : case_10_premises := ⟨C, [.kint], [.val .bool, .kint], Thin.drop .refl, .here, True.intro⟩

#joint_premises Solidity.Tm.eval_wk as case_11_premises
/-- One closed dependent witness for the exact original telescope. -/
theorem case_11_joint : case_11_premises := ⟨C, [.val .uint], [.val .bool, .val .uint], Thin.drop .refl, shiftedState, .val .uint, .pvV .here, True.intro⟩

#joint_premises Solidity.Tm.denote_wk as case_12_premises
/-- One closed dependent witness for the exact original telescope. -/
theorem case_12_joint : case_12_premises := ⟨C, [.val .uint], [.val .bool, .val .uint], Thin.drop .refl, shiftedState, .val .uint, .pvV .here, True.intro⟩

#joint_premises Solidity.Tm.castV_wk as case_13_premises
/-- One closed dependent witness for the exact original telescope. -/
theorem case_13_joint : case_13_premises := ⟨C, [.val .uint], [.val .bool, .val .uint], Thin.drop .refl, .uint, .uint, rfl, .pvV .here, True.intro⟩

#joint_premises Solidity.Simple.lower_wk as case_14_premises
/-- One closed dependent witness for the exact original telescope. -/
theorem case_14_joint : case_14_premises := ⟨C, [.val .uint], [.val .bool, .val .uint], Thin.drop .refl, .uint, .local .here, True.intro⟩

#joint_premises Solidity.SPath.lower_wk as case_15_premises
/-- One closed dependent witness for the exact original telescope. -/
theorem case_15_joint : case_15_premises := ⟨C, [.val .uint], [.val .bool, .val .uint], Thin.drop .refl, .prim .uint, .loc (.root "x" rfl), True.intro⟩

#joint_premises Solidity.Loc.lower_wk as case_16_premises
/-- One closed dependent witness for the exact original telescope. -/
theorem case_16_joint : case_16_premises := ⟨C, [.val .uint], [.val .bool, .val .uint], Thin.drop .refl, .prim .uint, .root "x" rfl, True.intro⟩

#joint_premises Solidity.MPath.lower_wk as case_17_premises
/-- One closed dependent witness for the exact original telescope. -/
theorem case_17_joint : case_17_premises := ⟨C, [.mem (.array (.prim .uint))], [.val .bool, .mem (.array (.prim .uint))], Thin.drop .refl, .ref (.array (.prim .uint)), memoryPath, True.intro⟩

#joint_premises Solidity.MLoc.lower_wk as case_18_premises
/-- One closed dependent witness for the exact original telescope. -/
theorem case_18_joint : case_18_premises := ⟨C, [.mem (.array (.prim .uint))], [.val .bool, .mem (.array (.prim .uint))], Thin.drop .refl, .prim .uint, memoryLoc, True.intro⟩

#joint_premises Solidity.Val.lower_wk as case_19_premises
/-- One closed dependent witness for the exact original telescope. -/
theorem case_19_joint : case_19_premises := ⟨C, [.val .uint], [.val .bool, .val .uint], Thin.drop .refl, .uint, .simple (.local .here), True.intro⟩

#joint_premises Solidity.Val.lower_denote_up as case_20_premises
/-- One closed dependent witness for the exact original telescope. -/
theorem case_20_joint : case_20_premises := ⟨C, [.val .uint], .val .bool, .uint, .simple (.local .here), baseState, true, True.intro⟩

#joint_premises Solidity.Idx.up_eq as case_21_premises
/-- One closed dependent witness for the exact original telescope. -/
theorem case_21_joint : case_21_premises := ⟨[.val .uint], .val .uint, .val .bool, .here, True.intro⟩

#joint_premises Solidity.Simple.up_eq as case_22_premises
/-- One closed dependent witness for the exact original telescope. -/
theorem case_22_joint : case_22_premises := ⟨C, [.val .uint], .val .bool, .uint, .local .here, True.intro⟩

#joint_premises Solidity.SPath.up_eq as case_23_premises
/-- One closed dependent witness for the exact original telescope. -/
theorem case_23_joint : case_23_premises := ⟨C, [.val .uint], .val .bool, .prim .uint, .loc (.root "x" rfl), True.intro⟩

#joint_premises Solidity.Loc.up_eq as case_24_premises
/-- One closed dependent witness for the exact original telescope. -/
theorem case_24_joint : case_24_premises := ⟨C, [.val .uint], .val .bool, .prim .uint, .root "x" rfl, True.intro⟩

#joint_premises Solidity.MPath.up_eq as case_25_premises
/-- One closed dependent witness for the exact original telescope. -/
theorem case_25_joint : case_25_premises := ⟨C, [.mem (.array (.prim .uint))], .val .bool, .ref (.array (.prim .uint)), memoryPath, True.intro⟩

#joint_premises Solidity.MLoc.up_eq as case_26_premises
/-- One closed dependent witness for the exact original telescope. -/
theorem case_26_joint : case_26_premises := ⟨C, [.mem (.array (.prim .uint))], .val .bool, .prim .uint, memoryLoc, True.intro⟩

#joint_premises Solidity.Val.up_eq as case_27_premises
/-- One closed dependent witness for the exact original telescope. -/
theorem case_27_joint : case_27_premises := ⟨C, [.val .uint], .val .bool, .uint, .simple (.local .here), True.intro⟩

#joint_premises Solidity.ARhs.up_eq as case_28_premises
/-- One closed dependent witness for the exact original telescope. -/
theorem case_28_joint : case_28_premises := ⟨C, [.val .uint], .val .bool, (.array (.prim .uint)), .path (.loc (.root "a" rfl)), True.intro⟩

#joint_premises Solidity.Src.up_eq as case_29_premises
/-- One closed dependent witness for the exact original telescope. -/
theorem case_29_joint : case_29_premises := ⟨C, [.val .uint], .val .bool, .prim .uint, .val (.simple (.local .here)), True.intro⟩

#joint_premises Solidity.MSrc.up_eq as case_30_premises
/-- One closed dependent witness for the exact original telescope. -/
theorem case_30_joint : case_30_premises := ⟨C, [.val .uint], .val .bool, .prim .uint, .val (.simple (.local .here)), True.intro⟩

#joint_premises Solidity.MRhs.up_eq as case_31_premises
/-- One closed dependent witness for the exact original telescope. -/
theorem case_31_joint : case_31_premises := ⟨C, [.mem (.array (.prim .uint))], .val .bool, (.array (.prim .uint)), .alias memoryPath, True.intro⟩

#joint_premises Solidity.NewLhs.up_eq as case_32_premises
/-- One closed dependent witness for the exact original telescope. -/
theorem case_32_joint : case_32_premises := ⟨C, [.val .uint], .val .bool, (.array (.prim .uint)), .store (.root "a" rfl), True.intro⟩

#joint_premises Solidity.OpLoc.up_eq as case_33_premises
/-- One closed dependent witness for the exact original telescope. -/
theorem case_33_joint : case_33_premises := ⟨C, [.val .uint], .val .bool, .uint, .local .here, True.intro⟩

#verify_joint Solidity.Tm.wk_pvV with case_1_joint
#verify_joint Solidity.Tm.wk_pvP with case_2_joint
#verify_joint Solidity.Tm.wk_pvS with case_3_joint
#verify_joint Solidity.Tm.wk_pvI with case_4_joint
#verify_joint Solidity.Tm.wk_netOf with case_5_joint
#verify_joint Solidity.Tm.wk_app0 with case_6_joint
#verify_joint Solidity.Tm.wk_app1 with case_7_joint
#verify_joint Solidity.Tm.wk_app2 with case_8_joint
#verify_joint Solidity.Tm.wk_app3 with case_9_joint
#verify_joint Solidity.Tm.wk_pvZ with case_10_joint
#verify_joint Solidity.Tm.eval_wk with case_11_joint
#verify_joint Solidity.Tm.denote_wk with case_12_joint
#verify_joint Solidity.Tm.castV_wk with case_13_joint
#verify_joint Solidity.Simple.lower_wk with case_14_joint
#verify_joint Solidity.SPath.lower_wk with case_15_joint
#verify_joint Solidity.Loc.lower_wk with case_16_joint
#verify_joint Solidity.MPath.lower_wk with case_17_joint
#verify_joint Solidity.MLoc.lower_wk with case_18_joint
#verify_joint Solidity.Val.lower_wk with case_19_joint
#verify_joint Solidity.Val.lower_denote_up with case_20_joint
#verify_joint Solidity.Idx.up_eq with case_21_joint
#verify_joint Solidity.Simple.up_eq with case_22_joint
#verify_joint Solidity.SPath.up_eq with case_23_joint
#verify_joint Solidity.Loc.up_eq with case_24_joint
#verify_joint Solidity.MPath.up_eq with case_25_joint
#verify_joint Solidity.MLoc.up_eq with case_26_joint
#verify_joint Solidity.Val.up_eq with case_27_joint
#verify_joint Solidity.ARhs.up_eq with case_28_joint
#verify_joint Solidity.Src.up_eq with case_29_joint
#verify_joint Solidity.MSrc.up_eq with case_30_joint
#verify_joint Solidity.MRhs.up_eq with case_31_joint
#verify_joint Solidity.NewLhs.up_eq with case_32_joint
#verify_joint Solidity.OpLoc.up_eq with case_33_joint

end H62.AuditCalculus.Scope
