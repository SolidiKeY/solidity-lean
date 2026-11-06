import Solidity.Lowering.V07.Controls
import Solidity.Lowering.V07.Operands
import Solidity.Source.SemanticsExamples

namespace Solidity.Lowering.V07.ReadControls
open Source.SemanticsExamples

def source : Source.EMState E0 [.int Source.IntTy.u8, .int Source.IntTy.u8] :=
  (.cons (.int 7 (by decide)) (.cons (.int 3 (by decide)) .nil), s0)

def target : State (default : Contract) [.val .uint, .val .uint] :=
  ((State.init default).push (integerValue Source.IntTy.u8 3 (by decide))).push
    (integerValue Source.IntTy.u8 7 (by decide))

theorem read_transport (p : Roadmap.Pipeline) (fuel : Nat) :
    (Source.evalE (G0 p) F0 (fuel+1) (.local .here)).run source =
      (.ok (.val (.int 7 (by decide))),source) ∧
    (.simple (.local .here) : Val (default : Contract) [.val .uint, .val .uint] .uint).evalT target =
      .ok (integerValue Source.IntTy.u8 7 (by decide)) ∧
    IntValueRel Source.IntTy.u8 (.int 7 (by decide) : Source.Val E0.layout (.int Source.IntTy.u8))
      (integerValue Source.IntTy.u8 7 (by decide)) :=
  source_local_transport (G0 p) F0 fuel source target Source.IntTy.u8 .here .here 7 (by decide) rfl rfl

theorem pair_transport (p : Roadmap.Pipeline) (fuel : Nat) :
    (Source.evalPair (G0 p) F0 (fuel+2) (.local .here) (.local (.there .here))).run source =
      (.ok (.val (.int 7 (by decide)), .val (.int 3 (by decide))),source) :=
  source_local_pair (G0 p) F0 fuel source Source.IntTy.u8 .here (.there .here) 7 3
    (by decide) (by decide) rfl rfl

theorem alias_pair (p : Roadmap.Pipeline) (fuel : Nat) :
    (Source.evalPair (G0 p) F0 (fuel+2) (.local .here) (.local .here)).run source =
      (.ok (.val (.int 7 (by decide)), .val (.int 7 (by decide))),source) :=
  source_local_pair (G0 p) F0 fuel source Source.IntTy.u8 .here .here 7 7
    (by decide) (by decide) rfl rfl

theorem wrong_index :
    ((.simple (.local (.there .here)) :
      Val (default : Contract) [.val .uint,.val .uint] .uint).evalT target) ≠ .ok (integerValue Source.IntTy.u8 7 (by decide)) := by
  intro h
  change Except.ok (integerValue Source.IntTy.u8 3 (by decide)) = _ at h
  have e := integer_injective Source.IntTy.u8 3 7 (by decide) (by decide) (Except.ok.inj h)
  omega

theorem operand_transport (p : Roadmap.Pipeline) (fuel : Nat) :
    (Source.evalE (G0 p) F0 (fuel+1) (.local .here)).run source =
      (.ok (.val (.int 7 (by decide))),source) ∧
    (DeferredSource.Operand.ofSrc (.val (.simple (.local .here)) :
      Src (default : Contract) [.val .uint,.val .uint] (.prim .uint))).run target =
      .ok (⟨target,List.prefix_refl _⟩,.prim (integerValue Source.IntTy.u8 7 (by decide))) ∧
    IntValueRel Source.IntTy.u8 (.int 7 (by decide) : Source.Val E0.layout (.int Source.IntTy.u8))
      (integerValue Source.IntTy.u8 7 (by decide)) :=
  source_local_operand_transport (G0 p) F0 fuel source target Source.IntTy.u8 .here .here 7
    (by decide) rfl rfl

end Solidity.Lowering.V07.ReadControls
