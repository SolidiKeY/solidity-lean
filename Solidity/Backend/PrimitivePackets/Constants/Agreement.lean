import Solidity.Backend.PrimitivePackets.Constants.Target

/-! Source literal to publicly selected PUSH, for arbitrary width/sign and
machine state. Only the existing intrinsic literal range evidence is required. -/
namespace Solidity.Backend.PrimitivePackets.Constants
open Evm Evm.Memory Solidity.Lowering.V07

theorem success {E : Source.Env} {srcΓ : Source.RCtx} {C : Contract} {Γ : Ctx}
    (G : Source.Glob E) (SF : Source.Fr) (fuel : Nat) (source : Source.EMState E srcΓ)
    (offset : Nat) (F : Frag Γ) (t : Source.IntTy) (z : Int)
    (h : t.lo ≤ z ∧ z ≤ t.hi) (machine : Machine) (tail : List Word) :
    Memory.compileVal offset F (value (C:=C) t z h) = some (selected offset F t z h) ∧
    (Source.evalE G SF (fuel+2)
      (.conv (.const (Source.Q.ofInt z)) (.inl (IntegerConstants.allowed E t z h)))).run source =
      (.ok (.val (.int z h)),source) ∧
    IntValueRel t (.int z h : Source.Val E.layout (.int t)) (integerValue t z h) ∧
    (∀ target : State C Γ, (value t z h).evalT target = .ok (integerValue t z h)) ∧
    ReprV (integerPrim t) (integerValue t z h) (.val (sword z)) ∧
    run (selected (C:=C) offset F t z h).code {machine with stack := tail} =
      .ok ({machine with stack := tail}.push (.val (sword z))) 0 :=
  ⟨public_selection offset F t z h,source_success G SF fuel source t z h,
    integer_related t z h,(fun target => IntegerConstants.value_run target t z h),
    word_agreement t z h,target_success offset F t z h machine tail⟩

end Solidity.Backend.PrimitivePackets.Constants
