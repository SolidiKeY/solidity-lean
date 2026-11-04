import Solidity.Backend.InternalFlow.RuntimeFrameV3ScalarRecursiveTurn

/-! Exact all-index primitive return from genuine native recursive calls. -/
namespace Solidity.Backend.InternalFlow.RuntimeFrame.ScalarRecursiveSource
open Evm Evm.Memory RecursiveSource

theorem all_horizons {C : Contract} {R : RefTy} (hm : (Ty.ref R).mapFree=true)
 (depth : Nat) (σ : State C (Frame R)) (count : Nat) (bound : count<W) (ref : HRef σ.H R)
 (counter : TEnv.get (.there .here : Idx (Frame R) (.val .uint)) σ.env=countValue count bound)
 (alias : TEnv.get (.there (.there .here) : Idx (Frame R) (.mem R)) σ.env=some ref) :
 (body R hm depth).run σ=if count<depth then .ok ⟨finished σ count bound,List.prefix_refl _⟩ else .error .exhausted := by
 induction depth generalizing σ count with
 | zero =>
   change (.error .exhausted : TRes (Solidity.Out C σ.H (Frame R)))=_
   simp only [Nat.not_lt_zero,if_false]
 | succ depth ih =>
   cases count with
   | zero =>
     simpa only [Nat.zero_lt_succ,if_true] using zero_return hm depth σ counter
   | succ count =>
     have nested := ih (entered σ count (by omega) ref) count (by omega) ref rfl rfl
     have actual := turn_result hm depth σ count bound counter (call_result hm depth σ count bound ref counter alias nested)
     by_cases enough : count<depth
     · have enough' : count+1<depth+1 := by omega
       simpa only [if_pos enough,if_pos enough'] using actual
     · have short : ¬count+1<depth+1 := by omega
       simpa only [if_neg enough,if_neg short] using actual

end Solidity.Backend.InternalFlow.RuntimeFrame.ScalarRecursiveSource
