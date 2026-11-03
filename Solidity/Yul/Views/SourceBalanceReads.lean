import Solidity.Yul.Views.SourceBalanceInputs

namespace Solidity.Yul.Views

theorem sourceUintWrapWord (D : Source.Layout) (word : Roadmap.Word) :
    Source.intWrap (D := D) Source.IntTy.u256 word.val=uintValueOfWord D word := by
  have lower : 0≤(word.val : Int) := Int.natCast_nonneg _
  have upper : (word.val : Int)<(2^256 : Nat) := Int.ofNat_lt.mpr word.isLt
  have same : Source.IntTy.u256.wrap (word.val : Int)=(word.val : Int) := by
    simpa only [Source.IntTy.wrap,Source.wrapBits,Source.IntTy.u256,Bool.false_eq_true,false_and,if_false]
      using Int.emod_eq_of_lt lower upper
  change Source.Val.int _ _=Source.Val.int _ _
  congr 1

def sourceBalanceExpr {E Γ} (index : Source.Idx Γ (.address false)) : Source.RExpr E Γ (.int Source.IntTy.u256) :=
  .balance (.local index)

/-- Actual owner balance evaluation, including system/external selection and
current history. The local-address profile has no operand effects. -/
theorem sourceBalanceLocal_run {E Γ} (G : Source.Glob E) (F : Source.Fr) (n : Nat) (s : Source.EMState E Γ)
    (index : Source.Idx Γ (.address false)) (address : Roadmap.Address)
    (localValue : s.1.get index=Source.Val.address address) :
    (Source.evalE G F (n+2) (sourceBalanceExpr index)).run s=
      (.ok (.val (uintValueOfWord E.layout (sourceObservedBalance G s address))),s) := by
  have localRun : (Source.evalE G F (n+1) (Source.RExpr.local index)).run s=
      (.ok (.val (Source.Val.address address)),s) := by
    change ((Except.ok (Source.RVal.val (s.1.get index)) : Except Source.Halt (Source.RVal E.layout (.address false))),s)= _
    rw [localValue]
  have stateRun : (Source.EM.st : Source.EM E Γ (Source.St E)).run s=(.ok s.2,s) := by cases s; rfl
  rw [sourceBalanceExpr,Source.evalE,Source.Hoare.run_bind,localRun]
  simp only []
  change (do
    let state ← Source.EM.st
    let word := match (state.ex.world.accounts address).code with
      | some _ => (state.ex.world.accounts address).balance
      | none => G.fixed.ledger G.balance0 state.events address
    pure (Source.RVal.val (Source.intWrap Source.IntTy.u256 word.val))).run s= _
  rw [Source.Hoare.run_bind,stateRun]
  change ((Except.ok (Source.RVal.val (Source.intWrap Source.IntTy.u256 (sourceObservedBalance G s address).val))),s)= _
  rw [sourceUintWrapWord]

/-- Funds are CONSTRUCTED from this actual source snapshot. Matching an
independent target ledger/world and effectful operands remain separate. -/
theorem sourceBalanceLocal_target {E Γ} (G : Source.Glob E) (F : Source.Fr) (n : Nat) (s : Source.EMState E Γ)
    (index : Source.Idx Γ (.address false)) (address : Roadmap.Address)
    (localValue : s.1.get index=Source.Val.address address) :
    let value := uintValueOfWord E.layout (sourceObservedBalance G s address)
    (Source.evalE G F (n+2) (sourceBalanceExpr index)).run s=(.ok (.val value),s) ∧
    value.word.map environmentWord=some (sourceObservedFunds G s (environmentAddress address)) := by
  refine ⟨sourceBalanceLocal_run G F n s index address localValue,?_⟩
  rw [uintValueOfWord_word,sourceObservedFunds_address]
  rfl

/-- Exact positive-horizon state identity transports every original owner H. -/
theorem sourceBalanceLocal_every_H {E Γ} (G : Source.Glob E) (F : Source.Fr) (n : Nat) (s : Source.EMState E Γ)
    (index : Source.Idx Γ (.address false)) (address : Roadmap.Address)
    (localValue : s.1.get index=Source.Val.address address) (H : Source.HeapTy) (ok : Source.MemOK E H s) :
    Source.MemOK E H ((Source.evalE G F (n+2) (sourceBalanceExpr index)).run s).2 := by
  rw [sourceBalanceLocal_run G F n s index address localValue]
  exact ok

end Solidity.Yul.Views
