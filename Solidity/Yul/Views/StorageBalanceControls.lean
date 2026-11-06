import Solidity.Yul.Views.StorageBalanceSequence
import Solidity.Yul.Views.PackedResidualTypedSourceControls
import Solidity.Yul.Views.SourceBalanceControls

namespace Solidity.Yul.Views.Controls

/-- An actual owner Program input. No program reachability or monetary-ledger
adequacy is inferred from these API states. The synthetic hash is unused. -/
def sbeProgram : Source.Program packedTypedEnv where
  body _ := none
  consts _ := none
  inits _ := []
  ctor _ := none
  ctorLocals _ := []
  baseArgs _ := []
  contracts := []

def sbeGlob : Source.Glob packedTypedEnv :=
  ⟨sbeProgram,.legacy,sbGlob.fixed,fun _ => 7,fun _ _ => false,fun _ => .answer (.success []),0⟩

def sbeState : Source.EMState packedTypedEnv [.address false] :=
  ⟨.cons (.address account) .nil,{packedTypedState.2 with
    ex := packedTypedState.2.ex.apply (.account account (fun ac => {ac with code := some 0,balance := 77}))
    events := [.credit account 1]}⟩

theorem sbe_transient_prepares : (preparePackedFrame (ps := packedTypedRegistry) (ts := packedTypedRegistry)
    packedStepFrame true 7 packedRawB).isSome := by decide

def sbeTransientPlan := (preparePackedFrame (ps := packedTypedRegistry) (ts := packedTypedRegistry)
  packedStepFrame true 7 packedRawB).get sbe_transient_prepares

def sbePlans := [packedTypedPlan,sbeTransientPlan,packedTypedChildPlan]
def sbeRun := runPackedSource packedStepFrame sbePlans sbeState packedTypedResidual

theorem sbe_success_and_journals : sbeRun.1.1=.ok () ∧
    sbeRun.1.2.2.ex.journal.length=4 ∧ sbeRun.2.journal.length=3 := ⟨rfl,rfl,rfl⟩

theorem sbe_balances : sourceObservedBalance sbeGlob sbeState account=77 ∧
    sourceObservedBalance sbeGlob sbeRun.1.2 account=77 :=
  ⟨rfl,runPackedSource_observed_balance sbeGlob packedStepFrame sbePlans sbeState packedTypedResidual account⟩

theorem sbe_full_funds : sourceObservedFunds sbeGlob sbeRun.1.2=sourceObservedFunds sbeGlob sbeState :=
  runPackedSource_observed_funds sbeGlob packedStepFrame sbePlans sbeState packedTypedResidual

theorem sbe_poststate_read (n : Nat) :
    (Source.evalE sbeGlob packedStepFrame (n+2) (sourceBalanceExpr .here)).run sbeRun.1.2=
      (.ok (.val (uintValueOfWord packedTypedEnv.layout 77)),sbeRun.1.2) :=
  runPackedSource_balanceLocal sbeGlob packedStepFrame n sbePlans sbeState packedTypedResidual .here account rfl

theorem sbe_static_exact : runPackedSource {packedStepFrame with static := true} sbePlans sbeState packedTypedResidual=
    ((.error (.revert []),sbeState),packedTypedResidual) :=
  runPackedSource_static _ _ _ _ _ rfl

theorem sbe_static_funds : sourceObservedFunds sbeGlob
    (runPackedSource {packedStepFrame with static := true} sbePlans sbeState packedTypedResidual).1.2=
      sourceObservedFunds sbeGlob sbeState := runPackedSource_observed_funds _ _ _ _ _

theorem sbe_every_H (H : Source.HeapTy) (ok : Source.MemOK packedTypedEnv H sbeState) :
    Source.MemOK packedTypedEnv H sbeRun.1.2 := runPackedSource_MemOK _ _ _ _ H ok

theorem sbe_inhabited_MemOK : Source.MemOK packedTypedEnv sbeState.2.heap.ty sbeState :=
  ⟨⟨⟨Source.HeapOK.empty,Source.HeapTy.Le.refl _⟩,⟨trivial,trivial⟩⟩,Source.HeapShaped.empty,Source.HeapInner.empty⟩

/-- This counter-control excludes arbitrary account updates from the theorem.
Code/balance preservation was proved for actual prepared STORAGE operations. -/
def sbeChanged : Source.EMState packedTypedEnv [.address false] :=
  ⟨sbeState.1,{sbeState.2 with ex := sbeState.2.ex.apply (.account account (fun ac => {ac with balance := 88}))}⟩

theorem sbe_balance_change_detected : sourceObservedBalance sbeGlob sbeChanged account=88 ∧
    sourceObservedBalance sbeGlob sbeChanged account≠sourceObservedBalance sbeGlob sbeState account := by decide

theorem sbe_target_change_detected : sourceObservedFunds sbeGlob sbeChanged (environmentAddress account)≠
    sourceObservedFunds sbeGlob sbeState (environmentAddress account) := by
  rw [sourceObservedFunds_address,sourceObservedFunds_address]
  intro same
  have eq := environmentWord_injective same
  exact (by decide : (88 : Roadmap.Word)≠77) eq

end Solidity.Yul.Views.Controls
