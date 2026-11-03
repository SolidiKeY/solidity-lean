import Solidity.Yul.Views.SourceEnvironmentInputs
import Solidity.Yul.Views.StaticUintMemory

namespace Solidity.Yul.Views

def sourceTimestampExpr {E Γ} : Source.RExpr E Γ (.int Source.IntTy.u256) :=
  .magic .block "timestamp" rfl

def sourceSenderExpr {E Γ} : Source.RExpr E Γ (.address false) :=
  .magic .msg "sender" rfl

def sourceValueExpr {E Γ} : Source.RExpr E Γ (.int Source.IntTy.u256) :=
  .magic .msg "value" rfl

theorem sourceMkIntWord (D : Source.Layout) (word : Roadmap.Word) :
    Source.mkInt (D := D) Source.IntTy.u256 word.val=.ok (uintValueOfWord D word) := by
  have range : Source.IntTy.u256.lo≤(word.val : Int) ∧ (word.val : Int)≤Source.IntTy.u256.hi := by
    have bound := word.isLt
    change 0≤(word.val : Int) ∧ (word.val : Int)≤(2^256 : Nat)-1
    omega
  unfold Source.mkInt
  rw [dif_pos range]
  rfl

/-- Real owner evalE at every positive horizon. No state projection: the
complete result includes the ORIGINAL locals, heap, world and events. -/
theorem sourceTimestamp_run {E Γ} (G : Source.Glob E) (F : Source.Fr) (n : Nat) (s : Source.EMState E Γ) :
    (Source.evalE G F (n+1) sourceTimestampExpr).run s=
      (.ok (.val (uintValueOfWord E.layout G.timestamp)),s) := by
  change (do
    let value ← Source.EM.lift (Source.mkInt Source.IntTy.u256 G.timestamp.val)
    pure (Source.RVal.val value)).run s= _
  rw [sourceMkIntWord]
  rfl

theorem sourceSender_run {E Γ} (G : Source.Glob E) (F : Source.Fr) (n : Nat) (s : Source.EMState E Γ) :
    (Source.evalE G F (n+1) sourceSenderExpr).run s=
      (.ok (.val (Source.Val.address F.sender)),s) := rfl

theorem sourceValue_run {E Γ} (G : Source.Glob E) (F : Source.Fr) (n : Nat) (s : Source.EMState E Γ) :
    (Source.evalE G F (n+1) sourceValueExpr).run s=
      (.ok (.val (uintValueOfWord E.layout F.value)),s) := by
  change (do
    let value ← Source.EM.lift (Source.mkInt Source.IntTy.u256 F.value.val)
    pure (Source.RVal.val value)).run s= _
  rw [sourceMkIntWord]
  rfl

/-- Matches the actual runTx Glob timestamp update, without assuming
arbitrary original G.timestamp equals the request. Not runTx adequacy. -/
theorem sourceTransactionTimestamp {E Γ} (G : Source.Glob E) (F : Source.Fr) (n : Nat)
    (s : Source.EMState E Γ) (environment : Environment) (tx : Source.TxConfig) :
    let value := uintValueOfWord E.layout tx.request.timestamp
    (Source.evalE { G with timestamp := tx.request.timestamp } F (n+1) sourceTimestampExpr).run s=
      (.ok (.val value),s) ∧ value.word=some ((environment.bindTransaction tx).read .timestamp) :=
  ⟨sourceTimestamp_run _ F n s,uintValueOfWord_word _ _⟩

/-- Typed source magic reads of an actual frame. No call success, legality,
contract resolution or owner-frame execution theorem is inferred. -/
theorem sourceCallInputs {E Γ} (G : Source.Glob E) (frame : Source.CallFrame) (contract : String)
    (checked : Bool) (depth n : Nat) (s : Source.EMState E Γ) :
    let F := sourceFrameOfCall frame contract checked depth
    (Source.evalE G F (n+1) sourceSenderExpr).run s=(.ok (.val (Source.Val.address frame.caller)),s) ∧
    (Source.evalE G F (n+1) sourceValueExpr).run s=(.ok (.val (uintValueOfWord E.layout frame.value)),s) ∧
    (Source.Val.address (D := E.layout) (p := false) frame.caller).word=some (addressInputWord frame.caller) ∧
    (uintValueOfWord E.layout frame.value).word=some frame.value :=
  ⟨sourceSender_run G _ n s,sourceValue_run G _ n s,sourceAddress_input_word _ _,uintValueOfWord_word _ _⟩

/-- Concrete sequence of ACTUAL owner expressions, not another evaluator. -/
def sourceMagicReads {E Γ} (G : Source.Glob E) (F : Source.Fr) (horizon : Nat) :
    Source.EM E Γ (Source.RVal E.layout (.int Source.IntTy.u256) ×
      Source.RVal E.layout (.address false) × Source.RVal E.layout (.int Source.IntTy.u256)) := do
  let timestamp ← Source.evalE G F horizon sourceTimestampExpr
  let sender ← Source.evalE G F horizon sourceSenderExpr
  let value ← Source.evalE G F horizon sourceValueExpr
  pure (timestamp,sender,value)

/-- Complete owner result/state equality at every positive horizon. -/
theorem sourceMagic_sequence {E Γ} (G : Source.Glob E) (F : Source.Fr) (n : Nat) (s : Source.EMState E Γ) :
    (sourceMagicReads G F (n+1)).run s=
      (.ok (.val (uintValueOfWord E.layout G.timestamp),.val (Source.Val.address F.sender),
        .val (uintValueOfWord E.layout F.value)),s) := by
  unfold sourceMagicReads
  rw [Source.Hoare.run_bind,sourceTimestamp_run]
  simp only []
  rw [Source.Hoare.run_bind,sourceSender_run]
  simp only []
  rw [Source.Hoare.run_bind,sourceValue_run]
  rfl

theorem sourceMagic_timeout {E Γ} (G : Source.Glob E) (F : Source.Fr) (s : Source.EMState E Γ) :
    (sourceMagicReads G F 0).run s=(.error .timeout,s) := rfl

/-- Every ORIGINAL owner typing survives, including the real timeout case.
No safety/output-placement conclusion is supplied as an input. -/
theorem sourceMagic_every_H {E Γ} (G : Source.Glob E) (F : Source.Fr) (horizon : Nat)
    (H : Source.HeapTy) (s : Source.EMState E Γ) (ok : Source.MemOK E H s) :
    Source.MemOK E H ((sourceMagicReads G F horizon).run s).2 := by
  cases horizon with
  | zero => rw [sourceMagic_timeout]; exact ok
  | succ n => rw [sourceMagic_sequence]; exact ok

end Solidity.Yul.Views
