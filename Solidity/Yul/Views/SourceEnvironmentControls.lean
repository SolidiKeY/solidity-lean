import Solidity.Yul.Views.SourceMagicReads
import Solidity.Yul.Views.HeapEnumerationControls
import Solidity.Yul.Views.MemoryControls

namespace Solidity.Yul.Views.Controls

def emTx : Source.TxConfig := ⟨⟨⟨0x42,by decide⟩,⟨0x123,by decide⟩,highestUint,17,[1,2,3,4]⟩⟩

def emFrame : Source.CallFrame := ⟨⟨99,by decide⟩,⟨88,by decide⟩,highestUint,[0xaa],true,5⟩

def emSourceFrame := sourceFrameOfCall emFrame "C" false 9

theorem em_transaction_inputs :
    (environment.bindTransaction emTx).read .timestamp=17 ∧
    (environment.bindTransaction emTx).read .origin=0x42 ∧
    (environment.bindTransaction emTx).read .number=1000 ∧
    (environment.bindTransaction emTx).read .chainid=1 ∧
    blockhash (environment.bindTransaction emTx) 744=42 ∧
    blobhash (environment.bindTransaction emTx) 1=0 := by decide

theorem em_actual_sequence (G : Source.Glob mixedEnv) (n : Nat) :
    (sourceMagicReads { G with timestamp := emTx.request.timestamp } emSourceFrame (n+1)).run mixedState=
      (.ok (.val (uintValueOfWord mixedLayout 17),.val (Source.Val.address emFrame.caller),
        .val (uintValueOfWord mixedLayout highestUint)),mixedState) :=
  sourceMagic_sequence _ _ n mixedState

theorem em_actual_owner_MemOK (G : Source.Glob mixedEnv) (horizon : Nat) (H : Source.HeapTy)
    (ok : Source.MemOK mixedEnv H mixedState) :
    Source.MemOK mixedEnv H ((sourceMagicReads G emSourceFrame horizon).run mixedState).2 :=
  sourceMagic_every_H _ _ _ H mixedState ok

theorem em_actual_timeout (G : Source.Glob mixedEnv) :
    (sourceMagicReads G emSourceFrame 0).run mixedState=(.error .timeout,mixedState) :=
  sourceMagic_timeout _ _ mixedState

/-- Existing static frame value need not be zero. STATICCALL's new child
has zero value by context construction; static alone is not that rule. -/
theorem em_static_reads_value (G : Source.Glob mixedEnv) (n : Nat) :
    emSourceFrame.static=true ∧
    (Source.evalE G emSourceFrame (n+1) sourceValueExpr).run mixedState=
      (.ok (.val (uintValueOfWord mixedLayout highestUint)),mixedState) ∧
    (uintValueOfWord mixedLayout highestUint).word=some highestUint :=
  ⟨rfl,sourceValue_run G emSourceFrame n mixedState,uintValueOfWord_word _ _⟩

theorem em_sender_exact :
    (Source.Val.address (D := mixedLayout) (p := false) emFrame.caller).word=some (addressInputWord emFrame.caller) :=
  sourceAddress_input_word _ _

theorem em_wrong_original_timestamp : environment.read .timestamp≠emTx.request.timestamp := by decide

theorem em_wrong_frame_sender : addressInputWord emFrame.this≠addressInputWord emFrame.caller := by decide

theorem em_not_static_zero : emSourceFrame.value≠0 := by decide

theorem em_no_number_source_expression : Source.Builtin.memberTy .block "number"=none := rfl

theorem em_no_origin_source_expression : Source.Builtin.memberTy .tx "origin"=none := rfl

end Solidity.Yul.Views.Controls
