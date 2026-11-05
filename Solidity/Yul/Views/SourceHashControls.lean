import Solidity.Yul.Views.SourceHashBinding
import Solidity.Yul.Views.HeapEnumerationControls
import Solidity.Yul.Views.ObjectAllocationRetainedControls

namespace Solidity.Yul.Views.Controls

def hmResidual : ByteView := fun _ => 0xa5
def hmMemory := encodeMixedHeap mixedPlacement (generatedHeapEntries mixedPlacement) hmResidual

theorem hm_payload : readBytes hmMemory 160 3=mixedChild :=
  encodedSourceBytes mixedHeap.ty mixedState mixedPlacement hmResidual mixed_actual_MemOK
    generated_mixed_types_supported 0 mixedChild rfl

theorem hm_actual_source_and_word (G : Source.Glob mixedEnv) (n : Nat) :
    let value := Source.mkBytes (D := mixedLayout) (n := 32) (h := by decide) (Source.wordBytes (G.fixed.hash mixedChild))
    (Source.evalE G mixedReadFrame (n+4) (sourceMemoryHashExpr Source.Idx.here)).run mixedState=(.ok (.val value),mixedState) ∧
      value.word=some (keccak256 G.fixed.evm hmMemory 160 3) :=
  sourceMemoryHash_encoded G mixedReadFrame n mixedHeap.ty mixedState mixedPlacement hmResidual mixed_actual_MemOK
    generated_mixed_types_supported .here 0 mixedChild rfl rfl

theorem hm_timeout (G : Source.Glob mixedEnv) :
    (Source.evalE G mixedReadFrame 0 (sourceMemoryHashExpr Source.Idx.here)).run mixedState=(.error .timeout,mixedState) := rfl

theorem hm_builtin_timeout (G : Source.Glob mixedEnv) :
    (Source.evalBuiltin G mixedReadFrame 0 .keccak256 (Source.RArgs.cons (.local Source.Idx.here) .nil) Source.STy.bytes32).run
      mixedState=(.error .timeout,mixedState) := rfl

/-- Wrong payload is rejected as a BYTE relation. No unqualified hash
inequality is inferred; arbitrary bounded Fixed functions may collide. -/
def hmWrong := saveByte hmMemory 160 0xee

theorem hm_wrong_payload : readBytes hmWrong 160 3≠mixedChild := by
  intro same
  have first := congrArg (fun xs : List UInt8 => xs[0]?) same
  change some (0xee : UInt8)=some 0x11 at first
  exact (by decide : (0xee : UInt8)≠0x11) (Option.some.inj first)

theorem hm_padding_is_not_payload : readBytes hmMemory 160 32≠mixedChild := by
  intro same
  have length := congrArg List.length same
  simp only [readBytes,List.length_map,List.length_range,mixedChild,List.length_cons,List.length_nil] at length
  cases length

/-- An actual retained source write supplies this valid current placement
and original capacity. Hash input is the current empty payload. This FRESH
residual encoding does not witness preservation of a previous raw tail. -/
theorem hm_retained_empty_hash (G : Source.Glob mixedEnv) (n : Nat) :
    let memory := encodeMixedHeap omShrunkPlacement (generatedHeapEntries omShrunkPlacement) hmResidual
    let value := Source.mkBytes (D := mixedLayout) (n := 32) (h := by decide) (Source.wordBytes (G.fixed.hash []))
    (Source.evalE G mixedReadFrame (n+4) (sourceMemoryHashExpr Source.Idx.here)).run omShrunkState=(.ok (.val value),omShrunkState) ∧
      value.word=some (keccak256 G.fixed.evm memory 160 0) :=
  sourceMemoryHash_encoded G mixedReadFrame n mixedHeap.ty omShrunkState omShrunkPlacement hmResidual
    (om_shrunk_every_H _ mixed_actual_MemOK) om_shrunk_support .here 0 [] rfl (Source.Heap.write_get _ _ _ (by rfl))

/-- A BOUNDED synthetic hash, not the approved real-Keccak instance. This
control prevents accidentally deriving injectivity from mere boundedness. -/
def hmConstant (fixed : Roadmap.Evm.Fixed) : Roadmap.Evm.Fixed :=
  {fixed with keccak := fun _ => 0,keccak_lt := fun _ => by decide}

theorem hm_bounded_collision (fixed : Roadmap.Evm.Fixed) :
    (hmConstant fixed).keccak mixedChild=(hmConstant fixed).keccak [0xee] := rfl

/-- Malformed API-state control only: it is not an admitted/reachable source
program and does not contradict the positive every-MemOK/domain theorem. -/
theorem hm_missing_reference (F : Source.Fr) (n : Nat) :
    (Source.bytesOfRV F n (Source.RVal.val (Source.Val.memRef (τ := .bytes .memory) rfl 999))).run mixedState=
      (.error (.stuck "dangling memory reference"),mixedState) := sourceBytesOfMemory_missing F n mixedState 999 rfl

end Solidity.Yul.Views.Controls
