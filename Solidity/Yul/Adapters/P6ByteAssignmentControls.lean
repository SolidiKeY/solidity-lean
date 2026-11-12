import Solidity.Yul.Adapters.P6ByteAssignment
import Solidity.Yul.Adapters.P6ByteReferenceWriteControls
import Solidity.Yul.Views.HeapByteResizeControls

/-! Actual resolved assignment producers in both Source pipeline selections.
The fixture supplies a real typed reference/index/value context; no historical
reference formation, allocator trace or compiler correspondence is inferred. -/
namespace Solidity.Yul.Adapters.P6ByteAssignment.Controls
open Solidity.Yul.Views Solidity.Yul.Views.Controls
open Solidity.Backend Solidity.Backend.MemoryOps.Physical Solidity.Evm.TryByteImage
open P6ByteFamilyCopy.Controls (placement entries residual carrier fits)
open P6ByteReferenceWrite.Controls (image reached)

def glob (p : Pipeline) : Source.Glob heapByteEnv :=
  ⟨{body:=fun _=>none,consts:=fun _=>none,inits:=fun _=>[],ctor:=fun _=>none,
    ctorLocals:=fun _=>[],baseArgs:=fun _=>[],contracts:=[]},
    (match p with | .legacy=>.legacy | .viaIR=>.viaIR),
    ⟨Roadmap.Evm.withKeccak,fun bal _ a=>bal a,1,0⟩,
    fun _=>⟨0,by decide⟩,fun _ _=>true,fun _=>.answer (.success []),⟨0,by decide⟩⟩

def state (i : Roadmap.Word) : Source.EMState heapByteEnv [.bytes .memory,.int .u256,.fixedBytes 1 (by decide)] :=
  (.cons (.memRef rfl 1) (.cons (uintValueOfWord heapByteEnv.layout i)
    (.cons (.fixedBytes [0xff] rfl) .nil)),stringAliasState.2)

def assignment : Source.RExpr heapByteEnv [.bytes .memory,.int .u256,.fixedBytes 1 (by decide)] (.fixedBytes 1 (by decide)) :=
  expression .here (.there .here) (.there (.there .here))

/-- Both real pipeline values execute the assignment and refresh the full map. -/
theorem actual_assignment (pipeline : Pipeline) (n : Nat) : ∃ r : InventoryRealization placement,
    (Source.evalE (glob pipeline) byteReadFrame (n+3) assignment).run (state 32)=
      (.ok (.val (Source.Val.fixedBytes (n:=1) (h:=by decide) [0xff] rfl)),withSourceHeap (state 32) r.heap) ∧
    encodeMixedHeap r.placement r.entries (frameBytes reached)=frameBytes reached ∧
    CoversMixedHeap r.entries ∧ r.entries.map MixedHeapEntry.id=entries.map MixedHeapEntry.id ∧
    (∀ H,Source.MemOK heapByteEnv H (state 32) → Source.MemOK heapByteEnv H (withSourceHeap (state 32) r.heap)) ∧
    r.heap.get 1=some ⟨.string .memory,Source.Data.string (stringOld.set 32 0xff)⟩ := by
  have initial : frameBytes image=encodeMixedHeap placement entries residual := FrameHeap.frameOf_bytes _ _ _ _ _ _
  exact inventory (glob pipeline) byteReadFrame n (state 32) .here (.there .here) (.there (.there .here))
    1 32 0xff rfl rfl rfl placement placement .initial entries P6ByteFamilyCopy.Controls.coverage (by decide)
    image residual initial true stringOld rfl (by decide) (by decide)

theorem initial_safe : Source.MemOK heapByteEnv byteHeap.ty (state 32) := by
  refine ⟨⟨string_alias_initial_MemOK.1.1,?_⟩,string_alias_initial_MemOK.2⟩
  exact ⟨⟨.string .memory,rfl,rfl⟩,trivial,trivial,trivial⟩

/-- Enough horizon forms index40, but the actual write then panics unchanged. -/
theorem bounds_error (pipeline : Pipeline) (n : Nat) :
    (Source.evalE (glob pipeline) byteReadFrame (n+3) assignment).run (state 40)=
      (.error (.revert (Source.panicData .index)),state 40) :=
  outside (glob pipeline) byteReadFrame n (state 40) .here (.there .here) (.there (.there .here))
    1 40 0xff rfl rfl rfl true stringOld rfl (by decide)

/-- Low horizon fails before location formation, independently of valid bounds. -/
theorem horizon_error (pipeline : Pipeline) :
    (Source.evalE (glob pipeline) byteReadFrame 1 assignment).run (state 32)=(.error .timeout,state 32) :=
  timeout_rhs (glob pipeline) byteReadFrame (state 32) .here (.there .here) (.there (.there .here))

/-- The real returned Source bytes1 word remains LEFT aligned. -/
theorem returned_word : (Source.Val.fixedBytes (D:=heapByteEnv.layout) (n:=1) (h:=by decide) [0xff] rfl).word=
    some ⟨255*2^248,by decide⟩ := by decide
end Solidity.Yul.Adapters.P6ByteAssignment.Controls
