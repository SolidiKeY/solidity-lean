import Solidity.Yul.Views.BytePlanHashFrames
import Solidity.Yul.Views.BytePlanHashAliasControls

/-! A child returns the hash of a mutated string-backed bytes alias while its
caller retains different aliases. The same reached raw map reconstructs the
whole caller store, for every original heap typing. Halt controls preserve the
real source heap prefix; local substitution does not implement heap rollback. -/
namespace Solidity.Yul.Views.BytePlanHashFrames.Controls
open Solidity.Yul.Views.Controls
open MultiRootByteWrites.Controls
open BytePlanHashAlias.Controls

def output (G : Source.Glob mixedEnv) := Source.mkBytes (D:=mixedLayout) (n:=32) (h:=by decide)
  (Source.wordBytes (G.fixed.hash [0x80,0x61]))

theorem success_return (G : Source.Glob mixedEnv) (n : Nat) :
    (Source.EM.sub aliases (BytePlanHash.program G mixedReadFrame 0 n writePrefix .here)).run mixedState=
      (.ok (.val (output G),aliases),after) := by
  first | (simp only;done) | decide | omega | rfl

/-- The universal frame theorem is inhabited for arbitrary original H, rather
than only at the heap's current typing or with empty caller/callee locals. -/
theorem derived_return_and_map (G : Source.Glob mixedEnv) (n : Nat) (H : Source.HeapTy)
    (ok : Source.MemOK mixedEnv H mixedState) :
    Source.MemOK mixedEnv H after ∧
    (∃ q : Placement after.2.heap,
      q.address=mixedPlacement.address ∧ q.free=mixedPlacement.free ∧
      encodeMixedHeap q (generatedHeapEntries q) raw=raw ∧
      ∃ history : RetainedAllocation mixedPlacement q,
        enumeratedMemoryWriteback after mixedPlacement q history raw=.ok (some (.ok (),after)) ∧
        ReservedOK raw q.free) ∧
    ∃ bytes,after.2.heap.get 1=some ⟨.string .memory,Source.Data.string bytes⟩ ∧
      let value := Source.mkBytes (D:=mixedLayout) (n:=32) (h:=by decide) (Source.wordBytes (G.fixed.hash bytes))
      (Source.EM.sub aliases (BytePlanHash.program G mixedReadFrame 0 n writePrefix .here)).run mixedState=
        (.ok (.val value,aliases),after) ∧
      value.word=some (keccak256 G.fixed.evm raw 416 bytes.length) := by
  first | (simp only;done) | decide | omega | rfl | skip
  have result := transport G mixedReadFrame 0 n writePrefix H mixedState aliases incoming.1.2
    mixedPlacement mixedPlacement (retainInitial _ _) ok StructWordHeap.Controls.support
    mixedPhysical ByteElementStore.Controls.oldReads mixed_reserved .here 1 true [0xff,0x61] rfl rfl
  have reached := actual_plan
  dsimp only [initial] at reached
  dsimp only at result
  rw [reached] at result
  exact ⟨result.1.2.1,result.1.2.2,result.2⟩

theorem late_child_failure (G : Source.Glob mixedEnv) (n : Nat) :
    (Source.EM.sub aliases (BytePlanHash.program G mixedReadFrame 0 n requests .here)).run mixedState=
      (.error (.stuck "not bytes"),after) := by
  first | (simp only;done) | decide | omega | rfl

/-- A nested child has no locals while the surrounding child retains aliases. -/
theorem suspended_child (G : Source.Glob mixedEnv) (n : Nat) :
    (Source.EM.sub aliases (do
      let _ ← Source.EM.sub (Source.Locals.nil : Source.Locals mixedLayout [])
        (MultiRootByteWrites.program mixedReadFrame 0 writePrefix)
      Source.evalE G mixedReadFrame (n+4) (sourceMemoryHashExpr .here))).run mixedState=
        (.ok (.val (output G),aliases),after) := by
  first | (simp only;done) | decide | omega | rfl

/-- A later source halt keeps the actual heap prefix. It is not a transaction
rollback theorem and must not be presented as automatic heap restoration. -/
theorem halt_after_return (G : Source.Glob mixedEnv) (n : Nat) :
    ((do let _ ← Source.EM.sub aliases (BytePlanHash.program G mixedReadFrame 0 n writePrefix .here)
         Source.EM.halt (.revert [0xde,0xad])) : Source.EM mixedEnv _ Unit).run mixedState=
      (.error (.revert [0xde,0xad]),after) := by
  first | (simp only;done) | decide | omega | rfl

/-- Dropping the child, discarding its mutation, or hashing its old object is
observable through post-call bytes, without assuming hash injectivity. -/
theorem post_call_aliases_and_chronology :
    (Source.bytesOfRV mixedReadFrame 0 (.val (after.1.get .here))).run after=(.ok [0x11,0x22,0x55],after) ∧
    (Source.bytesOfRV mixedReadFrame 0 (.val (after.1.get (.there .here)))).run after=(.ok [0x11,0x22,0x55],after) ∧
    readBytes mixedPhysical 416 2≠readBytes raw 416 2 ∧ raw 418=0xa5 := by
  first | (simp only;done) | decide | omega | rfl | skip
  exact ⟨rfl,rfl,by decide,by decide⟩
end Solidity.Yul.Views.BytePlanHashFrames.Controls
