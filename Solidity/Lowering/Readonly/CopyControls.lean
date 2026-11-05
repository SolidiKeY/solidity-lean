import Solidity.Lowering.Readonly.StoreEffects
import Solidity.Lowering.Readonly.Controls

/-! Actual Source byte-copy controls from a populated typed environment.
The checkpoint follows seeding, before the copy. These are Source helper runs,
not native calls or compiler adequacy claims. -/
namespace Solidity.Lowering.Readonly.CopyControls
open Solidity.Source
open SourceHistory

def unit : Syn .unit := .unit (.cons (.contract false "C" .none .nil
  (.cons (.stateVar (.elem .bytes) none none none false "src" .none)
    (.cons (.stateVar (.elem .bytes) none none none false "dst" .none) .nil))) .nil)
def E : Env := unit.env
def frame : Fr := Solidity.Source.SemanticsExamples.FC
def src : Solidity.Source.SPath := ⟨⟨some "C", "src"⟩, []⟩
def dst : Solidity.Source.SPath := ⟨⟨some "C", "dst"⟩, []⟩
def bytesTy : STy := .bytes .storage
def sourceRef : Solidity.Source.Val E.layout bytesTy := .storRef rfl src

def seed : EM E [] Unit := do
  writeLen frame src 2
  writeAt frame (src.go (.index 0)) (Solidity.Source.Val.fixedBytes (n := 1) (h := by decide) [7] rfl)
  writeAt frame (src.go (.index 1)) (Solidity.Source.Val.fixedBytes (n := 1) (h := by decide) [9] rfl)
  writeLen frame dst 3
  writeAt frame (dst.go (.index 0)) (Solidity.Source.Val.fixedBytes (n := 1) (h := by decide) [1] rfl)
  writeAt frame (dst.go (.index 1)) (Solidity.Source.Val.fixedBytes (n := 1) (h := by decide) [2] rfl)
  writeAt frame (dst.go (.index 2)) (Solidity.Source.Val.fixedBytes (n := 1) (h := by decide) [3] rfl)

def checkpoint := (seed.run (L0 E, St.init E)).2.2
def loaded := (loadElem {frame with static := true} 12 (.bytes .memory) src : EM E [] _).run (L0 E, checkpoint)
def copied (mode : Bool) := (storeVal {frame with static := mode} 12 bytesTy dst sourceRef : EM E [] Unit).run (L0 E, checkpoint)
def selfCopied := (storeVal {frame with static := true} 12 bytesTy src sourceRef : EM E [] Unit).run (L0 E, checkpoint)
def exhausted := (storeVal {frame with static := true} 0 bytesTy dst sourceRef : EM E [] Unit).run (L0 E, checkpoint)
def mismatched := (storeData frame 12 bytesTy dst (Solidity.Source.Data.val (.bool true)) : EM E [] Unit).run (L0 E, checkpoint)
def observe (s : St E) := (do
  let len ← readLen frame dst
  let data ← loadBytes frame 8 dst 0 3
  pure (len, data) : EM E [] _).run (L0 E, s) |>.1


theorem observations :
    E.pathTy src = some (.bytes .storage) ∧
    E.pathTy dst = some (.bytes .storage) ∧
    (seed.run (L0 E, St.init E)).1 = .ok () ∧
    checkpoint.ex.journal.length = 7 ∧
    loaded.1 = .ok (.memRef (by rfl) 0) ∧
    loaded.2.2.heap.get 0 = some ⟨.bytes .memory, .bytes [7,9]⟩ ∧
    loaded.2.2.ex = checkpoint.ex ∧
    (copied false).1 = .ok () ∧
    observe (copied false).2.2 = .ok (2, [7,9,0]) ∧
    (copied false).2.2.ex.journal.length = checkpoint.ex.journal.length + 4 ∧
    (copied true).1 = .error (.revert []) ∧
    observe (copied true).2.2 = .ok (3, [1,2,3]) ∧
    (copied true).2.2.ex = checkpoint.ex ∧
    selfCopied.1 = .ok () ∧
    selfCopied.2.2.ex = checkpoint.ex ∧
    selfCopied.2.2.heap.next = 0 ∧
    exhausted.1 = .error .timeout ∧
    mismatched.1 = .error (.stuck "storage cell type") := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;> rfl

theorem store_history (mode : Bool) (n : Nat) :
    StaticJournal.History checkpoint.ex mode
      ((storeVal {frame with static := mode} n bytesTy dst sourceRef :
        EM E [] Unit).run (L0 E, checkpoint)).2.2.ex :=
  (store_histories (E := E) (Γ := []) {frame with static := mode} n).2.1
    bytesTy dst sourceRef (L0 E) checkpoint

theorem load_history (mode : Bool) (n : Nat) :
    StaticJournal.History checkpoint.ex mode
      ((loadElem {frame with static := true} n (.bytes .memory) src :
        EM E [] _).run (L0 E, checkpoint)).2.2.ex :=
  (load_histories (E := E) (Γ := []) mode {frame with static := true} n).2.1
    (.bytes .memory) src (L0 E) checkpoint

theorem ordinary_changes : observe (copied false).2.2 ≠ observe checkpoint := by
  change (.ok (2, [7,9,0]) : Except Halt (Nat × List UInt8)) ≠ .ok (3, [1,2,3])
  intro h
  cases h

end Solidity.Lowering.Readonly.CopyControls
