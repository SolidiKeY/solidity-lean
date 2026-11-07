import Solidity.Lowering.StorageOps.SourceFixedStorageCopy
import Solidity.Lowering.StorageOps.SourceIntCopyReadbacks

/-! Inhabited actual signed fixed-length Source copy, complete ordered
observations, intrinsically non-word fixed roots, failure/alias/snapshot controls.
Source operation evidence only; physical fixed target composition is separate. -/
namespace Solidity.Backend.StorageOps.SourceFixedStorageCopy.Controls
open TypeGraph Solidity.Storage Solidity.Storage.Representation Solidity.Storage.Representation.Graph
open SourceStorageCopy
open SourceArrayDeleteTarget (wordAt)
open SourceIntCopyReadbacks (int256 sourceValue word_agrees)
private def uintSyntax : Source.Syn .typeName := .elem (.int false 256 (by decide))
private def unit : Source.Syn .unit := .unit (.cons (.contract false "C" .none .nil
  (.cons (.stateVar (.array (.elem (.int true 256 (by decide))) (.some (.lit (.num (.dec 3 0 0))))) none none none false "left" .none)
    (.cons (.stateVar (.array (.elem (.int true 256 (by decide))) (.some (.lit (.num (.dec 3 0 0))))) none none none false "right" .none)
      (.cons (.stateVar (.elem .bool) none none none false "bad" .none)
        (.cons (.stateVar uintSyntax none none none true "scratch" .none)
          (.cons (.stateVar uintSyntax none none none false "sentinel" .none) .nil)))))) .nil)
private def env : Source.Env := unit.env
private def left : Source.SPath := ⟨⟨some "C","left"⟩,[]⟩
private def right : Source.SPath := ⟨⟨some "C","right"⟩,[]⟩
private def bad : Source.SPath := ⟨⟨some "C","bad"⟩,[]⟩
private def scratch : Source.SPath := ⟨⟨some "C","scratch"⟩,[]⟩
private def sentinel : Source.SPath := ⟨⟨some "C","sentinel"⟩,[]⟩
private def missing : Source.SPath := ⟨⟨some "C","missing"⟩,[]⟩
private def elem (p : Source.SPath) (i : Nat) : Source.SPath := p.go (.index i)
private def address : Roadmap.Address := ⟨7,by decide⟩
private def zeroInt : PrimTy.int.Denote := ⟨0,by decide⟩
private def pos7 : PrimTy.int.Denote := ⟨7,by decide⟩
private def neg17 : PrimTy.int.Denote := ⟨-17,by decide⟩
private def neg31 : PrimTy.int.Denote := ⟨-31,by decide⟩
private def neg1 : PrimTy.int.Denote := ⟨-1,by decide⟩
private def neg23 : PrimTy.int.Denote := ⟨-23,by decide⟩
private def neg71 : PrimTy.int.Denote := ⟨-71,by decide⟩
private def sw (v : PrimTy.int.Denote) : Semantics.Word := PrimTy.toWord v
private def bits (v : PrimTy.int.Denote) : Nat := (TargetOperations.encodeWord (sw v)).val
private def storage : Source.Storage env.layout env.cellTy :=
 let s := (Source.Storage.empty : Source.Storage env.layout env.cellTy)
 let s := s.write (elem left 0) (sourceValue neg17)
 let s := s.write (elem left 2) (sourceValue neg31)
 let s := s.write (elem right 0) (sourceValue pos7)
 let s := s.write (elem right 1) (sourceValue neg1)
 let s := s.write (elem right 2) (sourceValue neg23)
 let s := s.write (elem right 3) (sourceValue neg71)
 let s := s.write bad (.bool true)
 s.write sentinel (.int 99 (by decide))
private def state : Source.St env :=
  { ex :=
      { world := ⟨fun a => if a = address then
          { balance := 19, nonce := 3, code := some 0, storage := storage }
          else Source.Account.empty _⟩
        transient := Source.Transient.empty.set address
          ((Source.Storage.empty : Source.Storage env.layout env.cellTy).write scratch (.int 5 (by decide)))
        journal := [] }
    heap := Source.Heap.empty
    events := []
    logs := []
    fnLocals := ⟨[],.nil⟩ }
private def frame : Source.Fr :=
  {this := address,sender := ⟨13,by decide⟩,value := ⟨0,by decide⟩,static := false,contract := "C"}
private def initial : Source.Locals env.layout [] × Source.St env := (.nil,state)

private def ty : Source.STy := .array .storage (.int int256) (some 3)
private def payload (j : Nat) : Source.Val env.layout (.int int256) := sourceValue (if j=0 then neg17 else if j=1 then zeroInt else neg31)
private def sourceOp (src dst : Source.SPath) : Source.EM env [] Unit := Source.storeVal frame 7 ty dst (Source.Val.storRef (τ:=ty) rfl src)
private def copied := (sourceOp left right).run initial
private def log := writes frame int256 right payload (fun j => (SourceFixedStorageCopy.element_type (E:=env) int256 right 3 rfl j).symm) 0 3
private def snapshot : Source.Data env.layout (.array .memory (.int int256) (some 3)) :=
 .array 3 (fun _ h => by cases h; rfl) (fun j => .val (payload j.val))
private def changed : Source.Locals env.layout [] × Source.St env :=
 (.nil,{state with ex:=state.ex.apply (cellOp env frame (elem left 0) (some (sourceValue zeroInt)))})
private def captured := (Source.storeData (E:=env) (Γ:=[]) frame 6 ty right snapshot).run changed
private def fresh := (sourceOp left right).run changed
private def shortCopied := (Source.storeVal (E:=env) (Γ:=[]) frame 6 ty right (Source.Val.storRef (τ:=ty) rfl left)).run initial
private def staticCopied := (Source.storeVal (E:=env) (Γ:=[]) {frame with static:=true} 7 ty right (Source.Val.storRef (τ:=ty) rfl left)).run initial
private def wrongDynamic := (Source.storeVal (E:=env) (Γ:=[]) frame 7 (.array .storage (.int int256) none) right
 (Source.Val.storRef (τ:=.array .storage (.int int256) none) rfl left)).run initial
private def sourcePaths := [left,elem left 0,elem left 1,elem left 2,elem left 3,right,elem right 0,elem right 1,elem right 2,elem right 3,bad,sentinel,missing]
private def view (ex : Source.ExecState env.layout env.lay env.lay) := sourcePaths.map (wordAt frame ex) ++
 [(((ex.transient.cells frame.this).read scratch).bind Source.Val.word).map Fin.val]
private def context (s : Source.St env) := (s.heap,s.events,s.logs,s.fnLocals,
 (s.ex.world.accounts address).balance,(s.ex.world.accounts address).nonce,(s.ex.world.accounts address).code,
 (s.ex.world.accounts ⟨11,by decide⟩).balance,(s.ex.world.accounts ⟨11,by decide⟩).nonce,(s.ex.world.accounts ⟨11,by decide⟩).code)
private theorem reads : ∀ j<3,(Source.readAt (E:=env) (Γ:=[]) frame (elem left j) (.int int256)).run initial=(.ok (payload j),initial) := by
 intro j inside
 have alternatives : j=0 ∨ j=1 ∨ j=2 := by omega
 rcases alternatives with rfl|rfl|rfl <;> rfl

theorem certificate : copied=(.ok (),(Source.Locals.nil,{state with ex:=state.ex.run log})) :=
 complete frame rfl int256 left right (by decide) 3 0 payload rfl .nil state reads
private theorem source_word (ex : Source.ExecState env.layout env.lay env.lay) (path : Source.SPath)
 (v : PrimTy.int.Denote) (typed : env.cellTy path=.int int256)
 (stored : (ex.world.accounts frame.this).storage.read path=some (show Source.Val env.layout (env.cellTy path) from typed.symm ▸ sourceValue v)) :
 wordAt frame ex path=some (bits v) := by
 unfold wordAt
 rw [stored]
 simp only [Option.bind_some,SourceCopyReadbacks.word_cast]
 exact word_agrees v

private theorem initial_view : view state.ex=[none,some (bits neg17),some (bits zeroInt),some (bits neg31),some (bits zeroInt),none,some (bits pos7),some (bits neg1),some (bits neg23),some (bits neg71),some 1,some 99,none,some 5] := by
 have h0 := source_word state.ex (elem left 0) neg17 rfl rfl
 have h1 := source_word state.ex (elem left 1) zeroInt rfl rfl
 have h2 := source_word state.ex (elem left 2) neg31 rfl rfl
 have h3 := source_word state.ex (elem left 3) zeroInt rfl rfl
 have h4 := source_word state.ex (elem right 0) pos7 rfl rfl
 have h5 := source_word state.ex (elem right 1) neg1 rfl rfl
 have h6 := source_word state.ex (elem right 2) neg23 rfl rfl
 have h7 := source_word state.ex (elem right 3) neg71 rfl rfl
 unfold view sourcePaths
 simp only [List.map_cons,List.map_nil]
 rw [h0,h1,h2,h3,h4,h5,h6,h7]
 rfl
private theorem copied_view : view copied.2.2.ex=[none,some (bits neg17),some (bits zeroInt),some (bits neg31),some (bits zeroInt),none,some (bits neg17),some (bits zeroInt),some (bits neg31),some (bits neg71),some 1,some 99,none,some 5] := by
 have h0 := source_word copied.2.2.ex (elem left 0) neg17 rfl rfl
 have h1 := source_word copied.2.2.ex (elem left 1) zeroInt rfl rfl
 have h2 := source_word copied.2.2.ex (elem left 2) neg31 rfl rfl
 have h3 := source_word copied.2.2.ex (elem left 3) zeroInt rfl rfl
 have h4 := source_word copied.2.2.ex (elem right 0) neg17 rfl rfl
 have h5 := source_word copied.2.2.ex (elem right 1) zeroInt rfl rfl
 have h6 := source_word copied.2.2.ex (elem right 2) neg31 rfl rfl
 have h7 := source_word copied.2.2.ex (elem right 3) neg71 rfl rfl
 unfold view sourcePaths
 simp only [List.map_cons,List.map_nil]
 rw [h0,h1,h2,h3,h4,h5,h6,h7]
 rfl
private theorem short_view : view shortCopied.2.2.ex=[none,some (bits neg17),some (bits zeroInt),some (bits neg31),some (bits zeroInt),none,some (bits neg17),some (bits zeroInt),some (bits neg23),some (bits neg71),some 1,some 99,none,some 5] := by
 have h0 := source_word shortCopied.2.2.ex (elem left 0) neg17 rfl rfl
 have h1 := source_word shortCopied.2.2.ex (elem left 1) zeroInt rfl rfl
 have h2 := source_word shortCopied.2.2.ex (elem left 2) neg31 rfl rfl
 have h3 := source_word shortCopied.2.2.ex (elem left 3) zeroInt rfl rfl
 have h4 := source_word shortCopied.2.2.ex (elem right 0) neg17 rfl rfl
 have h5 := source_word shortCopied.2.2.ex (elem right 1) zeroInt rfl rfl
 have h6 := source_word shortCopied.2.2.ex (elem right 2) neg23 rfl rfl
 have h7 := source_word shortCopied.2.2.ex (elem right 3) neg71 rfl rfl
 unfold view sourcePaths
 simp only [List.map_cons,List.map_nil]
 rw [h0,h1,h2,h3,h4,h5,h6,h7]
 rfl
private theorem captured_view : view captured.2.2.ex=[none,some (bits zeroInt),some (bits zeroInt),some (bits neg31),some (bits zeroInt),none,some (bits neg17),some (bits zeroInt),some (bits neg31),some (bits neg71),some 1,some 99,none,some 5] := by
 have h0 := source_word captured.2.2.ex (elem left 0) zeroInt rfl rfl
 have h1 := source_word captured.2.2.ex (elem left 1) zeroInt rfl rfl
 have h2 := source_word captured.2.2.ex (elem left 2) neg31 rfl rfl
 have h3 := source_word captured.2.2.ex (elem left 3) zeroInt rfl rfl
 have h4 := source_word captured.2.2.ex (elem right 0) neg17 rfl rfl
 have h5 := source_word captured.2.2.ex (elem right 1) zeroInt rfl rfl
 have h6 := source_word captured.2.2.ex (elem right 2) neg31 rfl rfl
 have h7 := source_word captured.2.2.ex (elem right 3) neg71 rfl rfl
 unfold view sourcePaths
 simp only [List.map_cons,List.map_nil]
 rw [h0,h1,h2,h3,h4,h5,h6,h7]
 rfl
private theorem fresh_view : view fresh.2.2.ex=[none,some (bits zeroInt),some (bits zeroInt),some (bits neg31),some (bits zeroInt),none,some (bits zeroInt),some (bits zeroInt),some (bits neg31),some (bits neg71),some 1,some 99,none,some 5] := by
 have h0 := source_word fresh.2.2.ex (elem left 0) zeroInt rfl rfl
 have h1 := source_word fresh.2.2.ex (elem left 1) zeroInt rfl rfl
 have h2 := source_word fresh.2.2.ex (elem left 2) neg31 rfl rfl
 have h3 := source_word fresh.2.2.ex (elem left 3) zeroInt rfl rfl
 have h4 := source_word fresh.2.2.ex (elem right 0) zeroInt rfl rfl
 have h5 := source_word fresh.2.2.ex (elem right 1) zeroInt rfl rfl
 have h6 := source_word fresh.2.2.ex (elem right 2) neg31 rfl rfl
 have h7 := source_word fresh.2.2.ex (elem right 3) neg71 rfl rfl
 unfold view sourcePaths
 simp only [List.map_cons,List.map_nil]
 rw [h0,h1,h2,h3,h4,h5,h6,h7]
 rfl

theorem ordered : (view state.ex,view copied.2.2.ex,copied.2.2.ex.journal.length)=
 ([none,some (bits neg17),some (bits zeroInt),some (bits neg31),some (bits zeroInt),none,some (bits pos7),some (bits neg1),some (bits neg23),some (bits neg71),some 1,some 99,none,some 5],[none,some (bits neg17),some (bits zeroInt),some (bits neg31),some (bits zeroInt),none,some (bits neg17),some (bits zeroInt),some (bits neg31),some (bits neg71),some 1,some 99,none,some 5],3) := by
 exact Prod.ext initial_view (Prod.ext copied_view rfl)

theorem source_context : context copied.2.2=context state := by rfl

/-- Fixed roots have intrinsic empty-tuple CELL TYPES, with no Val or default,
not integer length headers. Both roots have absent cells and no word. A dynamic
length read fails without a value; the actual declared fixed copy succeeds.
The wrong dynamic annotation is a malformed interpretation, not an admission. -/
theorem no_dynamic_header :
 (Source.readLen (E:=env) (Γ:=[]) frame left).run initial=(.error (.stuck "storage cell without a value"),initial) ∧
 (Source.readLen (E:=env) (Γ:=[]) frame right).run initial=(.error (.stuck "storage cell without a value"),initial) ∧
 wordAt frame copied.2.2.ex left=none ∧ wordAt frame copied.2.2.ex right=none ∧
 (copied.2.2.ex.world.accounts address).storage.cell left=none ∧
 (copied.2.2.ex.world.accounts address).storage.cell right=none ∧
 wrongDynamic=(.error (.stuck "storage cell without a value"),initial) := by exact ⟨rfl,rfl,rfl,rfl,rfl,rfl,rfl⟩

private def arrayRef : Source.Val env.layout ty := .storRef rfl right
private def alias : Source.Loc env.layout [] (.int int256) := .stor (elem right 2)

theorem live_fixed_alias :
 (Source.indexLoc (E:=env) (Γ:=[]) frame arrayRef 2).run initial=(.ok alias,initial) ∧
 (Source.readLoc (E:=env) (Γ:=[]) frame alias).run initial=(.ok (sourceValue neg23),initial) ∧
 (Source.indexLoc (E:=env) (Γ:=[]) frame arrayRef 2).run copied.2=(.ok alias,copied.2) ∧
 (Source.readLoc (E:=env) (Γ:=[]) frame alias).run copied.2=(.ok (sourceValue neg31),copied.2) ∧
 (Source.indexLoc (E:=env) (Γ:=[]) frame arrayRef 3).run copied.2=(.error (.revert (Source.panicData .index)),copied.2) ∧
 (Source.readAt (E:=env) (Γ:=[]) frame (elem right 3) (.int int256)).run copied.2=(.ok (sourceValue neg71),copied.2) ∧
 Source.panicData .index=([0x4e,0x48,0x7b,0x71] ++ List.replicate 31 0 ++ [0x32]) := by exact ⟨rfl,rfl,rfl,rfl,rfl,rfl,rfl⟩

theorem fuel_static : (shortCopied.1,view shortCopied.2.2.ex,shortCopied.2.2.ex.journal.length)=
 (.error .timeout,[none,some (bits neg17),some (bits zeroInt),some (bits neg31),some (bits zeroInt),none,some (bits neg17),some (bits zeroInt),some (bits neg23),some (bits neg71),some 1,some 99,none,some 5],2) ∧ staticCopied=(.error (.revert []),initial) := by
 exact ⟨Prod.ext rfl (Prod.ext short_view rfl),rfl⟩

theorem malformed_source :
 (sourceOp bad right).run initial=(.error (.stuck "storage cell without a value"),initial) ∧
 (Source.storeVal (E:=env) (Γ:=[]) frame 7 (.array .storage (.int Source.IntTy.u256) (some 3)) right
  (Source.Val.storRef (τ:=.array .storage (.int Source.IntTy.u256) (some 3)) rfl left)).run initial=
 (.error (.stuck "storage cell type"),initial) := by exact ⟨rfl,rfl⟩

theorem snapshot_order :
 (Source.loadMem (E:=env) (Γ:=[]) frame 5 (.array .memory (.int int256) (some 3)) left).run initial=(.ok snapshot,initial) ∧
 (captured.1,fresh.1,view captured.2.2.ex,view fresh.2.2.ex,captured.2.2.ex.journal.length,fresh.2.2.ex.journal.length)=
 (.ok (),.ok (),[none,some (bits zeroInt),some (bits zeroInt),some (bits neg31),some (bits zeroInt),none,some (bits neg17),some (bits zeroInt),some (bits neg31),some (bits neg71),some 1,some 99,none,some 5],[none,some (bits zeroInt),some (bits zeroInt),some (bits neg31),some (bits zeroInt),none,some (bits zeroInt),some (bits zeroInt),some (bits neg31),some (bits neg71),some 1,some 99,none,some 5],4,4) := by
 refine ⟨load_fixed frame int256 left 3 0 payload initial reads,?_⟩
 exact Prod.ext rfl (Prod.ext rfl (Prod.ext captured_view (Prod.ext fresh_view rfl)))

theorem same_path : (sourceOp left left).run initial=(.ok (),initial) ∧
 (Source.storeVal (E:=env) (Γ:=[]) {frame with static:=true} 7 ty left (Source.Val.storRef (τ:=ty) rfl left)).run initial=(.ok (),initial) := by exact ⟨rfl,rfl⟩

theorem explicit_restore :
 (copied.2.1,{copied.2.2 with ex:=(state.ex.enter frame.this frame.sender frame.value [] frame.static).rollback copied.2.2.ex})=(Source.Locals.nil,state) :=
 rollback frame rfl int256 left right (by decide) 3 0 payload rfl .nil state [] reads
/-- info: 'Solidity.Backend.StorageOps.SourceFixedStorageCopy.Controls.certificate' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in #print axioms certificate
/-- info: 'Solidity.Backend.StorageOps.SourceFixedStorageCopy.Controls.ordered' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in #print axioms ordered
/-- info: 'Solidity.Backend.StorageOps.SourceFixedStorageCopy.Controls.source_context' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in #print axioms source_context
/-- info: 'Solidity.Backend.StorageOps.SourceFixedStorageCopy.Controls.no_dynamic_header' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in #print axioms no_dynamic_header
/-- info: 'Solidity.Backend.StorageOps.SourceFixedStorageCopy.Controls.live_fixed_alias' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in #print axioms live_fixed_alias
/-- info: 'Solidity.Backend.StorageOps.SourceFixedStorageCopy.Controls.fuel_static' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in #print axioms fuel_static
/-- info: 'Solidity.Backend.StorageOps.SourceFixedStorageCopy.Controls.malformed_source' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in #print axioms malformed_source
/-- info: 'Solidity.Backend.StorageOps.SourceFixedStorageCopy.Controls.snapshot_order' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in #print axioms snapshot_order
/-- info: 'Solidity.Backend.StorageOps.SourceFixedStorageCopy.Controls.same_path' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in #print axioms same_path
/-- info: 'Solidity.Backend.StorageOps.SourceFixedStorageCopy.Controls.explicit_restore' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in #print axioms explicit_restore
end Solidity.Backend.StorageOps.SourceFixedStorageCopy.Controls
