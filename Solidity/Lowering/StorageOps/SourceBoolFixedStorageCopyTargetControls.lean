import Solidity.Lowering.StorageOps.SourceBoolFixedStorageCopyTarget

/-! C121 Bool Source fixture reused unchanged as actual Source/snapshot target
combination; raw absent differs from present false, no UInt value coercion. -/
namespace Solidity.Backend.StorageOps.SourceBoolFixedStorageCopyTarget.Controls
open TypeGraph Solidity.Storage Solidity.Storage.Representation Solidity.Storage.Representation.Graph
open SourceStorageCopy
open SourceArrayDeleteTarget (wordAt)
private def uintSyntax : Source.Syn .typeName := .elem (.int false 256 (by decide))
private def unit : Source.Syn .unit := .unit (.cons (.contract false "C" .none .nil
  (.cons (.stateVar (.array (.elem .bool) (.some (.lit (.num (.dec 3 0 0))))) none none none false "left" .none)
    (.cons (.stateVar (.array (.elem .bool) (.some (.lit (.num (.dec 3 0 0))))) none none none false "right" .none)
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
private def falseValue : Bool := false
private def trueValue : Bool := true
private def sw (v : Bool) : Semantics.Word := PrimTy.toWord (p:=.bool) v
private def bits (v : Bool) : Nat := (TargetOperations.encodeWord (sw v)).val
private def sourceValue {D : Source.Layout} (v : Bool) : Source.Val D .bool := .bool v
private theorem word_agrees {D : Source.Layout} (v : Bool) :
 (sourceValue (D:=D) v).word.map Fin.val=some (bits v) := by cases v <;> rfl
private def storage : Source.Storage env.layout env.cellTy :=
 let s := (Source.Storage.empty : Source.Storage env.layout env.cellTy)
 let s := s.write (elem left 0) (sourceValue trueValue)
 let s := s.write (elem left 2) (sourceValue falseValue)
 let s := s.write (elem right 0) (sourceValue falseValue)
 let s := s.write (elem right 1) (sourceValue trueValue)
 let s := s.write (elem right 2) (sourceValue trueValue)
 let s := s.write (elem right 3) (sourceValue trueValue)
 let s := s.write bad (.bool true)
 s.write sentinel (.int 99 (by decide))
private def state : Source.St env :=
  { ex :=
      { world := ⟨fun a => if a = address then
          { balance := ⟨19,by decide⟩, nonce := 3, code := some 0, storage := storage }
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

private def ty : Source.STy := .array .storage .bool (some 3)
private def payload (j : Nat) : Source.Val env.layout .bool := sourceValue (if j=0 then trueValue else if j=1 then falseValue else falseValue)
private def sourceOp (src dst : Source.SPath) : Source.EM env [] Unit := Source.storeVal frame 7 ty dst (Source.Val.storRef (τ:=ty) rfl src)
private def copied := (sourceOp left right).run initial
private def log := SourceBoolStorageCopy.writes frame right payload (fun j => (SourceBoolFixedStorageCopy.element_type (E:=env) right 3 rfl j).symm) 0 3
private def sourcePaths := [left,elem left 0,elem left 1,elem left 2,elem left 3,right,elem right 0,elem right 1,elem right 2,elem right 3,bad,sentinel,missing]
private def view (ex : Source.ExecState env.layout env.lay env.lay) := sourcePaths.map (wordAt frame ex) ++
 [(((ex.transient.cells frame.this).read scratch).bind Source.Val.word).map Fin.val]
private def context (s : Source.St env) := (s.heap,s.events,s.logs,s.fnLocals,
 (s.ex.world.accounts address).balance,(s.ex.world.accounts address).nonce,(s.ex.world.accounts address).code,
 (s.ex.world.accounts ⟨11,by decide⟩).balance,(s.ex.world.accounts ⟨11,by decide⟩).nonce,(s.ex.world.accounts ⟨11,by decide⟩).code)
private theorem reads : ∀ j<3,(Source.readAt (E:=env) (Γ:=[]) frame (elem left j) .bool).run initial=(.ok (payload j),initial) := by
 intro j inside
 have alternatives : j=0 ∨ j=1 ∨ j=2 := by omega
 rcases alternatives with rfl|rfl|rfl <;> rfl

private theorem source_word (ex : Source.ExecState env.layout env.lay env.lay) (path : Source.SPath)
 (v : Bool) (typed : env.cellTy path=.bool)
 (stored : (ex.world.accounts frame.this).storage.read path=some (show Source.Val env.layout (env.cellTy path) from typed.symm ▸ sourceValue v)) :
 wordAt frame ex path=some (bits v) := by
 unfold wordAt
 rw [stored]
 simp only [Option.bind_some,SourceCopyReadbacks.word_cast]
 exact word_agrees v

private theorem initial_view : view state.ex=[none,some (bits trueValue),some (bits falseValue),some (bits falseValue),some (bits falseValue),none,some (bits falseValue),some (bits trueValue),some (bits trueValue),some (bits trueValue),some 1,some 99,none,some 5] := by
 have h0 := source_word state.ex (elem left 0) trueValue rfl rfl
 have h1 := source_word state.ex (elem left 1) falseValue rfl rfl
 have h2 := source_word state.ex (elem left 2) falseValue rfl rfl
 have h3 := source_word state.ex (elem left 3) falseValue rfl rfl
 have h4 := source_word state.ex (elem right 0) falseValue rfl rfl
 have h5 := source_word state.ex (elem right 1) trueValue rfl rfl
 have h6 := source_word state.ex (elem right 2) trueValue rfl rfl
 have h7 := source_word state.ex (elem right 3) trueValue rfl rfl
 unfold view sourcePaths
 simp only [List.map_cons,List.map_nil]
 rw [h0,h1,h2,h3,h4,h5,h6,h7]
 rfl
private theorem copied_view : view copied.2.2.ex=[none,some (bits trueValue),some (bits falseValue),some (bits falseValue),some (bits falseValue),none,some (bits trueValue),some (bits falseValue),some (bits falseValue),some (bits trueValue),some 1,some 99,none,some 5] := by
 have h0 := source_word copied.2.2.ex (elem left 0) trueValue rfl rfl
 have h1 := source_word copied.2.2.ex (elem left 1) falseValue rfl rfl
 have h2 := source_word copied.2.2.ex (elem left 2) falseValue rfl rfl
 have h3 := source_word copied.2.2.ex (elem left 3) falseValue rfl rfl
 have h4 := source_word copied.2.2.ex (elem right 0) trueValue rfl rfl
 have h5 := source_word copied.2.2.ex (elem right 1) falseValue rfl rfl
 have h6 := source_word copied.2.2.ex (elem right 2) falseValue rfl rfl
 have h7 := source_word copied.2.2.ex (elem right 3) trueValue rfl rfl
 unfold view sourcePaths
 simp only [List.map_cons,List.map_nil]
 rw [h0,h1,h2,h3,h4,h5,h6,h7]
 rfl
private def size : TypeGraph.FixedSize := ⟨3,by decide⟩
private def indices : List Nat := [2,0,3,1,2,4]
private def src : Evm.Slot := .root 0
private def dst : Evm.Slot := .root 8
private noncomputable def target : Evm.Machine :=
 {Evm.Machine.init (fun _ => 19) ⟨7,by decide⟩ with
 store:=⟨fun l => if l=.root 0 then TargetOperations.encodeWord (sw trueValue) else
   if l=.root 2 then TargetOperations.encodeWord (sw falseValue) else
   if l=.root 8 then TargetOperations.encodeWord (sw falseValue) else
   if l=.root 9 then TargetOperations.encodeWord (sw trueValue) else
   if l=.root 10 then TargetOperations.encodeWord (sw trueValue) else
   if l=.root 11 then TargetOperations.encodeWord (sw trueValue) else
   if l=.root 20 then ⟨1,by decide⟩ else if l=.root 21 then ⟨99,by decide⟩ else ⟨0,by decide⟩⟩
 stack:=[.val ⟨23,by decide⟩,.slot (.root 31)]
 mem:=fun _ => .val ⟨41,by decide⟩
 caller:=⟨13,by decide⟩
 timestamp:=⟨53,by decide⟩}
private noncomputable def output := TargetFixedSnapshot.afterCopy .bool size target src dst
private theorem sourceWords : ∀ j<size.val,(payload j).word.map Fin.val=some (target.store (src.add j)) := by
 intro j inside
 change j<3 at inside
 have cases : j=0 ∨ j=1 ∨ j=2 := by omega
 rcases cases with rfl|rfl|rfl
 · exact word_agrees trueValue
 · exact word_agrees falseValue
 · exact word_agrees falseValue
private theorem olderWords : ∀ j ∈ indices,size.val≤j → wordAt frame state.ex (elem right j)=some (target.store (dst.add j)) := by
 intro j member older
 change 3≤j at older
 simp only [indices,List.mem_cons,List.not_mem_nil,or_false] at member
 rcases member with rfl|rfl|rfl|rfl|rfl|rfl
 all_goals first
  | omega
  | exact source_word state.ex (elem right 3) trueValue rfl rfl
  | exact source_word state.ex (elem right 4) falseValue rfl rfl

theorem certificate : copied=(.ok (),(Source.Locals.nil,{state with ex:=state.ex.run log})) ∧
 Evm.run (TargetFixedSnapshot.code .bool size src dst) target=.ok output 0 ∧
 (∀ j ∈ indices,wordAt frame copied.2.2.ex (elem right j)=some (output.store (dst.add j))) := by
 exact complete frame rfl left right (by decide) size 0 indices payload rfl rfl .nil state reads target src dst sourceWords olderWords

theorem source_ordered : (view state.ex,view copied.2.2.ex,copied.2.2.ex.journal.length)=
 ([none,some (bits trueValue),some (bits falseValue),some (bits falseValue),some (bits falseValue),none,some (bits falseValue),some (bits trueValue),some (bits trueValue),some (bits trueValue),some 1,some 99,none,some 5],
 [none,some (bits trueValue),some (bits falseValue),some (bits falseValue),some (bits falseValue),none,some (bits trueValue),some (bits falseValue),some (bits falseValue),some (bits trueValue),some 1,some 99,none,some 5],3) ∧
 context copied.2.2=context state := by
 exact ⟨Prod.ext initial_view (Prod.ext copied_view rfl),rfl⟩

private def targetSlots : List Evm.Slot := [.root 0,.root 1,.root 2,.root 3,.root 8,.root 9,.root 10,.root 11,.root 12,.root 20,.root 21,.root 31]
private def targetView (m : Evm.Machine) := targetSlots.map (fun l => m.store l)
private theorem copied_word (j : Nat) (inside : j<size.val) : output.store (dst.add j)=target.store (src.add j) :=
 TargetFixedSnapshot.after_data .bool size target src dst j inside
private theorem other_word (l : Evm.Slot) (outside : ∀ j<size.val,l≠dst.add j) : output.store l=target.store l :=
 TargetFixedSnapshot.after_outside .bool size target src dst l outside
private theorem after_view (machine : Evm.Machine) :
 targetView (TargetFixedSnapshot.afterCopy .bool size machine src dst)=
 [machine.store (.root 0),machine.store (.root 1),machine.store (.root 2),machine.store (.root 3),
  machine.store (.root 0),machine.store (.root 1),machine.store (.root 2),machine.store (.root 11),
  machine.store (.root 12),machine.store (.root 20),machine.store (.root 21),machine.store (.root 31)] := by
 have h0:=TargetFixedSnapshot.after_data .bool size machine src dst 0 (by decide)
 have h1:=TargetFixedSnapshot.after_data .bool size machine src dst 1 (by decide)
 have h2:=TargetFixedSnapshot.after_data .bool size machine src dst 2 (by decide)
 change (TargetFixedSnapshot.afterCopy .bool size machine src dst).store (.root 8)=_ at h0
 change (TargetFixedSnapshot.afterCopy .bool size machine src dst).store (.root 9)=_ at h1
 change (TargetFixedSnapshot.afterCopy .bool size machine src dst).store (.root 10)=_ at h2
 unfold targetView targetSlots
 simp only [List.map_cons,List.map_nil]
 rw [h0,h1,h2]
 have frame : ∀ l ∈ ([.root 0,.root 1,.root 2,.root 3,.root 11,.root 12,.root 20,.root 21,.root 31] : List Evm.Slot),(TargetFixedSnapshot.afterCopy .bool size machine src dst).store l=machine.store l := by
  intro l member
  apply TargetFixedSnapshot.after_outside .bool size machine src dst
  intro j inside equal
  change j<3 at inside
  have cases : j=0 ∨ j=1 ∨ j=2 := by omega
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl <;> rcases cases with rfl|rfl|rfl <;> cases equal
 rw [frame (.root 0) (by decide),frame (.root 1) (by decide),frame (.root 2) (by decide),frame (.root 3) (by decide),
  frame (.root 11) (by decide),frame (.root 12) (by decide),frame (.root 20) (by decide),frame (.root 21) (by decide),frame (.root 31) (by decide)]
 rfl

private theorem output_words : targetView output=
 [bits trueValue,0,bits falseValue,0,bits trueValue,0,bits falseValue,bits trueValue,0,1,99,0] := after_view target

theorem target_ordered : targetView target=[bits trueValue,0,bits falseValue,0,bits falseValue,bits trueValue,bits trueValue,bits trueValue,0,1,99,0] ∧
 targetView output=[bits trueValue,0,bits falseValue,0,bits trueValue,0,bits falseValue,bits trueValue,0,1,99,0] ∧
 {output with store:=target.store}=target := ⟨rfl,output_words,rfl⟩

theorem selected_ordered : indices.map (fun j => wordAt frame copied.2.2.ex (elem right j))=
 [some (bits falseValue),some (bits trueValue),some (bits trueValue),some 0,some (bits falseValue),some 0] := by
 have same : indices.map (fun j => wordAt frame copied.2.2.ex (elem right j))=indices.map (fun j => some (output.store (dst.add j))) :=
  List.map_congr_left (fun j member => certificate.2.2 j member)
 rw [same]
 have h0:=copied_word 0 (by decide)
 have h1:=copied_word 1 (by decide)
 have h2:=copied_word 2 (by decide)
 have h3:=other_word (.root 11) (by intro j inside same; have eq:=Evm.Slot.add_inj (s:=dst) (i:=3) (j:=j) same; change j<3 at inside; omega)
 have h4:=other_word (.root 12) (by intro j inside same; have eq:=Evm.Slot.add_inj (s:=dst) (i:=4) (j:=j) same; change j<3 at inside; omega)
 change output.store (.root 8)=_ at h0
 change output.store (.root 9)=_ at h1
 change output.store (.root 10)=_ at h2
 change [some (output.store (.root 10)),some (output.store (.root 8)),some (output.store (.root 11)),some (output.store (.root 9)),some (output.store (.root 10)),some (output.store (.root 12))]=_
 rw [h0,h1,h2,h3,h4]
 rfl

theorem root_presence : wordAt frame copied.2.2.ex left=none ∧ wordAt frame copied.2.2.ex right=none ∧
 ((state.ex.world.accounts address).storage.cell (elem left 1))=none ∧
 output.store dst=bits trueValue := by
 refine ⟨rfl,rfl,rfl,?_⟩
 exact copied_word 0 (by decide)

private noncomputable def wrongSource := {target with store:=Evm.WordStore.write target.store (.root 1) 1}
private noncomputable def wrongSourceOutput := TargetFixedSnapshot.afterCopy .bool size wrongSource src dst
private noncomputable def wrongOlder := {target with store:=Evm.WordStore.write target.store (.root 12) 1}
private noncomputable def wrongOlderOutput := TargetFixedSnapshot.afterCopy .bool size wrongOlder src dst

theorem required_old_agreements :
 ¬(∀ j<size.val,(payload j).word.map Fin.val=some (wrongSource.store (src.add j))) ∧
 ¬(∀ j ∈ indices,size.val≤j → wordAt frame state.ex (elem right j)=some (wrongOlder.store (dst.add j))) := by
 constructor
 · intro alleged
   have bad:=alleged 1 (by decide)
   have good:=word_agrees (D:=env.layout) falseValue
   change (sourceValue falseValue).word.map Fin.val=some 1 at bad
   rw [good] at bad
   change some (0:Nat)=some 1 at bad
   cases bad
 · intro alleged
   have bad:=alleged 4 (by decide) (by decide)
   have good:=source_word state.ex (elem right 4) falseValue rfl rfl
   rw [good] at bad
   change some (0:Nat)=some 1 at bad
   cases bad

theorem wrong_execution :
 Evm.run (TargetFixedSnapshot.code .bool size src dst) wrongSource=.ok wrongSourceOutput 0 ∧
 Evm.run (TargetFixedSnapshot.code .bool size src dst) wrongOlder=.ok wrongOlderOutput 0 ∧
 wrongSourceOutput.store (.root 9)=1 ∧ wrongOlderOutput.store (.root 12)=1 ∧
 wordAt frame copied.2.2.ex (elem right 1)=some 0 ∧ wordAt frame copied.2.2.ex (elem right 4)=some 0 := by
 refine ⟨TargetFixedSnapshot.run_code _ _ _ _ _,TargetFixedSnapshot.run_code _ _ _ _ _,?_,?_,?_,?_⟩
 · exact TargetFixedSnapshot.after_data .bool size wrongSource src dst 1 (by decide)
 · exact TargetFixedSnapshot.after_outside .bool size wrongOlder src dst (.root 12) (by intro j inside same; have eq:=Evm.Slot.add_inj (s:=dst) (i:=4) (j:=j) same; change j<3 at inside; omega)
 · exact source_word copied.2.2.ex (elem right 1) falseValue rfl rfl
 · exact source_word copied.2.2.ex (elem right 4) falseValue rfl rfl

/-- Complete OLD/result target observations for both failing agreement cases.
The independent Source result remains the one in source_ordered. -/
theorem wrong_ordered :
 targetView wrongSource=[bits trueValue,1,bits falseValue,0,bits falseValue,bits trueValue,bits trueValue,bits trueValue,0,1,99,0] ∧
 targetView wrongSourceOutput=[bits trueValue,1,bits falseValue,0,bits trueValue,1,bits falseValue,bits trueValue,0,1,99,0] ∧
 targetView wrongOlder=[bits trueValue,0,bits falseValue,0,bits falseValue,bits trueValue,bits trueValue,bits trueValue,1,1,99,0] ∧
 targetView wrongOlderOutput=[bits trueValue,0,bits falseValue,0,bits trueValue,0,bits falseValue,bits trueValue,1,1,99,0] ∧
 {wrongSourceOutput with store:=target.store}=target ∧ {wrongOlderOutput with store:=target.store}=target := by
 exact ⟨rfl,after_view wrongSource,rfl,after_view wrongOlder,rfl,rfl⟩

/-- Equal zero word observations do not erase the independent Source raw
presence distinction between absent and explicitly stored false. -/
theorem false_presence :
 (state.ex.world.accounts address).storage.cell (elem left 1)=none ∧
 (state.ex.world.accounts address).storage.cell (elem left 2)=some (.bool false) ∧
 (copied.2.2.ex.world.accounts address).storage.cell (elem left 1)=none ∧
 (copied.2.2.ex.world.accounts address).storage.cell (elem right 1)=some (.bool false) ∧
 (copied.2.2.ex.world.accounts address).storage.cell (elem right 2)=some (.bool false) ∧
 output.store (dst.add 1)=0 ∧ output.store (dst.add 2)=0 := by
 refine ⟨rfl,rfl,rfl,rfl,rfl,?_,?_⟩
 · exact copied_word 1 (by decide)
 · exact copied_word 2 (by decide)

/-- info: 'Solidity.Backend.StorageOps.SourceBoolFixedStorageCopyTarget.Controls.certificate' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in #print axioms certificate
/-- info: 'Solidity.Backend.StorageOps.SourceBoolFixedStorageCopyTarget.Controls.source_ordered' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in #print axioms source_ordered
/-- info: 'Solidity.Backend.StorageOps.SourceBoolFixedStorageCopyTarget.Controls.target_ordered' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in #print axioms target_ordered
/-- info: 'Solidity.Backend.StorageOps.SourceBoolFixedStorageCopyTarget.Controls.selected_ordered' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in #print axioms selected_ordered
/-- info: 'Solidity.Backend.StorageOps.SourceBoolFixedStorageCopyTarget.Controls.root_presence' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in #print axioms root_presence
/-- info: 'Solidity.Backend.StorageOps.SourceBoolFixedStorageCopyTarget.Controls.required_old_agreements' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in #print axioms required_old_agreements
/-- info: 'Solidity.Backend.StorageOps.SourceBoolFixedStorageCopyTarget.Controls.wrong_execution' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in #print axioms wrong_execution
/-- info: 'Solidity.Backend.StorageOps.SourceBoolFixedStorageCopyTarget.Controls.wrong_ordered' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in #print axioms wrong_ordered
/-- info: 'Solidity.Backend.StorageOps.SourceBoolFixedStorageCopyTarget.Controls.false_presence' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in #print axioms false_presence
end Solidity.Backend.StorageOps.SourceBoolFixedStorageCopyTarget.Controls
