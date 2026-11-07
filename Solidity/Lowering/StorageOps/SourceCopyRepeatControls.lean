import Solidity.Lowering.StorageOps.SourceCopyRepeat
import Solidity.Backend.StorageOps.TargetArrayRepeat

/-! Independent actual Source operations and actual runtime target programs.
All Source journals/partial effects/refusals and whole context are retained.
The entered-frame rollback below is explicit, never inferred from failure. -/
namespace Solidity.Backend.StorageOps.SourceCopyRepeat.Controls
open SourceStorageCopy SourceArrayDeleteTarget
private def uintSyntax : Source.Syn .typeName := .elem (.int false 256 (by decide))
private def unit : Source.Syn .unit := .unit (.cons (.contract false "C" .none .nil
  (.cons (.stateVar (.array uintSyntax .none) none none none false "left" .none)
    (.cons (.stateVar (.array uintSyntax .none) none none none false "right" .none)
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
private def storage : Source.Storage env.layout env.cellTy :=
  let s := (Source.Storage.empty : Source.Storage env.layout env.cellTy).write left (.int 2 (by decide))
  let s := s.write (elem left 0) (.int 53 (by decide))
  let s := s.write (elem left 1) (.int 59 (by decide))
  let s := s.write (elem left 2) (.int 61 (by decide))
  let s := s.write right (.int 3 (by decide))
  let s := s.write (elem right 0) (.int 7 (by decide))
  let s := s.write (elem right 1) (.int 17 (by decide))
  let s := s.write (elem right 2) (.int 23 (by decide))
  let s := s.write (elem right 3) (.int 71 (by decide))
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

private def target : Evm.Machine :=
 {stack := [.val ⟨17,by decide⟩,.slot (.root 9)],
  store := .ofFn (fun l => if l=.root 0 then 2 else if l=.root 1 then 3 else if l=.root 2 then 99 else
   if l=.data (.root 0) 0 then 53 else if l=.data (.root 0) 1 then 59 else if l=.data (.root 0) 2 then 61 else
   if l=.data (.root 1) 0 then 7 else if l=.data (.root 1) 1 then 17 else if l=.data (.root 1) 2 then 23 else if l=.data (.root 1) 3 then 71 else 0),
  mem := fun _ => .val ⟨31,by decide⟩,bal:=fun _ => 41,bal₀:=fun _ => 43,
  self:=⟨47,by decide⟩,caller:=⟨53,by decide⟩,callvalue:=⟨59,by decide⟩,timestamp:=⟨61,by decide⟩,accepts:=fun _ _ => false}
private def sourcePaths := [left,elem left 0,elem left 1,elem left 2,right,elem right 0,elem right 1,elem right 2,elem right 3,bad,sentinel,missing]
private def sourceView (ex : Source.ExecState env.layout env.lay env.lay) := sourcePaths.map (wordAt frame ex) ++
 [(((ex.transient.cells frame.this).read scratch).bind Source.Val.word).map Fin.val]
private def targetSlots : List Evm.Slot := [.root 0,.root 1,.root 2,.data (.root 0) 0,.data (.root 0) 1,.data (.root 0) 2,.data (.root 0) 3,
 .data (.root 1) 0,.data (.root 1) 1,.data (.root 1) 2,.data (.root 1) 3]
private def targetView (s : Evm.Machine) := targetSlots.map (fun slot => s.store slot)

private def ty : Source.STy := .array .storage (.int Source.IntTy.u256) none
private def payload (j : Nat) : Source.Val env.layout (.int Source.IntTy.u256) := if j=0 then .int 53 (by decide) else .int 59 (by decide)
private def op (budget : Nat) : Source.EM env [] Unit := Source.storeVal frame budget ty right (Source.Val.storRef (τ:=ty) rfl left)
private def first := (op 7).run initial
private def second := (op 6).run first.2
private def combined := (op 7 >>= fun _ => op 6).run initial
private def firstLog := copyLog frame Source.IntTy.u256 right 2 3 payload rfl
private def secondLog := copyLog frame Source.IntTy.u256 right 2 2 payload rfl
private def expectedFirst : Source.St env := {state with ex:=state.ex.run firstLog}
private def expectedFinal : Source.St env := {state with ex:=(state.ex.run firstLog).run secondLog}
private def target1 := TargetArrayCopyTail.afterCopy target target.stack (.root 0) (.root 1)
private def target2 := TargetArrayCopyTail.afterCopy target1 target.stack (.root 0) (.root 1)
private theorem outside : ∀ query,query=left ∨ (∃ j<2,query=elem left j) →
 query≠right ∧ (∀ j<2,query≠elem right j) ∧ (∀ j∈List.range' 2 (3-2),query≠elem right j) := by
 intro query member
 rcases member with rfl | ⟨i,_,rfl⟩
 all_goals refine ⟨?_,?_,?_⟩
 all_goals first
  | (intro same; have roots:=congrArg Source.SPath.root same; exact (by decide : left.root≠right.root) roots)
  | (intro j _ same; have roots:=congrArg Source.SPath.root same; exact (by decide : left.root≠right.root) roots)
private theorem sourceReads : ∀ j<2,(Source.readAt (E:=env) (Γ:=[]) frame (elem left j) (.int Source.IntTy.u256)).run initial=(.ok (payload j),initial) := by
 intro j inside
 have choices : j=0 ∨ j=1 := by omega
 rcases choices with rfl|rfl <;> rfl

/-- Every OLD premise is inhabited; no intermediate Source relation assumed. -/
theorem certificate : first=(.ok (),(Source.Locals.nil,expectedFirst)) ∧
 second=(.ok (),(Source.Locals.nil,expectedFinal)) ∧ combined=(.ok (),(Source.Locals.nil,expectedFinal)) ∧
 (∀ query,wordAt frame second.2.2.ex query=wordAt frame first.2.2.ex query) ∧
 second.2.2.ex.journal.length=7 ∧ first.2.2.ex.journal.length<second.2.2.ex.journal.length := by
 have actual := SourceCopyRepeat.complete (E:=env) (Γ:=[]) frame rfl left right (by decide) 2 3 (by decide) payload rfl rfl .nil state rfl sourceReads rfl outside
 have one : first=(.ok (),(Source.Locals.nil,expectedFirst)) := actual.1
 have two : second=(.ok (),(Source.Locals.nil,expectedFinal)) := by
  change (op 6).run first.2=_
  rw [one]
  exact actual.2.1
 refine ⟨one,two,actual.2.2.1,?_,?_,?_⟩
 · rw [one,two]
   exact actual.2.2.2.1
 · rw [two]
   exact actual.2.2.2.2.1
 · rw [one,two]
   exact actual.2.2.2.2.2

/-- COMPLETE old/once/twice Source observations, including Bool/transient/
missing/retained fields, and COMPLETE old/once/twice target word vectors. -/
theorem ordered :
 (sourceView state.ex,sourceView first.2.2.ex,sourceView second.2.2.ex,
  targetView target,targetView target1,targetView target2,
  state.ex.journal.length,first.2.2.ex.journal.length,second.2.2.ex.journal.length)=
 ([some 2,some 53,some 59,some 61,some 3,some 7,some 17,some 23,some 71,some 1,some 99,none,some 5],
  [some 2,some 53,some 59,some 61,some 2,some 53,some 59,some 0,some 71,some 1,some 99,none,some 5],
  [some 2,some 53,some 59,some 61,some 2,some 53,some 59,some 0,some 71,some 1,some 99,none,some 5],
  [2,3,99,53,59,61,0,7,17,23,71],
  [2,2,99,53,59,61,0,53,59,0,71],
  [2,2,99,53,59,61,0,53,59,0,71],0,4,7) := by
 rw [certificate.1,certificate.2.1]
 rfl

/-- TWO actual target programs and the independent Source second-copy reads
agree on the captured operands; no ordinary Source compiler is assumed. -/
theorem target_agreement :
 Evm.run (TargetArrayRepeat.code (.root 0) (.root 1)++TargetArrayRepeat.code (.root 0) (.root 1)) target=.ok target1 0 ∧
 wordAt frame second.2.2.ex right=some (target1.store (.root 1)) ∧
 (∀ j∈[0,1,2,3],wordAt frame second.2.2.ex (elem right j)=some (target1.store (.data (.root 1) j))) := by
 refine ⟨(TargetArrayRepeat.complete target (.root 0) (.root 1) (Or.inr (by decide))).1,?_,?_⟩
 · rw [certificate.2.1]
   rfl
 · intro j member
   simp only [List.mem_cons,List.not_mem_nil,or_false] at member
   rcases member with rfl|rfl|rfl|rfl <;> rw [certificate.2.1] <;> rfl

/-- Repeated storage observations do NOT make the actual Source state repeat. -/
theorem state_nonidentity : second.2.2≠first.2.2 ∧
 (∀ query,wordAt frame second.2.2.ex query=wordAt frame first.2.2.ex query) := by
 refine ⟨?_,certificate.2.2.2.1⟩
 intro same
 have lengths : 7=4 := congrArg (fun s : Source.St env => s.ex.journal.length) same
 exact (by decide : 7≠4) lengths

/-- Explicit original frame rollback after BOTH actual operations, not an
implicit result of Source timeout/revert or the target program. -/
theorem explicit_rollback :
 (state.ex.enter frame.this frame.sender frame.value [] frame.static).rollback second.2.2.ex=state.ex := by
 rw [certificate.2.1]
 change (state.ex.enter frame.this frame.sender frame.value [] frame.static).rollback
  ((state.ex.run firstLog).run secondLog)=state.ex
 rw [← Source.run_append]
 exact Source.rollback_run state.ex (firstLog++secondLog) frame.this frame.sender frame.value [] frame.static

private def sourceContext (s : Source.St env) := (s.heap,s.events,s.logs,s.fnLocals,s.ex.transient,
 (s.ex.world.accounts frame.this).balance,(s.ex.world.accounts frame.this).nonce,(s.ex.world.accounts frame.this).code)
private def targetContext (m : Evm.Machine) := (m.stack,m.mem,m.bal,m.bal₀,m.self,m.accepts,m.caller,m.callvalue,m.timestamp)
/-- Full function-valued local contexts of each model stay exact, separately. -/
theorem full_context : sourceContext first.2.2=sourceContext state ∧ sourceContext second.2.2=sourceContext state ∧
 targetContext target1=targetContext target ∧ targetContext target2=targetContext target := by
 rw [certificate.1,certificate.2.1]
 repeat' constructor

private def short := (op 5).run initial
private def lower := (op 4).run initial
private def zero := (op 0).run initial
private def staticRun := (Source.storeVal (E:=env) (Γ:=[]) {frame with static:=true} 7 ty right (Source.Val.storRef (τ:=ty) rfl left)).run initial
/-- Partial writes on low fuel are retained; failure is NOT rollback. -/
theorem fuel_static_controls :
 (short.1,lower.1,zero.1,staticRun.1)=(.error .timeout,.error .timeout,.error .timeout,.error (.revert [])) ∧
 (sourceView short.2.2.ex,sourceView lower.2.2.ex,sourceView zero.2.2.ex,sourceView staticRun.2.2.ex,
  short.2.2.ex.journal.length,lower.2.2.ex.journal.length,zero.2.2.ex.journal.length,staticRun.2.2.ex.journal.length)=
 ([some 2,some 53,some 59,some 61,some 3,some 53,some 17,some 23,some 71,some 1,some 99,none,some 5],
  [some 2,some 53,some 59,some 61,some 3,some 7,some 17,some 23,some 71,some 1,some 99,none,some 5],
  [some 2,some 53,some 59,some 61,some 3,some 7,some 17,some 23,some 71,some 1,some 99,none,some 5],
  [some 2,some 53,some 59,some 61,some 3,some 7,some 17,some 23,some 71,some 1,some 99,none,some 5],1,0,0,0) := by
 exact ⟨rfl,rfl⟩


private def growOp : Source.EM env [] Unit := Source.storeVal frame 7 ty left (Source.Val.storRef (τ:=ty) rfl right)
private def grow1 := growOp.run initial
private def grow2 := growOp.run grow1.2
private def emptyStorage := storage.write left (.int 0 (by decide))
private def emptyState : Source.St env :=
 {state with ex:={state.ex with world:=state.ex.world.set address {(state.ex.world.accounts address) with storage:=emptyStorage}}}
private def emptyInitial : Source.Locals env.layout [] × Source.St env := (.nil,emptyState)
private def empty1 := (op 7).run emptyInitial
private def empty2 := (op 4).run empty1.2
private def growTarget := TargetArrayCopyTail.afterCopy target target.stack (.root 1) (.root 0)
private def emptyTarget : Evm.Machine := {target with store:=Evm.WordStore.write target.store (.root 0) 0}
private def emptyTarget1 := TargetArrayCopyTail.afterCopy emptyTarget emptyTarget.stack (.root 0) (.root 1)
/-- Varying actual runtime lengths: repeated growth and empty copies preserve
all OLD observations but add another complete Source journal effect. -/
theorem growth_empty :
 (grow1.1,grow2.1,empty1.1,empty2.1)=(.ok (),.ok (),.ok (),.ok ()) ∧
 Evm.run (TargetArrayRepeat.code (.root 1) (.root 0)++TargetArrayRepeat.code (.root 1) (.root 0)) target=.ok growTarget 0 ∧
 Evm.run (TargetArrayRepeat.code (.root 0) (.root 1)++TargetArrayRepeat.code (.root 0) (.root 1)) emptyTarget=.ok emptyTarget1 0 ∧
 (sourceView state.ex,sourceView grow1.2.2.ex,sourceView grow2.2.2.ex,
  sourceView emptyState.ex,sourceView empty1.2.2.ex,sourceView empty2.2.2.ex,
  targetView target,targetView growTarget,targetView emptyTarget,targetView emptyTarget1,
  grow1.2.2.ex.journal.length,grow2.2.2.ex.journal.length,empty1.2.2.ex.journal.length,empty2.2.2.ex.journal.length)=
 ([some 2,some 53,some 59,some 61,some 3,some 7,some 17,some 23,some 71,some 1,some 99,none,some 5],
  [some 3,some 7,some 17,some 23,some 3,some 7,some 17,some 23,some 71,some 1,some 99,none,some 5],
  [some 3,some 7,some 17,some 23,some 3,some 7,some 17,some 23,some 71,some 1,some 99,none,some 5],
  [some 0,some 53,some 59,some 61,some 3,some 7,some 17,some 23,some 71,some 1,some 99,none,some 5],
  [some 0,some 53,some 59,some 61,some 0,some 0,some 0,some 0,some 71,some 1,some 99,none,some 5],
  [some 0,some 53,some 59,some 61,some 0,some 0,some 0,some 0,some 71,some 1,some 99,none,some 5],
  [2,3,99,53,59,61,0,7,17,23,71],
  [3,3,99,7,17,23,0,7,17,23,71],
  [0,3,99,53,59,61,0,7,17,23,71],
  [0,0,99,53,59,61,0,0,0,0,71],4,8,4,5) := by
 exact ⟨rfl,(TargetArrayRepeat.complete target (.root 1) (.root 0) (Or.inr (by decide))).1,
  (TargetArrayRepeat.complete emptyTarget (.root 0) (.root 1) (Or.inr (by decide))).1,rfl⟩

/-- info: 'Solidity.Backend.StorageOps.SourceCopyRepeat.Controls.certificate' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in #print axioms certificate
/-- info: 'Solidity.Backend.StorageOps.SourceCopyRepeat.Controls.ordered' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in #print axioms ordered
/-- info: 'Solidity.Backend.StorageOps.SourceCopyRepeat.Controls.target_agreement' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in #print axioms target_agreement
/-- info: 'Solidity.Backend.StorageOps.SourceCopyRepeat.Controls.state_nonidentity' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in #print axioms state_nonidentity
/-- info: 'Solidity.Backend.StorageOps.SourceCopyRepeat.Controls.explicit_rollback' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in #print axioms explicit_rollback
/-- info: 'Solidity.Backend.StorageOps.SourceCopyRepeat.Controls.full_context' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in #print axioms full_context
/-- info: 'Solidity.Backend.StorageOps.SourceCopyRepeat.Controls.fuel_static_controls' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in #print axioms fuel_static_controls
/-- info: 'Solidity.Backend.StorageOps.SourceCopyRepeat.Controls.growth_empty' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in #print axioms growth_empty
end Solidity.Backend.StorageOps.SourceCopyRepeat.Controls
