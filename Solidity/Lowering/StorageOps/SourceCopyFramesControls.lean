import Solidity.Lowering.StorageOps.SourceCopyFrames
import Solidity.Source.Eval

/-! Actual complete Source-copy observer, older-shadow, alias and rollback
controls. Complete ordered outcomes retain original failure/timeout boundaries. -/
namespace Solidity.Backend.StorageOps.SourceCopyFrames.Controls
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

private def ty : Source.STy := .array .storage (.int Source.IntTy.u256) none
private def copy : Source.EM env [] Unit := Source.storeVal frame 7 ty right (Source.Val.storRef (τ:=ty) rfl left)
private def copied := copy.run initial
private def payload (j : Nat) : Source.Val env.layout (.int Source.IntTy.u256) :=
 if j=0 then .int 53 (by decide) else .int 59 (by decide)
private def after := {state with ex:=state.ex.run (copyLog frame Source.IntTy.u256 right 2 3 payload rfl)}
private def observers := [left,scratch,bad,missing]
private def readViews (input : Source.Locals env.layout [] × Source.St env) :=
 observers.map (fun query => ((Source.readLen (E:=env) (Γ:=[]) frame query).run input).1)
private def paths := [left,elem left 0,elem left 1,elem left 2,right,elem right 0,elem right 1,elem right 2,elem right 3,bad,sentinel,missing]
private def view (ex : Source.ExecState env.layout env.lay env.lay) := paths.map (wordAt frame ex) ++
 [(((ex.transient.cells frame.this).read scratch).bind Source.Val.word).map Fin.val]
private def restored := (state.ex.enter frame.this frame.sender frame.value [] frame.static).rollback copied.2.2.ex
private def arrayRef : Source.Val env.layout (.array .storage (.int Source.IntTy.u256) none) := .storRef rfl right
private def alias : Source.Loc env.layout [] (.int Source.IntTy.u256) := .stor (elem right 2)
private theorem reads : ∀ j<2,(Source.readAt (E:=env) (Γ:=[]) frame (left.go (.index j)) (.int Source.IntTy.u256)).run initial=(.ok (payload j),initial) := by
 intro j member
 have alternatives : j=0 ∨ j=1 := by omega
 rcases alternatives with rfl|rfl <;> rfl
private theorem completed : copied=(.ok (),(.nil,after)) :=
 SourceStorageCopy.complete frame rfl Source.IntTy.u256 left right (by decide) 2 3 payload rfl .nil state rfl reads rfl

theorem actual_frame (query : Source.SPath)
 (header : query≠right) (written : ∀ j<2,query≠elem right j)
 (cleared : query≠elem right 2) :
 ((Source.readAt (E:=env) (Γ:=[]) frame query (.int Source.IntTy.u256)).run copied.2).1=
 ((Source.readAt (E:=env) (Γ:=[]) frame query (.int Source.IntTy.u256)).run initial).1 ∧
 copied.2.2.ex.journal.length=4 ∧ restored=state.ex := by
 have result := actual frame rfl Source.IntTy.u256 left right query (by decide) 2 3 payload rfl .nil state (.int Source.IntTy.u256) [] rfl reads rfl header written (by
  intro j member
  simp only [List.range'_succ,List.range'_zero,List.mem_cons,List.not_mem_nil,or_false] at member
  subst j
  exact cleared)
 exact ⟨result.2.1,result.2.2.1,result.2.2.2.1⟩

theorem ordered :
 (readViews initial,readViews copied.2,view state.ex,view copied.2.2.ex,copied.2.2.ex.journal.length)=
 ([.ok 2,.ok 5,.error (.stuck "storage cell type"),.error (.stuck "storage cell without a value")],
 [.ok 2,.ok 5,.error (.stuck "storage cell type"),.error (.stuck "storage cell without a value")],
 [some 2,some 53,some 59,some 61,some 3,some 7,some 17,some 23,some 71,some 1,some 99,none,some 5],
 [some 2,some 53,some 59,some 61,some 2,some 53,some 59,some 0,some 71,some 1,some 99,none,some 5],4) := by rfl

theorem subsequent_snapshot :
 (Source.loadMem (E:=env) (Γ:=[]) frame 4 (.array .memory (.int Source.IntTy.u256) none) left).run (.nil,after)=
 (.ok (Source.Data.array (l:=.memory) (n:=none) 2 (fun _ h => nomatch h) (fun j : Fin 2 => .val (payload j.val))),(.nil,after)) := by
 apply snapshot frame Source.IntTy.u256 Source.IntTy.u256 right left 2 3 2 0 payload payload rfl .nil state
 · intro probe demanded
   have root : probe.root=left.root := by
    rcases demanded with rfl|⟨j,member,rfl⟩ <;> rfl
   have apart : probe.root≠right.root := by rw [root]; decide
   refine ⟨?_,?_,?_⟩
   · intro same; exact apart (congrArg Source.SPath.root same)
   · intro j member same
     have roots := congrArg Source.SPath.root same
     exact apart roots
   · intro j member same
     have roots := congrArg Source.SPath.root same
     exact apart roots
 · rfl
 · exact reads

/-- Same-root older shadow is framed by the actual computed touched set,
without replacing it by a stronger distinct-root condition. -/
theorem older_same_root :
 ((after.ex.world.accounts frame.this).storage.read (elem right 3)=
 (state.ex.world.accounts frame.this).storage.read (elem right 3)) ∧
 ((Source.readAt (E:=env) (Γ:=[]) frame (elem right 3) (.int Source.IntTy.u256)).run copied.2)=
 (.ok (.int 71 (by decide)),copied.2) := by
 have frames := copy_other frame Source.IntTy.u256 right (elem right 3) 2 3 payload rfl state.ex (by decide) (by
  intro j member
  have alternatives : j=0 ∨ j=1 := by omega
  rcases alternatives with rfl|rfl <;> decide) (by
  intro j member
  simp only [List.range'_succ,List.range'_zero,List.mem_cons,List.not_mem_nil,or_false] at member
  subst j; decide)
 exact ⟨frames.1,rfl⟩

/-- Explicit rollback restores the exact Source state; the completed copy itself
has different cells and a nonempty ordered journal. -/
theorem explicit_restore : (copied.2.1,{copied.2.2 with ex:=restored})=initial ∧
 view copied.2.2.ex≠view state.ex ∧ (view restored,restored.journal.length)=
 ([some 2,some 53,some 59,some 61,some 3,some 7,some 17,some 23,some 71,some 1,some 99,none,some 5],0) := by
 have restore : restored=state.ex := by
  unfold restored
  rw [completed]
  exact rollback frame Source.IntTy.u256 right 2 3 payload rfl state.ex []
 rw [restore]
 refine ⟨?_,by decide,rfl⟩
 rw [completed]
 rfl

/-- The written-cell and live-index negatives retain exact runtime behavior. -/
theorem wrong_frame_live_alias :
 wordAt frame copied.2.2.ex (elem right 0)≠wordAt frame state.ex (elem right 0) ∧
 (Source.indexLoc (E:=env) (Γ:=[]) frame arrayRef 2).run initial=(.ok alias,initial) ∧
 (Source.readLoc (E:=env) (Γ:=[]) frame alias).run copied.2=(.ok (.int 0 (by decide)),copied.2) ∧
 (Source.indexLoc (E:=env) (Γ:=[]) frame arrayRef 2).run copied.2=(.error (.revert (Source.panicData .index)),copied.2) ∧
 Source.panicData .index=([0x4e,0x48,0x7b,0x71] ++ List.replicate 31 0 ++ [0x32]) := by
 exact ⟨by decide,rfl,rfl,rfl,rfl⟩

/-- info: 'Solidity.Backend.StorageOps.SourceCopyFrames.Controls.actual_frame' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in #print axioms actual_frame
/-- info: 'Solidity.Backend.StorageOps.SourceCopyFrames.Controls.ordered' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in #print axioms ordered
/-- info: 'Solidity.Backend.StorageOps.SourceCopyFrames.Controls.subsequent_snapshot' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in #print axioms subsequent_snapshot
/-- info: 'Solidity.Backend.StorageOps.SourceCopyFrames.Controls.older_same_root' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in #print axioms older_same_root
/-- info: 'Solidity.Backend.StorageOps.SourceCopyFrames.Controls.explicit_restore' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in #print axioms explicit_restore
/-- info: 'Solidity.Backend.StorageOps.SourceCopyFrames.Controls.wrong_frame_live_alias' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in #print axioms wrong_frame_live_alias
end Solidity.Backend.StorageOps.SourceCopyFrames.Controls
