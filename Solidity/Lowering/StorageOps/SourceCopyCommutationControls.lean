import Solidity.Lowering.StorageOps.SourceCopyCommutation

/-! Independent actual Source operations and exact ordered operation logs.
All Source journals/partial effects/refusals and whole context are retained.
The entered-frame rollback below is explicit, never inferred from failure. -/
namespace Solidity.Backend.StorageOps.SourceCopyCommutation.Controls
open SourceStorageCopy SourceArrayDeleteTarget
private def uintSyntax : Source.Syn .typeName := .elem (.int false 256 (by decide))
private def unit : Source.Syn .unit := .unit (.cons (.contract false "C" .none .nil
  (.cons (.stateVar (.array uintSyntax .none) none none none false "left" .none)
    (.cons (.stateVar (.array uintSyntax .none) none none none false "right" .none)
      (.cons (.stateVar (.array uintSyntax .none) none none none false "other" .none)
      (.cons (.stateVar (.elem .bool) none none none false "bad" .none)
        (.cons (.stateVar uintSyntax none none none true "scratch" .none)
          (.cons (.stateVar uintSyntax none none none false "sentinel" .none) .nil))))))) .nil)
private def env : Source.Env := unit.env
private def left : Source.SPath := ⟨⟨some "C","left"⟩,[]⟩
private def right : Source.SPath := ⟨⟨some "C","right"⟩,[]⟩
private def other : Source.SPath := ⟨⟨some "C","other"⟩,[]⟩
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
  let s := s.write other (.int 1 (by decide))
  let s := s.write (elem other 0) (.int 29 (by decide))
  let s := s.write (elem other 1) (.int 31 (by decide))
  let s := s.write (elem other 2) (.int 37 (by decide))
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

private def ty : Source.STy := .array .storage (.int Source.IntTy.u256) none
private def payload (j : Nat) : Source.Val env.layout (.int Source.IntTy.u256) := if j=0 then .int 53 (by decide) else .int 59 (by decide)
private def op (src dst : Source.SPath) (budget : Nat) : Source.EM env [] Unit :=
 Source.storeVal frame budget ty dst (Source.Val.storRef (τ:=ty) rfl src)
private def l1 := copyLog (E:=env) frame Source.IntTy.u256 right 2 3 payload rfl
private def l2 := copyLog (E:=env) frame Source.IntTy.u256 other 2 1 payload rfl
private def expectedForward : Source.St env := {state with ex:=(state.ex.run l1).run l2}
private def expectedReverse : Source.St env := {state with ex:=(state.ex.run l2).run l1}
private def forward := (op left right 7 >>= fun _ => op left other 6).run initial
private def reverse := (op left other 6 >>= fun _ => op left right 7).run initial
private def paths := [left,elem left 0,elem left 1,elem left 2,right,elem right 0,elem right 1,elem right 2,elem right 3,
 other,elem other 0,elem other 1,elem other 2,bad,sentinel,missing]
private def view (ex : Source.ExecState env.layout env.lay env.lay) := paths.map (wordAt (E:=env) frame ex) ++
 [(((ex.transient.cells frame.this).read scratch).bind Source.Val.word).map Fin.val]

/-- BOTH real Source operation orders generate their exact ordered Op logs. -/
theorem runs : forward=(.ok (),(Source.Locals.nil,expectedForward)) ∧
 reverse=(.ok (),(Source.Locals.nil,expectedReverse))  := by
 have one := SourceStorageCopy.complete (E:=env) (Γ:=[]) frame rfl Source.IntTy.u256 left right (by decide) 2 3 payload rfl .nil state rfl
  (by
   intro j inside
   have cases : j=0 ∨ j=1 := by omega
   rcases cases with rfl|rfl <;> rfl) rfl
 have two := SourceStorageCopy.complete (E:=env) (Γ:=[]) frame rfl Source.IntTy.u256 left other (by decide) 2 1 payload rfl .nil
  {state with ex:=state.ex.run l1} rfl
  (by
   intro j inside
   have cases : j=0 ∨ j=1 := by omega
   rcases cases with rfl|rfl <;> rfl) rfl
 have oneR := SourceStorageCopy.complete (E:=env) (Γ:=[]) frame rfl Source.IntTy.u256 left other (by decide) 2 1 payload rfl .nil state rfl
  (by
   intro j inside
   have cases : j=0 ∨ j=1 := by omega
   rcases cases with rfl|rfl <;> rfl) rfl
 have twoR := SourceStorageCopy.complete (E:=env) (Γ:=[]) frame rfl Source.IntTy.u256 left right (by decide) 2 3 payload rfl .nil
  {state with ex:=state.ex.run l2} rfl
  (by
   intro j inside
   have cases : j=0 ∨ j=1 := by omega
   rcases cases with rfl|rfl <;> rfl) rfl
 constructor
 · change ((op left right 7) >>= fun _ => op left other 6).run initial=_
   have first : (op left right 7).run initial=(.ok (),(.nil,{state with ex:=state.ex.run l1})) := one
   rw [Source.Hoare.run_bind,first]
   exact two
 · change ((op left other 6) >>= fun _ => op left right 7).run initial=_
   have first : (op left other 6).run initial=(.ok (),(.nil,{state with ex:=state.ex.run l2})) := oneR
   rw [Source.Hoare.run_bind,first]
   exact twoR

/-- Complete OLD/forward/reverse observations retain copied, cleared, older,
Bool, missing and transient cells. Both destinations actually change. -/
theorem ordered :
 view state.ex=[some 2,some 53,some 59,some 61,some 3,some 7,some 17,some 23,some 71,some 1,some 29,some 31,some 37,some 1,some 99,none,some 5] ∧
 view forward.2.2.ex=[some 2,some 53,some 59,some 61,some 2,some 53,some 59,some 0,some 71,some 2,some 53,some 59,some 37,some 1,some 99,none,some 5] ∧
 view reverse.2.2.ex=[some 2,some 53,some 59,some 61,some 2,some 53,some 59,some 0,some 71,some 2,some 53,some 59,some 37,some 1,some 99,none,some 5] ∧
 forward.2.2.ex.journal.length=7 ∧ reverse.2.2.ex.journal.length=7 := by
 rw [runs.1,runs.2]
 decide

private theorem rightType : env.pathTy right=some ty := rfl
private theorem otherType : env.pathTy other=some ty := rfl
private theorem apart : ∀ query,Touched right 2 3 query → ¬Touched other 2 1 query := by
 intro query inside1 inside2
 have root1 : query.root=right.root := by
  rcases inside1 with h|⟨j,_,h⟩ <;> simpa only [Source.SPath.go] using congrArg Source.SPath.root h
 have root2 : query.root=other.root := by
  rcases inside2 with h|⟨j,_,h⟩ <;> simpa only [Source.SPath.go] using congrArg Source.SPath.root h
 exact (by decide : right.root≠other.root) (root1.symm.trans root2)
private theorem ordinaryRight : env.transientRoot right=false := rfl
private theorem ordinaryOther : env.transientRoot other=false := rfl
private theorem log_words : ∀ query,wordAt (E:=env) frame expectedForward.ex query=wordAt (E:=env) frame expectedReverse.ex query := by
 dsimp only [expectedForward,expectedReverse,l1,l2]
 exact SourceCopyCommutation.commute (E:=env) frame right other 2 3 2 1 payload payload rightType otherType ordinaryRight ordinaryOther state.ex apart

/-- The derived theorem compares ALL path word observations, not a finite
sample and not the two journal-bearing Source states. -/
theorem all_words : ∀ query,wordAt (E:=env) frame forward.2.2.ex query=wordAt (E:=env) frame reverse.2.2.ex query := by
 rw [runs.1,runs.2]
 exact log_words

private def headRight (ex : Source.ExecState env.layout env.lay env.lay) : Option Nat :=
 ex.journal.head?.bind (fun entry => match entry with
 | .account _ old => ((old.storage.read right).bind Source.Val.word).map Fin.val
 | .transient _ _ => none)

/-- Ordered journal snapshots distinguish actual Source states. -/
theorem journal_order : headRight forward.2.2.ex=some 2 ∧ headRight reverse.2.2.ex=some 3 := by
 rw [runs.1,runs.2]
 exact ⟨rfl,rfl⟩

/-- Equal final word functions do not identify journal-bearing Source states. -/
theorem state_nonidentity : forward.2.2≠reverse.2.2 := by
 intro same
 have seen := congrArg (fun s : Source.St env => headRight s.ex) same
 dsimp only at seen
 rw [journal_order.1,journal_order.2] at seen
 exact (by decide : (some 2 : Option Nat)≠some 3) seen

/-- Same destination violates disjointness: BOTH actual operations succeed
but copied payloads, headers and stale tails depend on order. -/
theorem same_target :
 let a := (op left right 7 >>= fun _ => op other right 6).run initial
 let b := (op other right 7 >>= fun _ => op left right 6).run initial
 (a.1,b.1,view a.2.2.ex,view b.2.2.ex)=
 (.ok (),.ok (),
 [some 2,some 53,some 59,some 61,some 1,some 29,some 0,some 0,some 71,some 1,some 29,some 31,some 37,some 1,some 99,none,some 5],
 [some 2,some 53,some 59,some 61,some 2,some 53,some 59,some 0,some 71,some 1,some 29,some 31,some 37,some 1,some 99,none,some 5]) := by rfl

/-- Incremental source capture violates the fixed-capture premise. -/
theorem wrong_order :
 let a := (op left right 7 >>= fun _ => op right other 6).run initial
 let b := (op right other 7 >>= fun _ => op left right 7).run initial
 a.1=.ok () ∧ b.1=.ok () ∧
 view a.2.2.ex=[some 2,some 53,some 59,some 61,some 2,some 53,some 59,some 0,some 71,some 2,some 53,some 59,some 37,some 1,some 99,none,some 5] ∧
 view b.2.2.ex=[some 2,some 53,some 59,some 61,some 2,some 53,some 59,some 0,some 71,some 3,some 7,some 17,some 23,some 1,some 99,none,some 5] := by
 refine ⟨rfl,rfl,?_,?_⟩ <;> rfl

/-- Rollback is explicit; success and observational commutation do not erase
journals. The existing entered-frame operation restores BOTH ordered logs. -/
theorem explicit_rollback :
 (state.ex.enter frame.this frame.sender frame.value [] frame.static).rollback expectedForward.ex=state.ex ∧
 (state.ex.enter frame.this frame.sender frame.value [] frame.static).rollback expectedReverse.ex=state.ex := by
 exact ⟨Source.rollback_run state.ex (l1++l2) frame.this frame.sender frame.value [] frame.static,
  Source.rollback_run state.ex (l2++l1) frame.this frame.sender frame.value [] frame.static⟩

/-- info: 'Solidity.Backend.StorageOps.SourceCopyCommutation.Controls.runs' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in #print axioms runs

/-- info: 'Solidity.Backend.StorageOps.SourceCopyCommutation.Controls.ordered' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in #print axioms ordered

/-- info: 'Solidity.Backend.StorageOps.SourceCopyCommutation.Controls.all_words' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in #print axioms all_words

/-- info: 'Solidity.Backend.StorageOps.SourceCopyCommutation.Controls.journal_order' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in #print axioms journal_order

/-- info: 'Solidity.Backend.StorageOps.SourceCopyCommutation.Controls.state_nonidentity' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in #print axioms state_nonidentity

/-- info: 'Solidity.Backend.StorageOps.SourceCopyCommutation.Controls.same_target' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in #print axioms same_target

/-- info: 'Solidity.Backend.StorageOps.SourceCopyCommutation.Controls.wrong_order' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in #print axioms wrong_order

/-- info: 'Solidity.Backend.StorageOps.SourceCopyCommutation.Controls.explicit_rollback' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in #print axioms explicit_rollback

end Solidity.Backend.StorageOps.SourceCopyCommutation.Controls
