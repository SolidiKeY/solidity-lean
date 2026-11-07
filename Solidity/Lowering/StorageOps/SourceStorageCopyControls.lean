import Solidity.Lowering.StorageOps.SourceStorageCopy

/-! Complete ordered actual Source storage-to-storage copy observations.
Different roots, shrinking/growing/empty-live/short-fuel/static and captured
source controls preserve all previous fixtures; no target/world claim. -/
namespace Solidity.Backend.StorageOps.SourceStorageCopy.Controls
open SourceArrayDeleteTarget SourceScalarDeleteLog
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

private def ty : Source.STy := .array .storage (.int Source.IntTy.u256) none
private def copy (fuel : Nat) (src dst : Source.SPath) (F : Source.Fr := frame) : Source.EM env [] Unit :=
 Source.storeVal F fuel ty dst (Source.Val.storRef (τ:=ty) rfl src)
private def copied := (copy 7 left right).run initial
private def grown := (copy 7 right left).run initial
private def short := (copy 5 left right).run initial
private def tooShort := (copy 2 left right).run initial
private def payload (j : Nat) : Source.Val env.layout (.int Source.IntTy.u256) :=
 if j=0 then .int 53 (by decide) else .int 59 (by decide)
private def paths := [left,elem left 0,elem left 1,elem left 2,right,elem right 0,elem right 1,elem right 2,elem right 3,bad,sentinel,missing]
private def view (ex : Source.ExecState env.layout env.lay env.lay) := paths.map (wordAt frame ex) ++
 [(((ex.transient.cells frame.this).read scratch).bind Source.Val.word).map Fin.val]
private def readViews (input : Source.Locals env.layout [] × Source.St env) :=
 [left,right,scratch,bad,missing].map (fun query => ((Source.readLen (E:=env) (Γ:=[]) frame query).run input).1)
private def snapshot := Source.Data.array (l:=.memory) (τ:=.int Source.IntTy.u256) (n:=none) 2 (fun _ h => nomatch h)
 (fun j : Fin 2 => .val (payload j.val))
private def captured : Source.EM env [] Unit := do
 let saved ← Source.loadMem frame 4 (.array .memory (.int Source.IntTy.u256) none) left
 Source.deleteRange frame 2 (.int Source.IntTy.u256) left 0 1
 Source.storeData frame 5 ty right saved
private def wrongOrder : Source.EM env [] Unit := do
 Source.deleteRange frame 2 (.int Source.IntTy.u256) left 0 1
 copy 7 left right
private def emptyInitial : Source.Locals env.layout [] × Source.St env :=
 (.nil,{state with ex:=state.ex.apply (cellOp env frame left (some (.int 0 (by decide))))})
private def emptied := (copy 7 left right).run emptyInitial

theorem certificate : copied=
 (.ok (),(Source.Locals.nil,{state with ex:=state.ex.run (copyLog frame Source.IntTy.u256 right 2 3 payload rfl)})) := by
 apply complete frame rfl Source.IntTy.u256 left right (by decide) 2 3 payload rfl .nil state rfl
 · intro j member
   have cases : j=0 ∨ j=1 := by omega
   rcases cases with rfl|rfl <;> rfl
 · rfl

theorem ordered :
 (copied.1,grown.1,view state.ex,view copied.2.2.ex,view grown.2.2.ex,
 copied.2.2.ex.journal.length,grown.2.2.ex.journal.length)=
 (.ok (),.ok (),
 [some 2,some 53,some 59,some 61,some 3,some 7,some 17,some 23,some 71,some 1,some 99,none,some 5],
 [some 2,some 53,some 59,some 61,some 2,some 53,some 59,some 0,some 71,some 1,some 99,none,some 5],
 [some 3,some 7,some 17,some 23,some 3,some 7,some 17,some 23,some 71,some 1,some 99,none,some 5],4,4) := by rfl

theorem readbacks : (readViews initial,readViews copied.2)=
 ([.ok 2,.ok 3,.ok 5,.error (.stuck "storage cell type"),.error (.stuck "storage cell without a value")],
 [.ok 2,.ok 2,.ok 5,.error (.stuck "storage cell type"),.error (.stuck "storage cell without a value")]) := by rfl

theorem exact_context : copied.2.1=initial.1 ∧ copied.2.2.heap=state.heap ∧ copied.2.2.events=state.events ∧
 copied.2.2.logs=state.logs ∧ copied.2.2.fnLocals=state.fnLocals ∧
 (copied.2.2.ex.world.accounts address).balance=19 ∧
 (copied.2.2.ex.world.accounts address).nonce=3 ∧ (copied.2.2.ex.world.accounts address).code=some 0 := by
 exact ⟨rfl,rfl,rfl,rfl,rfl,rfl,rfl,rfl⟩

/-- Timeout after the first actual destination write RETAINS that prefix;
shorter timeout before the snapshot performs no write. Neither rolls back. -/
theorem fuel_failures :
 (short.1,view short.2.2.ex,short.2.2.ex.journal.length)=
 (.error .timeout,[some 2,some 53,some 59,some 61,some 3,some 53,some 17,some 23,some 71,some 1,some 99,none,some 5],1) ∧
 tooShort=(.error .timeout,initial) ∧
 (copy 7 left right {frame with static:=true}).run initial=(.error (.revert []),initial) := by
 exact ⟨rfl,rfl,rfl⟩

theorem empty_retained :
 (emptied.1,view emptyInitial.2.ex,view emptied.2.2.ex,emptied.2.2.ex.journal.length)=
 (.ok (),
 [some 0,some 53,some 59,some 61,some 3,some 7,some 17,some 23,some 71,some 1,some 99,none,some 5],
 [some 0,some 53,some 59,some 61,some 0,some 0,some 0,some 0,some 71,some 1,some 99,none,some 5],5) := by rfl

/-- Mutating the source AFTER capture keeps53; mutating it BEFORE actual
copy captures0. Actual operations discriminate snapshot and wrong order. -/
theorem snapshot_order :
 ((captured.run initial).1,(wrongOrder.run initial).1,view (captured.run initial).2.2.ex,
 view (wrongOrder.run initial).2.2.ex,(captured.run initial).2.2.ex.journal.length,
 (wrongOrder.run initial).2.2.ex.journal.length)=
 (.ok (),.ok (),
 [some 2,some 0,some 59,some 61,some 2,some 53,some 59,some 0,some 71,some 1,some 99,none,some 5],
 [some 2,some 0,some 59,some 61,some 2,some 0,some 59,some 0,some 71,some 1,some 99,none,some 5],5,5) := by rfl

private def headerFirst : Source.EM env [] Unit := do
 Source.writeLen frame right 2
 copy 5 left right
private def clearOlder : Source.EM env [] Unit := do
 copy 7 left right
 Source.deleteRange frame 3 (.int Source.IntTy.u256) right 2 2

/-- Wrong header-first and over-clearing programs execute, changing exactly
observable original-fuel prefixes and the older shadow which must survive. -/
theorem wrong_tail_header :
 ((headerFirst.run initial).1,view (headerFirst.run initial).2.2.ex,(headerFirst.run initial).2.2.ex.journal.length,
 (clearOlder.run initial).1,view (clearOlder.run initial).2.2.ex,(clearOlder.run initial).2.2.ex.journal.length)=
 (.error .timeout,
 [some 2,some 53,some 59,some 61,some 2,some 53,some 17,some 23,some 71,some 1,some 99,none,some 5],2,
 .ok (),[some 2,some 53,some 59,some 61,some 2,some 53,some 59,some 0,some 0,some 1,some 99,none,some 5],6) := by rfl

/-- info: 'Solidity.Backend.StorageOps.SourceStorageCopy.Controls.wrong_tail_header' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in #print axioms wrong_tail_header

/-- info: 'Solidity.Backend.StorageOps.SourceStorageCopy.Controls.certificate' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in #print axioms certificate
/-- info: 'Solidity.Backend.StorageOps.SourceStorageCopy.Controls.ordered' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in #print axioms ordered
/-- info: 'Solidity.Backend.StorageOps.SourceStorageCopy.Controls.readbacks' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in #print axioms readbacks
/-- info: 'Solidity.Backend.StorageOps.SourceStorageCopy.Controls.exact_context' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in #print axioms exact_context
/-- info: 'Solidity.Backend.StorageOps.SourceStorageCopy.Controls.fuel_failures' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in #print axioms fuel_failures
/-- info: 'Solidity.Backend.StorageOps.SourceStorageCopy.Controls.empty_retained' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in #print axioms empty_retained
/-- info: 'Solidity.Backend.StorageOps.SourceStorageCopy.Controls.snapshot_order' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in #print axioms snapshot_order
end Solidity.Backend.StorageOps.SourceStorageCopy.Controls
