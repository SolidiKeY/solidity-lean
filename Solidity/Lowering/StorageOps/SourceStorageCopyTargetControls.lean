import Solidity.Lowering.StorageOps.SourceStorageCopyTarget

/-! Inhabited actual independent Source/numeric/target runtime storage-copy
certificate with complete ordered old/result observations and a bad OLD shadow
agreement control. No general Source compiler/address/world claim. -/
namespace Solidity.Backend.StorageOps.SourceStorageCopyTarget.Controls
open TypeGraph Solidity.Storage Solidity.Storage.Representation Solidity.Storage.Representation.Graph
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

private def graph : Schema 0 where
 origin := "v10-source-copy-target"
 declId := fun i => nomatch i
 declId_injective := by intro i; exact Fin.elim0 i
 name := fun i => nomatch i
 fields := fun i => nomatch i
 rank := fun i => nomatch i
 nonempty := by intro i; exact Fin.elim0 i
 distinct := by intro i; exact Fin.elim0 i
 guarded := by intro i; exact Fin.elim0 i
private def ix (i : Fin 4) : Index := ⟨i.val,by have bound:=i.isLt; omega⟩
private def indices : List Index := [ix 0,ix 1,ix 2,ix 3]
private def w (x : Fin 100) : Semantics.Word := lengthWord x.val (by have bound:=x.isLt; omega)
private def source : Value graph (.array (.prim .uint)) := .array ⟨3,by decide⟩ ⟨2,by decide⟩ (by decide)
 (fun i => .present (.prim (if i.val=0 then w 53 else if i.val=1 then w 59 else w 61)))
private def old : Value graph (.array (.prim .uint)) := .array ⟨4,by decide⟩ ⟨3,by decide⟩ (by decide)
 (fun i => .present (.prim (if i.val=0 then w 7 else if i.val=1 then w 17 else if i.val=2 then w 23 else w 71)))
private def src : Solidity.Storage.Loc := .root 0
private def dst : Solidity.Storage.Loc := .root 1
private def hash (p : Solidity.Storage.Pre) : Nat := if p=.data 0 then 4 else if p=.data 1 then 8 else 0
private def preimages : List Solidity.Storage.Pre := [.data 0,.data 1]
private def locations : List Solidity.Storage.Loc := [.root 0,.root 1,.root 2,
 .data src 0,.data src 1,.data src 2,.data src 3,.data dst 0,.data dst 1,.data dst 2,.data dst 3]
private def store : Store := fun l =>
 if l=.root 0 then w 2 else if l=.root 1 then w 3 else if l=.root 2 then w 99 else
 if l=.data src 0 then w 53 else if l=.data src 1 then w 59 else if l=.data src 2 then w 61 else
 if l=.data dst 0 then w 7 else if l=.data dst 1 then w 17 else if l=.data dst 2 then w 23 else if l=.data dst 3 then w 71 else w 0
private def numeric : WordStore := fun a =>
 if a=0 then w 2 else if a=1 then w 3 else if a=2 then w 99 else
 if a=4 then w 53 else if a=5 then w 59 else if a=6 then w 61 else
 if a=8 then w 7 else if a=9 then w 17 else if a=10 then w 23 else if a=11 then w 71 else w 0
private def target : Evm.Machine :=
 {stack := [.val ⟨17,by decide⟩,.slot (.root 9)],
  store := .ofFn (fun l => if l=.root 0 then 2 else if l=.root 1 then 3 else if l=.root 2 then 99 else
   if l=.data (.root 0) 0 then 53 else if l=.data (.root 0) 1 then 59 else if l=.data (.root 0) 2 then 61 else
   if l=.data (.root 1) 0 then 7 else if l=.data (.root 1) 1 then 17 else if l=.data (.root 1) 2 then 23 else if l=.data (.root 1) 3 then 71 else 0),
  mem := fun _ => .val ⟨31,by decide⟩,bal:=fun _ => 41,bal₀:=fun _ => 43,
  self:=⟨47,by decide⟩,caller:=⟨53,by decide⟩,callvalue:=⟨59,by decide⟩,timestamp:=⟨61,by decide⟩,accepts:=fun _ _ => false}
private def payload (j : Nat) : Source.Val env.layout (.int Source.IntTy.u256) := if j=0 then .int 53 (by decide) else .int 59 (by decide)
private def grownPayload (j : Nat) : Source.Val env.layout (.int Source.IntTy.u256) := if j=0 then .int 7 (by decide) else if j=1 then .int 17 (by decide) else .int 23 (by decide)
private def ty : Source.STy := .array .storage (.int Source.IntTy.u256) none
private def sourceOp (sourcePath dstPath : Source.SPath) : Source.EM env [] Unit := Source.storeVal frame 7 ty dstPath (Source.Val.storRef (τ:=ty) rfl sourcePath)
private def copied := (sourceOp left right).run initial
private def grown := (sourceOp right left).run initial
private def targetResult := TargetArrayCopyTail.afterCopy target target.stack (.root 0) (.root 1)
private def grownTarget := TargetArrayCopyTail.afterCopy target target.stack (.root 1) (.root 0)
private def numericResult := NumericTraversal.copy 32 hash dst src numeric
private def afterStore := CopyTransport.symbolicCopy dst src store
private def sourcePaths := [left,elem left 0,elem left 1,elem left 2,right,elem right 0,elem right 1,elem right 2,elem right 3,bad,sentinel,missing]
private def sourceView (ex : Source.ExecState env.layout env.lay env.lay) := sourcePaths.map (wordAt frame ex) ++
 [(((ex.transient.cells frame.this).read scratch).bind Source.Val.word).map Fin.val]
private def numericView (s : WordStore) := [s 0,s 1,s 2,s 4,s 5,s 6,s 7,s 8,s 9,s 10,s 11] |>.map (fun w => w.val)
private def targetSlots : List Evm.Slot := [.root 0,.root 1,.root 2,.data (.root 0) 0,.data (.root 0) 1,.data (.root 0) 2,.data (.root 0) 3,
 .data (.root 1) 0,.data (.root 1) 1,.data (.root 1) 2,.data (.root 1) 3]
private def targetView (s : Evm.Machine) := targetSlots.map (fun slot => s.store slot)
private def graphView (v : Value graph (.array (.prim .uint))) := (PrimitivePop.queries indices).map (fun q => (q.read v).map (fun w => w.val))
private def targetContext (m : Evm.Machine) := (m.stack,m.mem,m.bal,m.bal₀,m.self,m.accepts,m.caller,m.callvalue,m.timestamp)
private theorem finite : FiniteRun 32 4 3 hash preimages locations := by
 constructor
 · intro p; simp only [hash]; split <;> first | decide | (split <;> decide)
 · decide
 · decide
 · decide
 · intro l member
   simp only [locations,List.mem_cons,List.not_mem_nil,or_false] at member
   rcases member with rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl <;> simp only [Solidity.Storage.Loc.Bounded,src,dst] <;> decide
 · intro l member
   simp only [locations,List.mem_cons,List.not_mem_nil,or_false] at member
   rcases member with rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl <;> decide
private theorem transported : Transport 32 hash locations store numeric := by
 intro l member
 simp only [locations,List.mem_cons,List.not_mem_nil,or_false] at member
 rcases member with rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl <;> rfl
private theorem fitting : ∀ l ∈ locations,TargetOperations.KeysFit l := by
 intro l member
 simp only [locations,List.mem_cons,List.not_mem_nil,or_false] at member
 rcases member with rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl <;> exact True.intro
private theorem agreement : ∀ l (member : l ∈ locations),target.store.cells (TargetOperations.toSlot l (fitting l member))=TargetOperations.encodeWord (store l) := by
 intro l member
 simp only [locations,List.mem_cons,List.not_mem_nil,or_false] at member
 rcases member with rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl <;> rfl
private theorem beforeSource : Represented source (PrimitivePop.queries indices) src store := by
 intro q member
 simp only [PrimitivePop.queries,indices,List.map_cons,List.map_nil,List.mem_cons,List.not_mem_nil,or_false] at member
 rcases member with rfl|rfl|rfl|rfl|rfl
 · refine ⟨True.intro,⟨by decide,by decide⟩,?_⟩
   intro word observed; change some (w 2)=some word at observed; cases observed; rfl
 · refine ⟨⟨by change 0<lmax; decide,True.intro⟩,True.intro,?_⟩
   intro word observed; change some (w 53)=some word at observed; cases observed; rfl
 · refine ⟨⟨by change 1<lmax; decide,True.intro⟩,True.intro,?_⟩
   intro word observed; change some (w 59)=some word at observed; cases observed; rfl
 · refine ⟨⟨by change 2<lmax; decide,True.intro⟩,True.intro,?_⟩
   intro word observed; change some (w 61)=some word at observed; cases observed; rfl
 · refine ⟨⟨by change 3<lmax; decide,True.intro⟩,True.intro,?_⟩
   intro word observed; change (none : Option Semantics.Word)=some word at observed; cases observed
private theorem beforeOld : Represented old (PrimitivePop.queries indices) dst store := by
 intro q member
 simp only [PrimitivePop.queries,indices,List.map_cons,List.map_nil,List.mem_cons,List.not_mem_nil,or_false] at member
 rcases member with rfl|rfl|rfl|rfl|rfl
 · refine ⟨True.intro,⟨by decide,by decide⟩,?_⟩
   intro word observed; change some (w 3)=some word at observed; cases observed; rfl
 · refine ⟨⟨by change 0<lmax; decide,True.intro⟩,True.intro,?_⟩
   intro word observed; change some (w 7)=some word at observed; cases observed; rfl
 · refine ⟨⟨by change 1<lmax; decide,True.intro⟩,True.intro,?_⟩
   intro word observed; change some (w 17)=some word at observed; cases observed; rfl
 · refine ⟨⟨by change 2<lmax; decide,True.intro⟩,True.intro,?_⟩
   intro word observed; change some (w 23)=some word at observed; cases observed; rfl
 · refine ⟨⟨by change 3<lmax; decide,True.intro⟩,True.intro,?_⟩
   intro word observed; change some (w 71)=some word at observed; cases observed; rfl
private theorem sourceReads : ∀ j<2,(Source.readAt (E:=env) (Γ:=[]) frame (left.go (.index j)) (.int Source.IntTy.u256)).run initial=(.ok (payload j),initial) := by
 intro j member
 have alternatives : j=0 ∨ j=1 := by omega
 rcases alternatives with rfl|rfl <;> rfl
private theorem dstCoverage : ∀ i ∈ indices,Solidity.Storage.Loc.data dst i.val ∈ locations := by
 intro i member
 simp only [indices,List.mem_cons,List.not_mem_nil,or_false] at member
 rcases member with rfl|rfl|rfl|rfl <;> decide
private theorem srcCoverage : ∀ i ∈ indices,Solidity.Storage.Loc.data src i.val ∈ locations := by
 intro i member
 simp only [indices,List.mem_cons,List.not_mem_nil,or_false] at member
 rcases member with rfl|rfl|rfl|rfl <;> decide
private theorem readCoverage : ∀ j<source.length.val,Solidity.Storage.Loc.data src j ∈ locations := by
 intro j member
 change j<2 at member
 have alternatives : j=0 ∨ j=1 := by omega
 rcases alternatives with rfl|rfl <;> decide
private theorem writeCoverage : ∀ j<max old.length.val source.length.val,Solidity.Storage.Loc.data dst j ∈ locations := by
 intro j member
 change j<max 3 2 at member
 have alternatives : j=0 ∨ j=1 ∨ j=2 := by omega
 rcases alternatives with rfl|rfl|rfl <;> decide

theorem certificate : copied=(.ok (),(Source.Locals.nil,{state with ex:=state.ex.run (copyLog frame Source.IntTy.u256 right 2 3 payload rfl)})) ∧
 Evm.run TargetArrayCopy.code {target with stack:=.slot (.root 0) :: .slot (.root 1) :: target.stack}=.ok targetResult 0 ∧
 Represented (old.overlay source) (PrimitivePop.queries indices) dst afterStore ∧ Transport 32 hash locations afterStore numericResult ∧
 (∀ l (member : l ∈ locations),targetResult.store.cells (TargetOperations.toSlot l (fitting l member))=TargetOperations.encodeWord (numericResult (l.word 32 hash))) ∧
 wordAt frame copied.2.2.ex right=some (TargetOperations.encodeWord (numericResult 1)).val ∧
 (∀ i ∈ indices,wordAt frame copied.2.2.ex (right.go (.index i.val))=some (TargetOperations.encodeWord (numericResult ((Solidity.Storage.Loc.data dst i.val).word 32 hash))).val) ∧
 (∀ q ∈ PrimitivePop.queries (G:=graph) (p:=.uint) indices,∀ word,q.read (old.overlay source)=some word → numericResult ((q.location dst).word 32 hash)=word) := by
 apply complete_numeric (E:=env) (Γ:=[]) finite frame rfl left right (by decide) .nil state rfl rfl old source indices dst src True.intro True.intro store numeric target target.stack payload rfl sourceReads rfl beforeOld beforeSource transported
   (by decide) (by decide) dstCoverage srcCoverage readCoverage writeCoverage fitting agreement
 · intro j live
   change j<2 at live
   have alternatives : j=0 ∨ j=1 := by omega
   rcases alternatives with rfl|rfl <;> rfl
 · intro i member unvisited
   simp only [indices,List.mem_cons,List.not_mem_nil,or_false] at member
   rcases member with rfl|rfl|rfl|rfl
   · change max 2 3≤0 at unvisited; omega
   · change max 2 3≤1 at unvisited; omega
   · change max 2 3≤2 at unvisited; omega
   · rfl

theorem ordered :
 (sourceView state.ex,sourceView copied.2.2.ex,graphView old,graphView (old.overlay source),numericView numeric,numericView numericResult,targetView target,targetView targetResult,copied.2.2.ex.journal.length)=
 ([some 2,some 53,some 59,some 61,some 3,some 7,some 17,some 23,some 71,some 1,some 99,none,some 5],
 [some 2,some 53,some 59,some 61,some 2,some 53,some 59,some 0,some 71,some 1,some 99,none,some 5],
 [some 3,some 7,some 17,some 23,some 71],[some 2,some 53,some 59,some 0,some 71],
 [2,3,99,53,59,61,0,7,17,23,71],[2,2,99,53,59,61,0,53,59,0,71],
 [2,3,99,53,59,61,0,7,17,23,71],[2,2,99,53,59,61,0,53,59,0,71],4) := by rfl

theorem full_target_context : targetContext targetResult=targetContext target := by rfl

private def emptyInitial : Source.Locals env.layout [] × Source.St env :=
 (.nil,{state with ex:=state.ex.apply (cellOp env frame left (some (.int 0 (by decide))))})
private def emptyTarget := {target with store:=Evm.WordStore.write target.store (.root 0) 0}
private def emptied := (sourceOp left right).run emptyInitial
private def emptyTargetResult := TargetArrayCopyTail.afterCopy emptyTarget emptyTarget.stack (.root 0) (.root 1)
private def badOlderTarget := {target with store:=Evm.WordStore.write target.store (.data (.root 1) 3) 87}
private def badOlderResult := TargetArrayCopyTail.afterCopy badOlderTarget badOlderTarget.stack (.root 0) (.root 1)
private def badPayloadTarget := {target with store:=Evm.WordStore.write target.store (.data (.root 0) 0) 55}
private def badPayloadResult := TargetArrayCopyTail.afterCopy badPayloadTarget badPayloadTarget.stack (.root 0) (.root 1)

private theorem grownReads : ∀ j<3,(Source.readAt (E:=env) (Γ:=[]) frame (right.go (.index j)) (.int Source.IntTy.u256)).run initial=(.ok (grownPayload j),initial) := by
 intro j member
 have alternatives : j=0 ∨ j=1 ∨ j=2 := by omega
 rcases alternatives with rfl|rfl|rfl <;> rfl

theorem grow_certificate : grown=(.ok (),(Source.Locals.nil,{state with ex:=state.ex.run (copyLog frame Source.IntTy.u256 left 3 2 grownPayload rfl)})) ∧
 Evm.run TargetArrayCopy.code {target with stack:=.slot (.root 1) :: .slot (.root 0) :: target.stack}=.ok grownTarget 0 ∧
 wordAt frame grown.2.2.ex left=some (grownTarget.store (.root 0)) ∧
 (∀ j ∈ [0,1,2,3],wordAt frame grown.2.2.ex (left.go (.index j))=some (grownTarget.store (.data (.root 0) j))) := by
 apply complete (E:=env) (Γ:=[]) frame rfl right left (by decide) 3 2 (by decide) [0,1,2,3] grownPayload rfl rfl .nil state rfl grownReads rfl target target.stack (.root 1) (.root 0) rfl rfl
 · intro j member
   have alternatives : j=0 ∨ j=1 ∨ j=2 := by omega
   rcases alternatives with rfl|rfl|rfl <;> rfl
 · intro j member unvisited
   simp only [List.mem_cons,List.not_mem_nil,or_false] at member
   rcases member with rfl|rfl|rfl|rfl
   · omega
   · omega
   · omega
   · rfl

theorem empty_certificate : emptied=(.ok (),(Source.Locals.nil,{emptyInitial.2 with ex:=emptyInitial.2.ex.run (copyLog frame Source.IntTy.u256 right 0 3 payload rfl)})) ∧
 Evm.run TargetArrayCopy.code {emptyTarget with stack:=.slot (.root 0) :: .slot (.root 1) :: emptyTarget.stack}=.ok emptyTargetResult 0 ∧
 wordAt frame emptied.2.2.ex right=some (emptyTargetResult.store (.root 1)) ∧
 (∀ j ∈ [0,1,2,3],wordAt frame emptied.2.2.ex (right.go (.index j))=some (emptyTargetResult.store (.data (.root 1) j))) := by
 apply complete (E:=env) (Γ:=[]) frame rfl left right (by decide) 0 3 (by decide) [0,1,2,3] payload rfl rfl .nil emptyInitial.2 rfl (by intro j impossible; omega) rfl emptyTarget emptyTarget.stack (.root 0) (.root 1) rfl rfl
 · intro j impossible; omega
 · intro j member unvisited
   simp only [List.mem_cons,List.not_mem_nil,or_false] at member
   rcases member with rfl|rfl|rfl|rfl
   · omega
   · omega
   · omega
   · rfl

theorem varied_ordered :
 (sourceView grown.2.2.ex,targetView grownTarget,sourceView emptyInitial.2.ex,sourceView emptied.2.2.ex,targetView emptyTargetResult,
 grown.2.2.ex.journal.length,emptied.2.2.ex.journal.length)=
 ([some 3,some 7,some 17,some 23,some 3,some 7,some 17,some 23,some 71,some 1,some 99,none,some 5],
 [3,3,99,7,17,23,0,7,17,23,71],
 [some 0,some 53,some 59,some 61,some 3,some 7,some 17,some 23,some 71,some 1,some 99,none,some 5],
 [some 0,some 53,some 59,some 61,some 0,some 0,some 0,some 0,some 71,some 1,some 99,none,some 5],
 [0,0,99,53,59,61,0,0,0,0,71],4,5) := by rfl

/-- Correct target code cannot preserve an initially FALSE Source/target
relation. Both missing OLD agreements are independently discriminated. -/
theorem bad_old_agreements :
 Evm.run TargetArrayCopy.code {badOlderTarget with stack:=.slot (.root 0) :: .slot (.root 1) :: badOlderTarget.stack}=.ok badOlderResult 0 ∧
 Evm.run TargetArrayCopy.code {badPayloadTarget with stack:=.slot (.root 0) :: .slot (.root 1) :: badPayloadTarget.stack}=.ok badPayloadResult 0 ∧
 (sourceView copied.2.2.ex,targetView badOlderResult,targetView badPayloadResult)=
 ([some 2,some 53,some 59,some 61,some 2,some 53,some 59,some 0,some 71,some 1,some 99,none,some 5],
 [2,2,99,53,59,61,0,53,59,0,87],[2,2,99,55,59,61,0,55,59,0,71]) ∧
 wordAt frame state.ex (elem right 3)≠some (badOlderTarget.store (.data (.root 1) 3)) ∧
 (payload 0).word.map Fin.val≠some (badPayloadTarget.store (.data (.root 0) 0)) ∧
 wordAt frame copied.2.2.ex (elem right 3)≠some (badOlderResult.store (.data (.root 1) 3)) ∧
 wordAt frame copied.2.2.ex (elem right 0)≠some (badPayloadResult.store (.data (.root 1) 0)) := by
 exact ⟨TargetArrayCopyTail.run_current _ _ _ _,TargetArrayCopyTail.run_current _ _ _ _,rfl,by decide,by decide,by decide,by decide⟩

theorem readbacks :
 (Source.readAt (E:=env) (Γ:=[]) frame right (.int Source.IntTy.u256)).run copied.2=(.ok (.int 2 (by decide)),copied.2) ∧
 (Source.readAt (E:=env) (Γ:=[]) frame (elem right 0) (.int Source.IntTy.u256)).run copied.2=(.ok (.int 53 (by decide)),copied.2) ∧
 (Source.readAt (E:=env) (Γ:=[]) frame (elem right 2) (.int Source.IntTy.u256)).run copied.2=(.ok (.int 0 (by decide)),copied.2) ∧
 Evm.run (TargetOperations.readCode (.root 1)) targetResult=.ok {targetResult with stack:=.val ⟨2,by decide⟩ :: targetResult.stack} 0 ∧
 Evm.run (TargetOperations.readCode (.data (.root 1) 0)) targetResult=.ok {targetResult with stack:=.val ⟨53,by decide⟩ :: targetResult.stack} 0 ∧
 Evm.run (TargetOperations.readCode (.data (.root 1) 2)) targetResult=.ok {targetResult with stack:=.val ⟨0,by decide⟩ :: targetResult.stack} 0 ∧
 Evm.run (TargetOperations.readCode (.data (.root 1) 3)) targetResult=.ok {targetResult with stack:=.val ⟨71,by decide⟩ :: targetResult.stack} 0 := by
 exact ⟨rfl,rfl,rfl,rfl,rfl,rfl,rfl⟩

/-- info: 'Solidity.Backend.StorageOps.SourceStorageCopyTarget.Controls.certificate' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in #print axioms certificate
/-- info: 'Solidity.Backend.StorageOps.SourceStorageCopyTarget.Controls.ordered' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in #print axioms ordered
/-- info: 'Solidity.Backend.StorageOps.SourceStorageCopyTarget.Controls.full_target_context' does not depend on any axioms -/
#guard_msgs in #print axioms full_target_context
/-- info: 'Solidity.Backend.StorageOps.SourceStorageCopyTarget.Controls.grow_certificate' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in #print axioms grow_certificate
/-- info: 'Solidity.Backend.StorageOps.SourceStorageCopyTarget.Controls.empty_certificate' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in #print axioms empty_certificate
/-- info: 'Solidity.Backend.StorageOps.SourceStorageCopyTarget.Controls.varied_ordered' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in #print axioms varied_ordered
/-- info: 'Solidity.Backend.StorageOps.SourceStorageCopyTarget.Controls.bad_old_agreements' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in #print axioms bad_old_agreements
/-- info: 'Solidity.Backend.StorageOps.SourceStorageCopyTarget.Controls.readbacks' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in #print axioms readbacks
end Solidity.Backend.StorageOps.SourceStorageCopyTarget.Controls
