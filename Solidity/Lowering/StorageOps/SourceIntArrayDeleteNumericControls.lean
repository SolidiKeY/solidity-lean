import Solidity.Lowering.StorageOps.SourceIntArrayDeleteNumeric

/-! Inhabited actual independent Source/numeric/target runtime storage-delete
certificate with complete ordered old/result observations and a bad OLD shadow
agreement control. No general Source compiler/address/world claim. -/
namespace Solidity.Backend.StorageOps.SourceIntArrayDeleteNumeric.Controls
open TypeGraph Solidity.Storage Solidity.Storage.Representation Solidity.Storage.Representation.Graph
open SourceStorageCopy
open SourceArrayDeleteTarget (wordAt)
open SourceIntCopyReadbacks (int256 sourceValue word_agrees)
private def uintSyntax : Source.Syn .typeName := .elem (.int false 256 (by decide))
private def unit : Source.Syn .unit := .unit (.cons (.contract false "C" .none .nil
  (.cons (.stateVar (.array (.elem (.int true 256 (by decide))) .none) none none none false "left" .none)
    (.cons (.stateVar (.array (.elem (.int true 256 (by decide))) .none) none none none false "right" .none)
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
 let s := (Source.Storage.empty : Source.Storage env.layout env.cellTy).write left (.int 2 (by decide))
 let s := s.write (elem left 0) (sourceValue neg17)
 let s := s.write (elem left 2) (sourceValue neg31)
 let s := s.write right (.int 3 (by decide))
 let s := s.write (elem right 0) (sourceValue pos7)
 let s := s.write (elem right 1) (sourceValue neg1)
 let s := s.write (elem right 2) (sourceValue neg23)
 let s := s.write (elem right 3) (sourceValue neg71)
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
private def source : Value graph (.array (.prim .int)) := .array ⟨3,by decide⟩ ⟨2,by decide⟩ (by decide)
 (fun i => if i.val=1 then .absent else .present (.prim (if i.val=0 then neg17 else neg31)))
private def old : Value graph (.array (.prim .int)) := .array ⟨4,by decide⟩ ⟨3,by decide⟩ (by decide)
 (fun i => .present (.prim (if i.val=0 then pos7 else if i.val=1 then neg1 else if i.val=2 then neg23 else neg71)))
private def src : Solidity.Storage.Loc := .root 0
private def dst : Solidity.Storage.Loc := .root 1
private def hash (p : Solidity.Storage.Pre) : Nat := if p=.data 0 then 4 else if p=.data 1 then 8 else 0
private def preimages : List Solidity.Storage.Pre := [.data 0,.data 1]
private def locations : List Solidity.Storage.Loc := [.root 0,.root 1,.root 2,
 .data src 0,.data src 1,.data src 2,.data src 3,.data dst 0,.data dst 1,.data dst 2,.data dst 3]
private def store : Store := fun l =>
 if l=.root 0 then w 2 else if l=.root 1 then w 3 else if l=.root 2 then w 99 else
 if l=.data src 0 then sw neg17 else if l=.data src 2 then sw neg31 else
 if l=.data dst 0 then sw pos7 else if l=.data dst 1 then sw neg1 else if l=.data dst 2 then sw neg23 else if l=.data dst 3 then sw neg71 else w 0
private def numeric : WordStore := fun a =>
 if a=0 then w 2 else if a=1 then w 3 else if a=2 then w 99 else
 if a=4 then sw neg17 else if a=6 then sw neg31 else
 if a=8 then sw pos7 else if a=9 then sw neg1 else if a=10 then sw neg23 else if a=11 then sw neg71 else w 0
private def target : Evm.Machine :=
 {stack := [.val ⟨17,by decide⟩,.slot (.root 9)],
  store := ⟨fun l => if l=.root 0 then ⟨2,by decide⟩ else if l=.root 1 then ⟨3,by decide⟩ else if l=.root 2 then ⟨99,by decide⟩ else
   if l=.data (.root 0) 0 then TargetOperations.encodeWord (sw neg17) else if l=.data (.root 0) 2 then TargetOperations.encodeWord (sw neg31) else
   if l=.data (.root 1) 0 then TargetOperations.encodeWord (sw pos7) else if l=.data (.root 1) 1 then TargetOperations.encodeWord (sw neg1) else if l=.data (.root 1) 2 then TargetOperations.encodeWord (sw neg23) else if l=.data (.root 1) 3 then TargetOperations.encodeWord (sw neg71) else ⟨0,by decide⟩⟩,
  mem := fun _ => .val ⟨31,by decide⟩,bal:=fun _ => 41,bal₀:=fun _ => 43,
  self:=⟨47,by decide⟩,caller:=⟨53,by decide⟩,callvalue:=⟨59,by decide⟩,timestamp:=⟨61,by decide⟩,accepts:=fun _ _ => false}
private def ty : Source.STy := .array .storage (.int int256) none
private def deleted := (Source.deleteStor (E:=env) (Γ:=[]) frame 5 ty right).run initial
private def targetResult := TargetArrayClear.afterClear target target.stack (.root 1)
private def numericResult := TargetClearRepresentation.execute 32 hash dst numeric
private def afterStore := TargetClearRepresentation.afterStore old dst store
private def sourcePaths := [left,elem left 0,elem left 1,elem left 2,right,elem right 0,elem right 1,elem right 2,elem right 3,bad,sentinel,missing]
private def sourceView (ex : Source.ExecState env.layout env.lay env.lay) := sourcePaths.map (wordAt frame ex) ++
 [(((ex.transient.cells frame.this).read scratch).bind Source.Val.word).map Fin.val]
private def numericView (s : WordStore) := [s 0,s 1,s 2,s 4,s 5,s 6,s 7,s 8,s 9,s 10,s 11] |>.map (fun w => w.val)
private def targetSlots : List Evm.Slot := [.root 0,.root 1,.root 2,.data (.root 0) 0,.data (.root 0) 1,.data (.root 0) 2,.data (.root 0) 3,
 .data (.root 1) 0,.data (.root 1) 1,.data (.root 1) 2,.data (.root 1) 3]
private def targetView (s : Evm.Machine) := targetSlots.map (fun slot => s.store slot)
private def graphView (v : Value graph (.array (.prim .int))) := (PrimitivePop.queries indices).map (fun q => (q.read v).map (fun w => w.val))
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
private theorem before : Represented old (TargetClearRepresentation.oldQueries old indices) dst store := by
 change Represented old [.length .nil,PrimitivePop.elementQuery (ix 3)] dst store
 intro q member
 simp only [List.mem_cons,List.not_mem_nil,or_false] at member
 rcases member with rfl|rfl
 · refine ⟨True.intro,⟨by decide,by decide⟩,?_⟩
   intro word observed
   change some (w 3)=some word at observed
   change w 3=word
   exact Option.some.inj observed
 · refine ⟨⟨by change 3<lmax; decide,True.intro⟩,True.intro,?_⟩
   intro word observed
   change some (sw neg71)=some word at observed
   change sw neg71=word
   exact Option.some.inj observed
private theorem covered : ∀ q ∈ PrimitivePop.queries (G:=graph) (p:=.int) indices,q.location dst ∈ locations := by
 intro q member
 simp only [PrimitivePop.queries,indices,List.map_cons,List.map_nil,List.mem_cons,List.not_mem_nil,or_false] at member
 rcases member with rfl|rfl|rfl|rfl|rfl <;> decide
private theorem visited : ∀ j<old.length.val,Solidity.Storage.Loc.data dst j ∈ locations := by
 intro j inside
 change j<3 at inside
 have alternatives : j=0 ∨ j=1 ∨ j=2 := by omega
 rcases alternatives with rfl|rfl|rfl <;> decide

theorem certificate :
 deleted=(.ok (),(Source.Locals.nil,{state with ex:=state.ex.run (((List.range' 0 3).map (fun i => SourceScalarDeleteLog.clearOp env frame (elem right i))) ++ [SourceScalarDeleteLog.clearOp env frame right])})) ∧
 Evm.run TargetArrayClear.code {target with stack:=.slot (.root 1)::target.stack}=.ok targetResult 0 ∧
 Represented old.clear (PrimitivePop.queries indices) dst afterStore ∧ Transport 32 hash locations afterStore numericResult ∧
 (∀ l (member : l ∈ locations),targetResult.store.cells (TargetOperations.toSlot l (fitting l member))=TargetOperations.encodeWord (numericResult (l.word 32 hash))) ∧
 wordAt frame deleted.2.2.ex right=some (TargetOperations.encodeWord (numericResult 1)).val ∧
 (∀ i ∈ indices,wordAt frame deleted.2.2.ex (elem right i.val)=some (TargetOperations.encodeWord (numericResult ((Solidity.Storage.Loc.data dst i.val).word 32 hash))).val) ∧
 (∀ q ∈ PrimitivePop.queries (G:=graph) (p:=.int) indices,∀ word,q.read old.clear=some word → numericResult ((q.location dst).word 32 hash)=word) := by
 apply complete (E:=env) (Γ:=[]) finite frame int256 rfl right .nil state rfl rfl old indices dst True.intro store numeric target target.stack rfl before transported covered visited fitting agreement
 intro i member unvisited
 simp only [indices,List.mem_cons,List.not_mem_nil,or_false] at member
 rcases member with rfl|rfl|rfl|rfl
 · change 3≤0 at unvisited; omega
 · change 3≤1 at unvisited; omega
 · change 3≤2 at unvisited; omega
 · exact word_agrees neg71
private theorem source_word (ex : Source.ExecState env.layout env.lay env.lay) (path : Source.SPath)
 (v : PrimTy.int.Denote) (typed : env.cellTy path=.int int256)
 (stored : (ex.world.accounts frame.this).storage.read path=some (show Source.Val env.layout (env.cellTy path) from typed.symm ▸ sourceValue v)) :
 wordAt frame ex path=some (bits v) := by
 unfold wordAt
 rw [stored]
 simp only [Option.bind_some,SourceCopyReadbacks.word_cast]
 exact word_agrees v

private theorem initial_source_view : sourceView state.ex=
 [some 2,some (bits neg17),some 0,some (bits neg31),some 3,some 7,some (bits neg1),some (bits neg23),some (bits neg71),some 1,some 99,none,some 5] := by
 have a := source_word state.ex (elem left 0) neg17 rfl rfl
 have b := source_word state.ex (elem left 1) zeroInt rfl rfl
 have c := source_word state.ex (elem left 2) neg31 rfl rfl
 have d := source_word state.ex (elem right 0) pos7 rfl rfl
 have e := source_word state.ex (elem right 1) neg1 rfl rfl
 have f := source_word state.ex (elem right 2) neg23 rfl rfl
 have g := source_word state.ex (elem right 3) neg71 rfl rfl
 unfold sourceView sourcePaths
 simp only [List.map_cons,List.map_nil]
 rw [a,b,c,d,e,f,g]
 rfl

private theorem deleted_source_view : sourceView deleted.2.2.ex=[some 2,some (bits neg17),some 0,some (bits neg31),some 0,some 0,some 0,some 0,some (bits neg71),some 1,some 99,none,some 5] := by
 have h0 := source_word deleted.2.2.ex (elem left 0) neg17 rfl rfl
 have h1 := source_word deleted.2.2.ex (elem left 1) zeroInt rfl rfl
 have h2 := source_word deleted.2.2.ex (elem left 2) neg31 rfl rfl
 have h3 := source_word deleted.2.2.ex (elem right 0) zeroInt rfl rfl
 have h4 := source_word deleted.2.2.ex (elem right 1) zeroInt rfl rfl
 have h5 := source_word deleted.2.2.ex (elem right 2) zeroInt rfl rfl
 have h6 := source_word deleted.2.2.ex (elem right 3) neg71 rfl rfl
 unfold sourceView sourcePaths
 simp only [List.map_cons,List.map_nil]
 rw [h0,h1,h2,h3,h4,h5,h6]
 rfl
private theorem deleted_target_view : targetView targetResult=[2,0,99,bits neg17,0,bits neg31,0,0,0,0,bits neg71] := by
 have h0 : targetResult.store (.root 0)=2 := by
  change (TargetArrayClear.afterClear target target.stack (.root 1)).store (.root 0)=_
  rw [TargetArrayClear.after_outside _ _ _ _ (by intro impossible; cases impossible) (by intro j member impossible; cases impossible)]
  rfl
 have h1 : targetResult.store (.root 1)=0 := by
  change (TargetArrayClear.afterClear target target.stack (.root 1)).store (.root 1)=_
  exact TargetArrayClear.after_header target target.stack (.root 1)
 have h2 : targetResult.store (.root 2)=99 := by
  change (TargetArrayClear.afterClear target target.stack (.root 1)).store (.root 2)=_
  rw [TargetArrayClear.after_outside _ _ _ _ (by intro impossible; cases impossible) (by intro j member impossible; cases impossible)]
  rfl
 have h3 : targetResult.store (.data (.root 0) 0)=bits neg17 := by
  change (TargetArrayClear.afterClear target target.stack (.root 1)).store (.data (.root 0) 0)=_
  rw [TargetArrayClear.after_outside _ _ _ _ (by intro impossible; cases impossible) (by intro j member impossible; cases impossible)]
  rfl
 have h4 : targetResult.store (.data (.root 0) 1)=0 := by
  change (TargetArrayClear.afterClear target target.stack (.root 1)).store (.data (.root 0) 1)=_
  rw [TargetArrayClear.after_outside _ _ _ _ (by intro impossible; cases impossible) (by intro j member impossible; cases impossible)]
  rfl
 have h5 : targetResult.store (.data (.root 0) 2)=bits neg31 := by
  change (TargetArrayClear.afterClear target target.stack (.root 1)).store (.data (.root 0) 2)=_
  rw [TargetArrayClear.after_outside _ _ _ _ (by intro impossible; cases impossible) (by intro j member impossible; cases impossible)]
  rfl
 have h6 : targetResult.store (.data (.root 0) 3)=0 := by
  change (TargetArrayClear.afterClear target target.stack (.root 1)).store (.data (.root 0) 3)=_
  rw [TargetArrayClear.after_outside _ _ _ _ (by intro impossible; cases impossible) (by intro j member impossible; cases impossible)]
  rfl
 have h7 : targetResult.store (.data (.root 1) 0)=0 := by
  change (TargetArrayClear.afterClear target target.stack (.root 1)).store (.data (.root 1) 0)=_
  rw [TargetArrayClear.after_data]
  rfl
 have h8 : targetResult.store (.data (.root 1) 1)=0 := by
  change (TargetArrayClear.afterClear target target.stack (.root 1)).store (.data (.root 1) 1)=_
  rw [TargetArrayClear.after_data]
  rfl
 have h9 : targetResult.store (.data (.root 1) 2)=0 := by
  change (TargetArrayClear.afterClear target target.stack (.root 1)).store (.data (.root 1) 2)=_
  rw [TargetArrayClear.after_data]
  rfl
 have h10 : targetResult.store (.data (.root 1) 3)=bits neg71 := by
  change (TargetArrayClear.afterClear target target.stack (.root 1)).store (.data (.root 1) 3)=_
  rw [TargetArrayClear.after_data]
  rfl
 unfold targetView targetSlots
 simp only [List.map_cons,List.map_nil]
 rw [h0,h1,h2,h3,h4,h5,h6,h7,h8,h9,h10]

theorem ordered :
 (sourceView state.ex,sourceView deleted.2.2.ex,graphView old,graphView old.clear,numericView numeric,numericView numericResult,targetView target,targetView targetResult,deleted.2.2.ex.journal.length)=
 ([some 2,some (bits neg17),some 0,some (bits neg31),some 3,some 7,some (bits neg1),some (bits neg23),some (bits neg71),some 1,some 99,none,some 5],
 [some 2,some (bits neg17),some 0,some (bits neg31),some 0,some 0,some 0,some 0,some (bits neg71),some 1,some 99,none,some 5],
 [some 3,some 7,some (sw neg1).val,some (sw neg23).val,some (sw neg71).val],[some 0,some 0,some 0,some 0,some (sw neg71).val],
 [2,3,99,(sw neg17).val,0,(sw neg31).val,0,7,(sw neg1).val,(sw neg23).val,(sw neg71).val],[2,0,99,(sw neg17).val,0,(sw neg31).val,0,0,0,0,(sw neg71).val],
 [2,3,99,bits neg17,0,bits neg31,0,7,bits neg1,bits neg23,bits neg71],[2,0,99,bits neg17,0,bits neg31,0,0,0,0,bits neg71],4) := by
 apply Prod.ext
 · exact initial_source_view
 apply Prod.ext
 · exact deleted_source_view
 apply Prod.ext
 · rfl
 apply Prod.ext
 · rfl
 apply Prod.ext
 · rfl
 apply Prod.ext
 · rfl
 apply Prod.ext
 · rfl
 apply Prod.ext
 · exact deleted_target_view
 rfl

theorem full_target_context : targetContext targetResult=targetContext target := by rfl


private def emptyInitial : Source.Locals env.layout [] × Source.St env :=
 (.nil,{state with ex:=state.ex.apply (SourceScalarDeleteLog.clearOp env frame right)})
private def emptyDeleted := (Source.deleteStor (E:=env) (Γ:=[]) frame 2 ty right).run emptyInitial
private def emptyTarget := {target with store:=Evm.WordStore.write target.store (.root 1) 0}
private def emptyResult := TargetArrayClear.afterClear emptyTarget emptyTarget.stack (.root 1)
private def wrongTarget := {target with store:=Evm.WordStore.write target.store (.root 1) 4}
private def wrongResult := TargetArrayClear.afterClear wrongTarget wrongTarget.stack (.root 1)
private def shortDeleted := (Source.deleteStor (E:=env) (Γ:=[]) frame 3 ty right).run initial
private def staticDelete := (Source.deleteStor (E:=env) (Γ:=[]) {frame with static:=true} 5 ty right).run initial
private def arrayRef : Source.Val env.layout ty := .storRef rfl right
private def alias : Source.Loc env.layout [] (.int int256) := .stor (elem right 2)
private theorem empty_source_view : sourceView emptyInitial.2.ex=[some 2,some (bits neg17),some 0,some (bits neg31),some 0,some 7,some (bits neg1),some (bits neg23),some (bits neg71),some 1,some 99,none,some 5] := by
 have h0 := source_word emptyInitial.2.ex (elem left 0) neg17 rfl rfl
 have h1 := source_word emptyInitial.2.ex (elem left 1) zeroInt rfl rfl
 have h2 := source_word emptyInitial.2.ex (elem left 2) neg31 rfl rfl
 have h3 := source_word emptyInitial.2.ex (elem right 0) pos7 rfl rfl
 have h4 := source_word emptyInitial.2.ex (elem right 1) neg1 rfl rfl
 have h5 := source_word emptyInitial.2.ex (elem right 2) neg23 rfl rfl
 have h6 := source_word emptyInitial.2.ex (elem right 3) neg71 rfl rfl
 unfold sourceView sourcePaths
 simp only [List.map_cons,List.map_nil]
 rw [h0,h1,h2,h3,h4,h5,h6]
 rfl
private theorem empty_deleted_view : sourceView emptyDeleted.2.2.ex=[some 2,some (bits neg17),some 0,some (bits neg31),some 0,some 7,some (bits neg1),some (bits neg23),some (bits neg71),some 1,some 99,none,some 5] := by
 have h0 := source_word emptyDeleted.2.2.ex (elem left 0) neg17 rfl rfl
 have h1 := source_word emptyDeleted.2.2.ex (elem left 1) zeroInt rfl rfl
 have h2 := source_word emptyDeleted.2.2.ex (elem left 2) neg31 rfl rfl
 have h3 := source_word emptyDeleted.2.2.ex (elem right 0) pos7 rfl rfl
 have h4 := source_word emptyDeleted.2.2.ex (elem right 1) neg1 rfl rfl
 have h5 := source_word emptyDeleted.2.2.ex (elem right 2) neg23 rfl rfl
 have h6 := source_word emptyDeleted.2.2.ex (elem right 3) neg71 rfl rfl
 unfold sourceView sourcePaths
 simp only [List.map_cons,List.map_nil]
 rw [h0,h1,h2,h3,h4,h5,h6]
 rfl
private theorem partial_source_view : sourceView shortDeleted.2.2.ex=[some 2,some (bits neg17),some 0,some (bits neg31),some 3,some 0,some (bits neg1),some (bits neg23),some (bits neg71),some 1,some 99,none,some 5] := by
 have h0 := source_word shortDeleted.2.2.ex (elem left 0) neg17 rfl rfl
 have h1 := source_word shortDeleted.2.2.ex (elem left 1) zeroInt rfl rfl
 have h2 := source_word shortDeleted.2.2.ex (elem left 2) neg31 rfl rfl
 have h3 := source_word shortDeleted.2.2.ex (elem right 0) zeroInt rfl rfl
 have h4 := source_word shortDeleted.2.2.ex (elem right 1) neg1 rfl rfl
 have h5 := source_word shortDeleted.2.2.ex (elem right 2) neg23 rfl rfl
 have h6 := source_word shortDeleted.2.2.ex (elem right 3) neg71 rfl rfl
 unfold sourceView sourcePaths
 simp only [List.map_cons,List.map_nil]
 rw [h0,h1,h2,h3,h4,h5,h6]
 rfl
private theorem empty_target_view : targetView emptyResult=[2,0,99,bits neg17,0,bits neg31,0,7,bits neg1,bits neg23,bits neg71] := by
 have h0 : emptyResult.store (.root 0)=2 := by
  change (TargetArrayClear.afterClear emptyTarget emptyTarget.stack (.root 1)).store (.root 0)=_
  rw [TargetArrayClear.after_outside _ _ _ _ (by intro impossible; cases impossible) (by intro j member impossible; cases impossible)]
  change Evm.WordStore.write target.store (.root 1) 0 (.root 0)=_
  rw [Evm.WordStore.write_other _ _ (by intro impossible; cases impossible)]
  rfl
 have h1 : emptyResult.store (.root 1)=0 := by
  change (TargetArrayClear.afterClear emptyTarget emptyTarget.stack (.root 1)).store (.root 1)=_
  exact TargetArrayClear.after_header _ _ _
 have h2 : emptyResult.store (.root 2)=99 := by
  change (TargetArrayClear.afterClear emptyTarget emptyTarget.stack (.root 1)).store (.root 2)=_
  rw [TargetArrayClear.after_outside _ _ _ _ (by intro impossible; cases impossible) (by intro j member impossible; cases impossible)]
  change Evm.WordStore.write target.store (.root 1) 0 (.root 2)=_
  rw [Evm.WordStore.write_other _ _ (by intro impossible; cases impossible)]
  rfl
 have h3 : emptyResult.store (.data (.root 0) 0)=bits neg17 := by
  change (TargetArrayClear.afterClear emptyTarget emptyTarget.stack (.root 1)).store (.data (.root 0) 0)=_
  rw [TargetArrayClear.after_outside _ _ _ _ (by intro impossible; cases impossible) (by intro j member impossible; cases impossible)]
  change Evm.WordStore.write target.store (.root 1) 0 (.data (.root 0) 0)=_
  rw [Evm.WordStore.write_other _ _ (by intro impossible; cases impossible)]
  rfl
 have h4 : emptyResult.store (.data (.root 0) 1)=0 := by
  change (TargetArrayClear.afterClear emptyTarget emptyTarget.stack (.root 1)).store (.data (.root 0) 1)=_
  rw [TargetArrayClear.after_outside _ _ _ _ (by intro impossible; cases impossible) (by intro j member impossible; cases impossible)]
  change Evm.WordStore.write target.store (.root 1) 0 (.data (.root 0) 1)=_
  rw [Evm.WordStore.write_other _ _ (by intro impossible; cases impossible)]
  rfl
 have h5 : emptyResult.store (.data (.root 0) 2)=bits neg31 := by
  change (TargetArrayClear.afterClear emptyTarget emptyTarget.stack (.root 1)).store (.data (.root 0) 2)=_
  rw [TargetArrayClear.after_outside _ _ _ _ (by intro impossible; cases impossible) (by intro j member impossible; cases impossible)]
  change Evm.WordStore.write target.store (.root 1) 0 (.data (.root 0) 2)=_
  rw [Evm.WordStore.write_other _ _ (by intro impossible; cases impossible)]
  rfl
 have h6 : emptyResult.store (.data (.root 0) 3)=0 := by
  change (TargetArrayClear.afterClear emptyTarget emptyTarget.stack (.root 1)).store (.data (.root 0) 3)=_
  rw [TargetArrayClear.after_outside _ _ _ _ (by intro impossible; cases impossible) (by intro j member impossible; cases impossible)]
  change Evm.WordStore.write target.store (.root 1) 0 (.data (.root 0) 3)=_
  rw [Evm.WordStore.write_other _ _ (by intro impossible; cases impossible)]
  rfl
 have h7 : emptyResult.store (.data (.root 1) 0)=7 := by
  change (TargetArrayClear.afterClear emptyTarget emptyTarget.stack (.root 1)).store (.data (.root 1) 0)=_
  rw [TargetArrayClear.after_data]
  have header : emptyTarget.store (.root 1)=0 := Evm.WordStore.write_same_of_lt _ _ _ (by decide)
  rw [header]
  change Evm.WordStore.write target.store (.root 1) 0 (.data (.root 1) 0)=_
  rw [Evm.WordStore.write_other _ _ (by intro impossible; cases impossible)]
  rfl
 have h8 : emptyResult.store (.data (.root 1) 1)=bits neg1 := by
  change (TargetArrayClear.afterClear emptyTarget emptyTarget.stack (.root 1)).store (.data (.root 1) 1)=_
  rw [TargetArrayClear.after_data]
  have header : emptyTarget.store (.root 1)=0 := Evm.WordStore.write_same_of_lt _ _ _ (by decide)
  rw [header]
  change Evm.WordStore.write target.store (.root 1) 0 (.data (.root 1) 1)=_
  rw [Evm.WordStore.write_other _ _ (by intro impossible; cases impossible)]
  rfl
 have h9 : emptyResult.store (.data (.root 1) 2)=bits neg23 := by
  change (TargetArrayClear.afterClear emptyTarget emptyTarget.stack (.root 1)).store (.data (.root 1) 2)=_
  rw [TargetArrayClear.after_data]
  have header : emptyTarget.store (.root 1)=0 := Evm.WordStore.write_same_of_lt _ _ _ (by decide)
  rw [header]
  change Evm.WordStore.write target.store (.root 1) 0 (.data (.root 1) 2)=_
  rw [Evm.WordStore.write_other _ _ (by intro impossible; cases impossible)]
  rfl
 have h10 : emptyResult.store (.data (.root 1) 3)=bits neg71 := by
  change (TargetArrayClear.afterClear emptyTarget emptyTarget.stack (.root 1)).store (.data (.root 1) 3)=_
  rw [TargetArrayClear.after_data]
  have header : emptyTarget.store (.root 1)=0 := Evm.WordStore.write_same_of_lt _ _ _ (by decide)
  rw [header]
  change Evm.WordStore.write target.store (.root 1) 0 (.data (.root 1) 3)=_
  rw [Evm.WordStore.write_other _ _ (by intro impossible; cases impossible)]
  rfl
 unfold targetView targetSlots
 simp only [List.map_cons,List.map_nil]
 rw [h0,h1,h2,h3,h4,h5,h6,h7,h8,h9,h10]
private theorem wrong_target_view : targetView wrongResult=[2,0,99,bits neg17,0,bits neg31,0,0,0,0,0] := by
 have h0 : wrongResult.store (.root 0)=2 := by
  change (TargetArrayClear.afterClear wrongTarget wrongTarget.stack (.root 1)).store (.root 0)=_
  rw [TargetArrayClear.after_outside _ _ _ _ (by intro impossible; cases impossible) (by intro j member impossible; cases impossible)]
  change Evm.WordStore.write target.store (.root 1) 4 (.root 0)=_
  rw [Evm.WordStore.write_other _ _ (by intro impossible; cases impossible)]
  rfl
 have h1 : wrongResult.store (.root 1)=0 := by
  change (TargetArrayClear.afterClear wrongTarget wrongTarget.stack (.root 1)).store (.root 1)=_
  exact TargetArrayClear.after_header _ _ _
 have h2 : wrongResult.store (.root 2)=99 := by
  change (TargetArrayClear.afterClear wrongTarget wrongTarget.stack (.root 1)).store (.root 2)=_
  rw [TargetArrayClear.after_outside _ _ _ _ (by intro impossible; cases impossible) (by intro j member impossible; cases impossible)]
  change Evm.WordStore.write target.store (.root 1) 4 (.root 2)=_
  rw [Evm.WordStore.write_other _ _ (by intro impossible; cases impossible)]
  rfl
 have h3 : wrongResult.store (.data (.root 0) 0)=bits neg17 := by
  change (TargetArrayClear.afterClear wrongTarget wrongTarget.stack (.root 1)).store (.data (.root 0) 0)=_
  rw [TargetArrayClear.after_outside _ _ _ _ (by intro impossible; cases impossible) (by intro j member impossible; cases impossible)]
  change Evm.WordStore.write target.store (.root 1) 4 (.data (.root 0) 0)=_
  rw [Evm.WordStore.write_other _ _ (by intro impossible; cases impossible)]
  rfl
 have h4 : wrongResult.store (.data (.root 0) 1)=0 := by
  change (TargetArrayClear.afterClear wrongTarget wrongTarget.stack (.root 1)).store (.data (.root 0) 1)=_
  rw [TargetArrayClear.after_outside _ _ _ _ (by intro impossible; cases impossible) (by intro j member impossible; cases impossible)]
  change Evm.WordStore.write target.store (.root 1) 4 (.data (.root 0) 1)=_
  rw [Evm.WordStore.write_other _ _ (by intro impossible; cases impossible)]
  rfl
 have h5 : wrongResult.store (.data (.root 0) 2)=bits neg31 := by
  change (TargetArrayClear.afterClear wrongTarget wrongTarget.stack (.root 1)).store (.data (.root 0) 2)=_
  rw [TargetArrayClear.after_outside _ _ _ _ (by intro impossible; cases impossible) (by intro j member impossible; cases impossible)]
  change Evm.WordStore.write target.store (.root 1) 4 (.data (.root 0) 2)=_
  rw [Evm.WordStore.write_other _ _ (by intro impossible; cases impossible)]
  rfl
 have h6 : wrongResult.store (.data (.root 0) 3)=0 := by
  change (TargetArrayClear.afterClear wrongTarget wrongTarget.stack (.root 1)).store (.data (.root 0) 3)=_
  rw [TargetArrayClear.after_outside _ _ _ _ (by intro impossible; cases impossible) (by intro j member impossible; cases impossible)]
  change Evm.WordStore.write target.store (.root 1) 4 (.data (.root 0) 3)=_
  rw [Evm.WordStore.write_other _ _ (by intro impossible; cases impossible)]
  rfl
 have h7 : wrongResult.store (.data (.root 1) 0)=0 := by
  change (TargetArrayClear.afterClear wrongTarget wrongTarget.stack (.root 1)).store (.data (.root 1) 0)=_
  rw [TargetArrayClear.after_data]
  have header : wrongTarget.store (.root 1)=4 := Evm.WordStore.write_same_of_lt _ _ _ (by decide)
  rw [header]
  rfl
 have h8 : wrongResult.store (.data (.root 1) 1)=0 := by
  change (TargetArrayClear.afterClear wrongTarget wrongTarget.stack (.root 1)).store (.data (.root 1) 1)=_
  rw [TargetArrayClear.after_data]
  have header : wrongTarget.store (.root 1)=4 := Evm.WordStore.write_same_of_lt _ _ _ (by decide)
  rw [header]
  rfl
 have h9 : wrongResult.store (.data (.root 1) 2)=0 := by
  change (TargetArrayClear.afterClear wrongTarget wrongTarget.stack (.root 1)).store (.data (.root 1) 2)=_
  rw [TargetArrayClear.after_data]
  have header : wrongTarget.store (.root 1)=4 := Evm.WordStore.write_same_of_lt _ _ _ (by decide)
  rw [header]
  rfl
 have h10 : wrongResult.store (.data (.root 1) 3)=0 := by
  change (TargetArrayClear.afterClear wrongTarget wrongTarget.stack (.root 1)).store (.data (.root 1) 3)=_
  rw [TargetArrayClear.after_data]
  have header : wrongTarget.store (.root 1)=4 := Evm.WordStore.write_same_of_lt _ _ _ (by decide)
  rw [header]
  rfl
 unfold targetView targetSlots
 simp only [List.map_cons,List.map_nil]
 rw [h0,h1,h2,h3,h4,h5,h6,h7,h8,h9,h10]

theorem empty_retained :
 emptyDeleted=(.ok (),(Source.Locals.nil,{emptyInitial.2 with ex:=emptyInitial.2.ex.apply (SourceScalarDeleteLog.clearOp env frame right)})) ∧
 Evm.run TargetArrayClear.code {emptyTarget with stack:=.slot (.root 1)::emptyTarget.stack}=.ok emptyResult 0 ∧
 (sourceView emptyInitial.2.ex,sourceView emptyDeleted.2.2.ex,targetView emptyResult,emptyDeleted.2.2.ex.journal.length)=
 ([some 2,some (bits neg17),some 0,some (bits neg31),some 0,some 7,some (bits neg1),some (bits neg23),some (bits neg71),some 1,some 99,none,some 5],[some 2,some (bits neg17),some 0,some (bits neg31),some 0,some 7,some (bits neg1),some (bits neg23),some (bits neg71),some 1,some 99,none,some 5],[2,0,99,bits neg17,0,bits neg31,0,7,bits neg1,bits neg23,bits neg71],2) := by
 refine ⟨?_,TargetArrayClear.run_current _ _ _,?_⟩
 · exact SourceArrayDeleteTarget.source_array_run frame rfl int256 right 0 .nil emptyInitial.2 rfl
 · exact Prod.ext empty_source_view (Prod.ext empty_deleted_view (Prod.ext empty_target_view rfl))

theorem fuel_static :
 (shortDeleted.1,sourceView shortDeleted.2.2.ex,shortDeleted.2.2.ex.journal.length)=
 (.error .timeout,[some 2,some (bits neg17),some 0,some (bits neg31),some 3,some 0,some (bits neg1),some (bits neg23),some (bits neg71),some 1,some 99,none,some 5],1) ∧ staticDelete=(.error (.revert []),initial) := by
 exact ⟨Prod.ext rfl (Prod.ext partial_source_view rfl),rfl⟩

theorem live_alias_restore :
 (Source.indexLoc (E:=env) (Γ:=[]) frame arrayRef 2).run initial=(.ok alias,initial) ∧
 (Source.readLoc (E:=env) (Γ:=[]) frame alias).run deleted.2=(.ok (sourceValue zeroInt),deleted.2) ∧
 (Source.indexLoc (E:=env) (Γ:=[]) frame arrayRef 2).run deleted.2=(.error (.revert (Source.panicData .index)),deleted.2) ∧
 Source.panicData .index=([0x4e,0x48,0x7b,0x71] ++ List.replicate 31 0 ++ [0x32]) ∧
 (deleted.2.1,{deleted.2.2 with ex:=(state.ex.enter frame.this frame.sender frame.value [] frame.static).rollback deleted.2.2.ex})=(Source.Locals.nil,state) := by
 refine ⟨rfl,rfl,rfl,rfl,?_⟩
 exact SourceArrayDeleteTarget.source_array_restore frame rfl int256 right 3 .nil state [] rfl

/-- The wrong header4 makes the same actual target code erase older index3.
The actual Source delete and correct target count3 preserve signed -71. -/
theorem wrong_extent :
 Evm.run TargetArrayClear.code {wrongTarget with stack:=.slot (.root 1)::wrongTarget.stack}=.ok wrongResult 0 ∧
 (targetView targetResult,targetView wrongResult)=
 ([2,0,99,bits neg17,0,bits neg31,0,0,0,0,bits neg71],[2,0,99,bits neg17,0,bits neg31,0,0,0,0,0]) ∧
 wordAt frame deleted.2.2.ex (elem right 3)≠some (wrongResult.store (.data (.root 1) 3)) := by
 refine ⟨TargetArrayClear.run_current _ _ _,Prod.ext deleted_target_view wrong_target_view,?_⟩
 have sourceOld := source_word deleted.2.2.ex (elem right 3) neg71 rfl rfl
 have targetWrong : wrongResult.store (.data (.root 1) 3)=0 := congrArg (fun xs : List Nat => xs[10]!) wrong_target_view
 rw [sourceOld,targetWrong]
 intro equal
 have value := Option.some.inj equal
 simp only [bits,sw,TargetOperations.encodeWord,keyWord,PrimTy.toWord,neg71,show ¬(0:Int)≤ -71 by omega,dite_false] at value
 omega

theorem readbacks_presence :
 (Source.readAt (E:=env) (Γ:=[]) frame right (.int Source.IntTy.u256)).run deleted.2=(.ok (.int 0 (by decide)),deleted.2) ∧
 (Source.readAt (E:=env) (Γ:=[]) frame (elem right 3) (.int int256)).run deleted.2=(.ok (sourceValue neg71),deleted.2) ∧
 (deleted.2.2.ex.world.accounts address).storage.cell right=none ∧
 (deleted.2.2.ex.world.accounts address).storage.cell (elem right 0)=none ∧
 (deleted.2.2.ex.world.accounts address).storage.cell (elem left 1)=none ∧
 Evm.run (TargetOperations.readCode (.data (.root 1) 3)) targetResult=.ok {targetResult with stack:=.val (TargetOperations.encodeWord (sw neg71))::targetResult.stack} 0 := by
 refine ⟨rfl,rfl,rfl,rfl,rfl,?_⟩
 have observed : targetResult.store (.data (.root 1) 3)=bits neg71 := by
  change (TargetArrayClear.afterClear target target.stack (.root 1)).store (.data (.root 1) 3)=_
  rw [TargetArrayClear.after_data]
  rfl
 have cell : targetResult.store.cells (.data (.root 1) 3)=TargetOperations.encodeWord (sw neg71) := Fin.ext observed
 rw [TargetOperations.run_read,cell]
/-- info: 'Solidity.Backend.StorageOps.SourceIntArrayDeleteNumeric.Controls.certificate' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in #print axioms certificate
/-- info: 'Solidity.Backend.StorageOps.SourceIntArrayDeleteNumeric.Controls.ordered' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in #print axioms ordered
/-- info: 'Solidity.Backend.StorageOps.SourceIntArrayDeleteNumeric.Controls.full_target_context' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in #print axioms full_target_context
/-- info: 'Solidity.Backend.StorageOps.SourceIntArrayDeleteNumeric.Controls.empty_retained' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in #print axioms empty_retained
/-- info: 'Solidity.Backend.StorageOps.SourceIntArrayDeleteNumeric.Controls.fuel_static' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in #print axioms fuel_static
/-- info: 'Solidity.Backend.StorageOps.SourceIntArrayDeleteNumeric.Controls.live_alias_restore' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in #print axioms live_alias_restore
/-- info: 'Solidity.Backend.StorageOps.SourceIntArrayDeleteNumeric.Controls.wrong_extent' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in #print axioms wrong_extent
/-- info: 'Solidity.Backend.StorageOps.SourceIntArrayDeleteNumeric.Controls.readbacks_presence' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in #print axioms readbacks_presence
end Solidity.Backend.StorageOps.SourceIntArrayDeleteNumeric.Controls
