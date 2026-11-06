import Solidity.Lowering.StorageOps.SourceSignedStorageCopyTarget

/-! Inhabited actual independent Source/numeric/target runtime storage-copy
certificate with complete ordered old/result observations and a bad OLD shadow
agreement control. No general Source compiler/address/world claim. -/
namespace Solidity.Backend.StorageOps.SourceSignedStorageCopyTarget.Controls
open TypeGraph Solidity.Storage Solidity.Storage.Representation Solidity.Storage.Representation.Graph
open SourceStorageCopy SourceArrayDeleteTarget
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
private def payload (j : Nat) : Source.Val env.layout (.int int256) := sourceValue (if j=0 then neg17 else zeroInt)
private def grownPayload (j : Nat) : Source.Val env.layout (.int int256) := sourceValue (if j=0 then pos7 else if j=1 then neg1 else neg23)
private def ty : Source.STy := .array .storage (.int int256) none
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
private theorem beforeSource : Represented source (PrimitivePop.queries indices) src store := by
 intro q member
 simp only [PrimitivePop.queries,indices,List.map_cons,List.map_nil,List.mem_cons,List.not_mem_nil,or_false] at member
 rcases member with rfl|rfl|rfl|rfl|rfl
 · refine ⟨True.intro,⟨by decide,by decide⟩,?_⟩
   intro word observed
   change some (w 2)=some word at observed
   change w 2=word
   exact Option.some.inj observed
 · refine ⟨⟨by change 0<lmax; decide,True.intro⟩,True.intro,?_⟩
   intro word observed
   change some (sw neg17)=some word at observed
   change sw neg17=word
   exact Option.some.inj observed
 · refine ⟨⟨by change 1<lmax; decide,True.intro⟩,True.intro,?_⟩
   intro word observed
   change some (w 0)=some word at observed
   change w 0=word
   exact Option.some.inj observed
 · refine ⟨⟨by change 2<lmax; decide,True.intro⟩,True.intro,?_⟩
   intro word observed
   change some (sw neg31)=some word at observed
   change sw neg31=word
   exact Option.some.inj observed
 · refine ⟨⟨by change 3<lmax; decide,True.intro⟩,True.intro,?_⟩
   intro word observed; change (none : Option Semantics.Word)=some word at observed; cases observed
private theorem beforeOld : Represented old (PrimitivePop.queries indices) dst store := by
 intro q member
 simp only [PrimitivePop.queries,indices,List.map_cons,List.map_nil,List.mem_cons,List.not_mem_nil,or_false] at member
 rcases member with rfl|rfl|rfl|rfl|rfl
 · refine ⟨True.intro,⟨by decide,by decide⟩,?_⟩
   intro word observed
   change some (w 3)=some word at observed
   change w 3=word
   exact Option.some.inj observed
 · refine ⟨⟨by change 0<lmax; decide,True.intro⟩,True.intro,?_⟩
   intro word observed
   change some (sw pos7)=some word at observed
   change sw pos7=word
   exact Option.some.inj observed
 · refine ⟨⟨by change 1<lmax; decide,True.intro⟩,True.intro,?_⟩
   intro word observed
   change some (sw neg1)=some word at observed
   change sw neg1=word
   exact Option.some.inj observed
 · refine ⟨⟨by change 2<lmax; decide,True.intro⟩,True.intro,?_⟩
   intro word observed
   change some (sw neg23)=some word at observed
   change sw neg23=word
   exact Option.some.inj observed
 · refine ⟨⟨by change 3<lmax; decide,True.intro⟩,True.intro,?_⟩
   intro word observed
   change some (sw neg71)=some word at observed
   change sw neg71=word
   exact Option.some.inj observed
private theorem sourceReads : ∀ j<2,(Source.readAt (E:=env) (Γ:=[]) frame (left.go (.index j)) (.int int256)).run initial=(.ok (payload j),initial) := by
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

theorem certificate : copied=(.ok (),(Source.Locals.nil,{state with ex:=state.ex.run (copyLog frame int256 right 2 3 payload rfl)})) ∧
 Evm.run TargetArrayCopy.code {target with stack:=.slot (.root 0) :: .slot (.root 1) :: target.stack}=.ok targetResult 0 ∧
 Represented (old.overlay source) (PrimitivePop.queries indices) dst afterStore ∧ Transport 32 hash locations afterStore numericResult ∧
 (∀ l (member : l ∈ locations),targetResult.store.cells (TargetOperations.toSlot l (fitting l member))=TargetOperations.encodeWord (numericResult (l.word 32 hash))) ∧
 wordAt frame copied.2.2.ex right=some (TargetOperations.encodeWord (numericResult 1)).val ∧
 (∀ i ∈ indices,wordAt frame copied.2.2.ex (right.go (.index i.val))=some (TargetOperations.encodeWord (numericResult ((Solidity.Storage.Loc.data dst i.val).word 32 hash))).val) ∧
 (∀ q ∈ PrimitivePop.queries (G:=graph) (p:=.int) indices,∀ word,q.read (old.overlay source)=some word → numericResult ((q.location dst).word 32 hash)=word) := by
 apply complete_numeric (E:=env) (Γ:=[]) finite frame rfl left right (by decide) .nil state rfl rfl old source indices dst src True.intro True.intro store numeric target target.stack payload rfl sourceReads rfl beforeOld beforeSource transported
   (by decide) (by decide) dstCoverage srcCoverage readCoverage writeCoverage fitting agreement
 · intro j live
   change j<2 at live
   have alternatives : j=0 ∨ j=1 := by omega
   rcases alternatives with rfl|rfl
   · exact word_agrees neg17
   · exact word_agrees zeroInt
 · intro i member unvisited
   simp only [indices,List.mem_cons,List.not_mem_nil,or_false] at member
   rcases member with rfl|rfl|rfl|rfl
   · change max 2 3≤0 at unvisited; omega
   · change max 2 3≤1 at unvisited; omega
   · change max 2 3≤2 at unvisited; omega
   · change ((sourceValue (D:=env.layout) neg71).word).map Fin.val=some (bits neg71)
     exact word_agrees neg71

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

private theorem copied_source_view : sourceView copied.2.2.ex=
 [some 2,some (bits neg17),some 0,some (bits neg31),some 2,some (bits neg17),some 0,some 0,some (bits neg71),some 1,some 99,none,some 5] := by
 have a := source_word copied.2.2.ex (elem left 0) neg17 rfl rfl
 have b := source_word copied.2.2.ex (elem left 1) zeroInt rfl rfl
 have c := source_word copied.2.2.ex (elem left 2) neg31 rfl rfl
 have d := source_word copied.2.2.ex (elem right 0) neg17 rfl rfl
 have e := source_word copied.2.2.ex (elem right 1) zeroInt rfl rfl
 have f := source_word copied.2.2.ex (elem right 2) zeroInt rfl rfl
 have g := source_word copied.2.2.ex (elem right 3) neg71 rfl rfl
 unfold sourceView sourcePaths
 simp only [List.map_cons,List.map_nil]
 rw [a,b,c,d,e,f,g]
 rfl

private theorem source_target_cell (j : Nat) : targetResult.store (.data (.root 0) j)=target.store (.data (.root 0) j) :=
 TargetArrayCopyTail.after_outside target target.stack (.root 0) (.root 1) _
  (by intro impossible; cases impossible) (by intro i inside impossible; cases impossible)
private theorem target_root_zero : targetResult.store (.root 0)=target.store (.root 0) :=
 TargetArrayCopyTail.after_outside target target.stack (.root 0) (.root 1) _
  (by intro impossible; cases impossible) (by intro i inside impossible; cases impossible)
private theorem target_root_two : targetResult.store (.root 2)=target.store (.root 2) :=
 TargetArrayCopyTail.after_outside target target.stack (.root 0) (.root 1) _
  (by intro impossible; cases impossible) (by intro i inside impossible; cases impossible)
private theorem target_child (j : Nat) : targetResult.store (.data (.root 1) j)=
 if j<2 then target.store (.data (.root 0) j) else if j<3 then 0 else target.store (.data (.root 1) j) :=
 TargetArrayCopyTail.after_data target target.stack (.root 0) (.root 1) j
private theorem target_header : targetResult.store (.root 1)=2 :=
 TargetArrayCopyTail.after_header target target.stack (.root 0) (.root 1)
private theorem neg17_bits : bits neg17=2^256-17 := by
 simp only [bits,sw,TargetOperations.encodeWord,keyWord,PrimTy.toWord,neg17,show ¬(0:Int)≤ -17 by omega,dite_false]
 omega
private theorem neg71_bits : bits neg71=2^256-71 := by
 simp only [bits,sw,TargetOperations.encodeWord,keyWord,PrimTy.toWord,neg71,show ¬(0:Int)≤ -71 by omega,dite_false]
 omega
private theorem copied_target_view : targetView targetResult=[2,2,99,bits neg17,0,bits neg31,0,bits neg17,0,0,bits neg71] := by
 unfold targetView targetSlots
 simp only [List.map_cons,List.map_nil]
 rw [target_root_zero,target_root_two,source_target_cell 0,source_target_cell 1,source_target_cell 2,source_target_cell 3,
  target_header,target_child 0,target_child 1,target_child 2,target_child 3]
 rfl

theorem ordered :
 (sourceView state.ex,sourceView copied.2.2.ex,graphView old,graphView (old.overlay source),numericView numeric,numericView numericResult,targetView target,targetView targetResult,copied.2.2.ex.journal.length)=
 ([some 2,some (bits neg17),some 0,some (bits neg31),some 3,some 7,some (bits neg1),some (bits neg23),some (bits neg71),some 1,some 99,none,some 5],
 [some 2,some (bits neg17),some 0,some (bits neg31),some 2,some (bits neg17),some 0,some 0,some (bits neg71),some 1,some 99,none,some 5],
 [some 3,some 7,some (sw neg1).val,some (sw neg23).val,some (sw neg71).val],[some 2,some (sw neg17).val,some 0,some 0,some (sw neg71).val],
 [2,3,99,(sw neg17).val,0,(sw neg31).val,0,7,(sw neg1).val,(sw neg23).val,(sw neg71).val],[2,2,99,(sw neg17).val,0,(sw neg31).val,0,(sw neg17).val,0,0,(sw neg71).val],
 [2,3,99,bits neg17,0,bits neg31,0,7,bits neg1,bits neg23,bits neg71],[2,2,99,bits neg17,0,bits neg31,0,bits neg17,0,0,bits neg71],4) := by
 apply Prod.ext
 · exact initial_source_view
 apply Prod.ext
 · exact copied_source_view
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
 · exact copied_target_view
 rfl

theorem full_target_context : targetContext targetResult=targetContext target := by rfl

private def emptyInitial : Source.Locals env.layout [] × Source.St env :=
 (.nil,{state with ex:=state.ex.apply (cellOp env frame left (some (.int 0 (by decide))))})
private def emptyTarget := {target with store:=Evm.WordStore.write target.store (.root 0) 0}
private def emptied := (sourceOp left right).run emptyInitial
private def emptyTargetResult := TargetArrayCopyTail.afterCopy emptyTarget emptyTarget.stack (.root 0) (.root 1)
private def badOlderTarget := {target with store:=Evm.WordStore.write target.store (.data (.root 1) 3) 71}
private def badOlderResult := TargetArrayCopyTail.afterCopy badOlderTarget badOlderTarget.stack (.root 0) (.root 1)
private def badPayloadTarget := {target with store:=Evm.WordStore.write target.store (.data (.root 0) 0) 17}
private def badPayloadResult := TargetArrayCopyTail.afterCopy badPayloadTarget badPayloadTarget.stack (.root 0) (.root 1)

private theorem grownReads : ∀ j<3,(Source.readAt (E:=env) (Γ:=[]) frame (right.go (.index j)) (.int int256)).run initial=(.ok (grownPayload j),initial) := by
 intro j member
 have alternatives : j=0 ∨ j=1 ∨ j=2 := by omega
 rcases alternatives with rfl|rfl|rfl <;> rfl

theorem grow_certificate : grown=(.ok (),(Source.Locals.nil,{state with ex:=state.ex.run (copyLog frame int256 left 3 2 grownPayload rfl)})) ∧
 Evm.run TargetArrayCopy.code {target with stack:=.slot (.root 1) :: .slot (.root 0) :: target.stack}=.ok grownTarget 0 ∧
 wordAt frame grown.2.2.ex left=some (grownTarget.store (.root 0)) ∧
 (∀ j ∈ [0,1,2,3],wordAt frame grown.2.2.ex (left.go (.index j))=some (grownTarget.store (.data (.root 0) j))) := by
 apply complete (E:=env) (Γ:=[]) frame rfl right left (by decide) 3 2 (by decide) [0,1,2,3] grownPayload rfl rfl .nil state rfl grownReads rfl target target.stack (.root 1) (.root 0) rfl rfl
 · intro j member
   have alternatives : j=0 ∨ j=1 ∨ j=2 := by omega
   rcases alternatives with rfl|rfl|rfl
   · exact word_agrees pos7
   · exact word_agrees neg1
   · exact word_agrees neg23
 · intro j member unvisited
   simp only [List.mem_cons,List.not_mem_nil,or_false] at member
   rcases member with rfl|rfl|rfl|rfl
   · omega
   · omega
   · omega
   · rfl

theorem empty_certificate : emptied=(.ok (),(Source.Locals.nil,{emptyInitial.2 with ex:=emptyInitial.2.ex.run (copyLog frame int256 right 0 3 payload rfl)})) ∧
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
   · have value := source_word emptyInitial.2.ex (elem right 3) neg71 rfl rfl
     have cell : emptyTarget.store (.data (.root 1) 3)=bits neg71 := by
      change Evm.WordStore.write target.store (.root 0) 0 (.data (.root 1) 3)=_
      rw [Evm.WordStore.write_other _ _ (by intro impossible; cases impossible)]
      rfl
     rw [cell]
     exact value

private theorem grown_source_view : sourceView grown.2.2.ex=[some 3,some 7,some (bits neg1),some (bits neg23),some 3,some 7,some (bits neg1),some (bits neg23),some (bits neg71),some 1,some 99,none,some 5] := by
 have h0 := source_word grown.2.2.ex (elem left 0) pos7 rfl rfl
 have h1 := source_word grown.2.2.ex (elem left 1) neg1 rfl rfl
 have h2 := source_word grown.2.2.ex (elem left 2) neg23 rfl rfl
 have h3 := source_word grown.2.2.ex (elem right 0) pos7 rfl rfl
 have h4 := source_word grown.2.2.ex (elem right 1) neg1 rfl rfl
 have h5 := source_word grown.2.2.ex (elem right 2) neg23 rfl rfl
 have h6 := source_word grown.2.2.ex (elem right 3) neg71 rfl rfl
 unfold sourceView sourcePaths
 simp only [List.map_cons,List.map_nil]
 rw [h0,h1,h2,h3,h4,h5,h6]
 rfl
private theorem empty_source_view : sourceView emptyInitial.2.ex=[some 0,some (bits neg17),some 0,some (bits neg31),some 3,some 7,some (bits neg1),some (bits neg23),some (bits neg71),some 1,some 99,none,some 5] := by
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
private theorem emptied_source_view : sourceView emptied.2.2.ex=[some 0,some (bits neg17),some 0,some (bits neg31),some 0,some 0,some 0,some 0,some (bits neg71),some 1,some 99,none,some 5] := by
 have h0 := source_word emptied.2.2.ex (elem left 0) neg17 rfl rfl
 have h1 := source_word emptied.2.2.ex (elem left 1) zeroInt rfl rfl
 have h2 := source_word emptied.2.2.ex (elem left 2) neg31 rfl rfl
 have h3 := source_word emptied.2.2.ex (elem right 0) zeroInt rfl rfl
 have h4 := source_word emptied.2.2.ex (elem right 1) zeroInt rfl rfl
 have h5 := source_word emptied.2.2.ex (elem right 2) zeroInt rfl rfl
 have h6 := source_word emptied.2.2.ex (elem right 3) neg71 rfl rfl
 unfold sourceView sourcePaths
 simp only [List.map_cons,List.map_nil]
 rw [h0,h1,h2,h3,h4,h5,h6]
 rfl
private theorem grown_target_view : targetView grownTarget=[3,3,99,7,bits neg1,bits neg23,0,7,bits neg1,bits neg23,bits neg71] := by
 have o0 : target.store (.root 0)=2 := by
  rfl
 have o1 : target.store (.root 1)=3 := by
  rfl
 have o2 : target.store (.root 2)=99 := by
  rfl
 have o3 : target.store (.data (.root 0) 0)=bits neg17 := by
  rfl
 have o4 : target.store (.data (.root 0) 1)=0 := by
  rfl
 have o5 : target.store (.data (.root 0) 2)=bits neg31 := by
  rfl
 have o6 : target.store (.data (.root 0) 3)=0 := by
  rfl
 have o7 : target.store (.data (.root 1) 0)=7 := by
  rfl
 have o8 : target.store (.data (.root 1) 1)=bits neg1 := by
  rfl
 have o9 : target.store (.data (.root 1) 2)=bits neg23 := by
  rfl
 have o10 : target.store (.data (.root 1) 3)=bits neg71 := by
  rfl
 have h0 : grownTarget.store (.root 0)=3 := by
  change (TargetArrayCopyTail.afterCopy target target.stack (.root 1) (.root 0)).store (.root 0)=_
  rw [TargetArrayCopyTail.after_header,o1]
 have h1 : grownTarget.store (.root 1)=3 := by
  change (TargetArrayCopyTail.afterCopy target target.stack (.root 1) (.root 0)).store (.root 1)=_
  rw [TargetArrayCopyTail.after_outside _ _ _ _ _ (by intro impossible; cases impossible) (by intro j member impossible; cases impossible),o1]
 have h2 : grownTarget.store (.root 2)=99 := by
  change (TargetArrayCopyTail.afterCopy target target.stack (.root 1) (.root 0)).store (.root 2)=_
  rw [TargetArrayCopyTail.after_outside _ _ _ _ _ (by intro impossible; cases impossible) (by intro j member impossible; cases impossible),o2]
 have h3 : grownTarget.store (.data (.root 0) 0)=7 := by
  change (TargetArrayCopyTail.afterCopy target target.stack (.root 1) (.root 0)).store (.data (.root 0) 0)=_
  rw [TargetArrayCopyTail.after_data,o1,o0,o7,o3]
  rfl
 have h4 : grownTarget.store (.data (.root 0) 1)=bits neg1 := by
  change (TargetArrayCopyTail.afterCopy target target.stack (.root 1) (.root 0)).store (.data (.root 0) 1)=_
  rw [TargetArrayCopyTail.after_data,o1,o0,o8,o4]
  rfl
 have h5 : grownTarget.store (.data (.root 0) 2)=bits neg23 := by
  change (TargetArrayCopyTail.afterCopy target target.stack (.root 1) (.root 0)).store (.data (.root 0) 2)=_
  rw [TargetArrayCopyTail.after_data,o1,o0,o9,o5]
  rfl
 have h6 : grownTarget.store (.data (.root 0) 3)=0 := by
  change (TargetArrayCopyTail.afterCopy target target.stack (.root 1) (.root 0)).store (.data (.root 0) 3)=_
  rw [TargetArrayCopyTail.after_data,o1,o0,o10,o6]
  rfl
 have h7 : grownTarget.store (.data (.root 1) 0)=7 := by
  change (TargetArrayCopyTail.afterCopy target target.stack (.root 1) (.root 0)).store (.data (.root 1) 0)=_
  rw [TargetArrayCopyTail.after_outside _ _ _ _ _ (by intro impossible; cases impossible) (by intro j member impossible; cases impossible),o7]
 have h8 : grownTarget.store (.data (.root 1) 1)=bits neg1 := by
  change (TargetArrayCopyTail.afterCopy target target.stack (.root 1) (.root 0)).store (.data (.root 1) 1)=_
  rw [TargetArrayCopyTail.after_outside _ _ _ _ _ (by intro impossible; cases impossible) (by intro j member impossible; cases impossible),o8]
 have h9 : grownTarget.store (.data (.root 1) 2)=bits neg23 := by
  change (TargetArrayCopyTail.afterCopy target target.stack (.root 1) (.root 0)).store (.data (.root 1) 2)=_
  rw [TargetArrayCopyTail.after_outside _ _ _ _ _ (by intro impossible; cases impossible) (by intro j member impossible; cases impossible),o9]
 have h10 : grownTarget.store (.data (.root 1) 3)=bits neg71 := by
  change (TargetArrayCopyTail.afterCopy target target.stack (.root 1) (.root 0)).store (.data (.root 1) 3)=_
  rw [TargetArrayCopyTail.after_outside _ _ _ _ _ (by intro impossible; cases impossible) (by intro j member impossible; cases impossible),o10]
 unfold targetView targetSlots
 simp only [List.map_cons,List.map_nil]
 rw [h0,h1,h2,h3,h4,h5,h6,h7,h8,h9,h10]
private theorem empty_target_view : targetView emptyTargetResult=[0,0,99,bits neg17,0,bits neg31,0,0,0,0,bits neg71] := by
 have o0 : emptyTarget.store (.root 0)=0 := by
  change Evm.WordStore.write target.store (.root 0) 0 (.root 0)=_
  rw [Evm.WordStore.write_same_of_lt _ _ _ (by decide)]
 have o1 : emptyTarget.store (.root 1)=3 := by
  change Evm.WordStore.write target.store (.root 0) 0 (.root 1)=_
  rw [Evm.WordStore.write_other _ _ (by intro impossible; cases impossible)]
  rfl
 have o2 : emptyTarget.store (.root 2)=99 := by
  change Evm.WordStore.write target.store (.root 0) 0 (.root 2)=_
  rw [Evm.WordStore.write_other _ _ (by intro impossible; cases impossible)]
  rfl
 have o3 : emptyTarget.store (.data (.root 0) 0)=bits neg17 := by
  change Evm.WordStore.write target.store (.root 0) 0 (.data (.root 0) 0)=_
  rw [Evm.WordStore.write_other _ _ (by intro impossible; cases impossible)]
  rfl
 have o4 : emptyTarget.store (.data (.root 0) 1)=0 := by
  change Evm.WordStore.write target.store (.root 0) 0 (.data (.root 0) 1)=_
  rw [Evm.WordStore.write_other _ _ (by intro impossible; cases impossible)]
  rfl
 have o5 : emptyTarget.store (.data (.root 0) 2)=bits neg31 := by
  change Evm.WordStore.write target.store (.root 0) 0 (.data (.root 0) 2)=_
  rw [Evm.WordStore.write_other _ _ (by intro impossible; cases impossible)]
  rfl
 have o6 : emptyTarget.store (.data (.root 0) 3)=0 := by
  change Evm.WordStore.write target.store (.root 0) 0 (.data (.root 0) 3)=_
  rw [Evm.WordStore.write_other _ _ (by intro impossible; cases impossible)]
  rfl
 have o7 : emptyTarget.store (.data (.root 1) 0)=7 := by
  change Evm.WordStore.write target.store (.root 0) 0 (.data (.root 1) 0)=_
  rw [Evm.WordStore.write_other _ _ (by intro impossible; cases impossible)]
  rfl
 have o8 : emptyTarget.store (.data (.root 1) 1)=bits neg1 := by
  change Evm.WordStore.write target.store (.root 0) 0 (.data (.root 1) 1)=_
  rw [Evm.WordStore.write_other _ _ (by intro impossible; cases impossible)]
  rfl
 have o9 : emptyTarget.store (.data (.root 1) 2)=bits neg23 := by
  change Evm.WordStore.write target.store (.root 0) 0 (.data (.root 1) 2)=_
  rw [Evm.WordStore.write_other _ _ (by intro impossible; cases impossible)]
  rfl
 have o10 : emptyTarget.store (.data (.root 1) 3)=bits neg71 := by
  change Evm.WordStore.write target.store (.root 0) 0 (.data (.root 1) 3)=_
  rw [Evm.WordStore.write_other _ _ (by intro impossible; cases impossible)]
  rfl
 have h0 : emptyTargetResult.store (.root 0)=0 := by
  change (TargetArrayCopyTail.afterCopy emptyTarget emptyTarget.stack (.root 0) (.root 1)).store (.root 0)=_
  rw [TargetArrayCopyTail.after_outside _ _ _ _ _ (by intro impossible; cases impossible) (by intro j member impossible; cases impossible),o0]
 have h1 : emptyTargetResult.store (.root 1)=0 := by
  change (TargetArrayCopyTail.afterCopy emptyTarget emptyTarget.stack (.root 0) (.root 1)).store (.root 1)=_
  rw [TargetArrayCopyTail.after_header,o0]
 have h2 : emptyTargetResult.store (.root 2)=99 := by
  change (TargetArrayCopyTail.afterCopy emptyTarget emptyTarget.stack (.root 0) (.root 1)).store (.root 2)=_
  rw [TargetArrayCopyTail.after_outside _ _ _ _ _ (by intro impossible; cases impossible) (by intro j member impossible; cases impossible),o2]
 have h3 : emptyTargetResult.store (.data (.root 0) 0)=bits neg17 := by
  change (TargetArrayCopyTail.afterCopy emptyTarget emptyTarget.stack (.root 0) (.root 1)).store (.data (.root 0) 0)=_
  rw [TargetArrayCopyTail.after_outside _ _ _ _ _ (by intro impossible; cases impossible) (by intro j member impossible; cases impossible),o3]
 have h4 : emptyTargetResult.store (.data (.root 0) 1)=0 := by
  change (TargetArrayCopyTail.afterCopy emptyTarget emptyTarget.stack (.root 0) (.root 1)).store (.data (.root 0) 1)=_
  rw [TargetArrayCopyTail.after_outside _ _ _ _ _ (by intro impossible; cases impossible) (by intro j member impossible; cases impossible),o4]
 have h5 : emptyTargetResult.store (.data (.root 0) 2)=bits neg31 := by
  change (TargetArrayCopyTail.afterCopy emptyTarget emptyTarget.stack (.root 0) (.root 1)).store (.data (.root 0) 2)=_
  rw [TargetArrayCopyTail.after_outside _ _ _ _ _ (by intro impossible; cases impossible) (by intro j member impossible; cases impossible),o5]
 have h6 : emptyTargetResult.store (.data (.root 0) 3)=0 := by
  change (TargetArrayCopyTail.afterCopy emptyTarget emptyTarget.stack (.root 0) (.root 1)).store (.data (.root 0) 3)=_
  rw [TargetArrayCopyTail.after_outside _ _ _ _ _ (by intro impossible; cases impossible) (by intro j member impossible; cases impossible),o6]
 have h7 : emptyTargetResult.store (.data (.root 1) 0)=0 := by
  change (TargetArrayCopyTail.afterCopy emptyTarget emptyTarget.stack (.root 0) (.root 1)).store (.data (.root 1) 0)=_
  rw [TargetArrayCopyTail.after_data,o0,o1,o3,o7]
  rfl
 have h8 : emptyTargetResult.store (.data (.root 1) 1)=0 := by
  change (TargetArrayCopyTail.afterCopy emptyTarget emptyTarget.stack (.root 0) (.root 1)).store (.data (.root 1) 1)=_
  rw [TargetArrayCopyTail.after_data,o0,o1,o4,o8]
  rfl
 have h9 : emptyTargetResult.store (.data (.root 1) 2)=0 := by
  change (TargetArrayCopyTail.afterCopy emptyTarget emptyTarget.stack (.root 0) (.root 1)).store (.data (.root 1) 2)=_
  rw [TargetArrayCopyTail.after_data,o0,o1,o5,o9]
  rfl
 have h10 : emptyTargetResult.store (.data (.root 1) 3)=bits neg71 := by
  change (TargetArrayCopyTail.afterCopy emptyTarget emptyTarget.stack (.root 0) (.root 1)).store (.data (.root 1) 3)=_
  rw [TargetArrayCopyTail.after_data,o0,o1,o6,o10]
  rfl
 unfold targetView targetSlots
 simp only [List.map_cons,List.map_nil]
 rw [h0,h1,h2,h3,h4,h5,h6,h7,h8,h9,h10]
private theorem bad_older_view : targetView badOlderResult=[2,2,99,bits neg17,0,bits neg31,0,bits neg17,0,0,71] := by
 have o0 : badOlderTarget.store (.root 0)=2 := by
  change Evm.WordStore.write target.store (.data (.root 1) 3) 71 (.root 0)=_
  rw [Evm.WordStore.write_other _ _ (by intro impossible; cases impossible)]
  rfl
 have o1 : badOlderTarget.store (.root 1)=3 := by
  change Evm.WordStore.write target.store (.data (.root 1) 3) 71 (.root 1)=_
  rw [Evm.WordStore.write_other _ _ (by intro impossible; cases impossible)]
  rfl
 have o2 : badOlderTarget.store (.root 2)=99 := by
  change Evm.WordStore.write target.store (.data (.root 1) 3) 71 (.root 2)=_
  rw [Evm.WordStore.write_other _ _ (by intro impossible; cases impossible)]
  rfl
 have o3 : badOlderTarget.store (.data (.root 0) 0)=bits neg17 := by
  change Evm.WordStore.write target.store (.data (.root 1) 3) 71 (.data (.root 0) 0)=_
  rw [Evm.WordStore.write_other _ _ (by intro impossible; cases impossible)]
  rfl
 have o4 : badOlderTarget.store (.data (.root 0) 1)=0 := by
  change Evm.WordStore.write target.store (.data (.root 1) 3) 71 (.data (.root 0) 1)=_
  rw [Evm.WordStore.write_other _ _ (by intro impossible; cases impossible)]
  rfl
 have o5 : badOlderTarget.store (.data (.root 0) 2)=bits neg31 := by
  change Evm.WordStore.write target.store (.data (.root 1) 3) 71 (.data (.root 0) 2)=_
  rw [Evm.WordStore.write_other _ _ (by intro impossible; cases impossible)]
  rfl
 have o6 : badOlderTarget.store (.data (.root 0) 3)=0 := by
  change Evm.WordStore.write target.store (.data (.root 1) 3) 71 (.data (.root 0) 3)=_
  rw [Evm.WordStore.write_other _ _ (by intro impossible; cases impossible)]
  rfl
 have o7 : badOlderTarget.store (.data (.root 1) 0)=7 := by
  change Evm.WordStore.write target.store (.data (.root 1) 3) 71 (.data (.root 1) 0)=_
  rw [Evm.WordStore.write_other _ _ (by intro impossible; cases impossible)]
  rfl
 have o8 : badOlderTarget.store (.data (.root 1) 1)=bits neg1 := by
  change Evm.WordStore.write target.store (.data (.root 1) 3) 71 (.data (.root 1) 1)=_
  rw [Evm.WordStore.write_other _ _ (by intro impossible; cases impossible)]
  rfl
 have o9 : badOlderTarget.store (.data (.root 1) 2)=bits neg23 := by
  change Evm.WordStore.write target.store (.data (.root 1) 3) 71 (.data (.root 1) 2)=_
  rw [Evm.WordStore.write_other _ _ (by intro impossible; cases impossible)]
  rfl
 have o10 : badOlderTarget.store (.data (.root 1) 3)=71 := by
  change Evm.WordStore.write target.store (.data (.root 1) 3) 71 (.data (.root 1) 3)=_
  rw [Evm.WordStore.write_same_of_lt _ _ _ (by decide)]
 have h0 : badOlderResult.store (.root 0)=2 := by
  change (TargetArrayCopyTail.afterCopy badOlderTarget badOlderTarget.stack (.root 0) (.root 1)).store (.root 0)=_
  rw [TargetArrayCopyTail.after_outside _ _ _ _ _ (by intro impossible; cases impossible) (by intro j member impossible; cases impossible),o0]
 have h1 : badOlderResult.store (.root 1)=2 := by
  change (TargetArrayCopyTail.afterCopy badOlderTarget badOlderTarget.stack (.root 0) (.root 1)).store (.root 1)=_
  rw [TargetArrayCopyTail.after_header,o0]
 have h2 : badOlderResult.store (.root 2)=99 := by
  change (TargetArrayCopyTail.afterCopy badOlderTarget badOlderTarget.stack (.root 0) (.root 1)).store (.root 2)=_
  rw [TargetArrayCopyTail.after_outside _ _ _ _ _ (by intro impossible; cases impossible) (by intro j member impossible; cases impossible),o2]
 have h3 : badOlderResult.store (.data (.root 0) 0)=bits neg17 := by
  change (TargetArrayCopyTail.afterCopy badOlderTarget badOlderTarget.stack (.root 0) (.root 1)).store (.data (.root 0) 0)=_
  rw [TargetArrayCopyTail.after_outside _ _ _ _ _ (by intro impossible; cases impossible) (by intro j member impossible; cases impossible),o3]
 have h4 : badOlderResult.store (.data (.root 0) 1)=0 := by
  change (TargetArrayCopyTail.afterCopy badOlderTarget badOlderTarget.stack (.root 0) (.root 1)).store (.data (.root 0) 1)=_
  rw [TargetArrayCopyTail.after_outside _ _ _ _ _ (by intro impossible; cases impossible) (by intro j member impossible; cases impossible),o4]
 have h5 : badOlderResult.store (.data (.root 0) 2)=bits neg31 := by
  change (TargetArrayCopyTail.afterCopy badOlderTarget badOlderTarget.stack (.root 0) (.root 1)).store (.data (.root 0) 2)=_
  rw [TargetArrayCopyTail.after_outside _ _ _ _ _ (by intro impossible; cases impossible) (by intro j member impossible; cases impossible),o5]
 have h6 : badOlderResult.store (.data (.root 0) 3)=0 := by
  change (TargetArrayCopyTail.afterCopy badOlderTarget badOlderTarget.stack (.root 0) (.root 1)).store (.data (.root 0) 3)=_
  rw [TargetArrayCopyTail.after_outside _ _ _ _ _ (by intro impossible; cases impossible) (by intro j member impossible; cases impossible),o6]
 have h7 : badOlderResult.store (.data (.root 1) 0)=bits neg17 := by
  change (TargetArrayCopyTail.afterCopy badOlderTarget badOlderTarget.stack (.root 0) (.root 1)).store (.data (.root 1) 0)=_
  rw [TargetArrayCopyTail.after_data,o0,o1,o3,o7]
  rfl
 have h8 : badOlderResult.store (.data (.root 1) 1)=0 := by
  change (TargetArrayCopyTail.afterCopy badOlderTarget badOlderTarget.stack (.root 0) (.root 1)).store (.data (.root 1) 1)=_
  rw [TargetArrayCopyTail.after_data,o0,o1,o4,o8]
  rfl
 have h9 : badOlderResult.store (.data (.root 1) 2)=0 := by
  change (TargetArrayCopyTail.afterCopy badOlderTarget badOlderTarget.stack (.root 0) (.root 1)).store (.data (.root 1) 2)=_
  rw [TargetArrayCopyTail.after_data,o0,o1,o5,o9]
  rfl
 have h10 : badOlderResult.store (.data (.root 1) 3)=71 := by
  change (TargetArrayCopyTail.afterCopy badOlderTarget badOlderTarget.stack (.root 0) (.root 1)).store (.data (.root 1) 3)=_
  rw [TargetArrayCopyTail.after_data,o0,o1,o6,o10]
  rfl
 unfold targetView targetSlots
 simp only [List.map_cons,List.map_nil]
 rw [h0,h1,h2,h3,h4,h5,h6,h7,h8,h9,h10]
private theorem bad_payload_view : targetView badPayloadResult=[2,2,99,17,0,bits neg31,0,17,0,0,bits neg71] := by
 have o0 : badPayloadTarget.store (.root 0)=2 := by
  change Evm.WordStore.write target.store (.data (.root 0) 0) 17 (.root 0)=_
  rw [Evm.WordStore.write_other _ _ (by intro impossible; cases impossible)]
  rfl
 have o1 : badPayloadTarget.store (.root 1)=3 := by
  change Evm.WordStore.write target.store (.data (.root 0) 0) 17 (.root 1)=_
  rw [Evm.WordStore.write_other _ _ (by intro impossible; cases impossible)]
  rfl
 have o2 : badPayloadTarget.store (.root 2)=99 := by
  change Evm.WordStore.write target.store (.data (.root 0) 0) 17 (.root 2)=_
  rw [Evm.WordStore.write_other _ _ (by intro impossible; cases impossible)]
  rfl
 have o3 : badPayloadTarget.store (.data (.root 0) 0)=17 := by
  change Evm.WordStore.write target.store (.data (.root 0) 0) 17 (.data (.root 0) 0)=_
  rw [Evm.WordStore.write_same_of_lt _ _ _ (by decide)]
 have o4 : badPayloadTarget.store (.data (.root 0) 1)=0 := by
  change Evm.WordStore.write target.store (.data (.root 0) 0) 17 (.data (.root 0) 1)=_
  rw [Evm.WordStore.write_other _ _ (by intro impossible; cases impossible)]
  rfl
 have o5 : badPayloadTarget.store (.data (.root 0) 2)=bits neg31 := by
  change Evm.WordStore.write target.store (.data (.root 0) 0) 17 (.data (.root 0) 2)=_
  rw [Evm.WordStore.write_other _ _ (by intro impossible; cases impossible)]
  rfl
 have o6 : badPayloadTarget.store (.data (.root 0) 3)=0 := by
  change Evm.WordStore.write target.store (.data (.root 0) 0) 17 (.data (.root 0) 3)=_
  rw [Evm.WordStore.write_other _ _ (by intro impossible; cases impossible)]
  rfl
 have o7 : badPayloadTarget.store (.data (.root 1) 0)=7 := by
  change Evm.WordStore.write target.store (.data (.root 0) 0) 17 (.data (.root 1) 0)=_
  rw [Evm.WordStore.write_other _ _ (by intro impossible; cases impossible)]
  rfl
 have o8 : badPayloadTarget.store (.data (.root 1) 1)=bits neg1 := by
  change Evm.WordStore.write target.store (.data (.root 0) 0) 17 (.data (.root 1) 1)=_
  rw [Evm.WordStore.write_other _ _ (by intro impossible; cases impossible)]
  rfl
 have o9 : badPayloadTarget.store (.data (.root 1) 2)=bits neg23 := by
  change Evm.WordStore.write target.store (.data (.root 0) 0) 17 (.data (.root 1) 2)=_
  rw [Evm.WordStore.write_other _ _ (by intro impossible; cases impossible)]
  rfl
 have o10 : badPayloadTarget.store (.data (.root 1) 3)=bits neg71 := by
  change Evm.WordStore.write target.store (.data (.root 0) 0) 17 (.data (.root 1) 3)=_
  rw [Evm.WordStore.write_other _ _ (by intro impossible; cases impossible)]
  rfl
 have h0 : badPayloadResult.store (.root 0)=2 := by
  change (TargetArrayCopyTail.afterCopy badPayloadTarget badPayloadTarget.stack (.root 0) (.root 1)).store (.root 0)=_
  rw [TargetArrayCopyTail.after_outside _ _ _ _ _ (by intro impossible; cases impossible) (by intro j member impossible; cases impossible),o0]
 have h1 : badPayloadResult.store (.root 1)=2 := by
  change (TargetArrayCopyTail.afterCopy badPayloadTarget badPayloadTarget.stack (.root 0) (.root 1)).store (.root 1)=_
  rw [TargetArrayCopyTail.after_header,o0]
 have h2 : badPayloadResult.store (.root 2)=99 := by
  change (TargetArrayCopyTail.afterCopy badPayloadTarget badPayloadTarget.stack (.root 0) (.root 1)).store (.root 2)=_
  rw [TargetArrayCopyTail.after_outside _ _ _ _ _ (by intro impossible; cases impossible) (by intro j member impossible; cases impossible),o2]
 have h3 : badPayloadResult.store (.data (.root 0) 0)=17 := by
  change (TargetArrayCopyTail.afterCopy badPayloadTarget badPayloadTarget.stack (.root 0) (.root 1)).store (.data (.root 0) 0)=_
  rw [TargetArrayCopyTail.after_outside _ _ _ _ _ (by intro impossible; cases impossible) (by intro j member impossible; cases impossible),o3]
 have h4 : badPayloadResult.store (.data (.root 0) 1)=0 := by
  change (TargetArrayCopyTail.afterCopy badPayloadTarget badPayloadTarget.stack (.root 0) (.root 1)).store (.data (.root 0) 1)=_
  rw [TargetArrayCopyTail.after_outside _ _ _ _ _ (by intro impossible; cases impossible) (by intro j member impossible; cases impossible),o4]
 have h5 : badPayloadResult.store (.data (.root 0) 2)=bits neg31 := by
  change (TargetArrayCopyTail.afterCopy badPayloadTarget badPayloadTarget.stack (.root 0) (.root 1)).store (.data (.root 0) 2)=_
  rw [TargetArrayCopyTail.after_outside _ _ _ _ _ (by intro impossible; cases impossible) (by intro j member impossible; cases impossible),o5]
 have h6 : badPayloadResult.store (.data (.root 0) 3)=0 := by
  change (TargetArrayCopyTail.afterCopy badPayloadTarget badPayloadTarget.stack (.root 0) (.root 1)).store (.data (.root 0) 3)=_
  rw [TargetArrayCopyTail.after_outside _ _ _ _ _ (by intro impossible; cases impossible) (by intro j member impossible; cases impossible),o6]
 have h7 : badPayloadResult.store (.data (.root 1) 0)=17 := by
  change (TargetArrayCopyTail.afterCopy badPayloadTarget badPayloadTarget.stack (.root 0) (.root 1)).store (.data (.root 1) 0)=_
  rw [TargetArrayCopyTail.after_data,o0,o1,o3,o7]
  rfl
 have h8 : badPayloadResult.store (.data (.root 1) 1)=0 := by
  change (TargetArrayCopyTail.afterCopy badPayloadTarget badPayloadTarget.stack (.root 0) (.root 1)).store (.data (.root 1) 1)=_
  rw [TargetArrayCopyTail.after_data,o0,o1,o4,o8]
  rfl
 have h9 : badPayloadResult.store (.data (.root 1) 2)=0 := by
  change (TargetArrayCopyTail.afterCopy badPayloadTarget badPayloadTarget.stack (.root 0) (.root 1)).store (.data (.root 1) 2)=_
  rw [TargetArrayCopyTail.after_data,o0,o1,o5,o9]
  rfl
 have h10 : badPayloadResult.store (.data (.root 1) 3)=bits neg71 := by
  change (TargetArrayCopyTail.afterCopy badPayloadTarget badPayloadTarget.stack (.root 0) (.root 1)).store (.data (.root 1) 3)=_
  rw [TargetArrayCopyTail.after_data,o0,o1,o6,o10]
  rfl
 unfold targetView targetSlots
 simp only [List.map_cons,List.map_nil]
 rw [h0,h1,h2,h3,h4,h5,h6,h7,h8,h9,h10]

theorem varied_ordered :
 (sourceView grown.2.2.ex,targetView grownTarget,sourceView emptyInitial.2.ex,sourceView emptied.2.2.ex,targetView emptyTargetResult,
 grown.2.2.ex.journal.length,emptied.2.2.ex.journal.length)=
 ([some 3,some 7,some (bits neg1),some (bits neg23),some 3,some 7,some (bits neg1),some (bits neg23),some (bits neg71),some 1,some 99,none,some 5],
 [3,3,99,7,bits neg1,bits neg23,0,7,bits neg1,bits neg23,bits neg71],
 [some 0,some (bits neg17),some 0,some (bits neg31),some 3,some 7,some (bits neg1),some (bits neg23),some (bits neg71),some 1,some 99,none,some 5],
 [some 0,some (bits neg17),some 0,some (bits neg31),some 0,some 0,some 0,some 0,some (bits neg71),some 1,some 99,none,some 5],
 [0,0,99,bits neg17,0,bits neg31,0,0,0,0,bits neg71],4,5) := by
 apply Prod.ext
 · exact grown_source_view
 apply Prod.ext
 · exact grown_target_view
 apply Prod.ext
 · exact empty_source_view
 apply Prod.ext
 · exact emptied_source_view
 apply Prod.ext
 · exact empty_target_view
 rfl

/-- Correct target code cannot preserve an initially FALSE Source/target
relation. Both missing OLD agreements are independently discriminated. -/
theorem bad_old_agreements :
 Evm.run TargetArrayCopy.code {badOlderTarget with stack:=.slot (.root 0) :: .slot (.root 1) :: badOlderTarget.stack}=.ok badOlderResult 0 ∧
 Evm.run TargetArrayCopy.code {badPayloadTarget with stack:=.slot (.root 0) :: .slot (.root 1) :: badPayloadTarget.stack}=.ok badPayloadResult 0 ∧
 (sourceView copied.2.2.ex,targetView badOlderResult,targetView badPayloadResult)=
 ([some 2,some (bits neg17),some 0,some (bits neg31),some 2,some (bits neg17),some 0,some 0,some (bits neg71),some 1,some 99,none,some 5],
 [2,2,99,bits neg17,0,bits neg31,0,bits neg17,0,0,71],[2,2,99,17,0,bits neg31,0,17,0,0,bits neg71]) ∧
 wordAt frame state.ex (elem right 3)≠some (badOlderTarget.store (.data (.root 1) 3)) ∧
 (payload 0).word.map Fin.val≠some (badPayloadTarget.store (.data (.root 0) 0)) ∧
 wordAt frame copied.2.2.ex (elem right 3)≠some (badOlderResult.store (.data (.root 1) 3)) ∧
 wordAt frame copied.2.2.ex (elem right 0)≠some (badPayloadResult.store (.data (.root 1) 0)) := by
 have older : badOlderTarget.store (.data (.root 1) 3)=71 := Evm.WordStore.write_same_of_lt _ _ _ (by decide)
 have payloadBad : badPayloadTarget.store (.data (.root 0) 0)=17 := Evm.WordStore.write_same_of_lt _ _ _ (by decide)
 have olderAfter : badOlderResult.store (.data (.root 1) 3)=71 := by
  have observed := congrArg (fun xs : List Nat => xs[10]!) bad_older_view
  exact observed
 have payloadAfter : badPayloadResult.store (.data (.root 1) 0)=17 := by
  have observed := congrArg (fun xs : List Nat => xs[7]!) bad_payload_view
  exact observed
 refine ⟨TargetArrayCopyTail.run_current _ _ _ _,TargetArrayCopyTail.run_current _ _ _ _,
  Prod.ext copied_source_view (Prod.ext bad_older_view bad_payload_view),?_,?_,?_,?_⟩
 · rw [source_word state.ex (elem right 3) neg71 rfl rfl,older]
   intro equal
   have value := Option.some.inj equal
   rw [neg71_bits] at value
   omega
 · change (sourceValue (D:=env.layout) neg17).word.map Fin.val≠some _
   rw [word_agrees,payloadBad]
   intro equal
   have value := Option.some.inj equal
   change bits neg17=17 at value
   rw [neg17_bits] at value
   omega
 · rw [source_word copied.2.2.ex (elem right 3) neg71 rfl rfl,olderAfter]
   intro equal
   have value := Option.some.inj equal
   rw [neg71_bits] at value
   omega
 · rw [source_word copied.2.2.ex (elem right 0) neg17 rfl rfl,payloadAfter]
   intro equal
   have value := Option.some.inj equal
   rw [neg17_bits] at value
   omega

theorem readbacks :
 (Source.readAt (E:=env) (Γ:=[]) frame right (.int Source.IntTy.u256)).run copied.2=(.ok (.int 2 (by decide)),copied.2) ∧
 (Source.readAt (E:=env) (Γ:=[]) frame (elem right 0) (.int int256)).run copied.2=(.ok (sourceValue neg17),copied.2) ∧
 (Source.readAt (E:=env) (Γ:=[]) frame (elem right 2) (.int int256)).run copied.2=(.ok (sourceValue zeroInt),copied.2) ∧
 Evm.run (TargetOperations.readCode (.root 1)) targetResult=.ok {targetResult with stack:=.val ⟨2,by decide⟩ :: targetResult.stack} 0 ∧
 Evm.run (TargetOperations.readCode (.data (.root 1) 0)) targetResult=.ok {targetResult with stack:=.val (TargetOperations.encodeWord (sw neg17)) :: targetResult.stack} 0 ∧
 Evm.run (TargetOperations.readCode (.data (.root 1) 2)) targetResult=.ok {targetResult with stack:=.val ⟨0,by decide⟩ :: targetResult.stack} 0 ∧
 Evm.run (TargetOperations.readCode (.data (.root 1) 3)) targetResult=.ok {targetResult with stack:=.val (TargetOperations.encodeWord (sw neg71)) :: targetResult.stack} 0 := by
 refine ⟨rfl,rfl,rfl,?_,?_,?_,?_⟩
 · have cell : targetResult.store.cells (.root 1)=⟨2,by decide⟩ := Fin.ext target_header
   rw [TargetOperations.run_read,cell]
 · have cell : targetResult.store.cells (.data (.root 1) 0)=TargetOperations.encodeWord (sw neg17) := by
    apply Fin.ext
    change targetResult.store (.data (.root 1) 0)=bits neg17
    rw [target_child 0]
    rfl
   rw [TargetOperations.run_read,cell]
 · have cell : targetResult.store.cells (.data (.root 1) 2)=⟨0,by decide⟩ := by
    apply Fin.ext
    change targetResult.store (.data (.root 1) 2)=0
    rw [target_child 2]
    rfl
   rw [TargetOperations.run_read,cell]
 · have cell : targetResult.store.cells (.data (.root 1) 3)=TargetOperations.encodeWord (sw neg71) := by
    apply Fin.ext
    change targetResult.store (.data (.root 1) 3)=bits neg71
    rw [target_child 3]
    rfl
   rw [TargetOperations.run_read,cell]

/-- The public encoding bridge covers all signed values; this control
uses negative data/shadows, absent zero and incorrect absolute-value encodings. -/
theorem signed_words_presence :
 (sourceValue (D:=env.layout) neg17).word.map Fin.val=some (bits neg17) ∧
 (sourceValue (D:=env.layout) neg71).word.map Fin.val=some (bits neg71) ∧
 bits neg17=2^256-17 ∧ bits neg71=2^256-71 ∧
 (state.ex.world.accounts address).storage.cell (elem left 1)=none ∧
 (Source.readAt (E:=env) (Γ:=[]) frame (elem left 1) (.int int256)).run initial=(.ok (sourceValue zeroInt),initial) ∧
 (copied.2.2.ex.world.accounts address).storage.cell (elem right 1)=some (sourceValue zeroInt) ∧
 (copied.2.2.ex.world.accounts address).storage.cell (elem right 2)=none ∧
 (Source.readAt (E:=env) (Γ:=[]) frame (elem right 3) (.int int256)).run copied.2=(.ok (sourceValue neg71),copied.2) := by
 exact ⟨word_agrees neg17,word_agrees neg71,neg17_bits,neg71_bits,rfl,rfl,rfl,rfl,rfl⟩

/-- info: 'Solidity.Backend.StorageOps.SourceSignedStorageCopyTarget.Controls.certificate' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in #print axioms certificate
/-- info: 'Solidity.Backend.StorageOps.SourceSignedStorageCopyTarget.Controls.ordered' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in #print axioms ordered
/-- info: 'Solidity.Backend.StorageOps.SourceSignedStorageCopyTarget.Controls.full_target_context' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in #print axioms full_target_context
/-- info: 'Solidity.Backend.StorageOps.SourceSignedStorageCopyTarget.Controls.grow_certificate' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in #print axioms grow_certificate
/-- info: 'Solidity.Backend.StorageOps.SourceSignedStorageCopyTarget.Controls.empty_certificate' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in #print axioms empty_certificate
/-- info: 'Solidity.Backend.StorageOps.SourceSignedStorageCopyTarget.Controls.varied_ordered' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in #print axioms varied_ordered
/-- info: 'Solidity.Backend.StorageOps.SourceSignedStorageCopyTarget.Controls.bad_old_agreements' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in #print axioms bad_old_agreements
/-- info: 'Solidity.Backend.StorageOps.SourceSignedStorageCopyTarget.Controls.readbacks' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in #print axioms readbacks
/-- info: 'Solidity.Backend.StorageOps.SourceSignedStorageCopyTarget.Controls.signed_words_presence' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in #print axioms signed_words_presence
end Solidity.Backend.StorageOps.SourceSignedStorageCopyTarget.Controls
