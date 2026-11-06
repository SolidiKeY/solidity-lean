import Solidity.Lowering.StorageOps.SourceTwoArrayDeleteNumeric

/-! Concrete independently evaluated Source input, two PUBLIC represented
regions, actual numeric/current-header target executions and discriminating
OLD-input disagreement. This is a captured-operation client, not AST lowering. -/
namespace Solidity.Backend.StorageOps.SourceTwoArrayDeleteNumeric.Controls
open TypeGraph Solidity.Storage Solidity.Storage.Representation Solidity.Storage.Representation.Graph
open SourceArrayDeleteTarget
open TwoClearRepresentation
private def graph : Schema 0 where
  origin := "v10-source-array-delete-numeric"
  declId := fun i => nomatch i
  declId_injective := by intro i; exact Fin.elim0 i
  name := fun i => nomatch i
  fields := fun i => nomatch i
  rank := fun i => nomatch i
  nonempty := by intro i; exact Fin.elim0 i
  distinct := by intro i; exact Fin.elim0 i
  guarded := by intro i; exact Fin.elim0 i
private def w0 : Semantics.Word := ⟨0,by decide⟩
private def w2 : Semantics.Word := ⟨2,by decide⟩
private def w3 : Semantics.Word := ⟨3,by decide⟩
private def w7 : Semantics.Word := ⟨7,by decide⟩
private def w17 : Semantics.Word := ⟨17,by decide⟩
private def w23 : Semantics.Word := ⟨23,by decide⟩
private def w53 : Semantics.Word := ⟨53,by decide⟩
private def w59 : Semantics.Word := ⟨59,by decide⟩
private def w61 : Semantics.Word := ⟨61,by decide⟩
private def w71 : Semantics.Word := ⟨71,by decide⟩
private def w87 : Semantics.Word := ⟨87,by decide⟩
private def w93 : Semantics.Word := ⟨93,by decide⟩
private def w99 : Semantics.Word := ⟨99,by decide⟩
private def ix (i : Fin 5) : Index := ⟨i.val,by have bound := i.isLt; omega⟩
private def leftIndices : List Index := [ix 2,ix 0,ix 1,ix 2]
private def rightIndices : List Index := [ix 3,ix 1,ix 0,ix 2,ix 3]
private def left : Value graph (.array (.prim .uint)) :=
 .array ⟨3,by decide⟩ ⟨2,by decide⟩ (by decide)
 (fun i => .present (.prim (if i.val = 0 then w53 else if i.val = 1 then w59 else w61)))
private def right : Value graph (.array (.prim .uint)) :=
 .array ⟨4,by decide⟩ ⟨3,by decide⟩ (by decide)
 (fun i => .present (.prim (if i.val = 0 then w7 else if i.val = 1 then w17 else if i.val = 2 then w23 else w71)))
private def leftBase : Solidity.Storage.Loc := .root 0
private def rightBase : Solidity.Storage.Loc := .root 1
private def hash (p : Solidity.Storage.Pre) : Nat := if p = .data 0 then 4 else if p = .data 1 then 8 else 0
private def preimages : List Solidity.Storage.Pre := [.data 0,.data 1]
private def locations : List Solidity.Storage.Loc := [leftBase,.data leftBase 0,.data leftBase 1,.data leftBase 2,
 rightBase,.data rightBase 0,.data rightBase 1,.data rightBase 2,.data rightBase 3]
private def store : Store := fun l =>
 if l = leftBase then w2 else if l = .data leftBase 0 then w53 else if l = .data leftBase 1 then w59 else
 if l = .data leftBase 2 then w61 else if l = rightBase then w3 else if l = .data rightBase 0 then w7 else
 if l = .data rightBase 1 then w17 else if l = .data rightBase 2 then w23 else if l = .data rightBase 3 then w71 else
 if l = .root 2 then w99 else if l = .root 15 then w87 else w93
private def numeric : WordStore := fun a =>
 if a = 0 then w2 else if a = 4 then w53 else if a = 5 then w59 else if a = 6 then w61 else
 if a = 1 then w3 else if a = 8 then w7 else if a = 9 then w17 else if a = 10 then w23 else if a = 11 then w71 else
 if a = 2 then w99 else if a = 15 then w87 else w93
private def targetStore : Evm.WordStore := .ofFn fun s =>
 if s = .root 0 then 2 else if s = .data (.root 0) 0 then 53 else if s = .data (.root 0) 1 then 59 else
 if s = .data (.root 0) 2 then 61 else if s = .root 1 then 3 else if s = .data (.root 1) 0 then 7 else
 if s = .data (.root 1) 1 then 17 else if s = .data (.root 1) 2 then 23 else if s = .data (.root 1) 3 then 71 else
 if s = .root 2 then 99 else if s = .root 15 then 87 else 93
private def tail : List Evm.Word := [.val ⟨23,by decide⟩,.slot (.root 15)]
private def target : Evm.Machine :=
 {stack := tail,store := targetStore,mem := fun _ => .val ⟨31,by decide⟩,
  bal := fun _ => 19,bal₀ := fun _ => 19,self := ⟨7,by decide⟩,caller := ⟨13,by decide⟩,
  callvalue := ⟨0,by decide⟩,timestamp := ⟨53,by decide⟩,accepts := fun _ _ => false}
private def storeOut := afterStore left right leftBase rightBase store
private def numericOut := execute 16 hash leftBase rightBase numeric
private def targetOut := TargetArrayDeleteSequence.after target tail (.root 0) (.root 1)
private theorem run : FiniteRun 16 4 2 hash preimages locations := by
 constructor
 · intro p; simp only [hash]; split <;> (try split) <;> decide
 · decide
 · decide
 · decide
 · intro l member
   simp only [locations,List.mem_cons,List.not_mem_nil,or_false] at member
   rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
     simp only [leftBase,rightBase,Solidity.Storage.Loc.Bounded] <;> decide
 · intro l member
   simp only [locations,List.mem_cons,List.not_mem_nil,or_false] at member
   rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> decide
private theorem initialTransport : Transport 16 hash locations store numeric := by
 intro l member
 simp only [locations,List.mem_cons,List.not_mem_nil,or_false] at member
 rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> rfl
private theorem leftFull : Represented left (PrimitivePop.queries leftIndices) leftBase store := by
 intro query member
 simp only [PrimitivePop.queries,leftIndices,List.map_cons,List.map_nil,List.mem_cons,List.not_mem_nil,or_false] at member
 rcases member with rfl | rfl | rfl | rfl | rfl
 · refine ⟨True.intro,⟨by decide,by decide⟩,?_⟩
   intro word found
   change some w2 = some word at found
   cases found
   rfl
 · refine ⟨⟨by change 2 < lmax; decide,True.intro⟩,True.intro,?_⟩
   intro word found
   change some w61 = some word at found
   cases found
   rw [PrimitivePop.element_location]
   rfl
 · refine ⟨⟨by change 0 < lmax; decide,True.intro⟩,True.intro,?_⟩
   intro word found
   change some w53 = some word at found
   cases found
   rw [PrimitivePop.element_location]
   rfl
 · refine ⟨⟨by change 1 < lmax; decide,True.intro⟩,True.intro,?_⟩
   intro word found
   change some w59 = some word at found
   cases found
   rw [PrimitivePop.element_location]
   rfl
 · refine ⟨⟨by change 2 < lmax; decide,True.intro⟩,True.intro,?_⟩
   intro word found
   change some w61 = some word at found
   cases found
   rw [PrimitivePop.element_location]
   rfl
private theorem leftBefore : Represented left (TargetClearRepresentation.oldQueries left leftIndices) leftBase store := by
 intro query member
 apply leftFull query
 simp only [TargetClearRepresentation.oldQueries,PrimitivePop.queries,List.mem_cons,List.mem_map] at member
 rcases member with rfl | ⟨i,inside,rfl⟩
 · exact List.mem_cons_self
 · exact List.mem_cons_of_mem _ (List.mem_map.mpr ⟨i,(List.mem_filter.mp inside).1,rfl⟩)
private theorem leftCovered : ∀ query ∈ PrimitivePop.queries (G := graph) (p := .uint) leftIndices, query.location leftBase ∈ locations := by
 intro query member
 simp only [PrimitivePop.queries,leftIndices,List.map_cons,List.map_nil,List.mem_cons,List.not_mem_nil,or_false] at member
 rcases member with rfl | rfl | rfl | rfl | rfl <;>
   (try rw [PrimitivePop.element_location]) <;> decide
private theorem rightFull : Represented right (PrimitivePop.queries rightIndices) rightBase store := by
 intro query member
 simp only [PrimitivePop.queries,rightIndices,List.map_cons,List.map_nil,List.mem_cons,List.not_mem_nil,or_false] at member
 rcases member with rfl | rfl | rfl | rfl | rfl | rfl
 · refine ⟨True.intro,⟨by decide,by decide⟩,?_⟩
   intro word found
   change some w3 = some word at found
   cases found
   rfl
 · refine ⟨⟨by change 3 < lmax; decide,True.intro⟩,True.intro,?_⟩
   intro word found
   change some w71 = some word at found
   cases found
   rw [PrimitivePop.element_location]
   rfl
 · refine ⟨⟨by change 1 < lmax; decide,True.intro⟩,True.intro,?_⟩
   intro word found
   change some w17 = some word at found
   cases found
   rw [PrimitivePop.element_location]
   rfl
 · refine ⟨⟨by change 0 < lmax; decide,True.intro⟩,True.intro,?_⟩
   intro word found
   change some w7 = some word at found
   cases found
   rw [PrimitivePop.element_location]
   rfl
 · refine ⟨⟨by change 2 < lmax; decide,True.intro⟩,True.intro,?_⟩
   intro word found
   change some w23 = some word at found
   cases found
   rw [PrimitivePop.element_location]
   rfl
 · refine ⟨⟨by change 3 < lmax; decide,True.intro⟩,True.intro,?_⟩
   intro word found
   change some w71 = some word at found
   cases found
   rw [PrimitivePop.element_location]
   rfl
private theorem rightBefore : Represented right (TargetClearRepresentation.oldQueries right rightIndices) rightBase store := by
 intro query member
 apply rightFull query
 simp only [TargetClearRepresentation.oldQueries,PrimitivePop.queries,List.mem_cons,List.mem_map] at member
 rcases member with rfl | ⟨i,inside,rfl⟩
 · exact List.mem_cons_self
 · exact List.mem_cons_of_mem _ (List.mem_map.mpr ⟨i,(List.mem_filter.mp inside).1,rfl⟩)
private theorem rightCovered : ∀ query ∈ PrimitivePop.queries (G := graph) (p := .uint) rightIndices, query.location rightBase ∈ locations := by
 intro query member
 simp only [PrimitivePop.queries,rightIndices,List.map_cons,List.map_nil,List.mem_cons,List.not_mem_nil,or_false] at member
 rcases member with rfl | rfl | rfl | rfl | rfl | rfl <;>
   (try rw [PrimitivePop.element_location]) <;> decide
private theorem leftVisited : ∀ j, j < left.length.val → Solidity.Storage.Loc.data leftBase j ∈ locations := by
 intro j inside
 change j < 2 at inside
 have cases : j = 0 ∨ j = 1 := by omega
 rcases cases with rfl | rfl <;> decide
private theorem rightVisited : ∀ j, j < right.length.val → Solidity.Storage.Loc.data rightBase j ∈ locations := by
 intro j inside
 change j < 3 at inside
 have cases : j = 0 ∨ j = 1 ∨ j = 2 := by omega
 rcases cases with rfl | rfl | rfl <;> decide
private theorem rightFrame : ∀ query ∈ TargetClearRepresentation.oldQueries right rightIndices,
 query.location rightBase ≠ leftBase ∧ ∀ j, j < left.length.val → query.location rightBase ≠ .data leftBase j := by
 intro query member
 change query ∈ [.length .nil,PrimitivePop.elementQuery (ix 3),PrimitivePop.elementQuery (ix 3)] at member
 simp only [List.mem_cons,List.not_mem_nil,or_false] at member
 rcases member with rfl | rfl | rfl <;> constructor
 all_goals try decide
 all_goals intro j _; intro same; cases same
private theorem leftFrame : ∀ query ∈ PrimitivePop.queries (G := graph) (p := .uint) leftIndices,
 query.location leftBase ≠ rightBase ∧ ∀ j, j < right.length.val → query.location leftBase ≠ .data rightBase j := by
 intro query member
 simp only [PrimitivePop.queries,leftIndices,List.map_cons,List.map_nil,List.mem_cons,List.not_mem_nil,or_false] at member
 rcases member with rfl | rfl | rfl | rfl | rfl <;> constructor
 all_goals try decide
 all_goals intro j _; intro same; cases same
private theorem fitting : ∀ l ∈ locations, TargetOperations.KeysFit l := by
 intro l member
 simp only [locations,List.mem_cons,List.not_mem_nil,or_false] at member
 rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> trivial
private theorem targetInitial : ∀ l (member : l ∈ locations), target.store.cells (TargetOperations.toSlot l (fitting l member)) = TargetOperations.encodeWord (store l) := by
 intro l member
 simp only [locations,List.mem_cons,List.not_mem_nil,or_false] at member
 rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> rfl

private def uintSyntax : Source.Syn .typeName := .elem (.int false 256 (by decide))
private def unit : Source.Syn .unit := .unit (.cons (.contract false "C" .none .nil
  (.cons (.stateVar (.array uintSyntax .none) none none none false "leftPath" .none)
    (.cons (.stateVar (.array uintSyntax .none) none none none false "rightPath" .none)
      (.cons (.stateVar (.elem .bool) none none none false "bad" .none)
        (.cons (.stateVar uintSyntax none none none true "scratch" .none)
          (.cons (.stateVar uintSyntax none none none false "sentinel" .none) .nil)))))) .nil)
private def sourceEnv : Source.Env := unit.env
private def leftPath : Source.SPath := ⟨⟨some "C","leftPath"⟩,[]⟩
private def rightPath : Source.SPath := ⟨⟨some "C","rightPath"⟩,[]⟩
private def bad : Source.SPath := ⟨⟨some "C","bad"⟩,[]⟩
private def scratch : Source.SPath := ⟨⟨some "C","scratch"⟩,[]⟩
private def sentinel : Source.SPath := ⟨⟨some "C","sentinel"⟩,[]⟩
private def missing : Source.SPath := ⟨⟨some "C","missing"⟩,[]⟩
private def elem (p : Source.SPath) (i : Nat) : Source.SPath := p.go (.index i)
private def address : Roadmap.Address := ⟨7,by decide⟩
private def sourceStorage : Source.Storage sourceEnv.layout sourceEnv.cellTy :=
  let s := (Source.Storage.empty : Source.Storage sourceEnv.layout sourceEnv.cellTy).write leftPath (.int 2 (by decide))
  let s := s.write (elem leftPath 0) (.int 53 (by decide))
  let s := s.write (elem leftPath 1) (.int 59 (by decide))
  let s := s.write (elem leftPath 2) (.int 61 (by decide))
  let s := s.write rightPath (.int 3 (by decide))
  let s := s.write (elem rightPath 0) (.int 7 (by decide))
  let s := s.write (elem rightPath 1) (.int 17 (by decide))
  let s := s.write (elem rightPath 2) (.int 23 (by decide))
  let s := s.write (elem rightPath 3) (.int 71 (by decide))
  let s := s.write bad (.bool true)
  s.write sentinel (.int 99 (by decide))
private def sourceState : Source.St sourceEnv :=
  { ex :=
      { world := ⟨fun a => if a = address then
          { balance := ⟨19,by decide⟩, nonce := 3, code := some 0, storage := sourceStorage }
          else Source.Account.empty _⟩
        transient := Source.Transient.empty.set address
          ((Source.Storage.empty : Source.Storage sourceEnv.layout sourceEnv.cellTy).write scratch (.int 5 (by decide)))
        journal := [] }
    heap := Source.Heap.empty
    events := []
    logs := []
    fnLocals := ⟨[],.nil⟩ }
private def sourceFrame : Source.Fr :=
  {this := address,sender := ⟨13,by decide⟩,value := ⟨0,by decide⟩,static := false,contract := "C"}
private def sourceInitial : Source.Locals sourceEnv.layout [] × Source.St sourceEnv := (.nil,sourceState)
private def sourceOut := (SourceTwoArrayDeletes.program (E := sourceEnv) (Γ := []) sourceFrame Source.IntTy.u256 Source.IntTy.u256 leftPath rightPath 2 3).run sourceInitial

private theorem leftRootApart : leftPath.root ≠ rightPath.root := by decide
private theorem rightRootApart : rightPath.root ≠ leftPath.root := Ne.symm leftRootApart
private theorem sourceHeaders : rightPath ≠ leftPath := by
 intro same
 have roots := congrArg Source.SPath.root same; exact rightRootApart roots
private theorem sourceLeftData : ∀ j ∈ List.range' 0 left.length.val, rightPath ≠ leftPath.go (.index j) := by
 intro j _ same
 have roots := congrArg Source.SPath.root same; exact rightRootApart roots
private theorem sourceRightData : ∀ j ∈ List.range' 0 right.length.val, leftPath ≠ rightPath.go (.index j) := by
 intro j _ same
 have roots := congrArg Source.SPath.root same; exact leftRootApart roots
private theorem sourceLeftFrame : ∀ i ∈ leftIndices, leftPath.go (.index i.val) ≠ rightPath ∧
 ∀ j ∈ List.range' 0 right.length.val, leftPath.go (.index i.val) ≠ rightPath.go (.index j) := by
 intro i _
 constructor
 · intro same; have roots := congrArg Source.SPath.root same; exact leftRootApart roots
 · intro j _ same; have roots := congrArg Source.SPath.root same; exact leftRootApart roots
private theorem sourceRightFrame : ∀ i ∈ rightIndices, right.length.val ≤ i.val → rightPath.go (.index i.val) ≠ leftPath ∧
 ∀ j ∈ List.range' 0 left.length.val, rightPath.go (.index i.val) ≠ leftPath.go (.index j) := by
 intro i _ _
 constructor
 · intro same; have roots := congrArg Source.SPath.root same; exact rightRootApart roots
 · intro j _ same; have roots := congrArg Source.SPath.root same; exact rightRootApart roots
private theorem sourceLeftOld : ∀ i ∈ leftIndices, left.length.val ≤ i.val →
 wordAt sourceFrame sourceState.ex (leftPath.go (.index i.val)) = some (TargetOperations.encodeWord (store (.data leftBase i.val))).val := by
 intro i member unvisited
 simp only [leftIndices,List.mem_cons,List.not_mem_nil,or_false] at member
 rcases member with rfl | rfl | rfl | rfl
 · rfl
 · change 2 ≤ 0 at unvisited; omega
 · change 2 ≤ 1 at unvisited; omega
 · rfl
private theorem sourceRightOld : ∀ i ∈ rightIndices, right.length.val ≤ i.val →
 wordAt sourceFrame sourceState.ex (rightPath.go (.index i.val)) = some (TargetOperations.encodeWord (store (.data rightBase i.val))).val := by
 intro i member unvisited
 simp only [rightIndices,List.mem_cons,List.not_mem_nil,or_false] at member
 rcases member with rfl | rfl | rfl | rfl | rfl
 · rfl
 · change 3 ≤ 1 at unvisited; omega
 · change 3 ≤ 0 at unvisited; omega
 · change 3 ≤ 2 at unvisited; omega
 · rfl

/-- The actual full C95 certificate is instantiated with no unproved input. -/
theorem numeric_bridge :
    let finalStore := TwoClearRepresentation.afterStore left right leftBase rightBase store
    let finalNumeric := TwoClearRepresentation.execute 16 hash leftBase rightBase numeric
    let finalTarget := TargetArrayDeleteSequence.after target tail
      (TargetOperations.toSlot leftBase True.intro) (TargetOperations.toSlot rightBase True.intro)
    let sourceResult := (SourceTwoArrayDeletes.program sourceFrame Source.IntTy.u256 Source.IntTy.u256
      leftPath rightPath left.length.val right.length.val).run (.nil,sourceState)
    (Evm.run (TargetArrayDeleteSequence.code (TargetOperations.toSlot rightBase True.intro))
      {target with stack := .slot (TargetOperations.toSlot leftBase True.intro) :: tail} = .ok finalTarget 0 ∧
    Represented left.clear (PrimitivePop.queries leftIndices) leftBase finalStore ∧
    Represented right.clear (PrimitivePop.queries rightIndices) rightBase finalStore ∧
    Transport 16 hash locations finalStore finalNumeric ∧
    (∀ l (member : l ∈ locations), finalTarget.store.cells (TargetOperations.toSlot l (fitting l member)) =
      TargetOperations.encodeWord (finalNumeric (l.word 16 hash))) ∧
    (∀ query ∈ PrimitivePop.queries (G := graph) (p := .uint) leftIndices, ∀ word, query.read left.clear = some word →
      finalNumeric ((query.location leftBase).word 16 hash) = word) ∧
    (∀ query ∈ PrimitivePop.queries (G := graph) (p := .uint) rightIndices, ∀ word, query.read right.clear = some word →
      finalNumeric ((query.location rightBase).word 16 hash) = word)) ∧
    sourceResult = (.ok (), (.nil,{sourceState with ex := sourceState.ex.run (((List.range' 0 left.length.val).map (fun j => SourceScalarDeleteLog.clearOp sourceEnv sourceFrame (leftPath.go (.index j))) ++ [SourceScalarDeleteLog.clearOp sourceEnv sourceFrame leftPath]) ++ ((List.range' 0 right.length.val).map (fun j => SourceScalarDeleteLog.clearOp sourceEnv sourceFrame (rightPath.go (.index j))) ++ [SourceScalarDeleteLog.clearOp sourceEnv sourceFrame rightPath]))})) ∧
    wordAt sourceFrame sourceResult.2.2.ex leftPath = some (TargetOperations.encodeWord (finalNumeric (leftBase.word 16 hash))).val ∧
    wordAt sourceFrame sourceResult.2.2.ex rightPath = some (TargetOperations.encodeWord (finalNumeric (rightBase.word 16 hash))).val ∧
    (∀ i ∈ leftIndices, wordAt sourceFrame sourceResult.2.2.ex (leftPath.go (.index i.val)) =
      some (TargetOperations.encodeWord (finalNumeric ((Solidity.Storage.Loc.data leftBase i.val).word 16 hash))).val) ∧
    (∀ i ∈ rightIndices, wordAt sourceFrame sourceResult.2.2.ex (rightPath.go (.index i.val)) =
      some (TargetOperations.encodeWord (finalNumeric ((Solidity.Storage.Loc.data rightBase i.val).word 16 hash))).val) :=
 SourceTwoArrayDeleteNumeric.complete sourceFrame rfl leftPath rightPath .nil sourceState run left right leftIndices rightIndices
 leftBase rightBase True.intro True.intro store numeric target tail leftBefore rightBefore rightFrame leftFrame initialTransport
 leftCovered rightCovered leftVisited rightVisited fitting targetInitial rfl rfl rfl rfl rfl rfl
 sourceHeaders sourceLeftData sourceRightData sourceLeftFrame sourceRightFrame sourceLeftOld sourceRightOld

private def physicalView (m : WordStore) := [m 0,m 4,m 5,m 6,m 1,m 8,m 9,m 10,m 11,m 7,m 2,m 15]
private def symbolicView (m : Store) := [m leftBase,m (.data leftBase 0),m (.data leftBase 1),m (.data leftBase 2),
 m rightBase,m (.data rightBase 0),m (.data rightBase 1),m (.data rightBase 2),m (.data rightBase 3),m (.root 7),m (.root 2),m (.root 15)]
private def targetView (m : Evm.Machine) := [m.store (.root 0),m.store (.data (.root 0) 0),m.store (.data (.root 0) 1),m.store (.data (.root 0) 2),
 m.store (.root 1),m.store (.data (.root 1) 0),m.store (.data (.root 1) 1),m.store (.data (.root 1) 2),m.store (.data (.root 1) 3),m.store (.root 7),m.store (.root 2),m.store (.root 15)]
private def graphView (v : Value graph (.array (.prim .uint))) :=
 (v.length.val,v.extent.val,(PrimitivePop.elementQuery (ix 0)).read v,(PrimitivePop.elementQuery (ix 1)).read v,
  (PrimitivePop.elementQuery (ix 2)).read v,(PrimitivePop.elementQuery (ix 3)).read v,
  ((TypeGraph.Path.cons (.index (ix 0)) .nil).readLive Value.dflt v).map Value.head)
private def context (m : Evm.Machine) := (m.stack,m.mem 0,m.bal m.self,m.bal₀ m.self,m.self,m.caller,m.callvalue,m.timestamp,m.accepts m.self m.self)

theorem ordered :
 (graphView left,graphView left.clear,graphView right,graphView right.clear,
  symbolicView store,symbolicView storeOut,physicalView numeric,physicalView numericOut,
  targetView target,targetView targetOut,context targetOut) =
 ((2,3,some w53,some w59,some w61,none,some w53),(0,3,some w0,some w0,some w61,none,none),
  (3,4,some w7,some w17,some w23,some w71,some w7),(0,4,some w0,some w0,some w0,some w71,none),
  [w2,w53,w59,w61,w3,w7,w17,w23,w71,w93,w99,w87],
  [w0,w0,w0,w61,w0,w0,w0,w0,w71,w93,w99,w87],
  [w2,w53,w59,w61,w3,w7,w17,w23,w71,w93,w99,w87],
  [w0,w0,w0,w61,w0,w0,w0,w0,w71,w93,w99,w87],
  [2,53,59,61,3,7,17,23,71,93,99,87],[0,0,0,61,0,0,0,0,71,93,99,87],context target) := by rfl


private def paths := [leftPath,elem leftPath 0,elem leftPath 1,elem leftPath 2,elem leftPath 4,
 rightPath,elem rightPath 0,elem rightPath 1,elem rightPath 2,elem rightPath 3,elem rightPath 5,bad,sentinel,missing]
private def sourceView (s : Source.St sourceEnv) := paths.map (wordAt sourceFrame s.ex)
private def sourceContext (s : Source.St sourceEnv) :=
 ((s.ex.world.accounts sourceFrame.this).balance,(s.ex.world.accounts sourceFrame.this).nonce,
  (s.ex.world.accounts sourceFrame.this).code,((s.ex.transient.cells sourceFrame.this).read scratch).bind Source.Val.word,
  s.heap,s.events,s.logs,s.fnLocals)

/-- Every Source word/context and ordered journal length is pinned, alongside
ordered's complete graph/symbolic/numeric/target vectors. -/
theorem source_ordered :
 (sourceView sourceState,sourceView sourceOut.2.2,sourceOut.2.2.ex.journal.length,sourceContext sourceOut.2.2) =
 ([some 2,some 53,some 59,some 61,some 0,some 3,some 7,some 17,some 23,some 71,some 0,some 1,some 99,none],
  [some 0,some 0,some 0,some 61,some 0,some 0,some 0,some 0,some 0,some 71,some 0,some 1,some 99,none],
  7,sourceContext sourceState) := by rfl
private def wrongInput := (Source.setCell (E := sourceEnv) (Γ := []) sourceFrame (elem leftPath 2)
 (some (.int 62 (by decide)))).run sourceInitial
private def wrongSource := (SourceTwoArrayDeletes.program sourceFrame Source.IntTy.u256 Source.IntTy.u256 leftPath rightPath 2 3).run wrongInput.2

/-- Matching headers and successful operations do not supply OLD retained-word
agreement. With left retained62, actual Source keeps62 while numeric keeps61. -/
theorem wrong_retained_input :
 (sourceView wrongSource.2.2,wrongSource.2.2.ex.journal.length) =
 ([some 0,some 0,some 0,some 62,some 0,some 0,some 0,some 0,some 0,some 71,some 0,some 1,some 99,none],8) ∧
 wordAt sourceFrame wrongSource.2.2.ex (elem leftPath 2) ≠ some (TargetOperations.encodeWord (numericOut 6)).val := by
 refine ⟨rfl,?_⟩
 change some 62 ≠ some (61 : Nat)
 decide

/-- Actual defaulted Source words and unknown None remain different from raw
physical garbage, even when all selected represented observations agree. -/
theorem boundaries :
 (wordAt sourceFrame sourceOut.2.2.ex (elem leftPath 3),
  wordAt sourceFrame sourceOut.2.2.ex missing,numericOut 7,
  (PrimitivePop.elementQuery (ix 3)).read left.clear,numericOut 6,numericOut 11) =
 (some 0,none,w93,none,w61,w71) := by rfl

/-- info: 'Solidity.Backend.StorageOps.SourceTwoArrayDeleteNumeric.Controls.numeric_bridge' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in #print axioms numeric_bridge
/-- info: 'Solidity.Backend.StorageOps.SourceTwoArrayDeleteNumeric.Controls.ordered' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in #print axioms ordered
/-- info: 'Solidity.Backend.StorageOps.SourceTwoArrayDeleteNumeric.Controls.source_ordered' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in #print axioms source_ordered
/-- info: 'Solidity.Backend.StorageOps.SourceTwoArrayDeleteNumeric.Controls.wrong_retained_input' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in #print axioms wrong_retained_input
/-- info: 'Solidity.Backend.StorageOps.SourceTwoArrayDeleteNumeric.Controls.boundaries' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in #print axioms boundaries
end Solidity.Backend.StorageOps.SourceTwoArrayDeleteNumeric.Controls
