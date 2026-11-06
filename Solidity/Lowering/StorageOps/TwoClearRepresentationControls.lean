import Solidity.Backend.StorageOps.TwoClearRepresentation

/-! Inhabited two-region PUBLIC representation/numeric/target clients. Numeric
16 is an address modulus, not a Solidity payload width or source restriction. -/
namespace Solidity.Backend.StorageOps.TwoClearRepresentation.Controls
open TypeGraph Solidity.Storage Solidity.Storage.Representation Solidity.Storage.Representation.Graph
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

theorem bridge :
 Evm.run (TargetArrayDeleteSequence.code (.root 1)) {target with stack := .slot (.root 0) :: tail} = .ok targetOut 0 ∧
 Represented left.clear (PrimitivePop.queries leftIndices) leftBase storeOut ∧
 Represented right.clear (PrimitivePop.queries rightIndices) rightBase storeOut ∧
 Transport 16 hash locations storeOut numericOut ∧
 (∀ l (member : l ∈ locations), targetOut.store.cells (TargetOperations.toSlot l (fitting l member)) =
   TargetOperations.encodeWord (numericOut (l.word 16 hash))) ∧
 (∀ query ∈ PrimitivePop.queries (G := graph) (p := .uint) leftIndices, ∀ word, query.read left.clear = some word → numericOut ((query.location leftBase).word 16 hash) = word) ∧
 (∀ query ∈ PrimitivePop.queries (G := graph) (p := .uint) rightIndices, ∀ word, query.read right.clear = some word → numericOut ((query.location rightBase).word 16 hash) = word) :=
 complete run left right leftIndices rightIndices leftBase rightBase True.intro True.intro
 store numeric target tail leftBefore rightBefore rightFrame leftFrame initialTransport
 leftCovered rightCovered leftVisited rightVisited fitting targetInitial

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

/-- Every address in this ordered set is outside BOTH actual live writes;
6 and11 are retained tails,7 is unrepresented raw garbage,2/15 are sentinels. -/
theorem physical_frames : ∀ address ∈ [6,11,7,2,15], numericOut address = numeric address := by
 intro address member
 have leftHeader : Represented left [.length .nil] leftBase store := by
  intro query inside
  have same := List.mem_singleton.mp inside
  subst query
  exact leftFull _ List.mem_cons_self
 have rightHeader : Represented right [.length .nil] rightBase store := by
  intro query inside
  have same := List.mem_singleton.mp inside
  subst query
  exact rightFull _ List.mem_cons_self
 apply physical_frame run left right leftBase rightBase store numeric leftHeader rightHeader
   ⟨by decide,by intro j _; intro same; cases same⟩ initialTransport
   (by decide) (by decide) leftVisited address
 · simp only [List.mem_cons,List.not_mem_nil,or_false] at member
   rcases member with rfl | rfl | rfl | rfl | rfl <;> decide
 · intro j inside
   change j < 2 at inside
   have cases : j = 0 ∨ j = 1 := by omega
   simp only [List.mem_cons,List.not_mem_nil,or_false] at member
   rcases cases with rfl | rfl <;> rcases member with rfl | rfl | rfl | rfl | rfl <;> decide
 · simp only [List.mem_cons,List.not_mem_nil,or_false] at member
   rcases member with rfl | rfl | rfl | rfl | rfl <;> decide
 · intro j inside
   change j < 3 at inside
   have cases : j = 0 ∨ j = 1 ∨ j = 2 := by omega
   simp only [List.mem_cons,List.not_mem_nil,or_false] at member
   rcases cases with rfl | rfl | rfl <;> rcases member with rfl | rfl | rfl | rfl | rfl <;> decide

private def wrongNumeric := execute 16 hash leftBase rightBase (writeWord numeric 1 ⟨4,by decide⟩)
/-- An incorrect second header clears its older shadow71. Initial transport
and the OLD represented header are essential, not inferred from final reads. -/
theorem wrong_header :
 physicalView wrongNumeric = [w0,w0,w0,w61,w0,w0,w0,w0,w0,w93,w99,w87] ∧
 wrongNumeric 11 ≠ numericOut 11 := by
 refine ⟨rfl,?_⟩
 change w0 ≠ w71
 decide

/-- Colliding physical hash regions cannot inhabit the existing per-run owner. -/
theorem collision_control : ¬ FiniteRun 16 4 2 (fun _ => 0) preimages locations := by
 intro bad
 have same := bad.word_inj (a := leftBase) (b := .data leftBase 0) (by decide) (by decide) rfl
 cases same

/-- Neither logical failure nor fresh-liveness failure means a zero raw word. -/
theorem failed_query_boundary :
 ((PrimitivePop.elementQuery (ix 3)).read left.clear,
  ((TypeGraph.Path.cons (.index (ix 2)) .nil).readLive Value.dflt left.clear).map Value.head,
  numericOut 7,targetOut.store (.root 7),numericOut 6,targetOut.store (.data (.root 0) 2)) =
 (none,none,w93,93,w61,61) := by rfl

/-- info: 'Solidity.Backend.StorageOps.TwoClearRepresentation.Controls.bridge' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in #print axioms bridge
/-- info: 'Solidity.Backend.StorageOps.TwoClearRepresentation.Controls.ordered' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in #print axioms ordered
/-- info: 'Solidity.Backend.StorageOps.TwoClearRepresentation.Controls.physical_frames' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in #print axioms physical_frames
/-- info: 'Solidity.Backend.StorageOps.TwoClearRepresentation.Controls.wrong_header' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in #print axioms wrong_header
/-- info: 'Solidity.Backend.StorageOps.TwoClearRepresentation.Controls.collision_control' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in #print axioms collision_control
/-- info: 'Solidity.Backend.StorageOps.TwoClearRepresentation.Controls.failed_query_boundary' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in #print axioms failed_query_boundary
end Solidity.Backend.StorageOps.TwoClearRepresentation.Controls
