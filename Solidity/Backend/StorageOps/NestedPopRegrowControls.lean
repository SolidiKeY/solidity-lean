import Solidity.Backend.StorageOps.NestedPopRegrow

/-! Inhabited actual nested pop/regrowth: parent liveness returns, cleared child
payload does not. Finite per-run physical relation is separate from graph reads. -/
namespace Solidity.Backend.StorageOps.NestedPopRegrow.Controls
open TypeGraph Solidity.Storage Solidity.Storage.Representation Solidity.Storage.Representation.Graph
open NestedPopTransport
private def graph : Schema 0 where
 origin := "v10-target-nested-pop"
 declId := fun i => nomatch i
 declId_injective := by intro i; exact Fin.elim0 i
 name := fun i => nomatch i
 fields := fun i => nomatch i
 rank := fun i => nomatch i
 nonempty := by intro i; exact Fin.elim0 i
 distinct := by intro i; exact Fin.elim0 i
 guarded := by intro i; exact Fin.elim0 i
private def ix (i : Fin 5) : Index := ⟨i.val,by have bound := i.isLt; omega⟩
private def w0 : Semantics.Word := ⟨0,by decide⟩
private def w1 : Semantics.Word := ⟨1,by decide⟩
private def w2 : Semantics.Word := ⟨2,by decide⟩
private def w3 : Semantics.Word := ⟨3,by decide⟩
private def w7 : Semantics.Word := ⟨7,by decide⟩
private def w17 : Semantics.Word := ⟨17,by decide⟩
private def w23 : Semantics.Word := ⟨23,by decide⟩
private def w53 : Semantics.Word := ⟨53,by decide⟩
private def w59 : Semantics.Word := ⟨59,by decide⟩
private def w61 : Semantics.Word := ⟨61,by decide⟩
private def w71 : Semantics.Word := ⟨71,by decide⟩
private def w79 : Semantics.Word := ⟨79,by decide⟩
private def w83 : Semantics.Word := ⟨83,by decide⟩
private def w89 : Semantics.Word := ⟨89,by decide⟩
private def child0 : Value graph (.array (.prim .uint)) :=
 .array ⟨4,by decide⟩ ⟨3,by decide⟩ (by decide)
 (fun i => .present (.prim (if i.val=0 then w7 else if i.val=1 then w17 else if i.val=2 then w23 else w71)))
private def child1 : Value graph (.array (.prim .uint)) :=
 .array ⟨1,by decide⟩ ⟨0,by decide⟩ (by decide) (fun _ => .present (.prim w83))
private def child2 : Value graph (.array (.prim .uint)) :=
 .array ⟨3,by decide⟩ ⟨2,by decide⟩ (by decide)
 (fun i => .present (.prim (if i.val=0 then w53 else if i.val=1 then w59 else w61)))
private def child3 : Value graph (.array (.prim .uint)) :=
 .array ⟨2,by decide⟩ ⟨1,by decide⟩ (by decide) (fun i => .present (.prim (if i.val=0 then w79 else w89)))
private def old : Value graph (.array (.array (.prim .uint))) :=
 .array ⟨4,by decide⟩ ⟨3,by decide⟩ (by decide)
 (fun i => .present (if i.val=0 then child0 else if i.val=1 then child1 else if i.val=2 then child2 else child3))
private def popped := (recursivePop old).getD old
private def popped2 := (recursivePop popped).getD old
private def popped3 := (recursivePop popped2).getD old
private def w87 : Semantics.Word := ⟨87,by decide⟩
private def w93 : Semantics.Word := ⟨93,by decide⟩
private def w99 : Semantics.Word := ⟨99,by decide⟩
private def indices : List Index := [ix 3,ix 2,ix 0,ix 1,ix 2]
private def w91 : Semantics.Word := ⟨91,by decide⟩
private def w97 : Semantics.Word := ⟨97,by decide⟩
private def base : Solidity.Storage.Loc := .root 0
private def cb (i : Nat) : Solidity.Storage.Loc := .data base i
private def dataLoc (i j : Nat) : Solidity.Storage.Loc := .data (cb i) j
private def childBase := cb 2
private def hash (p : Solidity.Storage.Pre) : Nat := if p=.data 0 then 16 else if p=.data 16 then 48 else
 if p=.data 17 then 64 else if p=.data 18 then 80 else if p=.data 19 then 96 else if p=.data 20 then 112 else 0
private def preimages : List Solidity.Storage.Pre := [.data 0,.data 16,.data 17,.data 18,.data 19,.data 20]
private def locations : List Solidity.Storage.Loc := [base,cb 0,cb 1,cb 2,cb 3,cb 4,
 dataLoc 0 0,dataLoc 0 1,dataLoc 0 2,dataLoc 0 3,dataLoc 1 0,dataLoc 1 1,
 dataLoc 2 0,dataLoc 2 1,dataLoc 2 2,dataLoc 2 3,dataLoc 3 0,dataLoc 3 1,dataLoc 4 0]
private def symbolic : Store := fun l =>
 if l=base then w3 else if l=cb 0 then w3 else if l=cb 1 then w0 else if l=cb 2 then w2 else if l=cb 3 then w1 else if l=cb 4 then w91 else if l=dataLoc 0 0 then w7 else if l=dataLoc 0 1 then w17 else if l=dataLoc 0 2 then w23 else if l=dataLoc 0 3 then w71 else if l=dataLoc 1 0 then w83 else if l=dataLoc 1 1 then w93 else if l=dataLoc 2 0 then w53 else if l=dataLoc 2 1 then w59 else if l=dataLoc 2 2 then w61 else if l=dataLoc 2 3 then w93 else if l=dataLoc 3 0 then w79 else if l=dataLoc 3 1 then w89 else if l=dataLoc 4 0 then w97 else if l=.root 7 then w99 else w87
private def numeric : WordStore := fun a =>
 if a=0 then w3 else if a=16 then w3 else if a=17 then w0 else if a=18 then w2 else if a=19 then w1 else if a=20 then w91 else if a=48 then w7 else if a=49 then w17 else if a=50 then w23 else if a=51 then w71 else if a=64 then w83 else if a=65 then w93 else if a=80 then w53 else if a=81 then w59 else if a=82 then w61 else if a=83 then w93 else if a=96 then w79 else if a=97 then w89 else if a=112 then w97 else if a=7 then w99 else w87
private def outer : Evm.Slot := .root 0
private def child (i : Nat) : Evm.Slot := .data outer i
private def cell (i j : Nat) : Evm.Slot := .data (child i) j
private def rawOpaque : Evm.Slot := .hash ⟨7,by decide⟩ (child 2) 0
private def store : Evm.WordStore := .ofFn fun s =>
 if s=outer then 3 else if s=child 0 then 3 else if s=child 1 then 0 else if s=child 2 then 2 else if s=child 3 then 1 else
 if s=cell 0 0 then 7 else if s=cell 0 1 then 17 else if s=cell 0 2 then 23 else if s=cell 0 3 then 71 else
 if s=cell 1 0 then 83 else if s=cell 2 0 then 53 else if s=cell 2 1 then 59 else if s=cell 2 2 then 61 else
 if s=child 4 then 91 else if s=cell 4 0 then 97 else if s=cell 1 1 then 93 else if s=cell 2 3 then 93 else if s=cell 3 0 then 79 else if s=cell 3 1 then 89 else if s=rawOpaque then 77 else if s=.root 7 then 99 else 87
private def tail : List Evm.Word := [.val ⟨23,by decide⟩,.slot (.root 7)]
private def target : Evm.Machine :=
 {stack := tail,store := store,mem := fun _ => .val ⟨31,by decide⟩,
  bal := fun _ => 19,bal₀ := fun _ => 19,self := ⟨7,by decide⟩,caller := ⟨13,by decide⟩,
  callvalue := ⟨0,by decide⟩,timestamp := ⟨53,by decide⟩,accepts := fun _ _ => false}
private def popTarget := TargetNestedPop.after target outer
private def popNumeric := TargetClearRepresentation.execute 256 hash childBase (writeWord numeric 0 w2)
private def popStore := TargetClearRepresentation.afterStore (childValue old) childBase (Representation.write symbolic base w2)
private theorem run : FiniteRun 256 8 1 hash preimages locations := by
 constructor
 · intro p; simp only [hash]; split <;> (try split) <;> (try split) <;> (try split) <;> (try split) <;> (try split) <;> decide
 · decide
 · decide
 · decide
 · intro l member
   simp only [locations,List.mem_cons,List.not_mem_nil,or_false] at member
   rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp only [base,cb,dataLoc,Solidity.Storage.Loc.Bounded] <;> decide
 · intro l member
   simp only [locations,List.mem_cons,List.not_mem_nil,or_false] at member
   rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> decide
private theorem rootBefore : Represented old [.length .nil] base symbolic := by
 intro query member
 have same := List.mem_singleton.mp member
 subst query
 refine ⟨True.intro,⟨by decide,by decide⟩,?_⟩
 intro word found
 change some w3 = some word at found
 cases found
 rfl
private theorem fullChild : Represented (childValue old) (PrimitivePop.queries indices) childBase symbolic := by
 intro query member
 simp only [PrimitivePop.queries,indices,List.map_cons,List.map_nil,List.mem_cons,List.not_mem_nil,or_false] at member
 rcases member with rfl | rfl | rfl | rfl | rfl | rfl
 · refine ⟨True.intro,⟨by decide,by decide⟩,?_⟩
   intro word found
   change some w2 = some word at found
   cases found
   rfl
 · refine ⟨⟨by change 3 < lmax; decide,True.intro⟩,True.intro,?_⟩
   intro word found
   change none = some word at found
   cases found
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
private theorem childBefore : Represented (childValue old) (TargetClearRepresentation.oldQueries (childValue old) indices) childBase symbolic := by
 intro query member
 apply fullChild query
 simp only [TargetClearRepresentation.oldQueries,PrimitivePop.queries,List.mem_cons,List.mem_map] at member
 rcases member with rfl | ⟨i,inside,rfl⟩
 · exact List.mem_cons_self
 · exact List.mem_cons_of_mem _ (List.mem_map.mpr ⟨i,(List.mem_filter.mp inside).1,rfl⟩)
private theorem initial : Transport 256 hash locations symbolic numeric := by
 intro l member
 simp only [locations,List.mem_cons,List.not_mem_nil,or_false] at member
 rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> rfl
private theorem covered : ∀ query ∈ PrimitivePop.queries (G := graph) (p := .uint) indices, query.location childBase ∈ locations := by
 intro query member
 simp only [PrimitivePop.queries,indices,List.map_cons,List.map_nil,List.mem_cons,List.not_mem_nil,or_false] at member
 rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> (try rw [PrimitivePop.element_location]) <;> decide
private theorem visited : ∀ j, j < (childValue old).length.val → Solidity.Storage.Loc.data childBase j ∈ locations := by
 intro j inside
 change j < 2 at inside
 have cases : j=0 ∨ j=1 := by omega
 rcases cases with rfl | rfl <;> decide
private theorem fitting : ∀ l ∈ locations, TargetOperations.KeysFit l := by
 intro l member
 simp only [locations,List.mem_cons,List.not_mem_nil,or_false] at member
 rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> trivial
private theorem targetInitial : ∀ l (member : l ∈ locations), target.store.cells (TargetOperations.toSlot l (fitting l member)) = TargetOperations.encodeWord (symbolic l) := by
 intro l member
 simp only [locations,List.mem_cons,List.not_mem_nil,or_false] at member
 rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> rfl

private def path (i : Index) : TypeGraph.Path graph (.array (.array (.prim .uint))) (.array (.prim .uint)) := .cons (.index i) .nil
private def hq (i : Index) : Query graph (.array (.array (.prim .uint))) := .length (path i)
private def wq (i j : Index) : Query graph (.array (.array (.prim .uint))) := .word (.cons (.index i) (.cons (.index j) .nil))
private def graphView (v : Value graph (.array (.array (.prim .uint)))) :=
 (v.length.val,v.extent.val,[(hq (ix 0)).read v,(hq (ix 1)).read v,(hq (ix 2)).read v,(hq (ix 3)).read v,
  (wq (ix 0) (ix 0)).read v,(wq (ix 0) (ix 1)).read v,(wq (ix 0) (ix 2)).read v,(wq (ix 0) (ix 3)).read v,
  (wq (ix 1) (ix 0)).read v,(wq (ix 2) (ix 0)).read v,(wq (ix 2) (ix 1)).read v,(wq (ix 2) (ix 2)).read v,
  (wq (ix 3) (ix 0)).read v,(wq (ix 3) (ix 1)).read v],
  ((path (ix 2)).readLive Value.dflt v).map (fun child => child.length.val))

private def g0 : Index × List (Query graph (.array (.prim .uint))) := ⟨ix 0,PrimitivePop.queries [ix 3,ix 0,ix 1]⟩
private def g1 : Index × List (Query graph (.array (.prim .uint))) := ⟨ix 1,PrimitivePop.queries [ix 0,ix 1]⟩
private def g3 : Index × List (Query graph (.array (.prim .uint))) := ⟨ix 3,PrimitivePop.queries [ix 1,ix 0]⟩
private def g4 : Index × List (Query graph (.array (.prim .uint))) := ⟨ix 4,PrimitivePop.queries [ix 0]⟩
private def groups := [g0,g1,g3,g4,g0]
private theorem member_shape (query : Query graph (.array (.array (.prim .uint)))) :
 query ∈ AggregatePopFrames.contexts groups ↔ query ∈ [hq (ix 0),wq (ix 0) (ix 3),wq (ix 0) (ix 0),wq (ix 0) (ix 1),hq (ix 1),wq (ix 1) (ix 0),wq (ix 1) (ix 1),hq (ix 3),wq (ix 3) (ix 1),wq (ix 3) (ix 0),hq (ix 4),wq (ix 4) (ix 0),hq (ix 0),wq (ix 0) (ix 3),wq (ix 0) (ix 0),wq (ix 0) (ix 1)] := by rfl
private theorem contextBefore : Represented old (AggregatePopFrames.contexts groups) base symbolic := by
 intro query member
 rw [member_shape] at member
 simp only [List.mem_cons,List.not_mem_nil,or_false] at member
 rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
 · refine ⟨⟨by change 0 < lmax; decide,True.intro⟩,⟨by decide,by decide⟩,?_⟩
   intro word found
   change some w3 = some word at found
   cases found
   rfl
 · refine ⟨⟨by change 0 < lmax; decide,⟨by change 3 < lmax; decide,True.intro⟩⟩,True.intro,?_⟩
   intro word found
   change some w71 = some word at found
   cases found
   rfl
 · refine ⟨⟨by change 0 < lmax; decide,⟨by change 0 < lmax; decide,True.intro⟩⟩,True.intro,?_⟩
   intro word found
   change some w7 = some word at found
   cases found
   rfl
 · refine ⟨⟨by change 0 < lmax; decide,⟨by change 1 < lmax; decide,True.intro⟩⟩,True.intro,?_⟩
   intro word found
   change some w17 = some word at found
   cases found
   rfl
 · refine ⟨⟨by change 1 < lmax; decide,True.intro⟩,⟨by decide,by decide⟩,?_⟩
   intro word found
   change some w0 = some word at found
   cases found
   rfl
 · refine ⟨⟨by change 1 < lmax; decide,⟨by change 0 < lmax; decide,True.intro⟩⟩,True.intro,?_⟩
   intro word found
   change some w83 = some word at found
   cases found
   rfl
 · refine ⟨⟨by change 1 < lmax; decide,⟨by change 1 < lmax; decide,True.intro⟩⟩,True.intro,?_⟩
   intro word found
   change none = some word at found
   cases found
 · refine ⟨⟨by change 3 < lmax; decide,True.intro⟩,⟨by decide,by decide⟩,?_⟩
   intro word found
   change some w1 = some word at found
   cases found
   rfl
 · refine ⟨⟨by change 3 < lmax; decide,⟨by change 1 < lmax; decide,True.intro⟩⟩,True.intro,?_⟩
   intro word found
   change some w89 = some word at found
   cases found
   rfl
 · refine ⟨⟨by change 3 < lmax; decide,⟨by change 0 < lmax; decide,True.intro⟩⟩,True.intro,?_⟩
   intro word found
   change some w79 = some word at found
   cases found
   rfl
 · refine ⟨⟨by change 4 < lmax; decide,True.intro⟩,True.intro,?_⟩
   intro word found
   change none = some word at found
   cases found
 · refine ⟨⟨by change 4 < lmax; decide,⟨by change 0 < lmax; decide,True.intro⟩⟩,True.intro,?_⟩
   intro word found
   change none = some word at found
   cases found
 · refine ⟨⟨by change 0 < lmax; decide,True.intro⟩,⟨by decide,by decide⟩,?_⟩
   intro word found
   change some w3 = some word at found
   cases found
   rfl
 · refine ⟨⟨by change 0 < lmax; decide,⟨by change 3 < lmax; decide,True.intro⟩⟩,True.intro,?_⟩
   intro word found
   change some w71 = some word at found
   cases found
   rfl
 · refine ⟨⟨by change 0 < lmax; decide,⟨by change 0 < lmax; decide,True.intro⟩⟩,True.intro,?_⟩
   intro word found
   change some w7 = some word at found
   cases found
   rfl
 · refine ⟨⟨by change 0 < lmax; decide,⟨by change 1 < lmax; decide,True.intro⟩⟩,True.intro,?_⟩
   intro word found
   change some w17 = some word at found
   cases found
   rfl
private theorem other : ∀ group ∈ groups, group.1.val ≠ old.length.val-1 := by
 intro group member
 simp only [groups,List.mem_cons,List.not_mem_nil,or_false] at member
 rcases member with rfl | rfl | rfl | rfl | rfl <;> decide
private theorem outside : ∀ query ∈ AggregatePopFrames.contexts groups,
 query.location base ≠ base ∧ query.location base ≠ .data base (old.length.val-1) ∧
 ∀ j, j < (childValue old).length.val → query.location base ≠ .data (.data base (old.length.val-1)) j := by
 intro query member
 rw [member_shape] at member
 simp only [List.mem_cons,List.not_mem_nil,or_false] at member
 rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> constructor
 all_goals try decide
 all_goals constructor
 all_goals try decide
 all_goals intro j inside
 all_goals change j < 2 at inside
 all_goals have cases : j=0 ∨ j=1 := by omega
 all_goals rcases cases with rfl | rfl <;> decide
private theorem contextCovered : ∀ query ∈ AggregatePopFrames.contexts groups, query.location base ∈ locations := by
 intro query member
 rw [member_shape] at member
 simp only [List.mem_cons,List.not_mem_nil,or_false] at member
 rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> decide


private def regrown := (operationPush popped).getD old
private def finalNumeric := writeWord popNumeric 0 w3
private def finalStore := Representation.write popStore base w3
private def targetOut := TargetHeaderPush.incremented outer popTarget
/-- All selected/context OLD inputs inhabit the actual sequential certificate. -/
theorem bridge :
 let popWord := lengthWord popped.length.val popped.length.isLt
 let childBase := Solidity.Storage.Loc.data base (old.length.val-1)
 let popStore := TargetClearRepresentation.afterStore (childValue old) childBase (Representation.write symbolic base popWord)
 let growWord := lengthWord regrown.length.val regrown.length.isLt
 let finalStore := Representation.write popStore base growWord
 let popTarget := TargetNestedPop.after target (TargetOperations.toSlot base True.intro)
 let finalTarget := {popTarget with store := Evm.WordStore.write popTarget.store (TargetOperations.toSlot base True.intro) (TargetOperations.encodeWord growWord).val}
 ∃ finalNumeric, execute 256 hash base numeric = some finalNumeric ∧
 Evm.run (code (TargetOperations.toSlot base True.intro)) target = .ok finalTarget 0 ∧
 Represented regrown (RetainedPush.requested (allGroups old indices groups)) base finalStore ∧
 Transport 256 hash locations finalStore finalNumeric ∧
 (∀ l (member : l ∈ locations), finalTarget.store.cells (TargetOperations.toSlot l (fitting l member)) = TargetOperations.encodeWord (finalNumeric (l.word 256 hash))) ∧
 (∀ query ∈ RetainedPush.requested (allGroups old indices groups), ∀ word, query.read regrown = some word → finalNumeric ((query.location base).word 256 hash) = word) ∧
 regrown.length.val = old.length.val ∧ regrown.extent = old.extent :=
 NestedPopRegrow.complete run old popped regrown rfl rfl indices groups base True.intro symbolic numeric target
   rootBefore childBefore initial (by decide) covered visited fitting targetInitial contextBefore other outside contextCovered

/-- Pin the existential certificate to the actual concrete numeric execution. -/
theorem concrete_owner :
 NestedPopRegrow.execute 256 hash base numeric = some finalNumeric ∧
 Evm.run (NestedPopRegrow.code outer) target = .ok targetOut 0 ∧
 Represented regrown (RetainedPush.requested (allGroups old indices groups)) base finalStore ∧
 Transport 256 hash locations finalStore finalNumeric := by
 obtain ⟨final,performed,executed,owner,transported,agreement,reads,headers⟩ := bridge
 have known : NestedPopRegrow.execute 256 hash base numeric = some finalNumeric := by rfl
 have equal := Option.some.inj (performed.symm.trans known)
 subst final
 exact ⟨performed,executed,owner,transported⟩
private def numericView (m : WordStore) := [m 0,m 16,m 17,m 18,m 19,m 20,m 48,m 49,m 50,m 51,m 64,m 65,m 80,m 81,m 82,m 83,m 96,m 97,m 112,m 7,m 255]
private def symbolicView (m : Store) := (locations ++ [Solidity.Storage.Loc.root 7,Solidity.Storage.Loc.root 255]).map m
private def targets : List Evm.Slot := [.root 0,child 0,child 1,child 2,child 3,child 4,cell 0 0,cell 0 1,cell 0 2,cell 0 3,cell 1 0,cell 1 1,cell 2 0,cell 2 1,cell 2 2,cell 2 3,cell 3 0,cell 3 1,cell 4 0,rawOpaque,.root 7,.root 255]
private def targetView (m : Evm.Machine) := targets.map (fun s => m.store s)
private def contextView (v : Value graph (.array (.array (.prim .uint)))) := (AggregatePopFrames.contexts groups).map (fun q => q.read v)
private def machineContext (m : Evm.Machine) := (m.stack,m.mem 0,m.bal m.self,m.bal₀ m.self,m.self,m.caller,m.callvalue,m.timestamp,m.accepts m.self m.self)
private def selectedView (v : Value graph (.array (.array (.prim .uint)))) :=
 [(hq (ix 2)).read v,(wq (ix 2) (ix 0)).read v,(wq (ix 2) (ix 1)).read v,(wq (ix 2) (ix 2)).read v,(wq (ix 2) (ix 3)).read v]

theorem ordered :
 (selectedView old,selectedView popped,selectedView regrown,contextView old,contextView regrown,symbolicView symbolic,symbolicView finalStore,numericView numeric,numericView finalNumeric,
  targetView target,targetView targetOut,machineContext targetOut) =
 ([some w2,some w53,some w59,some w61,none],[some w0,some w0,some w0,some w61,none],[some w0,some w0,some w0,some w61,none],[some w3,some w71,some w7,some w17,some w0,some w83,none,some w1,some w89,some w79,none,none,some w3,some w71,some w7,some w17],[some w3,some w71,some w7,some w17,some w0,some w83,none,some w1,some w89,some w79,none,none,some w3,some w71,some w7,some w17],
  [w3,w3,w0,w2,w1,w91,w7,w17,w23,w71,w83,w93,w53,w59,w61,w93,w79,w89,w97,w99,w87],[w3,w3,w0,w0,w1,w91,w7,w17,w23,w71,w83,w93,w0,w0,w61,w93,w79,w89,w97,w99,w87],
  [w3,w3,w0,w2,w1,w91,w7,w17,w23,w71,w83,w93,w53,w59,w61,w93,w79,w89,w97,w99,w87],[w3,w3,w0,w0,w1,w91,w7,w17,w23,w71,w83,w93,w0,w0,w61,w93,w79,w89,w97,w99,w87],
  [3,3,0,2,1,91,7,17,23,71,83,93,53,59,61,93,79,89,97,77,99,87],[3,3,0,0,1,91,7,17,23,71,83,93,0,0,61,93,79,89,97,77,99,87],machineContext target) := by rfl

theorem alias_observations :
 (old.length.val,popped.length.val,regrown.length.val,old.extent.val,regrown.extent.val,
  ((path (ix 2)).readLive Value.dflt old).map (fun c => c.length.val),
  ((path (ix 2)).readLive Value.dflt popped).map (fun c => c.length.val),
  ((path (ix 2)).readLive Value.dflt regrown).map (fun c => c.length.val),
  ((TypeGraph.Path.cons (.index (ix 2)) (.cons (.index (ix 2)) .nil)).readLive Value.dflt regrown).map Value.head,
  (wq (ix 2) (ix 2)).read regrown,finalNumeric 82) =
 (3,2,3,4,4,some 2,none,some 0,none,some w61,w61) := by rfl

theorem false_restoration : regrown ≠ old ∧ finalNumeric ≠ numeric ∧
 targetOut.store (cell 2 0) ≠ target.store (cell 2 0) := by
 constructor
 · intro same
   have observed := congrArg (fun v => (wq (ix 2) (ix 0)).read v) same
   change some w0 = some w53 at observed
   exact (by decide : some w0 ≠ some w53) observed
 constructor
 · intro same
   have observed := congrFun same 80
   change w0 = w53 at observed
   exact (by decide : w0 ≠ w53) observed
 · change (0 : Nat) ≠ 53
   decide

private def wrongCode := TargetHeaderPush.code outer ++ TargetNestedPop.code outer
private def wrongTarget := TargetNestedPop.after (TargetHeaderPush.incremented outer target) outer
private def wrongNumeric := (do
 let grown ← LifecycleNumeric.pushHeader 256 hash base numeric
 NestedPopTransport.execute 256 hash base grown).getD numeric

/-- Actual reversed order selects older child3, not the popped live child2. -/
theorem wrong_order : Evm.run wrongCode target = .ok wrongTarget 0 ∧
 numericView wrongNumeric = [w3,w3,w0,w2,w0,w91,w7,w17,w23,w71,w83,w93,w53,w59,w61,w93,w0,w89,w97,w99,w87] ∧
 targetView wrongTarget = [3,3,0,2,0,91,7,17,23,71,83,93,53,59,61,93,0,89,97,77,99,87] ∧
 wrongNumeric 80 ≠ finalNumeric 80 := by
 constructor
 · unfold wrongCode
   rw [Evm.run_append_ok (m' := TargetHeaderPush.incremented outer target)
     (by rw [TargetHeaderPush.run_current]; rfl),TargetNestedPop.run_current]
   rfl
 exact ⟨rfl,rfl,by decide⟩

private def emptyNumeric := writeWord numeric 0 w0
private def emptyTarget : Evm.Machine := {target with store := Evm.WordStore.write target.store outer 0}
theorem empty_failure : NestedPopRegrow.execute 256 hash base emptyNumeric = none ∧
 Evm.run (NestedPopRegrow.code outer) emptyTarget = .revert :=
 ⟨rfl,run_empty outer emptyTarget rfl⟩

theorem capacity_witness : ∃ result, operationPush popped = some result := push_exists old popped rfl

/-- info: 'Solidity.Backend.StorageOps.NestedPopRegrow.Controls.bridge' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms bridge
/-- info: 'Solidity.Backend.StorageOps.NestedPopRegrow.Controls.concrete_owner' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in #print axioms concrete_owner
/-- info: 'Solidity.Backend.StorageOps.NestedPopRegrow.Controls.ordered' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in #print axioms ordered
/-- info: 'Solidity.Backend.StorageOps.NestedPopRegrow.Controls.alias_observations' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in #print axioms alias_observations
/-- info: 'Solidity.Backend.StorageOps.NestedPopRegrow.Controls.false_restoration' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in #print axioms false_restoration
/-- info: 'Solidity.Backend.StorageOps.NestedPopRegrow.Controls.wrong_order' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in #print axioms wrong_order
/-- info: 'Solidity.Backend.StorageOps.NestedPopRegrow.Controls.empty_failure' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in #print axioms empty_failure
/-- info: 'Solidity.Backend.StorageOps.NestedPopRegrow.Controls.capacity_witness' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in #print axioms capacity_witness
end Solidity.Backend.StorageOps.NestedPopRegrow.Controls
