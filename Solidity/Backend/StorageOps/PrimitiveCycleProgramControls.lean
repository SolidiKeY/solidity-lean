import Solidity.Backend.StorageOps.PrimitiveCycleProgram

/-! Actual triple client: old finite-run/public representation evidence only.
Complete ordered observations distinguish raw presence, live aliases and words;
no ordinary Source, bytecode/gas or world rollback is claimed. -/
namespace Solidity.Backend.StorageOps.PrimitiveCycleProgram.Controls
open TypeGraph Solidity.Storage Solidity.Storage.Representation Solidity.Storage.Representation.Graph
private def graph : Schema 0 where
 origin := "v10-primitive-cycle-transport"
 declId := fun i => nomatch i
 declId_injective := by intro i; exact Fin.elim0 i
 name := fun i => nomatch i
 fields := fun i => nomatch i
 rank := fun i => nomatch i
 nonempty := by intro i; exact Fin.elim0 i
 distinct := by intro i; exact Fin.elim0 i
 guarded := by intro i; exact Fin.elim0 i
private def ix (i : Fin 4) : Index := ⟨i.val,by have h:=i.isLt; omega⟩
private def i0 := ix 0
private def i1 := ix 1
private def i2 := ix 2
private def i3 := ix 3
private def ids : List Index := [i2,i1,i0,i3,i1]
private def w0 : Semantics.Word := ⟨0,by decide⟩
private def w1 : Semantics.Word := ⟨1,by decide⟩
private def w2 : Semantics.Word := ⟨2,by decide⟩
private def w87 : Semantics.Word := ⟨87,by decide⟩
private def w99 : Semantics.Word := ⟨99,by decide⟩
private def payload : (p : PrimTy) → p.Denote
 | .bool => true
 | .uint => ⟨53,by decide⟩
 | .int => ⟨-17,by decide⟩
private def encoded (p : PrimTy) : Semantics.Word := PrimTy.toWord (payload p)
private def old (p : PrimTy) : Value graph (.array (.prim p)) :=
 .array ⟨3,by decide⟩ i2 (by decide) (fun _ => .present (.prim (payload p)))
private def middle (p : PrimTy) := (recursivePop (old p)).getD (old p)
private def grown (p : PrimTy) := (operationPush (middle p)).getD (old p)
private def result (p : PrimTy) := (GraphRetainedCycle.execute (old p)).getD (old p)
private def base : Solidity.Storage.Loc := .root 0
private def loc (i : Nat) : Solidity.Storage.Loc := .data base i
private def store (p : PrimTy) : Store := fun l => if l=base then w2 else if l=loc 3 then w99 else encoded p
private def popStore (p : PrimTy) : Store := Representation.write (Representation.write (store p) (loc 1) w0) base w1
private theorem before (p : PrimTy) : Represented (old p) (PrimitivePop.queries ids) base (store p) := by
 intro query member
 simp only [PrimitivePop.queries,ids,List.map_cons,List.map_nil,List.mem_cons,List.not_mem_nil,or_false] at member
 rcases member with rfl | rfl | rfl | rfl | rfl | rfl
 · refine ⟨True.intro,⟨by change (2:Nat)≤lmax; decide,by change (3:Nat)≤lmax; decide⟩,?_⟩
   intro word found
   change some w2=some word at found
   cases found
   rfl
 · refine ⟨⟨by change i2.val<lmax; decide,True.intro⟩,True.intro,?_⟩
   intro word found
   change some (encoded p)=some word at found
   cases found
   rfl
 · refine ⟨⟨by change i1.val<lmax; decide,True.intro⟩,True.intro,?_⟩
   intro word found
   change some (encoded p)=some word at found
   cases found
   rfl
 · refine ⟨⟨by change i0.val<lmax; decide,True.intro⟩,True.intro,?_⟩
   intro word found
   change some (encoded p)=some word at found
   cases found
   rfl
 · refine ⟨⟨by change i3.val<lmax; decide,True.intro⟩,True.intro,?_⟩
   intro word found
   change none=some word at found
   cases found
 · refine ⟨⟨by change i1.val<lmax; decide,True.intro⟩,True.intro,?_⟩
   intro word found
   change some (encoded p)=some word at found
   cases found
   rfl

private def hash (key : Solidity.Storage.Pre) : Nat := if key=.data 0 then 4 else 0
private def locations : List Solidity.Storage.Loc := [base,loc 0,loc 1,loc 2,loc 3]
private def preimages : List Solidity.Storage.Pre := [.data 0]
private def numeric (p : PrimTy) : WordStore := fun address =>
 if address=0 then w2 else if address=7 then w99 else encoded p
private def popNumeric (p : PrimTy) : WordStore := writeWord (writeWord (numeric p) 5 w0) 0 w1
private theorem run : FiniteRun 16 4 1 hash preimages locations := by
 constructor
 · intro key; simp only [hash]; split <;> decide
 · decide
 · decide
 · decide
 · intro l member
   simp only [locations,List.mem_cons,List.not_mem_nil,or_false] at member
   rcases member with rfl | rfl | rfl | rfl | rfl <;> simp only [base,loc,Solidity.Storage.Loc.Bounded] <;> decide
 · intro l member
   simp only [locations,List.mem_cons,List.not_mem_nil,or_false] at member
   rcases member with rfl | rfl | rfl | rfl | rfl <;> decide


private theorem fitting : ∀ l ∈ locations, TargetOperations.KeysFit l := by
 intro l member
 simp only [locations,List.mem_cons,List.not_mem_nil,or_false] at member
 rcases member with rfl | rfl | rfl | rfl | rfl <;> exact True.intro
private theorem covered (p : PrimTy) : ∀ q ∈ PrimitivePop.queries (G:=graph) (p:=p) ids, q.location base ∈ locations := by
 intro q member
 simp only [PrimitivePop.queries,ids,List.map_cons,List.map_nil,List.mem_cons,List.not_mem_nil,or_false] at member
 rcases member with rfl | rfl | rfl | rfl | rfl | rfl
 · change base ∈ locations; decide
 all_goals rw [PrimitivePop.element_location]; decide
private noncomputable def target (p : PrimTy) : Evm.Machine :=
 { Evm.Machine.init (fun _ => 19) ⟨7,by decide⟩ with
   store := ⟨fun slot => TargetOperations.encodeWord (store p (Solidity.Storage.ofSlot slot))⟩
   stack := [.val ⟨23,by decide⟩,.slot (.root 9)]
   mem := fun _ => .val ⟨31,by decide⟩
   caller := ⟨13,by decide⟩
   timestamp := ⟨53,by decide⟩ }
private noncomputable def first (p : PrimTy) : Evm.Machine :=
 {target p with store := Evm.WordStore.write (Evm.WordStore.write (target p).store (.root 0) 1) (.data (.root 0) 1) 0}
private noncomputable def again (p : PrimTy) : Evm.Machine :=
 {first p with store := Evm.WordStore.write (Evm.WordStore.write (first p).store (.root 0) 2) (.data (.root 0) 1) 0}
private noncomputable def final (p : PrimTy) : Evm.Machine :=
 {again p with store := Evm.WordStore.write (Evm.WordStore.write (again p).store (.root 0) 1) (.data (.root 0) 1) 0}

/-- Genuine application of the whole triple certificate, including numeric
execution and successful final query readback; no final owner is an input. -/
theorem certificate (p : PrimTy) : ∃ numericFinal targetFinal,
 GraphRetainedCycle.execute (old p)=some (result p) ∧
 execute 16 hash base (numeric p)=some numericFinal ∧
 Evm.run (code (.root 0)) (target p)=.ok targetFinal 0 ∧
 Represented (result p) (PrimitivePop.queries ids) base (popStore p) ∧
 Transport 16 hash locations (popStore p) numericFinal ∧
 (∀ q ∈ PrimitivePop.queries ids, ∀ word, q.read (result p)=some word → numericFinal (q.location base |>.word 16 hash)=word) := by
 have initial : Transport 16 hash locations (store p) (numeric p) := by
  intro l member
  simp only [locations,List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl <;> rfl
 have agreement : ∀ l (member : l ∈ locations), (target p).store.cells (TargetOperations.toSlot l (fitting l member)) = TargetOperations.encodeWord (store p l) := by
  intro l member
  change TargetOperations.encodeWord (store p (Solidity.Storage.ofSlot (TargetOperations.toSlot l _))) = _
  rw [TargetOperations.ofSlot_toSlot]
 obtain ⟨num,intrinsic,numericRun,targetRun,owner,transported,_,readback,returned⟩ :=
  complete_numeric run (old p) (middle p) (grown p) (result p) rfl rfl rfl ids base True.intro (store p) (target p) (numeric p) fitting (before p) initial agreement (covered p) (by change loc 1 ∈ locations; decide)
 rw [returned] at owner transported
 exact ⟨num,_,intrinsic,numericRun,targetRun,owner,transported,readback⟩

private def graphView {p : PrimTy} (v : Value graph (.array (.prim p))) :=
 (PrimitivePop.queries ids).map (fun q => q.read v)
private def present {p : PrimTy} (v : Value graph (.array (.prim p))) (i : Index) : Bool :=
 if inside : i.val<v.extent.val then
  match v.slots ⟨i.val,inside⟩ with
  | .absent => false
  | .present _ => true
 else false
private def path (p : PrimTy) (i : Index) : TypeGraph.Path graph (.array (.prim p)) (.prim p) := .cons (.index i) .nil
private def live {p : PrimTy} (v : Value graph (.array (.prim p))) (i : Index) : Option Semantics.Word :=
 ((path p i).readLive Value.dflt v).map (fun value => PrimTy.toWord value.head)

/-- COMPLETE ordered requested queries, raw presence, metadata, retained/live
reads and failed raw-cell distinction; Bool, unsigned53 and signed-17. -/
theorem graph_ordered (p : PrimTy) :
 (graphView (old p),graphView (middle p),graphView (grown p),graphView (result p),
  present (old p) i1,present (middle p) i1,present (grown p) i1,present (result p) i1,
  present (result p) i2,(old p).extent.val,(middle p).extent.val,(grown p).extent.val,(result p).extent.val,
  live (old p) i1,live (middle p) i1,live (grown p) i1,live (result p) i1,
  live (result p) i0,live (result p) i2,live (result p) i3,
  popStore p (loc 0),popStore p (loc 1),popStore p (loc 2),popStore p (loc 3)) =
 ([some w2,some (encoded p),some (encoded p),some (encoded p),none,some (encoded p)],
  [some w1,some (encoded p),some w0,some (encoded p),none,some w0],
  [some w2,some (encoded p),some w0,some (encoded p),none,some w0],
  [some w1,some (encoded p),some w0,some (encoded p),none,some w0],
  true,true,false,false,true,3,3,3,3,
  some (encoded p),none,some w0,none,some (encoded p),none,none,
  encoded p,w0,encoded p,w99) := by cases p <;> rfl


private def slots : List Evm.Slot := [.root 0,.data (.root 0) 2,.data (.root 0) 1,.data (.root 0) 0,.data (.root 0) 3,.data (.root 0) 1,.root 9]
private def view (m : Evm.Machine) := slots.map (fun slot => m.store.cells slot)
private def context (m : Evm.Machine) := (m.stack,m.mem 0,m.bal m.self,m.bal₀ m.self,m.self,m.caller,m.callvalue,m.timestamp,m.accepts m.self m.self)

theorem target_execution (p : PrimTy) : Evm.run (code (.root 0)) (target p)=.ok (final p) 0 := by
 unfold code TargetPrimitivePopPush.code
 rw [Evm.run_append_ok (m' := again p) (by
   rw [Evm.run_append_ok (m' := first p) (by rw [TargetPrimitivePop.run_current]; rfl),TargetPrimitivePush.run_current]
   rfl),TargetPrimitivePop.run_current]
 rfl

/-- Entire ordered target vectors at all four actual operation states and
complete existing context: selected payload clears, older shadow99 survives. -/
theorem ordered (p : PrimTy) :
 (view (target p),view (first p),view (again p),view (final p),context (first p),context (again p),context (final p)) =
 ([TargetOperations.encodeWord w2,TargetOperations.encodeWord (encoded p),TargetOperations.encodeWord (encoded p),TargetOperations.encodeWord (encoded p),TargetOperations.encodeWord w99,TargetOperations.encodeWord (encoded p),TargetOperations.encodeWord (encoded p)],
  [TargetOperations.encodeWord w1,TargetOperations.encodeWord (encoded p),TargetOperations.encodeWord w0,TargetOperations.encodeWord (encoded p),TargetOperations.encodeWord w99,TargetOperations.encodeWord w0,TargetOperations.encodeWord (encoded p)],
  [TargetOperations.encodeWord w2,TargetOperations.encodeWord (encoded p),TargetOperations.encodeWord w0,TargetOperations.encodeWord (encoded p),TargetOperations.encodeWord w99,TargetOperations.encodeWord w0,TargetOperations.encodeWord (encoded p)],
  [TargetOperations.encodeWord w1,TargetOperations.encodeWord (encoded p),TargetOperations.encodeWord w0,TargetOperations.encodeWord (encoded p),TargetOperations.encodeWord w99,TargetOperations.encodeWord w0,TargetOperations.encodeWord (encoded p)],
  context (target p),context (target p),context (target p)) := by cases p <;> rfl

/-- Initial empty pop fails in the actual target program. This says nothing
about an enclosing caller/catch/world restoration rule. -/
theorem empty (p : PrimTy) : Evm.run (code (.root 0)) {target p with store := Evm.WordStore.write (target p).store (.root 0) 0}=.revert :=
 run_empty _ _ (by rw [Evm.WordStore.write_same_of_lt]; decide)


private def addresses : List Nat := [0,6,5,4,7,5,9]
private def numericView (s : WordStore) := addresses.map s
/-- COMPLETE ordered observations of ACTUAL numeric pop, pair and triple;
older retained shadow99 and outside payload remain, selected live payload clears. -/
theorem numeric_ordered (p : PrimTy) :
 (numericView (numeric p),
  (PrimitivePop.execute 16 hash base (numeric p)).map numericView,
  (TargetPrimitivePopPush.execute 16 hash base (numeric p)).map numericView,
  (execute 16 hash base (numeric p)).map numericView) =
 ([w2,encoded p,encoded p,encoded p,w99,encoded p,encoded p],
  some [w1,encoded p,w0,encoded p,w99,w0,encoded p],
  some [w2,encoded p,w0,encoded p,w99,w0,encoded p],
  some [w1,encoded p,w0,encoded p,w99,w0,encoded p]) := by rfl

/-- info: 'Solidity.Backend.StorageOps.PrimitiveCycleProgram.Controls.numeric_ordered' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in #print axioms numeric_ordered

private noncomputable def wrong (p : PrimTy) : Evm.Machine :=
 let up := {target p with store := Evm.WordStore.write (Evm.WordStore.write (target p).store (.root 0) 3) (.data (.root 0) 2) 0}
 {up with store := Evm.WordStore.write (Evm.WordStore.write up.store (.root 0) 2) (.data (.root 0) 2) 0}
/-- Actual push/pop on OLD input touches the older shadow instead. Reordering
or omitting first pop cannot satisfy the whole triple's ordered observation. -/
theorem wrong_order (p : PrimTy) :
 Evm.run (TargetPrimitivePush.code (.root 0) ++ TargetPrimitivePop.code (.root 0)) (target p)=.ok (wrong p) 0 ∧
 (wrong p).store (.data (.root 0) 2)=0 ∧
 (wrong p).store.cells (.data (.root 0) 1)=TargetOperations.encodeWord (encoded p) ∧
 wrong p ≠ final p := by
 refine ⟨?_,rfl,rfl,?_⟩
 · rw [Evm.run_append_ok (m' := {target p with store := Evm.WordStore.write (Evm.WordStore.write (target p).store (.root 0) 3) (.data (.root 0) 2) 0})
    (by rw [TargetPrimitivePush.run_current]; rfl),TargetPrimitivePop.run_current]
   rfl
 · intro same
   have bad := congrArg (fun m : Evm.Machine => m.store (.root 0)) same
   change (2:Nat)=1 at bad
   omega

/-- info: 'Solidity.Backend.StorageOps.PrimitiveCycleProgram.Controls.graph_ordered' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in #print axioms graph_ordered
/-- info: 'Solidity.Backend.StorageOps.PrimitiveCycleProgram.Controls.wrong_order' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in #print axioms wrong_order

/-- info: 'Solidity.Backend.StorageOps.PrimitiveCycleProgram.Controls.certificate' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in #print axioms certificate
/-- info: 'Solidity.Backend.StorageOps.PrimitiveCycleProgram.Controls.target_execution' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in #print axioms target_execution
/-- info: 'Solidity.Backend.StorageOps.PrimitiveCycleProgram.Controls.ordered' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in #print axioms ordered
/-- info: 'Solidity.Backend.StorageOps.PrimitiveCycleProgram.Controls.empty' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in #print axioms empty
end Solidity.Backend.StorageOps.PrimitiveCycleProgram.Controls
