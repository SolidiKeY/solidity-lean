import Solidity.Backend.StorageOps.FreshDefaultPush

/-! Nonzero-index multiword fresh allocation and actual initializer: dirty new
cells, correct stride, old contexts, raw nonlive tails and wrong-stride negative.
Captured typed-slot composition only, not Source/world allocation identity. -/
namespace Solidity.Backend.StorageOps.FreshDefaultPush.Controls
open TypeGraph Solidity.Storage Solidity.Storage.Representation Solidity.Storage.Representation.Graph
private def z : Fin 1 := ⟨0,by decide⟩
private def two : FixedSize := ⟨2,by decide⟩
private def fs : List (Name × TypeGraph.Ty 1) :=
 [("flag",.prim .bool),("pair",.fixed (.prim .uint) two),("children",.array (.node z))]
private def graph : Schema 1 where
 origin := "v10-target-default-init"
 declId := fun _ => 0
 declId_injective := by intro i j _; apply Fin.ext; omega
 name := fun _ => "InitNode"
 fields := fun _ => fs
 rank := fun _ => 2
 nonempty := fun _ => rfl
 distinct := fun _ => rfl
 guarded := by
  intro i f member
  simp only [fs,List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl <;> decide
private abbrev T : TypeGraph.Ty 1 := .node z
private def permit : CopyPermit graph T := CopyPermit.checked (fun _ => true) (by decide)
private def ix (i : Fin 3) : Index := ⟨i.val,by have h:=i.isLt; omega⟩
private def flag : TypeGraph.Path graph T (.prim .bool) := .cons (.field .here) .nil
private def pair (i : Index) : TypeGraph.Path graph T (.prim .uint) :=
 .cons (.field (.there .here)) (.cons (.fixed i) .nil)
private def children : TypeGraph.Path graph T (.array T) := .cons (.field (.there (.there .here))) .nil
private def descendant (i : Index) : TypeGraph.Path graph T (.prim .bool) :=
 children.append (.cons (.index i) flag)
private def queries : List (Query graph T) :=
 [.word (descendant (ix 0)),.word flag,.word (pair (ix 1)),.length children,.word (pair (ix 0)),.word (descendant (ix 1)),.word (pair (ix 0))]

private def node (value : Bool) (a b : PrimTy.uint.Denote) : Value graph T :=
 .node (fun pos => match pos with
 | .here => .prim value
 | .there .here => .fixed (fun i => .present (.prim (if i.val=0 then a else b)))
 | .there (.there .here) => Value.dflt (.array T)
 | .there (.there (.there q)) => nomatch q)
private def old : Value graph (.array T) :=
 .array ⟨2,by decide⟩ (ix 2) (by decide) (fun i => .present (if i.val=0 then node true ⟨53,by decide⟩ ⟨71,by decide⟩ else node false ⟨17,by decide⟩ ⟨23,by decide⟩))
private def result := (operationPush old).getD old
private def base : Solidity.Storage.Loc := .root 0
private def part (i : Nat) : Solidity.Storage.Loc := .data base i
private def freshBase : Solidity.Storage.Loc := part 8
private def header : Solidity.Storage.Loc := part 11
private def tail (i : Nat) : Solidity.Storage.Loc := .data header i
private def word (i : Fin 256) : Semantics.Word := ⟨i.val,by have h:=i.isLt; simp only [PrimTy.inRange,decide_eq_true_eq]; omega⟩
private def captured : Store := fun l =>
 if l=base then word 2 else if l=part 0 then word 1 else if l=part 1 then word 53 else if l=part 2 then word 71 else
 if l=part 3 then word 0 else if l=part 4 then word 0 else if l=part 5 then word 17 else if l=part 6 then word 23 else if l=part 7 then word 0 else
 if l=part 8 then word 1 else if l=part 9 then word 53 else if l=part 10 then word 71 else if l=part 11 then word 2 else
 if l=tail 0 then word 99 else if l=tail 1 then word 77 else word 87
private def numeric : WordStore := fun a =>
 if a=0 then word 2 else if a=16 then word 1 else if a=17 then word 53 else if a=18 then word 71 else
 if a=19 then word 0 else if a=20 then word 0 else if a=21 then word 17 else if a=22 then word 23 else if a=23 then word 0 else
 if a=24 then word 1 else if a=25 then word 53 else if a=26 then word 71 else if a=27 then word 2 else
 if a=64 then word 99 else if a=65 then word 77 else word 87
private def hash (p : Solidity.Storage.Pre) : Nat := if p=.data 0 then 16 else if p=.data 27 then 64 else 0
private def preimages : List Solidity.Storage.Pre := [.data 0,.data 27]
private def locations : List Solidity.Storage.Loc :=
 [base,part 0,part 1,part 2,part 3,part 4,part 5,part 6,part 7,part 8,part 9,part 10,part 11,tail 0,tail 1,tail 4]
private theorem run : FiniteRun 128 16 1 hash preimages locations := by
 constructor
 · intro p; simp only [hash]; split <;> first | decide | (split <;> decide)
 · decide
 · decide
 · decide
 · intro l member
   simp only [locations,List.mem_cons,List.not_mem_nil,or_false] at member
   rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
    simp only [base,part,header,tail,Solidity.Storage.Loc.Bounded] <;> decide
 · intro l member
   simp only [locations,List.mem_cons,List.not_mem_nil,or_false] at member
   rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> decide
private def pre := AggregatePopFrames.indexPath (G:=graph) (E:=T) old.length
private theorem before : Represented old [.length .nil] base captured := by
 intro q member
 have same:=List.mem_singleton.mp member; subst q
 refine ⟨True.intro,⟨by decide,by decide⟩,?_⟩
 intro value observed
 change some (word 2)=some value at observed
 cases observed
 rfl
private theorem initial : Transport 128 hash locations captured numeric := by
 intro l member
 simp only [locations,List.mem_cons,List.not_mem_nil,or_false] at member
 rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> rfl
private theorem covered : ∀ q ∈ CopyDefaults.demands graph T ++ queries, q.location (pathLoc pre base) ∈ locations := by
 intro q member
 change q ∈ [.word flag,.word (pair (ix 0)),.word (pair (ix 1)),.length children] ++ queries at member
 simp only [queries,List.mem_append,List.mem_cons,List.not_mem_nil,or_false] at member
 rcases member with (rfl | rfl | rfl | rfl) | (rfl | rfl | rfl | rfl | rfl | rfl | rfl) <;> decide
private theorem supported : ∀ q ∈ queries, q.supported := by
 intro q member
 simp only [queries,List.mem_cons,List.not_mem_nil,or_false] at member
 rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
  simp only [Query.supported,PathSupported,StepSupported,descendant,children,flag,pair,TypeGraph.Path.append] <;> decide
private theorem fitting : ∀ l ∈ locations, TargetOperations.KeysFit l := by
 intro l member
 simp only [locations,List.mem_cons,List.not_mem_nil,or_false] at member
 rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> exact True.intro
private noncomputable def target : Evm.Machine :=
 {Evm.Machine.init (fun _ => 19) ⟨7,by decide⟩ with
 store := ⟨fun slot => TargetOperations.encodeWord (captured (Solidity.Storage.ofSlot slot))⟩
 stack := [.val ⟨23,by decide⟩,.slot (.root 9)]
 mem := fun _ => .val ⟨31,by decide⟩
 caller := ⟨13,by decide⟩
 timestamp := ⟨53,by decide⟩}
private noncomputable def middleTarget : Evm.Machine := {target with store := Evm.WordStore.write target.store (.root 0) 3}
private def middleNumeric := writeWord numeric 0 (word 3)
private def middleStore := Representation.write captured base (word 3)
private noncomputable def output := TargetDefaultInit.afterInit graph T freshBase True.intro middleTarget
private noncomputable def numericOutput := CopyDefaults.numericInit (N:=128) graph T freshBase hash middleNumeric
private noncomputable def storeOutput := (CopyDefaults.updates graph T freshBase).foldl (fun s op => Representation.write s op.1 op.2) middleStore
private noncomputable def program := TargetHeaderPush.code (.root 0) ++ TargetDefaultInit.code graph T permit freshBase True.intro
private def outQueries : List (Query graph (.array T)) := .length .nil :: queries.map (Query.prefix pre)

/-- Full actual source/numeric/target composition, OLD header evidence only.
Fresh inline header/fields are dirty: untouched-history premise is absent. -/
theorem certificate :
 execute graph T 128 hash base numeric=some numericOutput ∧
 Evm.run program target=.ok output 0 ∧
 Represented result outQueries base storeOutput ∧
 Transport 128 hash locations storeOutput numericOutput ∧
 (∀ l (member : l ∈ locations), output.store.cells (TargetOperations.toSlot l (fitting l member))=TargetOperations.encodeWord (numericOutput (l.word 128 hash))) := by
 apply complete old result rfl rfl permit queries supported base True.intro run captured numeric target before initial (by decide) covered (by decide) fitting
 intro l member
 change TargetOperations.encodeWord (captured (Solidity.Storage.ofSlot (TargetOperations.toSlot l _)))=_
 rw [TargetOperations.ofSlot_toSlot]
private def prefixQuery (i : Index) (q : Query graph T) := q.prefix (AggregatePopFrames.indexPath i)
private def contextQueries : List (Query graph (.array T)) :=
 ([Query.word flag,.word (pair (ix 0)),.word (pair (ix 1)),.length children].map (prefixQuery (ix 0))) ++
 ([Query.word flag,.word (pair (ix 0)),.word (pair (ix 1)),.length children].map (prefixQuery (ix 1)))
private def graphView (v : Value graph (.array T)) :=
 (v.length.val,v.extent.val,outQueries.map (fun q => q.read v),contextQueries.map (fun q => q.read v),
  ((pre.append flag).readLive Value.dflt v).map (fun x => PrimTy.toWord (p:=.bool) x.head))
private def numericView (s : WordStore) := [0,16,17,18,19,20,21,22,23,24,25,26,27,64,65,68,127].map s
private def slots : List Evm.Slot := [.root 0,.data (.root 0) 0,.data (.root 0) 1,.data (.root 0) 2,.data (.root 0) 3,.data (.root 0) 4,.data (.root 0) 5,.data (.root 0) 6,.data (.root 0) 7,.data (.root 0) 8,.data (.root 0) 9,.data (.root 0) 10,.data (.root 0) 11,.data (.data (.root 0) 11) 0,.data (.data (.root 0) 11) 1,.data (.data (.root 0) 11) 4,.root 127]
private def targetView (m : Evm.Machine) := slots.map (fun s => m.store.cells s)
private def context (m : Evm.Machine) := (m.stack,m.mem 0,m.bal m.self,m.bal₀ m.self,m.self,m.caller,m.callvalue,m.timestamp,m.accepts m.self m.self)

/-- COMPLETE ordered old/fresh graph queries and raw numeric evolution, including
live-alias change, preserved old contexts and nonlive dirty99/77/nextnode87. -/
theorem ordered :
 (inlineSize graph T,pathLoc pre base,graphView old,graphView result,
  numericView numeric,numericView middleNumeric,numericView numericOutput) =
 (4,part 8,
  (2,2,[some (word 2),none,none,none,none,none,none,none],
   [some (word 1),some (word 53),some (word 71),some (word 0),some (word 0),some (word 17),some (word 23),some (word 0)],none),
  (3,3,[some (word 3),none,some (word 0),some (word 0),some (word 0),some (word 0),none,some (word 0)],
   [some (word 1),some (word 53),some (word 71),some (word 0),some (word 0),some (word 17),some (word 23),some (word 0)],some (word 0)),
  [word 2,word 1,word 53,word 71,word 0,word 0,word 17,word 23,word 0,word 1,word 53,word 71,word 2,word 99,word 77,word 87,word 87],
  [word 3,word 1,word 53,word 71,word 0,word 0,word 17,word 23,word 0,word 1,word 53,word 71,word 2,word 99,word 77,word 87,word 87],
  [word 3,word 1,word 53,word 71,word 0,word 0,word 17,word 23,word 0,word 0,word 0,word 0,word 0,word 99,word 77,word 87,word 87]) := rfl

/-- Complete actual target vectors correspond to numeric evolution and preserve
all Machine context. No numeric-address/ordinary Source bridge is inferred. -/
theorem target_ordered :
 (targetView target,targetView middleTarget,targetView output,context middleTarget,context output)=
 ([word 2,word 1,word 53,word 71,word 0,word 0,word 17,word 23,word 0,word 1,word 53,word 71,word 2,word 99,word 77,word 87,word 87].map TargetOperations.encodeWord,
  [word 3,word 1,word 53,word 71,word 0,word 0,word 17,word 23,word 0,word 1,word 53,word 71,word 2,word 99,word 77,word 87,word 87].map TargetOperations.encodeWord,
  [word 3,word 1,word 53,word 71,word 0,word 0,word 17,word 23,word 0,word 0,word 0,word 0,word 0,word 99,word 77,word 87,word 87].map TargetOperations.encodeWord,
  context target,context target) := rfl

private noncomputable def wrongStore := (CopyDefaults.updates graph T (part 2)).foldl (fun s op => Representation.write s op.1 op.2) middleStore
private noncomputable def wrongNumeric := CopyDefaults.numericInit (N:=128) graph T (part 2) hash middleNumeric
private noncomputable def wrongTarget := TargetDefaultInit.afterInit graph T (part 2) True.intro middleTarget
/-- Wrong one-word stride executes, but corrupts old cells and leaves the NEW
flag dirty1 where independent allocation reads0. Rejecting it is essential. -/
theorem wrong_stride :
 Evm.run (TargetHeaderPush.code (.root 0) ++ TargetDefaultInit.code graph T permit (part 2) True.intro) target=.ok wrongTarget 0 ∧
 (wrongNumeric 18,wrongNumeric 24)=(word 0,word 1) ∧
 ¬ Represented result outQueries base wrongStore := by
 refine ⟨?_,rfl,?_⟩
 · rw [Evm.run_append_ok (m' := middleTarget) (by rw [TargetHeaderPush.run_current]; rfl)]
   exact TargetDefaultInit.run_writes _ _ _
 · intro alleged
   have member : prefixQuery (ix 2) (.word flag) ∈ outQueries :=
    List.mem_cons_of_mem _ (List.mem_map.mpr ⟨.word flag,List.mem_cons_of_mem _ List.mem_cons_self,rfl⟩)
   have bad:=(alleged _ member).2.2 (word 0) rfl
   change word 1=word 0 at bad
   have impossible:=congrArg (fun w : Semantics.Word => w.val) bad
   change (1:Int)=0 at impossible
   omega

/-- Actual SLOAD of new flag/fixed pair and outer header reflects the successful
independent graph operation; absent recursive tails remain physical garbage. -/
theorem readbacks :
 Evm.run (TargetOperations.readCode (.root 0)) output=.ok {output with stack := .val (TargetOperations.encodeWord (word 3)) :: output.stack} 0 ∧
 Evm.run (TargetOperations.readCode (.data (.root 0) 9)) output=.ok {output with stack := .val (TargetOperations.encodeWord (word 0)) :: output.stack} 0 ∧
 output.store (.data (.data (.root 0) 11) 0)=99 ∧ output.store (.data (.data (.root 0) 11) 1)=77 := ⟨rfl,rfl,rfl,rfl⟩

private def fullNumeric := writeWord numeric 0 (lengthWord (2^256-1) (by decide))
private noncomputable def fullTarget := {target with store := Evm.WordStore.write target.store (.root 0) (Evm.W-1)}
/-- Existing full-word guard stops before actual initialization, not a new cap
or proof of enclosing world/catch rollback. -/
theorem capacity_failure : execute graph T 128 hash base fullNumeric=none ∧
 Evm.run program fullTarget=.revert := by
 constructor
 · rw [execute_failure]
   change 2^256≤2^256-1+1
   have positive : 0<2^256 := by decide
   omega
 · apply Evm.run_append_revert
   rw [TargetHeaderPush.run_current]
   rfl

/-- Both OLD populated contexts retain their PUBLIC owners after the actual
new-block initialization, not only their displayed logical/raw vectors. -/
theorem contexts_owned : Represented old contextQueries base captured ∧
 Represented result contextQueries base storeOutput := by
 constructor
 all_goals
  intro q member
  change q ∈ [prefixQuery (ix 0) (.word flag),prefixQuery (ix 0) (.word (pair (ix 0))),prefixQuery (ix 0) (.word (pair (ix 1))),prefixQuery (ix 0) (.length children),
   prefixQuery (ix 1) (.word flag),prefixQuery (ix 1) (.word (pair (ix 0))),prefixQuery (ix 1) (.word (pair (ix 1))),prefixQuery (ix 1) (.length children)] at member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  all_goals refine ⟨?_,?_,?_⟩
  all_goals first
   | exact True.intro
   | (simp only [Query.supported,Query.prefix,AggregatePopFrames.indexPath,prefixQuery,flag,pair,children,TypeGraph.Path.append,PathSupported,StepSupported]; decide)
   | (change (0:Nat)≤lmax ∧ (0:Nat)≤lmax; constructor <;> omega)
   | (intro value observed; have same:=Option.some.inj observed; subst value; rfl)

/-- info: 'Solidity.Backend.StorageOps.FreshDefaultPush.Controls.contexts_owned' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in #print axioms contexts_owned
/-- info: 'Solidity.Backend.StorageOps.FreshDefaultPush.Controls.certificate' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in #print axioms certificate
/-- info: 'Solidity.Backend.StorageOps.FreshDefaultPush.Controls.ordered' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in #print axioms ordered
/-- info: 'Solidity.Backend.StorageOps.FreshDefaultPush.Controls.target_ordered' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in #print axioms target_ordered
/-- info: 'Solidity.Backend.StorageOps.FreshDefaultPush.Controls.wrong_stride' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in #print axioms wrong_stride
/-- info: 'Solidity.Backend.StorageOps.FreshDefaultPush.Controls.readbacks' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in #print axioms readbacks
/-- info: 'Solidity.Backend.StorageOps.FreshDefaultPush.Controls.capacity_failure' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in #print axioms capacity_failure
end Solidity.Backend.StorageOps.FreshDefaultPush.Controls
