import Solidity.Backend.StorageOps.FreshDefaultRoot

/-! Actual ROOT allocation below a mapping/recursive-node prefix. Published
representation and per-run numerical transport are inhabited, not assumed as
postconditions. Source-hashed trace to FiniteRun remains an external premise. -/
namespace Solidity.Backend.StorageOps.FreshDefaultRoot.Controls
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

private def word (i : Fin 256) : Semantics.Word := ⟨i.val,by have h:=i.isLt; simp only [PrimTy.inRange,decide_eq_true_eq]; omega⟩
private def node (value : Bool) (a b : PrimTy.uint.Denote) (tail : Value graph (.array T)) : Value graph T :=
 .node (fun pos => match pos with
 | .here => .prim value
 | .there .here => .fixed (fun i => .present (.prim (if i.val=0 then a else b)))
 | .there (.there .here) => tail
 | .there (.there (.there q)) => nomatch q)
private def old : Value graph (.array T) :=
 .array ⟨2,by decide⟩ (ix 2) (by decide) (fun i => .present
  (if i.val=0 then node true (word 53) (word 71) (Value.dflt (.array T))
   else node false (word 17) (word 23) (Value.dflt (.array T))))
private def next := (operationPush old).getD old
private def wrap : Nat → Value graph (.array T) → Value graph (.array T)
 | 0, leaf => leaf
 | depth+1, leaf => .array ⟨1,by decide⟩ (ix 1) (by decide)
   (fun _ => .present (node true (word 7) (word 17) (wrap depth leaf)))
private abbrev Root : TypeGraph.Ty 1 := .mapping .uint (.array T)
private def rootAt (depth : Nat) : Value graph Root := .mapping (fun k =>
 if k=word 0 then .present (wrap depth old) else if k=word 1 then .present (wrap 1 (Value.dflt (.array T))) else .absent)
private def keyPath (k : Fin 256) : TypeGraph.Path graph Root (.array T) := .cons (.key (word k)) .nil
private def loop : Nat → TypeGraph.Path graph (.array T) (.array T)
 | 0 => .nil
 | depth+1 => .cons (.index (ix 0)) (children.append (loop depth))
private def rootPath (depth : Nat) := (keyPath 0).append (loop depth)
private def root := rootAt 1
private def pre := rootPath 1
private def result := (pushAt root pre).getD root
private def childPre := AggregatePopFrames.indexPath (G:=graph) (E:=T) old.length
private def outside : List (Query graph Root) := [.length (keyPath 1),.length (keyPath 2)]
private def outputQueries : List (Query graph Root) :=
 ((.length .nil :: queries.map (Query.prefix childPre)).map (Query.prefix pre))++outside
private def base : Solidity.Storage.Loc := .root 0
private def arrayRoot (k : Nat) : Solidity.Storage.Loc := .hash k base 0
private def outerPart (i : Nat) : Solidity.Storage.Loc := .data (arrayRoot 0) i
private def arrayBase : Solidity.Storage.Loc := outerPart 3
private def part (i : Nat) : Solidity.Storage.Loc := .data arrayBase i
private def freshBase : Solidity.Storage.Loc := part 8
private def header : Solidity.Storage.Loc := part 11
private def tail (i : Nat) : Solidity.Storage.Loc := .data header i
private def sentinel : Solidity.Storage.Loc := .root 1
private def hash (p : Solidity.Storage.Pre) : Nat :=
 if p=.entry 0 0 then 16 else if p=.entry 1 0 then 96 else if p=.entry 2 0 then 112 else
 if p=.data 16 then 40 else if p=.data 43 then 64 else if p=.data 75 then 80 else 0
private def preimages : List Solidity.Storage.Pre := [.entry 0 0,.entry 1 0,.entry 2 0,.data 16,.data 43,.data 75]
private def locations : List Solidity.Storage.Loc :=
 [base,sentinel,arrayRoot 0,arrayRoot 1,arrayRoot 2,outerPart 0,outerPart 1,outerPart 2,outerPart 3,
  part 0,part 1,part 2,part 3,part 4,part 5,part 6,part 7,part 8,part 9,part 10,part 11,tail 0,tail 1,tail 4]
private def captured : Store := fun l =>
 if l=sentinel then word 109 else if l=arrayRoot 0 then word 1 else if l=arrayRoot 1 then word 1 else
 if l=outerPart 0 then word 1 else if l=outerPart 1 then word 7 else if l=outerPart 2 then word 17 else if l=arrayBase then word 2 else
 if l=part 0 then word 1 else if l=part 1 then word 53 else if l=part 2 then word 71 else
 if l=part 4 then word 0 else if l=part 5 then word 17 else if l=part 6 then word 23 else
 if l=part 8 then word 1 else if l=part 9 then word 53 else if l=part 10 then word 71 else if l=part 11 then word 2 else
 if l=tail 0 then word 99 else if l=tail 1 then word 77 else if l=tail 4 then word 87 else word 0
private def numeric : WordStore := fun a =>
 if a=1 then word 109 else if a=16 then word 1 else if a=96 then word 1 else
 if a=40 then word 1 else if a=41 then word 7 else if a=42 then word 17 else if a=43 then word 2 else
 if a=64 then word 1 else if a=65 then word 53 else if a=66 then word 71 else
 if a=68 then word 0 else if a=69 then word 17 else if a=70 then word 23 else
 if a=72 then word 1 else if a=73 then word 53 else if a=74 then word 71 else if a=75 then word 2 else
 if a=80 then word 99 else if a=81 then word 77 else if a=84 then word 87 else word 0
private theorem finite : FiniteRun 128 16 3 hash preimages locations := by
 constructor
 · intro p; simp only [hash]; split <;> first | decide | (split <;> first | decide | (split <;> first | decide | (split <;> first | decide | (split <;> first | decide | (split <;> decide)))))
 · decide
 · decide
 · decide
 · intro l member
   simp only [locations,List.mem_cons,List.not_mem_nil,or_false] at member
   rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
    simp only [base,sentinel,arrayRoot,outerPart,arrayBase,part,header,tail,Solidity.Storage.Loc.Bounded] <;> decide
 · intro l member
   simp only [locations,List.mem_cons,List.not_mem_nil,or_false] at member
   rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> decide
private theorem transported : Transport 128 hash locations captured numeric := by
 intro l member
 simp only [locations,List.mem_cons,List.not_mem_nil,or_false] at member
 rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> rfl
private theorem fitting : ∀ l ∈ locations,TargetOperations.KeysFit l := by
 intro l member
 simp only [locations,List.mem_cons,List.not_mem_nil,or_false] at member
 rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> first | exact True.intro | exact ⟨by decide,True.intro⟩
private noncomputable def target : Evm.Machine :=
 {Evm.Machine.init (fun _ => 19) ⟨7,by decide⟩ with
 store:=⟨fun slot => TargetOperations.encodeWord (captured (Solidity.Storage.ofSlot slot))⟩
 stack:=[.val ⟨23,by decide⟩,.slot (.root 9)]
 mem:=fun _ => .val ⟨31,by decide⟩
 caller:=⟨13,by decide⟩
 timestamp:=⟨53,by decide⟩}
private theorem agreement : ∀ l (member : l ∈ locations),target.store.cells (TargetOperations.toSlot l (fitting l member))=TargetOperations.encodeWord (captured l) := by
 intro l member
 change TargetOperations.encodeWord (captured (Solidity.Storage.ofSlot (TargetOperations.toSlot l (fitting l member))))=TargetOperations.encodeWord (captured l)
 rw [TargetOperations.ofSlot_toSlot]
private theorem before : Represented root (([.length .nil] : List (Query graph (.array T))).map (Query.prefix pre)) base captured := by
 intro q member
 have same : q=(Query.length (.nil : TypeGraph.Path graph (.array T) (.array T))).prefix pre := by
  simp only [List.map_cons,List.map_nil,List.mem_singleton] at member
  exact member
 subst q
 refine ⟨by change True ∧ (0<lmax ∧ (True ∧ True)); decide,⟨by decide,by decide⟩,?_⟩
 intro value observed
 change some (word 2)=some value at observed
 change word 2=value
 exact Option.some.inj observed
private theorem beforeOutside : Represented root outside base captured := by
 intro q member
 simp only [outside,List.mem_cons,List.not_mem_nil,or_false] at member
 rcases member with rfl|rfl
 · refine ⟨by change True ∧ True; decide,⟨by decide,by decide⟩,?_⟩
   intro value observed
   change some (word 1)=some value at observed
   change word 1=value
   exact Option.some.inj observed
 · refine ⟨by change True ∧ True; decide,⟨by decide,by decide⟩,?_⟩
   intro value observed
   change some (word 0)=some value at observed
   change word 0=value
   exact Option.some.inj observed
private theorem supported : ∀ q ∈ queries,q.supported := by
 intro q member
 simp only [queries,List.mem_cons,List.not_mem_nil,or_false] at member
 rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
  simp only [Query.supported,PathSupported,StepSupported,descendant,children,flag,pair,TypeGraph.Path.append] <;> decide
private theorem covered : ∀ q ∈ CopyDefaults.demands graph T ++ queries,q.location freshBase ∈ locations := by
 intro q member
 change q ∈ [.word flag,.word (pair (ix 0)),.word (pair (ix 1)),.length children] ++ queries at member
 simp only [queries,List.mem_append,List.mem_cons,List.not_mem_nil,or_false] at member
 rcases member with (rfl|rfl|rfl|rfl)|(rfl|rfl|rfl|rfl|rfl|rfl|rfl) <;> decide
private theorem apart : ∀ q ∈ outside,q.apart pre := by
 intro q member
 simp only [outside,List.mem_cons,List.not_mem_nil,or_false] at member
 rcases member with rfl|rfl
 · exact .fork (.key (word 0) (word 1) (by decide)) _ _
 · exact .fork (.key (word 0) (word 2) (by decide)) _ _
private theorem headerApart : ∀ q ∈ outside,q.location base≠arrayBase := by
 intro q member
 simp only [outside,List.mem_cons,List.not_mem_nil,or_false] at member
 rcases member with rfl|rfl <;> decide
private theorem initApart : ∀ q ∈ outside,∀ demand ∈ CopyDefaults.demands graph T,q.location base≠demand.location freshBase := by
 intro q member demand inside
 simp only [outside,List.mem_cons,List.not_mem_nil,or_false] at member
 change demand ∈ [.word flag,.word (pair (ix 0)),.word (pair (ix 1)),.length children] at inside
 rcases member with rfl|rfl <;>
  simp only [List.mem_cons,List.not_mem_nil,or_false] at inside <;>
  rcases inside with rfl|rfl|rfl|rfl <;> decide
private def middleStore := Representation.write captured arrayBase (word 3)
private def middleNumeric := writeWord numeric 43 (word 3)
private noncomputable def middleTarget := {target with store:=Evm.WordStore.write target.store (TargetOperations.toSlot arrayBase (by exact ⟨by decide,True.intro⟩)) 3}
private noncomputable def storeOutput := (CopyDefaults.updates graph T freshBase).foldl (fun s op => Representation.write s op.1 op.2) middleStore
private noncomputable def numericOutput := CopyDefaults.numericInit (N:=128) graph T freshBase hash middleNumeric
private noncomputable def output := TargetDefaultInit.afterInit graph T freshBase (by exact ⟨by decide,True.intro⟩) middleTarget
private noncomputable def program := TargetHeaderPush.code (TargetOperations.toSlot arrayBase (by exact ⟨by decide,True.intro⟩)) ++ TargetDefaultInit.code graph T permit freshBase (by exact ⟨by decide,True.intro⟩)

theorem certificate :
 ∃ next : Value graph (.array T),operationPush old=some next ∧ root.save pre next=some result ∧
 FreshDefaultPush.execute graph T 128 hash arrayBase numeric=some numericOutput ∧
 Evm.run program target=.ok output 0 ∧ result.find (pre.append childPre)=some (Value.dflt T) ∧
 Represented result outputQueries base storeOutput ∧ Transport 128 hash locations storeOutput numericOutput ∧
 (∀ l (member : l ∈ locations),output.store.cells (TargetOperations.toSlot l (fitting l member))=TargetOperations.encodeWord (numericOutput (l.word 128 hash))) := by
 obtain ⟨value,changed,saved,rest⟩ := complete root result pre old rfl rfl rfl permit queries supported outside base True.intro
  finite captured numeric target before beforeOutside apart headerApart initApart transported
  (by decide) covered (by decide) fitting agreement
 have lengthEq := (operationPush_header old value changed).1
 change value.length.val=3 at lengthEq
 have wordEq : lengthWord value.length.val value.length.isLt=word 3 := by
  apply Subtype.ext
  exact congrArg Int.ofNat lengthEq
 refine ⟨value,changed,saved,?_⟩
 simpa only [wordEq] using rest

theorem logical_observations :
 outputQueries.map (fun q => (q.read root).map Subtype.val)=
 [some 2,none,none,none,none,none,none,none,some 1,some 0] ∧
 outputQueries.map (fun q => (q.read result).map Subtype.val)=
 [some 3,none,some 0,some 0,some 0,some 0,none,some 0,some 1,some 0] := by
 constructor <;> rfl

theorem symbolic_observations :
 locations.map (fun l => (captured l).val)=
 [0,109,1,1,0,1,7,17,2,1,53,71,0,0,17,23,0,1,53,71,2,99,77,87] ∧
 locations.map (fun l => (storeOutput l).val)=
 [0,109,1,1,0,1,7,17,3,1,53,71,0,0,17,23,0,0,0,0,0,99,77,87] := by
 constructor <;> rfl

theorem numeric_observations :
 locations.map (fun l => (numeric (l.word 128 hash)).val)=
 [0,109,1,1,0,1,7,17,2,1,53,71,0,0,17,23,0,1,53,71,2,99,77,87] ∧
 locations.map (fun l => (numericOutput (l.word 128 hash)).val)=
 [0,109,1,1,0,1,7,17,3,1,53,71,0,0,17,23,0,0,0,0,0,99,77,87] := by
 constructor <;> rfl

theorem target_observations :
 locations.attach.map (fun l => (target.store.cells (TargetOperations.toSlot l.val (fitting l.val l.property))).val)=
 [0,109,1,1,0,1,7,17,2,1,53,71,0,0,17,23,0,1,53,71,2,99,77,87] ∧
 locations.attach.map (fun l => (output.store.cells (TargetOperations.toSlot l.val (fitting l.val l.property))).val)=
 [0,109,1,1,0,1,7,17,3,1,53,71,0,0,17,23,0,0,0,0,0,99,77,87] := by
 constructor <;> rfl

theorem context_preserved : {output with store:=target.store}=target := by rfl

private theorem loop_find (depth : Nat) (leaf : Value graph (.array T)) :
 (wrap depth leaf).find (loop depth)=some leaf := by
 induction depth with
 | zero => rfl
 | succ depth ih =>
   change (wrap depth leaf).find (loop depth)=some leaf
   exact ih
private theorem root_find (depth : Nat) : (rootAt depth).find (rootPath depth)=some old := by
 change TypeGraph.Path.read Value.dflt ((keyPath 0).append (loop depth)) (rootAt depth)=some old
 rw [TypeGraph.Path.read_append]
 change (wrap depth old).find (loop depth)=some old
 exact loop_find depth old

/-- Arbitrarily many demanded recursive nodes below a mapping, with actual
path capture/save and successful default child readback. Numerical layout at
these arbitrary depths still requires the finite-run premises of complete. -/
theorem arbitrary_depth (depth : Nat) :
 (rootAt depth).find (rootPath depth)=some old ∧
 ∃ changed : Value graph Root, pushAt (rootAt depth) (rootPath depth)=some changed ∧
 changed.find ((rootPath depth).append childPre)=some (Value.dflt T) := by
 refine ⟨root_find depth,?_⟩
 obtain ⟨changed,saved⟩ := prefix_save_exists (rootPath depth) (rootAt depth) old next (root_find depth)
 refine ⟨changed,?_,?_⟩
 · simp only [pushAt,modifyAt,root_find]
   change (some next).bind ((rootAt depth).save (rootPath depth))=some changed
   exact saved
 · change TypeGraph.Path.read Value.dflt ((rootPath depth).append childPre) changed=some (Value.dflt T)
   rw [TypeGraph.Path.read_append]
   change (changed.find (rootPath depth)).bind (fun value => value.find childPre)=_
   rw [Value.find_save _ _ _ _ saved]
   exact FreshDefaultPush.fresh_find old next rfl rfl

private noncomputable def wrongStore := (CopyDefaults.updates graph T (part 2)).foldl (fun s op => Representation.write s op.1 op.2) middleStore
private noncomputable def wrongTarget := TargetDefaultInit.afterInit graph T (part 2) (by exact ⟨by decide,True.intro⟩) middleTarget
/-- A wrong one-word stride executes but corrupts the OLD pair and leaves
all new allocation cells dirty; complete observations include older shadows. -/
theorem wrong_stride :
 Evm.run (TargetHeaderPush.code (TargetOperations.toSlot arrayBase (by exact ⟨by decide,True.intro⟩)) ++
  TargetDefaultInit.code graph T permit (part 2) (by exact ⟨by decide,True.intro⟩)) target=.ok wrongTarget 0 ∧
 locations.map (fun l => (wrongStore l).val)=
 [0,109,1,1,0,1,7,17,3,1,53,0,0,0,0,23,0,1,53,71,2,99,77,87] ∧
 locations.attach.map (fun l => (wrongTarget.store.cells (TargetOperations.toSlot l.val (fitting l.val l.property))).val)=
 [0,109,1,1,0,1,7,17,3,1,53,0,0,0,0,23,0,1,53,71,2,99,77,87] ∧
 ¬ Represented result outputQueries base wrongStore := by
 refine ⟨?_,rfl,rfl,?_⟩
 · rw [Evm.run_append_ok (m' := middleTarget) (by rw [TargetHeaderPush.run_current]; rfl)]
   exact TargetDefaultInit.run_writes _ _ _
 · intro alleged
   have member : ((Query.word flag).prefix childPre).prefix pre ∈ outputQueries := by
    apply List.mem_append_left
    apply List.mem_map.mpr
    refine ⟨(Query.word flag).prefix childPre,?_,rfl⟩
    apply List.mem_cons_of_mem
    exact List.mem_map.mpr ⟨.word flag,List.mem_cons_of_mem _ List.mem_cons_self,rfl⟩
   have bad := (alleged _ member).2.2 (word 0) rfl
   change word 1=word 0 at bad
   have impossible := congrArg (fun w : Semantics.Word => w.val) bad
   change (1:Int)=0 at impossible
   omega

/-- Defaulted mapping reads and exact malformed suffix failure; physical
older shadows are deliberately NOT inferred from failed logical reads. -/
theorem default_failure_readback :
 root.find (keyPath 2)=some (Value.dflt (.array T)) ∧
 pushAt root (pre.append (.cons (.index (ix 2)) children))=none ∧
 result.find (pre.append (childPre.append (descendant (ix 0))))=none ∧
 Evm.run (TargetOperations.readCode (TargetOperations.toSlot arrayBase (by exact ⟨by decide,True.intro⟩))) output=
 .ok {output with stack:=.val (TargetOperations.encodeWord (word 3))::output.stack} 0 ∧
 Evm.run (TargetOperations.readCode (TargetOperations.toSlot freshBase (by exact ⟨by decide,True.intro⟩))) output=
 .ok {output with stack:=.val (TargetOperations.encodeWord (word 0))::output.stack} 0 ∧
 output.store (TargetOperations.toSlot (tail 0) (by exact ⟨by decide,True.intro⟩))=99 := by
 exact ⟨rfl,rfl,rfl,rfl,rfl,rfl⟩

/-- info: 'Solidity.Backend.StorageOps.FreshDefaultRoot.Controls.certificate' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in #print axioms certificate
/-- info: 'Solidity.Backend.StorageOps.FreshDefaultRoot.Controls.logical_observations' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in #print axioms logical_observations
/-- info: 'Solidity.Backend.StorageOps.FreshDefaultRoot.Controls.symbolic_observations' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in #print axioms symbolic_observations
/-- info: 'Solidity.Backend.StorageOps.FreshDefaultRoot.Controls.numeric_observations' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in #print axioms numeric_observations
/-- info: 'Solidity.Backend.StorageOps.FreshDefaultRoot.Controls.target_observations' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in #print axioms target_observations
/-- info: 'Solidity.Backend.StorageOps.FreshDefaultRoot.Controls.context_preserved' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in #print axioms context_preserved
/-- info: 'Solidity.Backend.StorageOps.FreshDefaultRoot.Controls.arbitrary_depth' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in #print axioms arbitrary_depth
/-- info: 'Solidity.Backend.StorageOps.FreshDefaultRoot.Controls.wrong_stride' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in #print axioms wrong_stride
/-- info: 'Solidity.Backend.StorageOps.FreshDefaultRoot.Controls.default_failure_readback' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in #print axioms default_failure_readback
end Solidity.Backend.StorageOps.FreshDefaultRoot.Controls
