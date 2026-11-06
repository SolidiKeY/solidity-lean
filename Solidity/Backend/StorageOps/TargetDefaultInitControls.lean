import Solidity.Backend.StorageOps.TargetDefaultInit

/-! Actual schema-directed default instructions for a guarded recursive node,
fixed children and a dynamic header. Dirty nonlive raw tails stay untouched;
this is initialization, not Source delete/allocation/world semantics. -/
namespace Solidity.Backend.StorageOps.TargetDefaultInit.Controls
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
private def base : Solidity.Storage.Loc := .data (.root 0) 0
private def root : Solidity.Storage.Loc := .root 0
private def header : Solidity.Storage.Loc := base.add 3
private def tail (i : Nat) : Solidity.Storage.Loc := .data header i
private def word (i : Fin 256) : Semantics.Word := ⟨i.val,by have h:=i.isLt; simp only [PrimTy.inRange,decide_eq_true_eq]; omega⟩
private def captured : Store := fun l =>
 if l=base then word 1 else if l=base.add 1 then word 53 else if l=base.add 2 then word 71 else
 if l=header then word 2 else if l=tail 0 then word 99 else if l=tail 1 then word 77 else word 87
private def numeric : WordStore := fun a =>
 if a=8 then word 1 else if a=9 then word 53 else if a=10 then word 71 else if a=11 then word 2 else
 if a=32 then word 99 else if a=33 then word 77 else word 87
private def hash (p : Solidity.Storage.Pre) : Nat := if p=.data 0 then 8 else if p=.data 11 then 32 else 0
private def preimages : List Solidity.Storage.Pre := [.data 0,.data 11]
private def locations : List Solidity.Storage.Loc := [base,base.add 1,base.add 2,header,tail 0,tail 1,tail 4,root]
private theorem run : FiniteRun 64 8 1 hash preimages locations := by
 constructor
 · intro p; simp only [hash]; split <;> first | decide | (split <;> decide)
 · decide
 · decide
 · decide
 · intro l member
   simp only [locations,List.mem_cons,List.not_mem_nil,or_false] at member
   rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp only [base,header,tail,root,Solidity.Storage.Loc.add,Solidity.Storage.Loc.Bounded] <;> decide
 · intro l member
   simp only [locations,List.mem_cons,List.not_mem_nil,or_false] at member
   rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> decide
private theorem covered : ∀ q ∈ CopyDefaults.demands graph T ++ queries, q.location base ∈ locations := by
 intro q member
 change q ∈ [.word flag,.word (pair (ix 0)),.word (pair (ix 1)),.length children] ++ queries at member
 simp only [queries,List.mem_append,List.mem_cons,List.not_mem_nil,or_false] at member
 rcases member with (rfl | rfl | rfl | rfl) | (rfl | rfl | rfl | rfl | rfl | rfl | rfl) <;> decide
private theorem supported : ∀ q ∈ queries, q.supported := by
 intro q member
 simp only [queries,List.mem_cons,List.not_mem_nil,or_false] at member
 rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
  simp only [Query.supported,PathSupported,StepSupported,descendant,children,flag,pair,TypeGraph.Path.append] <;> decide
private theorem initial : Transport 64 hash locations captured numeric := by
 intro l member
 simp only [locations,List.mem_cons,List.not_mem_nil,or_false] at member
 rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> rfl
private theorem fitting : ∀ l ∈ locations, TargetOperations.KeysFit l := by
 intro l member
 simp only [locations,List.mem_cons,List.not_mem_nil,or_false] at member
 rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> exact True.intro
private noncomputable def target : Evm.Machine :=
 {Evm.Machine.init (fun _ => 19) ⟨7,by decide⟩ with
 store := ⟨fun slot => TargetOperations.encodeWord (captured (Solidity.Storage.ofSlot slot))⟩
 stack := [.val ⟨23,by decide⟩,.slot (.root 9)]
 mem := fun _ => .val ⟨31,by decide⟩
 caller := ⟨13,by decide⟩
 timestamp := ⟨53,by decide⟩}
private noncomputable def output := afterInit graph T base True.intro target
private noncomputable def numericOutput := CopyDefaults.numericInit (N:=64) graph T base hash numeric
private noncomputable def storeOutput := (CopyDefaults.updates graph T base).foldl (fun s op => Representation.write s op.1 op.2) captured

/-- Genuine full certificate from OLD raw Transport and target agreement,
not old/default owner or final relation assumptions. -/
theorem certificate :
 Evm.run (code graph T permit base True.intro) target=.ok output 0 ∧
 Represented (Value.dflt T) queries base storeOutput ∧
 Transport 64 hash locations storeOutput numericOutput ∧
 (∀ l (member : l ∈ locations), output.store.cells (TargetOperations.toSlot l (fitting l member))=TargetOperations.encodeWord (numericOutput (l.word 64 hash))) ∧
 (∀ q ∈ queries, ∀ w, q.read (Value.dflt T)=some w →
 Evm.run (TargetOperations.readCode (TargetOperations.toSlot (q.location base) (TargetOperations.query_keysFit q base True.intro))) output=
 .ok {output with stack := .val (TargetOperations.encodeWord w) :: output.stack} 0) := by
 apply complete graph T permit queries supported base True.intro run captured numeric target initial covered fitting
 intro l member
 change TargetOperations.encodeWord (captured (Solidity.Storage.ofSlot (TargetOperations.toSlot l _)))=_
 rw [TargetOperations.ofSlot_toSlot]
private def slots : List Evm.Slot := [.data (.root 0) 0,.data (.root 0) 1,.data (.root 0) 2,.data (.root 0) 3,.data (.data (.root 0) 3) 0,.data (.data (.root 0) 3) 1,.data (.data (.root 0) 3) 4,.root 0,.root 63]
private def targetView (m : Evm.Machine) := slots.map (fun s => m.store.cells s)
private def numericView (s : WordStore) := [8,9,10,11,32,33,36,0,63].map s
private def context (m : Evm.Machine) := (m.stack,m.mem 0,m.bal m.self,m.bal₀ m.self,m.self,m.caller,m.callvalue,m.timestamp,m.accepts m.self m.self)

/-- COMPLETE ordered source/default query outcomes, actual emitted and numeric
words. Recursive dynamic child gets header0 ONLY; raw99/77 remain nonlive. -/
theorem ordered :
 (queries.map (fun q => q.read (Value.dflt T)),
  (Query.word (pair (ix 2))).read (Value.dflt T),
  targetView target,targetView output,numericView numeric,numericView numericOutput,
  context output,(code graph T permit base True.intro).length) =
 ([none,some (word 0),some (word 0),some (word 0),some (word 0),none,some (word 0)],none,
  [TargetOperations.encodeWord (word 1),TargetOperations.encodeWord (word 53),TargetOperations.encodeWord (word 71),TargetOperations.encodeWord (word 2),TargetOperations.encodeWord (word 99),TargetOperations.encodeWord (word 77),TargetOperations.encodeWord (word 87),TargetOperations.encodeWord (word 87),TargetOperations.encodeWord (word 87)],
  [TargetOperations.encodeWord (word 0),TargetOperations.encodeWord (word 0),TargetOperations.encodeWord (word 0),TargetOperations.encodeWord (word 0),TargetOperations.encodeWord (word 99),TargetOperations.encodeWord (word 77),TargetOperations.encodeWord (word 87),TargetOperations.encodeWord (word 87),TargetOperations.encodeWord (word 87)],
  [word 1,word 53,word 71,word 2,word 99,word 77,word 87,word 87,word 87],
  [word 0,word 0,word 0,word 0,word 99,word 77,word 87,word 87,word 87],context target,12) := rfl

/-- Whole-Machine context and EVERY ungenerated symbolic target slot frame. -/
theorem frames : {output with store := target.store}=target ∧
 ∀ observer, (∀ op (member : op ∈ CopyDefaults.updates graph T base), observer ≠ TargetOperations.toSlot op.1 (updates_fit graph T base True.intro op member)) →
 output.store observer=target.store observer :=
 ⟨context_writes _ _ _,fun observer apart => outside_writes _ _ _ observer apart⟩

/-- Omitted fixed-cell initialization is FALSE despite the dynamic header0:
actual reduced program leaves dirty53 where the independent default reads0. -/
theorem omitted_negative :
 Evm.run (TargetOperations.writeCode (.data (.root 0) 3) (word 0)) target=
 .ok {target with store := Evm.WordStore.write target.store (.data (.root 0) 3) 0} 0 ∧
 ¬ Represented (Value.dflt T) queries base (Representation.write captured header (word 0)) := by
 refine ⟨rfl,?_⟩
 intro alleged
 have member : Query.word (pair (ix 0)) ∈ queries :=
  List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ List.mem_cons_self)))
 have bad := (alleged _ member).2.2 (word 0) rfl
 change word 53=word 0 at bad
 have impossible:=congrArg (fun w : Semantics.Word => w.val) bad
 change (53:Int)=0 at impossible
 omega

/-- Dynamic default initialization is not delete: changing nonlive tails would
contradict the exact outside frame. Actual successful SLOAD reads both fixed
zeros, while malformed fixed2 and absent recursive children stay logical None. -/
theorem readbacks :
 Evm.run (TargetOperations.readCode (.data (.root 0) 1)) output=
 .ok {output with stack := .val (TargetOperations.encodeWord (word 0)) :: output.stack} 0 ∧
 Evm.run (TargetOperations.readCode (.data (.root 0) 2)) output=
 .ok {output with stack := .val (TargetOperations.encodeWord (word 0)) :: output.stack} 0 ∧
 output.store (.data (.data (.root 0) 3) 0)=99 ∧ output.store (.data (.data (.root 0) 3) 1)=77 := ⟨rfl,rfl,rfl,rfl⟩

/-- Original mapping refusal remains: no new permit/profile/exclusion is added.
The raw empty update list cannot supply mapping default representation. -/
theorem mapping_boundary :
 (CopyPermit.check graph (.mapping .bool (.prim .bool)) (fun _ => true)).isNone=true ∧
 CopyDefaults.demands graph (.mapping .bool (.prim .bool))=[] ∧
 (∀ _permit : CopyPermit graph (.mapping .bool (.prim .bool)), False) :=
 ⟨by decide,rfl,fun p => CopyPermit.no_mapping p⟩

/-- info: 'Solidity.Backend.StorageOps.TargetDefaultInit.Controls.certificate' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in #print axioms certificate
/-- info: 'Solidity.Backend.StorageOps.TargetDefaultInit.Controls.ordered' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in #print axioms ordered
/-- info: 'Solidity.Backend.StorageOps.TargetDefaultInit.Controls.frames' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in #print axioms frames
/-- info: 'Solidity.Backend.StorageOps.TargetDefaultInit.Controls.omitted_negative' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in #print axioms omitted_negative
/-- info: 'Solidity.Backend.StorageOps.TargetDefaultInit.Controls.readbacks' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in #print axioms readbacks
/-- info: 'Solidity.Backend.StorageOps.TargetDefaultInit.Controls.mapping_boundary' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms mapping_boundary
end Solidity.Backend.StorageOps.TargetDefaultInit.Controls
