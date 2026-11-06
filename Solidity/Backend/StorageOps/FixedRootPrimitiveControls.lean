import Solidity.Backend.StorageOps.FixedRootPrimitive

/-! ROOT runtime fixed operations at a retained outer array child. Actual
logical retained access is separated from live access and from Source lvalues. -/
namespace Solidity.Backend.StorageOps.FixedRootPrimitive.Controls
open TypeGraph Solidity.Storage Solidity.Storage.Representation Solidity.Storage.Representation.Graph
private def graph : Schema 0 where
 origin := "v10-fixed-primitive"
 declId := fun i => nomatch i
 declId_injective := by intro i; exact Fin.elim0 i
 name := fun i => nomatch i
 fields := fun i => nomatch i
 rank := fun i => nomatch i
 nonempty := by intro i; exact Fin.elim0 i
 distinct := by intro i; exact Fin.elim0 i
 guarded := by intro i; exact Fin.elim0 i
private def size : FixedSize := ⟨3,by decide⟩
private def ix (i : Fin 4) : Index := ⟨i.val,by have bound:=i.isLt; omega⟩
private def w (x : Fin 256) : Semantics.Word := lengthWord x.val (by have bound:=x.isLt; omega)

private abbrev T : TypeGraph.Ty 0 := .fixed (.prim .uint) size
private def leaf (a b c : Semantics.Word) : Value graph T := .fixed fun i =>
 if i.val=1 then (if b.val=0 then .absent else .present (.prim b)) else .present (.prim (if i.val=0 then a else c))
private def old : Value graph T := leaf (w 53) (w 0) (w 71)
private def root : Value graph (.array T) := .array ⟨2,by decide⟩ (ix 1) (by decide)
 (fun i => .present (if i.val=0 then leaf (w 7) (w 17) (w 23) else old))
private def pre : TypeGraph.Path graph (.array T) T := .cons (.index (ix 1)) .nil
private def dst := pre.append (TargetFixedPrimitive.path (p:=PrimTy.uint) (ix 1))
private def result := (root.save dst (.prim (w 71))).getD root
private def path (a b : Fin 4) : TypeGraph.Path graph (.array T) (.prim .uint) :=
 .cons (.index (ix a)) (TargetFixedPrimitive.path (ix b))
private def q (a b : Fin 4) : Query graph (.array T) := .word (path a b)
private def contexts := [q 0 1,q 1 0,q 1 2]
private def observations := [.length .nil,q 0 0,q 0 1,q 0 2,q 1 0,q 1 1,q 1 2,q 1 3,q 2 0]
private def base : Solidity.Storage.Loc := .root 0
private def part (i : Nat) : Solidity.Storage.Loc := .data base i
private def locations := [base,.root 1,part 0,part 1,part 2,part 3,part 4,part 5,part 6,part 7,part 8]
private def hash (_ : Solidity.Storage.Pre) : Nat := 16
private def store : Store := fun l => if l=base then w 1 else if l=.root 1 then w 109 else
 if l=part 0 then w 7 else if l=part 1 then w 17 else if l=part 2 then w 23 else
 if l=part 3 then w 53 else if l=part 5 then w 71 else if l=part 6 then w 87 else if l=part 8 then w 99 else w 0
private def numeric : WordStore := fun a => if a=0 then w 1 else if a=1 then w 109 else
 if a=16 then w 7 else if a=17 then w 17 else if a=18 then w 23 else
 if a=19 then w 53 else if a=21 then w 71 else if a=22 then w 87 else if a=24 then w 99 else w 0
private noncomputable def target : Evm.Machine :=
 {Evm.Machine.init (fun _ => 19) ⟨7,by decide⟩ with
 store:=⟨fun slot => TargetOperations.encodeWord (store (Solidity.Storage.ofSlot slot))⟩
 stack:=[.val ⟨23,by decide⟩,.slot (.root 9)]
 mem:=fun _ => .val ⟨31,by decide⟩
 caller:=⟨13,by decide⟩
 timestamp:=⟨53,by decide⟩}
private def afterStore := Representation.write store (part 4) (w 71)
private def afterNumeric := writeWord numeric 20 (w 71)
private noncomputable def output := {target with store:=Evm.WordStore.write target.store (.data (.root 0) 4) 71}
private theorem finite : FiniteRun 64 16 2 hash [.data 0] locations := by
 constructor
 · intro p; change 16<64; decide
 · decide
 · decide
 · decide
 · intro l member
   simp only [locations,List.mem_cons,List.not_mem_nil,or_false] at member
   rcases member with rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl <;> simp only [part,base,Solidity.Storage.Loc.Bounded] <;> decide
 · intro l member
   simp only [locations,List.mem_cons,List.not_mem_nil,or_false] at member
   rcases member with rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl <;> decide
private theorem transported : Transport 64 hash locations store numeric := by
 intro l member
 simp only [locations,List.mem_cons,List.not_mem_nil,or_false] at member
 rcases member with rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl <;> rfl
private theorem fitting : ∀ l ∈ locations,TargetOperations.KeysFit l := by
 intro l member
 simp only [locations,List.mem_cons,List.not_mem_nil,or_false] at member
 rcases member with rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl <;> exact True.intro
private theorem agreement : ∀ l (member : l ∈ locations),target.store.cells (TargetOperations.toSlot l (fitting l member))=TargetOperations.encodeWord (store l) := by
 intro l member
 change TargetOperations.encodeWord (store (Solidity.Storage.ofSlot (TargetOperations.toSlot l (fitting l member))))=_
 rw [TargetOperations.ofSlot_toSlot]
private theorem owner : Represented root contexts base store := by
 intro query member
 simp only [contexts,List.mem_cons,List.not_mem_nil,or_false] at member
 rcases member with rfl|rfl|rfl
 all_goals refine ⟨?_,True.intro,?_⟩
 all_goals first
  | (change (1<lmax ∧ (1<size.val ∧ True)); decide)
  | (change (0<lmax ∧ (1<size.val ∧ True)); decide)
  | (change (1<lmax ∧ (0<size.val ∧ True)); decide)
  | (change (1<lmax ∧ (2<size.val ∧ True)); decide)
  | (intro value observed; have same:=Option.some.inj observed; subst value; rfl)
private theorem selectedOwner : Represented root ([.word (TargetFixedPrimitive.path (p:=PrimTy.uint) (m:=size) (ix 1))].map (Query.prefix pre)) base store := by
 intro query member
 have same : query=(Query.word (TargetFixedPrimitive.path (p:=PrimTy.uint) (m:=size) (ix 1))).prefix pre := by
  simp only [List.map_cons,List.map_nil,List.mem_singleton] at member
  exact member
 subst query
 refine ⟨?_,True.intro,?_⟩
 · change 1<lmax ∧ (1<size.val ∧ True); decide
 · intro value observed; have same:=Option.some.inj observed; subst value; rfl

theorem read_certificate :
 Evm.run (TargetFixedPrimitive.readCode size) {target with stack:=.val ⟨1,by decide⟩:: .slot (.data (.root 0) 3)::target.stack}=
 .ok {target with stack:=.val (TargetOperations.encodeWord (w 0))::target.stack} 0 ∧ numeric 20=w 0 := by
 exact FixedRootPrimitive.read root pre old (ix 1) (w 0) rfl rfl base True.intro store numeric hash locations target target.stack selectedOwner transported (by decide) rfl

theorem write_certificate :
 Evm.run (TargetFixedPrimitive.writeCode size) {target with stack:=.val ⟨1,by decide⟩:: .slot (.data (.root 0) 3):: .val (TargetOperations.encodeWord (w 71))::target.stack}=.ok output 0 ∧
 Represented result (.word dst::contexts) base afterStore ∧ Transport 64 hash locations afterStore afterNumeric ∧
 (∀ l (member : l ∈ locations),output.store.cells (TargetOperations.toSlot l (fitting l member))=TargetOperations.encodeWord (afterStore l)) := by
 apply FixedRootPrimitive.write finite root result pre old (ix 1) (w 71) rfl
  (by change 1<lmax ∧ True; decide) rfl contexts base True.intro store numeric target target.stack owner
 · intro query member
   simp only [contexts,List.mem_cons,List.not_mem_nil,or_false] at member
   rcases member with rfl|rfl|rfl
   · exact Apart.fork (.index _ _ (by decide)) _ _
   · exact Apart.under (.index (ix 1)) (Apart.fork (.fixed _ _ (by decide)) .nil .nil)
   · exact Apart.under (.index (ix 1)) (Apart.fork (.fixed _ _ (by decide)) .nil .nil)
 · intro query member
   simp only [contexts,List.mem_cons,List.not_mem_nil,or_false] at member
   rcases member with rfl|rfl|rfl <;> decide
 · exact transported
 · decide
 · exact agreement

theorem ordered :
 observations.map (fun query => (query.read root).map Subtype.val)=[some 1,some 7,some 17,some 23,some 53,some 0,some 71,none,none] ∧
 observations.map (fun query => (query.read result).map Subtype.val)=[some 1,some 7,some 17,some 23,some 53,some 71,some 71,none,none] ∧
 locations.map (fun l => (store l).val)=[1,109,7,17,23,53,0,71,87,0,99] ∧
 locations.map (fun l => (afterStore l).val)=[1,109,7,17,23,53,71,71,87,0,99] ∧
 locations.map (fun l => (numeric (l.word 64 hash)).val)=[1,109,7,17,23,53,0,71,87,0,99] ∧
 locations.map (fun l => (afterNumeric (l.word 64 hash)).val)=[1,109,7,17,23,53,71,71,87,0,99] ∧
 locations.attach.map (fun l => (target.store.cells (TargetOperations.toSlot l.val (fitting l.val l.property))).val)=[1,109,7,17,23,53,0,71,87,0,99] ∧
 locations.attach.map (fun l => (output.store.cells (TargetOperations.toSlot l.val (fitting l.val l.property))).val)=[1,109,7,17,23,53,71,71,87,0,99] ∧
 {output with store:=target.store}=target := by
 exact ⟨rfl,rfl,rfl,rfl,rfl,rfl,rfl,by decide,rfl⟩

/-- Retained identity is still logically readable but NOT live. The operation
certificate does not bypass an enclosing Source lvalue liveness check. -/
theorem retained_live : root.find dst=some (.prim (w 0)) ∧ result.find dst=some (.prim (w 71)) ∧
 dst.readLive Value.dflt root=none ∧ dst.readLive Value.dflt result=none ∧
 root.find (path 0 1)=some (.prim (w 17)) ∧ result.find (path 0 1)=some (.prim (w 17)) ∧
 root.find (path 2 0)=none ∧ result.find (path 2 0)=none ∧
 root.extent.val=2 ∧ result.extent.val=2 ∧ root.length.val=1 ∧ result.length.val=1 := by
 exact ⟨rfl,rfl,rfl,rfl,rfl,rfl,rfl,rfl,rfl,rfl,rfl,rfl⟩

theorem malformed : root.find (path 1 3)=none ∧ root.save (path 1 3) (.prim (w 71))=none ∧
 Evm.run (TargetFixedPrimitive.writeCode size) {target with stack:=.val ⟨3,by decide⟩:: .slot (.data (.root 0) 3):: .val (TargetOperations.encodeWord (w 71))::target.stack}=.revert := by
 refine ⟨rfl,rfl,?_⟩
 exact TargetFixedPrimitive.run_write size target target.stack (.data (.root 0) 3) (ix 3) (TargetOperations.encodeWord (w 71))

private noncomputable def wrong := {target with store:=Evm.WordStore.write target.store (.data (.root 0) 1) 71}
/-- Wrong captured outer prefix executes successfully but modifies the LIVE
sibling and leaves the intended retained child unchanged. -/
theorem wrong_prefix :
 Evm.run (TargetFixedPrimitive.writeCode size) {target with stack:=.val ⟨1,by decide⟩:: .slot (.data (.root 0) 0):: .val (TargetOperations.encodeWord (w 71))::target.stack}=.ok wrong 0 ∧
 locations.attach.map (fun l => (wrong.store.cells (TargetOperations.toSlot l.val (fitting l.val l.property))).val)=[1,109,7,71,23,53,0,71,87,0,99] ∧
 wrong.store (.data (.root 0) 4)≠output.store (.data (.root 0) 4) := by
 refine ⟨?_,by decide,by decide⟩
 exact TargetFixedPrimitive.run_write size target target.stack (.data (.root 0) 0) (ix 1) (TargetOperations.encodeWord (w 71))

/-- info: 'Solidity.Backend.StorageOps.FixedRootPrimitive.Controls.read_certificate' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in #print axioms read_certificate
/-- info: 'Solidity.Backend.StorageOps.FixedRootPrimitive.Controls.write_certificate' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in #print axioms write_certificate
/-- info: 'Solidity.Backend.StorageOps.FixedRootPrimitive.Controls.ordered' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in #print axioms ordered
/-- info: 'Solidity.Backend.StorageOps.FixedRootPrimitive.Controls.retained_live' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in #print axioms retained_live
/-- info: 'Solidity.Backend.StorageOps.FixedRootPrimitive.Controls.malformed' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in #print axioms malformed
/-- info: 'Solidity.Backend.StorageOps.FixedRootPrimitive.Controls.wrong_prefix' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in #print axioms wrong_prefix
end Solidity.Backend.StorageOps.FixedRootPrimitive.Controls
