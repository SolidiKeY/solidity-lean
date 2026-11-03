import Solidity.Backend.StorageOps.TargetFixedPrimitive

/-! Inhabited fixed primitive runtime controls, complete ordered observations.
Physical absent-default zero follows OLD owner; wrong dynamic addressing is
executed independently and distinguished. No Source/compiler/world claim. -/
namespace Solidity.Backend.StorageOps.TargetFixedPrimitive.Controls
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
private def w (x : Fin 100) : Semantics.Word := lengthWord x.val (by have bound:=x.isLt; omega)
private def old : Value graph (.fixed (.prim .uint) size) := .fixed fun i =>
 if i.val=1 then .absent else .present (.prim (if i.val=0 then w 17 else w 53))
private def result : Value graph (.fixed (.prim .uint) size) := .fixed
 (Slots.write (fun i : Fin size.val => if i.val=1 then .absent else .present (.prim (if i.val=0 then w 17 else w 53))) ⟨1,by decide⟩ (.prim (w 71)))
private def q (i : Fin 4) : Query graph (.fixed (.prim .uint) size) := .word (path (ix i))
private def queries := [q 0,q 1,q 2,q 3]
private def contexts := [q 0,q 2]
private def base : Solidity.Storage.Loc := .root 0
private def store : Store := fun l => if l=.root 0 then w 17 else if l=.root 2 then w 53 else if l=.root 3 then w 99 else w 0
private def numeric : WordStore := fun a => if a=0 then w 17 else if a=2 then w 53 else if a=3 then w 99 else w 0
private def locations : List Solidity.Storage.Loc := [.root 0,.root 1,.root 2,.root 3]
private def hash (_ : Solidity.Storage.Pre) : Nat := 0
private def target : Evm.Machine :=
 { stack := [.val ⟨23,by decide⟩],
   store := .ofFn (fun slot => if slot = .root 0 then 17 else if slot = .root 2 then 53 else if slot = .root 3 then 99 else if slot = .data (.root 0) 2 then 87 else 0),
   mem := fun _ => .val ⟨41,by decide⟩,
   bal := fun _ => 43, bal₀ := fun _ => 47,
   caller := ⟨29,by decide⟩, callvalue := ⟨31,by decide⟩, timestamp := ⟨37,by decide⟩ }

private def afterStore := Representation.write store (.root 1) (w 71)
private def afterNumeric := writeWord numeric 1 (w 71)
private def afterTarget := {target with store:=Evm.WordStore.write target.store (.root 1) 71}
private def words (s : Store) := locations.map (fun l => (s l).val)
private def numbers (s : WordStore) := [s 0,s 1,s 2,s 3] |>.map (fun x => x.val)
private def cells (m : Evm.Machine) := [.root 0,.root 1,.root 2,.root 3,.data (.root 0) 2].map (fun l => m.store l)
private def observe (v : Value graph (.fixed (.prim .uint) size)) := queries.map (fun query => (query.read v).map (fun x => x.val))
private def context (m : Evm.Machine) := (m.stack,m.mem,m.bal,m.bal₀,m.self,m.accepts,m.caller,m.callvalue,m.timestamp)
private theorem owner : Represented old [q 0,q 1,q 2] base store := by
 intro query member
 simp only [List.mem_cons,List.not_mem_nil,or_false] at member
 rcases member with rfl|rfl|rfl
 · refine ⟨⟨by change 0 < size.val; decide,True.intro⟩,True.intro,?_⟩
   intro value observed; change some (w 17)=some value at observed; cases observed; rfl
 · refine ⟨⟨by change 1 < size.val; decide,True.intro⟩,True.intro,?_⟩
   intro value observed; change some (w 0)=some value at observed; cases observed; rfl
 · refine ⟨⟨by change 2 < size.val; decide,True.intro⟩,True.intro,?_⟩
   intro value observed; change some (w 53)=some value at observed; cases observed; rfl
private theorem finite : FiniteRun 16 4 4 hash [] locations := by
 constructor
 · intro pre; change 0<16; decide
 · decide
 · decide
 · decide
 · intro l member
   simp only [locations,List.mem_cons,List.not_mem_nil,or_false] at member
   rcases member with rfl|rfl|rfl|rfl <;> simp only [Solidity.Storage.Loc.Bounded] <;> decide
 · intro l member
   simp only [locations,List.mem_cons,List.not_mem_nil,or_false] at member
   rcases member with rfl|rfl|rfl|rfl <;> decide
private theorem transport : Transport 16 hash locations store numeric := by
 intro l member
 simp only [locations,List.mem_cons,List.not_mem_nil,or_false] at member
 rcases member with rfl|rfl|rfl|rfl <;> rfl
private theorem fitting : ∀ l ∈ locations,TargetOperations.KeysFit l := by
 intro l member
 simp only [locations,List.mem_cons,List.not_mem_nil,or_false] at member
 rcases member with rfl|rfl|rfl|rfl <;> exact True.intro
private theorem agreement : ∀ l (member : l ∈ locations),target.store.cells (TargetOperations.toSlot l (fitting l member))=TargetOperations.encodeWord (store l) := by
 intro l member
 simp only [locations,List.mem_cons,List.not_mem_nil,or_false] at member
 rcases member with rfl|rfl|rfl|rfl <;> rfl

theorem read_certificate : Evm.run (readCode size) {target with stack:=.val ⟨1,by decide⟩ :: .slot (.root 0) :: target.stack}=
 .ok {target with stack:=.val (TargetOperations.encodeWord (w 0)) :: target.stack} 0 ∧ numeric 1=w 0 := by
 exact complete_read old (ix 1) (w 0) rfl base True.intro store numeric hash locations target target.stack
  (fun query member => owner query (by have same:=List.mem_singleton.mp member; subst query; exact List.mem_cons_of_mem _ List.mem_cons_self)) transport (by decide) rfl

theorem write_certificate : Evm.run (writeCode size) {target with stack:=.val ⟨1,by decide⟩ :: .slot (.root 0) :: .val (TargetOperations.encodeWord (w 71)) :: target.stack}=.ok afterTarget 0 ∧
 Represented result (q 1 :: contexts) base afterStore ∧ Transport 16 hash locations afterStore afterNumeric ∧
 (∀ l (member : l ∈ locations),afterTarget.store.cells (TargetOperations.toSlot l (fitting l member))=TargetOperations.encodeWord (afterStore l)) := by
 apply complete_write finite old result (ix 1) (w 71) rfl contexts base True.intro store numeric target target.stack
 · intro query member
   simp only [contexts,List.mem_cons,List.not_mem_nil,or_false] at member
   rcases member with rfl|rfl
   · exact owner _ List.mem_cons_self
   · exact owner _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ List.mem_cons_self))
 · intro query member
   simp only [contexts,List.mem_cons,List.not_mem_nil,or_false] at member
   rcases member with rfl|rfl <;> exact Apart.fork (.fixed _ _ (by decide)) .nil .nil
 · intro query member
   simp only [contexts,List.mem_cons,List.not_mem_nil,or_false] at member
   rcases member with rfl|rfl <;> simp only [q,Query.location,location,base,Solidity.Storage.Loc.add] <;> decide
 · exact transport
 · decide
 · exact agreement

theorem ordered : observe old=[some 17,some 0,some 53,none] ∧ observe result=[some 17,some 71,some 53,none] ∧
 words store=[17,0,53,99] ∧ words afterStore=[17,71,53,99] ∧ numbers numeric=[17,0,53,99] ∧ numbers afterNumeric=[17,71,53,99] ∧
 cells target=[17,0,53,99,87] ∧ cells afterTarget=[17,71,53,99,87] ∧ context afterTarget=context target := by
 constructor; decide
 constructor; decide
 constructor; decide
 constructor; decide
 constructor; decide
 constructor; decide
 constructor; decide
 constructor; decide
 rfl

theorem changed_runtime : Evm.run (writeCode size) {target with stack:=.val ⟨2,by decide⟩ :: .slot (.root 0) :: .val ⟨23,by decide⟩ :: target.stack}=
 .ok {target with store:=Evm.WordStore.write target.store (.root 2) 23} 0 := by
 exact run_write size target target.stack (.root 0) (ix 2) ⟨23,by decide⟩

theorem malformed : old.find (path (ix 3))=none ∧ old.save (path (ix 3)) (.prim (w 71))=none ∧
 Evm.run (readCode size) {target with stack:=.val ⟨3,by decide⟩ :: .slot (.root 0) :: target.stack}=.revert ∧
 Evm.run (writeCode size) {target with stack:=.val ⟨3,by decide⟩ :: .slot (.root 0) :: .val ⟨71,by decide⟩ :: target.stack}=.revert := by
 refine ⟨rfl,rfl,?_,?_⟩
 · exact run_read size target target.stack (.root 0) (ix 3)
 · exact run_write size target target.stack (.root 0) (ix 3) ⟨71,by decide⟩

/-- Actually wrong dynamic code follows CURRENT first payload17 as header and
hashes to87. Fixed code reads inline53 instead. -/
theorem wrong_dynamic : Evm.run TargetArrayRead.code {target with stack:=.val ⟨2,by decide⟩ :: .slot (.root 0) :: target.stack}=
 .ok {target with stack:=.val ⟨87,by decide⟩ :: target.stack} 0 ∧
 Evm.run (readCode size) {target with stack:=.val ⟨2,by decide⟩ :: .slot (.root 0) :: target.stack}=
 .ok {target with stack:=.val ⟨53,by decide⟩ :: target.stack} 0 := by
 exact ⟨TargetArrayRead.run_current target target.stack (.root 0) 2 (by decide),run_read size target target.stack (.root 0) (ix 2)⟩

theorem readbacks :
 Evm.run (readCode size) {afterTarget with stack:=.val ⟨1,by decide⟩ :: .slot (.root 0) :: afterTarget.stack}=
 .ok {afterTarget with stack:=.val ⟨71,by decide⟩ :: afterTarget.stack} 0 ∧
 Evm.run (readCode size) {afterTarget with stack:=.val ⟨2,by decide⟩ :: .slot (.root 0) :: afterTarget.stack}=
 .ok {afterTarget with stack:=.val ⟨53,by decide⟩ :: afterTarget.stack} 0 := by
 exact ⟨run_read size afterTarget afterTarget.stack (.root 0) (ix 1),run_read size afterTarget afterTarget.stack (.root 0) (ix 2)⟩

/-- The incorrectly hashed read cannot certify the actual fixed word. -/
theorem wrong_owner : ¬ Represented old [q 2] base
 (Representation.write store (.root 2) (w 87)) := by
 intro assumed
 have bad := (assumed (q 2) List.mem_cons_self).2.2 (w 53) rfl
 change w 87=w 53 at bad
 exact (by decide : w 87≠w 53) bad

/-- info: 'Solidity.Backend.StorageOps.TargetFixedPrimitive.Controls.readbacks' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in #print axioms readbacks
/-- info: 'Solidity.Backend.StorageOps.TargetFixedPrimitive.Controls.wrong_owner' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in #print axioms wrong_owner

/-- info: 'Solidity.Backend.StorageOps.TargetFixedPrimitive.Controls.read_certificate' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in #print axioms read_certificate
/-- info: 'Solidity.Backend.StorageOps.TargetFixedPrimitive.Controls.write_certificate' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in #print axioms write_certificate
/-- info: 'Solidity.Backend.StorageOps.TargetFixedPrimitive.Controls.ordered' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in #print axioms ordered
/-- info: 'Solidity.Backend.StorageOps.TargetFixedPrimitive.Controls.changed_runtime' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in #print axioms changed_runtime
/-- info: 'Solidity.Backend.StorageOps.TargetFixedPrimitive.Controls.malformed' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in #print axioms malformed
/-- info: 'Solidity.Backend.StorageOps.TargetFixedPrimitive.Controls.wrong_dynamic' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in #print axioms wrong_dynamic
end Solidity.Backend.StorageOps.TargetFixedPrimitive.Controls
