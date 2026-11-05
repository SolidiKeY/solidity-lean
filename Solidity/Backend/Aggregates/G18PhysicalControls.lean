import Solidity.Backend.Aggregates.G18Physical
import Solidity.Source.Semantics

namespace Solidity.Backend.Aggregates.G18Physical.Controls
open MemoryOps MemoryOps.Physical

abbrev U : RefTy := .array (.prim .uint)
abbrev H : HTy := [U]
def r : HRef H U := ⟨0,rfl⟩
def u (n : Nat) : PrimTy.uint.Denote := Evm.Memory.indexValue (Evm.wmod n)
def hp : Heap H := (⟨[u 7,u 8],by decide +kernel⟩,())
def machine0 : Evm.Machine := {Evm.Machine.init with stack := [.val (Evm.wmod 77),.val (Evm.wmod 88)]}
def store (m : Evm.Machine) (a v : Nat) := Evm.Memory.writeMachine m a (.val (Evm.wmod v))
def machine : Evm.Machine := store (store (store machine0 8 2) 9 7) 10 8
def put (m : Environment.Memory) (a v : Nat) := Environment.writeBytes m (32*a) (Semantics.wordBytes v)
def bytes : Environment.Memory := put (put (put (fun _ => 0) 8 2) 9 7) 10 8
def E : Source.Env := ⟨[]⟩
def y0 : Source.EMState E [] := (.nil,Source.St.init E)
def y : Source.EMState E [] := ((Source.allocRef (sourceUintMemory [u 7,u 8])).run y0).2
def F : Source.Fr := {this := ⟨1,by decide +kernel⟩, sender := ⟨2,by decide +kernel⟩, value := ⟨0,by decide +kernel⟩,static := false,contract := "G18Physical"}

theorem length : hp.len r .dyn=2 := by
  simp only [Heap.len,MObj.elems_dyn]
  rfl

theorem elems : MObj.elems .dyn (hp.get r)=[u 7,u 8] := by
  simp only [MObj.elems_dyn,Heap.get,H,hp,r,Objs.get]

theorem frame : WordFrame machine bytes (fun c => ((False ∨ c=8) ∨ c=9) ∨ c=10) := by
  have h0 : WordFrame machine0 (fun _ => 0) (fun _ => False) := ⟨fun _ h => h.elim,fun _ h => h.elim⟩
  have h8 := h0.write 8 (Evm.wmod 2) (by decide +kernel)
  have h9 := h8.write 9 (Evm.wmod 7) (by decide +kernel)
  exact h9.write 10 (Evm.wmod 8) (by decide +kernel)

theorem initial : UintArrayAt y 0 hp r (Evm.wmod 8) machine bytes := by
  constructor
  · unfold SourceUintMemoryAt
    rw [elems]
    rfl
  · refine ⟨by rw [length];decide +kernel,by rw [length];rfl,?_⟩
    intro i v hv
    rw [elems] at hv
    match i with
    | 0 => cases hv;exact Evm.ReprV.uint_of rfl
    | 1 => cases hv;exact Evm.ReprV.uint_of rfl
    | i+2 => cases hv
  · constructor
    · intro c hc
      rw [length] at hc
      change 8≤c ∧ c<8+1+2 at hc
      have : c=8 ∨ c=9 ∨ c=10 := by omega
      rcases this with rfl | rfl | rfl <;> decide +kernel
    · intro c hc
      apply frame.cells
      rw [length] at hc
      change 8≤c ∧ c<8+1+2 at hc
      omega

def indices : List (Fin Evm.W) := [Evm.wmod 1,Evm.wmod 0,Evm.wmod 1]

theorem valid : ∀ i ∈ indices,i.val<hp.len r .dyn := by
  intro i hi
  simp only [indices,List.mem_cons,List.not_mem_nil,or_false] at hi
  rcases hi with rfl | rfl | rfl <;> decide +kernel

/-- Full requested vector, including repeated alias observation and reversed
index order; derived from the new consumer, not merely evaluated bytes. -/
theorem ordered : indices.map (fun i => Environment.readMemory bytes (32*(8+1+i.val)) 32)=
    [Semantics.wordBytes 8,Semantics.wordBytes 7,Semantics.wordBytes 8] := by
  have ho := (observations initial F indices valid).1
  simpa only [values,elems,indices,List.map_cons,List.map_nil] using ho

theorem spec : (indices.map (fun i => Environment.readMemory bytes (32*(8+1+i.val)) 32)=
    [Semantics.wordBytes 8,Semantics.wordBytes 7,Semantics.wordBytes 8]) := by
  apply (observation_spec initial F indices valid
    (fun xs => xs=[Semantics.wordBytes 8,Semantics.wordBytes 7,Semantics.wordBytes 8])).mpr
  simp only [values,elems,indices,List.map_cons,List.map_nil]
  rfl

/-- Inhabits the actual write consumer with a changing7→255 update, a preserved
second element, complete source state frame and nonempty target stack. -/
theorem update : ∃ out z,
    hp.writeAddr (.index r .dyn (u 0)) (u 255)=some out ∧
    (Source.writeLoc (E := E) (Γ := []) F 10 (.mem 0 0) (sourceUint (u 255))).run y=(.ok (),z) ∧
    Evm.run (Evm.Memory.writeArrayCode (Evm.wmod 8))
      ((machine.push (.val (Evm.wmod 255))).push (.val (Evm.wmod 0)))=
      .ok (store machine 9 255) 0 ∧
    UintArrayAt z 0 out r (Evm.wmod 8) (store machine 9 255) (put bytes 9 255) ∧
    z.1=y.1 ∧ z.2={y.2 with heap := z.2.heap} ∧
    (∀ k,k<288 ∨ 320≤k → put bytes 9 255 k=bytes k) ∧
    (∀ js : List (Fin Evm.W), (∀ j ∈ js,j.val<out.len r .dyn) →
      js.map (fun j => Environment.readMemory (put bytes 9 255) (32*(8+1+j.val)) 32)=
        (values out r js).map (fun v => Semantics.wordBytes v.val.toNat)) := by
  obtain ⟨out,z,ht,hs,hw,_,hr,hl,hst,_,hb,ho⟩ :=
    write_observations initial F 10 (Evm.wmod 0) (Evm.wmod 255) (by decide +kernel)
  exact ⟨out,z,ht,hs,hw,hr,hl,hst,hb,ho⟩

theorem wrong_order : indices.map (fun i => Environment.readMemory bytes (32*(8+1+i.val)) 32) ≠
    [Semantics.wordBytes 7,Semantics.wordBytes 8,Semantics.wordBytes 8] := by
  rw [ordered]
  decide +kernel

theorem wrong_frame : ¬ UintArrayAt y 0 hp r (Evm.wmod 9) machine bytes := by
  intro h
  have hb := h.words.length
  rw [length] at hb
  change Evm.Word.val (Evm.wmod 7)=Evm.Word.val (Evm.wmod 2) at hb
  have bad := congrArg Fin.val (Evm.Word.val.inj hb)
  contradiction

theorem invalid_index : ¬ ∀ i ∈ [Evm.wmod 2],i.val<hp.len r .dyn := by
  intro h
  have bad := h (Evm.wmod 2) (by exact List.mem_singleton_self _)
  rw [length] at bad
  change 2<2 at bad
  omega

theorem protected_stack : (store machine 9 255).stack=[.val (Evm.wmod 77),.val (Evm.wmod 88)] := rfl

theorem source_bounds :
    (Source.readLoc (E := E) (Γ := []) F (τ := .int .u256) (.mem 0 2)).run y=
      (.error (.revert (Source.panicData .index)),y) := by
  exact source_uint_bounds y 0 [u 7,u 8] (by simpa only [SourceUintMemoryAt,elems] using initial.source) 2 (by decide +kernel)

/-- Post-update observations are tied to the reached intrinsic write, including
unchanged second element and requested repeated first-cell alias. -/
theorem updated_vector :
    indices.map (fun i => Environment.readMemory (put bytes 9 255) (32*(8+1+i.val)) 32)=
      [Semantics.wordBytes 8,Semantics.wordBytes 255,Semantics.wordBytes 8] := by
  obtain ⟨out,z,ht,_,_,_,_,_,_,ho⟩ := update
  have hk : hp.writeAddr (.index r .dyn (u 0)) (u 255)=
      some (hp.set r (MObj.setElem .dyn (hp.get r) 0 (u 255))) := by
    simp only [Heap.writeAddr,Heap.setIndex,u,Evm.Memory.indexValue,Int.toNat_natCast,elems]
    rfl
  have he : out=hp.set r (MObj.setElem .dyn (hp.get r) 0 (u 255)) :=
    Option.some.inj (ht.symm.trans hk)
  subst out
  have hv : ∀ j ∈ indices,j.val<(hp.set r (MObj.setElem .dyn (hp.get r) 0 (u 255))).len r .dyn := by
    intro j hj
    simpa only [Heap.len,Heap.get_set_same,MObj.elems_setElem,List.length_set] using valid j hj
  have result := ho indices hv
  simpa only [values,Heap.get_set_same,MObj.elems_setElem,elems,indices,List.map_cons,List.map_nil] using result

theorem wrong_updated_payload :
    indices.map (fun i => Environment.readMemory (put bytes 9 255) (32*(8+1+i.val)) 32) ≠
      [Semantics.wordBytes 8,Semantics.wordBytes 7,Semantics.wordBytes 8] := by
  rw [updated_vector]
  decide +kernel

theorem wrong_postcondition : ¬
    ((fun xs => xs=[Semantics.wordBytes 7,Semantics.wordBytes 8,Semantics.wordBytes 8])
      (indices.map (fun i => Environment.readMemory bytes (32*(8+1+i.val)) 32))) := wrong_order

/-- Actual source index failure is neither timeout nor a successful read.
Its exact panic bytes stay distinct from the live target REVERT endpoints. -/
theorem wrong_source_failure :
    (Source.readLoc (E := E) (Γ := []) F (τ := .int .u256) (.mem 0 2)).run y ≠
      (.error .timeout,y) := by
  rw [source_bounds]
  intro h
  cases h

theorem store_endpoint :
    Environment.cryptoStep (.op .MSTORE) ⟨u 288::u 255::[u 77,u 88],bytes⟩=
      some ⟨[u 77,u 88],put bytes 9 255⟩ := by
  obtain ⟨_,_,_,_,_,⟨offset,he,hb⟩,_⟩ :=
    write_observations initial F 10 (Evm.wmod 0) (Evm.wmod 255) (by decide +kernel)
  have heq : offset=Evm.wmod 288 := Fin.ext he
  subst offset
  exact hb [u 77,u 88]

def tail : List Roadmap.Word := [⟨77,by decide +kernel⟩,⟨88,by decide +kernel⟩]
def revertInput : Failure.Slice.Machine := ⟨⟨288,by decide +kernel⟩::⟨32,by decide +kernel⟩::tail,bytes⟩

/-- The NEW observation endpoint is inhabited on a populated byte memory and
stack. It is a live pre-rollback endpoint; the suffix is not executed. -/
theorem revert_endpoint : Failure.Slice.run [.op .REVERT,.op .STOP] revertInput=
    some (⟨tail,bytes⟩,some (.revert (Semantics.wordBytes 7))) := by
  have valid0 : ∀ j ∈ [Evm.wmod 0],j.val<hp.len r .dyn := by
    intro j hj
    have he : j=Evm.wmod 0 := List.mem_singleton.mp hj
    subst j
    decide +kernel
  obtain ⟨v,hs,_,hr⟩ := (observations initial F [Evm.wmod 0] valid0).2
    (Evm.wmod 0) (List.mem_singleton_self _)
  have hv := (initial.source.read_nat_iff F 0 v).mp hs
  rw [elems] at hv
  change some (u 7)=some v at hv
  have he : v=u 7 := (Option.some.inj hv).symm
  subst v
  exact hr tail [.op .STOP]

theorem wrong_revert_payload : Failure.Slice.run [.op .REVERT,.op .STOP] revertInput ≠
    some (⟨tail,bytes⟩,some (.revert (Semantics.wordBytes 8))) := by
  rw [revert_endpoint]
  intro h
  have hb := Roadmap.Outcome.revert.inj (Option.some.inj (Prod.mk.inj (Option.some.inj h)).2)
  have bad := congrArg (fun xs : List UInt8 => xs[31]?) hb
  contradiction

theorem wrong_revert_success : Failure.Slice.run [.op .REVERT,.op .STOP] revertInput ≠
    some (⟨tail,bytes⟩,some (.success (Semantics.wordBytes 7))) := by
  rw [revert_endpoint]
  intro h
  have bad := Option.some.inj (Prod.mk.inj (Option.some.inj h)).2
  cases bad

end Solidity.Backend.Aggregates.G18Physical.Controls
