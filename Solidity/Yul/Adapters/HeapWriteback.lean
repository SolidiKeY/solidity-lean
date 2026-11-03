import Solidity.Yul.Adapters.P6Memory

/-! Structural composition of actual Source memory writes and P6's physical
writes. No alternative Source state or memory interpreter is introduced. -/
namespace Solidity.Yul.Adapters.HeapWriteback
open Solidity.Backend Solidity.Backend.MemoryOps Solidity.Backend.MemoryOps.Physical
abbrev Write := Fin Evm.W × Fin Evm.W
variable {E : Source.Env} {Γ : Source.RCtx}

def sourceWrites (F : Source.Fr) (fuel address : Nat) : List Write → Source.EM E Γ Unit
  | []=>pure ()
  | (i,w)::xs=>do
    Source.writeLoc F fuel (.mem address i.val) (sourceUint (Evm.Memory.indexValue w))
    sourceWrites F fuel address xs

def wordWrites (base : Fin Evm.W) (m : Evm.Machine) : List Write → Evm.Machine
  | []=>m
  | (i,w)::xs=>wordWrites base (Evm.Memory.writeMachine m (base.val+1+i.val) (.val w)) xs

def byteWrites (base : Fin Evm.W) (bytes : Environment.Memory) : List Write → Environment.Memory
  | []=>bytes
  | (i,w)::xs=>byteWrites base (Environment.writeBytes bytes (32*(base.val+1+i.val))
      (Semantics.wordBytes w.val)) xs

/-- Actual complete Source success and reached P6 relation for ANY finite
valid write sequence, including repeated/aliased indices. Bounds come from the
actual initial object. Every step refreshes all three concrete representations. -/
theorem run_writes {H : HTy} {y : Source.EMState E Γ} {address : Nat} {hp : Heap H}
    {r : HRef H (.array (.prim .uint))} {base : Fin Evm.W} {m : Evm.Machine}
    {bytes : Environment.Memory} (initial : UintArrayAt y address hp r base m bytes)
    (F : Source.Fr) (fuel : Nat) (xs : List Write)
    (valid : ∀ x∈xs, x.1.val<hp.len r .dyn) :
    ∃ (out : Heap H) (z : Source.EMState E Γ),
      (sourceWrites F fuel address xs).run y=(.ok (),z) ∧
      UintArrayAt z address out r base (wordWrites base m xs) (byteWrites base bytes xs) ∧
      out.len r .dyn=hp.len r .dyn ∧ z.1=y.1 ∧
      (∀ b,b≠address → z.2.heap.get b=y.2.heap.get b) ∧
      (∀ initialH : Source.HeapTy, Source.MemOK E initialH y → Source.MemOK E initialH z) := by
  induction xs generalizing hp y m bytes with
  | nil=>exact ⟨hp,y,rfl,initial,rfl,rfl,fun _ _=>rfl,fun _ h=>h⟩
  | cons x xs ih=>
    obtain ⟨i,w⟩:=x
    have hi : i.val<hp.len r .dyn := valid (i,w) (by simp only [List.mem_cons, true_or])
    obtain ⟨next,z,hw,hs,ht,hbyte,hnew,hl,hstate,hother,hheap,hexterior⟩:=initial.write_cell F fuel i w hi
    have actual : hp.writeAddr (.index r .dyn (Evm.Memory.indexValue i)) (Evm.Memory.indexValue w)=
        some (hp.set r (MObj.setElem .dyn (hp.get r) i.val (Evm.Memory.indexValue w))) := by
      have bound : i.val<(MObj.elems .dyn (hp.get r)).length := hi
      simp only [Heap.writeAddr,Heap.setIndex,Evm.Memory.indexValue,Int.toNat_natCast,bound,↓reduceIte]
    have same : next=hp.set r (MObj.setElem .dyn (hp.get r) i.val (Evm.Memory.indexValue w)) :=
      Option.some.inj (hw.symm.trans actual)
    have length : next.len r .dyn=hp.len r .dyn := by
      rw [same]
      simp only [Heap.len,Heap.get_set_same,MObj.elems_setElem,List.length_set]
    have remaining : ∀ x∈xs,x.1.val<next.len r .dyn := by
      intro x hx
      rw [length]
      exact valid x (List.mem_cons_of_mem _ hx)
    obtain ⟨out,final,run,repr,len,locals,other,mem⟩:=ih hnew remaining
    refine ⟨out,final,?_,repr,len.trans length,locals.trans hl,?_,?_⟩
    · rw [sourceWrites,Source.Hoare.run_bind,hs]
      exact run
    · intro b hb
      exact (other b hb).trans (hother b hb)
    · intro initialH ok
      apply mem initialH
      have preserve:=Source.writeLoc_memOK (E:=E) (Γ:=Γ) (H:=initialH) F fuel
        (.mem address i.val) (sourceUint (Evm.Memory.indexValue w)) y ⟨ok,by trivial⟩
      rw [hs] at preserve
      exact preserve

/-- Every unselected byte, including padding/reserved bytes, is identical after
all writes. The premise is actual interval disjointness for the given writes. -/
theorem bytes_outside (base : Fin Evm.W) (bytes : Environment.Memory) (xs : List Write) (k : Nat)
    (outside : ∀ x∈xs,k<32*(base.val+1+x.1.val) ∨ 32*(base.val+1+x.1.val)+32≤k) :
    byteWrites base bytes xs k=bytes k := by
  induction xs generalizing bytes with
  | nil=>rfl
  | cons x xs ih=>
    rw [byteWrites,ih]
    · exact Environment.writeBytes_frame _ _ _ _ (by
        rw [word_bytes_length]
        exact outside x (List.mem_cons_self))
    · intro x hx
      exact outside x (List.mem_cons_of_mem _ hx)
/-- The actual typed heap operation preserves its WHOLE administrative heap
when the supplied data is the original selected cell. No none/default or
unrelated cell is reconstructed from a projection. -/
theorem heap_write_same {D : Source.Layout} (h : Source.Heap D) (a : Nat)
    {τ : Source.STy} (x : Source.Data D τ) (typed : h.ty a=some τ)
    (found : h.get a=some ⟨τ,x⟩) : h.write a x typed=h := by
  have cells : (h.write a x typed).cells=h.cells := by
    funext b
    by_cases same : b=a
    · subst b
      exact (Source.Heap.write_get h a x typed).trans found.symm
    · exact Source.Heap.write_other h same x typed
  cases h with
  | mk c n hb=>
    change (⟨_,n,_⟩ : Source.Heap D)=⟨c,n,hb⟩
    congr 1

/-- Exact source sequencing, including the original successful prefix on halt. -/
theorem source_append (F : Source.Fr) (fuel address : Nat) (xs ys : List Write) :
    sourceWrites (E:=E) (Γ:=Γ) F fuel address (xs++ys)=
      (sourceWrites F fuel address xs >>= fun _=>sourceWrites F fuel address ys) := by
  induction xs with
  | nil=>rfl
  | cons x xs ih=>
    simp only [List.cons_append,sourceWrites,ih,bind_assoc]

/-- A late real Source bounds failure retains the already successful prefix.
No rollback is invented for this local monadic halt. -/
theorem late_bounds {H : HTy} {y : Source.EMState E Γ} {address : Nat} {hp : Heap H}
    {r : HRef H (.array (.prim .uint))} {base : Fin Evm.W} {m : Evm.Machine}
    {bytes : Environment.Memory} (initial : UintArrayAt y address hp r base m bytes)
    (F : Source.Fr) (fuel : Nat) (xs : List Write)
    (valid : ∀ x∈xs,x.1.val<hp.len r .dyn) (i w : Fin Evm.W) (bad : hp.len r .dyn≤i.val) :
    ∃ out z, (sourceWrites F fuel address xs).run y=(.ok (),z) ∧
      UintArrayAt z address out r base (wordWrites base m xs) (byteWrites base bytes xs) ∧
      (sourceWrites F fuel address (xs++[(i,w)])).run y=
        (.error (.revert (Source.panicData .index)),z) ∧
      (∀ initialH : Source.HeapTy, Source.MemOK E initialH y → Source.MemOK E initialH z) := by
  obtain ⟨out,z,run,repr,len,locals,other,mem⟩:=run_writes initial F fuel xs valid
  refine ⟨out,z,run,repr,?_,mem⟩
  rw [source_append,Source.Hoare.run_bind,run]
  change (sourceWrites F fuel address [(i,w)]).run z=_
  rw [sourceWrites,Source.Hoare.run_bind,P6Memory.source_bounds repr F fuel i.val w (by rw [len];exact bad)]
/-- The same actual owner evaluator observes the reached object through EVERY
retained local alias, at every positive indexing horizon. -/
theorem retained_aliases {H : HTy} {y : Source.EMState E Γ} {address : Nat} {hp : Heap H}
    {r : HRef H (.array (.prim .uint))} {base : Fin Evm.W} {m : Evm.Machine}
    {bytes : Environment.Memory} (initial : UintArrayAt y address hp r base m bytes)
    (F : Source.Fr) (fuel : Nat) (xs : List Write)
    (valid : ∀ x∈xs,x.1.val<hp.len r .dyn)
    (k : Fin Evm.W) (index : Source.Idx Γ (.int .u256))
    (indexed : y.1.get index=sourceUint (Evm.Memory.indexValue k)) (bound : k.val<hp.len r .dyn) :
    ∃ (out : Heap H) (z : Source.EMState E Γ), ∃ sameLength : out.len r .dyn=hp.len r .dyn,
      (sourceWrites F fuel address xs).run y=(.ok (),z) ∧
      ∀ (G : Source.Glob E) (n : Nat) (alias : Source.Idx Γ (.array .memory (.int .u256) none)),
      y.1.get alias=.memRef rfl address →
      (Source.evalE G F (n+2) (.indexArray (.local alias) (.local index) rfl)).run z=
        (.ok (.val (sourceUint ((MObj.elems .dyn (out.get r))[k.val]'(by
          have h : out.len r .dyn=hp.len r .dyn := sameLength
          change k.val<out.len r .dyn
          rw [h];exact bound)))),z) := by
  obtain ⟨out,z,run,repr,len,locals,other,mem⟩:=run_writes initial F fuel xs valid
  refine ⟨out,z,len,run,?_⟩
  intro G n alias found
  have root : z.1.get alias=.memRef rfl address := by rw [locals];exact found
  have ik : z.1.get index=sourceUint (Evm.Memory.indexValue k) := by rw [locals];exact indexed
  have hk : k.val<out.len r .dyn := by rw [len];exact bound
  exact repr.source.eval_index G F n alias index (Evm.Memory.indexValue k) root ik hk
end Solidity.Yul.Adapters.HeapWriteback
