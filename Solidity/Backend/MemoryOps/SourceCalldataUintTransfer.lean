import Solidity.Backend.MemoryOps.SourceCalldataUintCopy
import Solidity.Semantics.AllocBytes

/-! One observed typed table object projected from the REAL numeric Source
word decoder, then the EXISTING checked transfer. This does not construct an
all-offset ABI table, target allocator or second copy evaluator. -/
namespace Solidity.Backend.MemoryOps

def sourceUintTable {E : Source.Env} (F : Source.Fr) (off : Nat)
    (vs : List (Source.Val E.layout (.int .u256))) : Source.Calldata E.layout :=
  { input := F.cd
    objects := fun p => if p=off then some ⟨.array .calldata (.int .u256) none,
      .array vs.length (fun _ h => nomatch h) (fun i => .val (vs.get i))⟩ else none }

theorem sourceUintTable_payload {E : Source.Env} (F : Source.Fr) (off : Nat)
    (vs : List (Source.Val E.layout (.int .u256))) :
    calldataUints (sourceUintTable F off vs) off=some (sourceUintValuePayload vs) := by
  unfold calldataUints sourceUintTable
  dsimp only
  rw [if_pos rfl]
  change some (List.ofFn (fun i : Fin vs.length => calldataUint (.val (vs.get i))))=_
  apply congrArg some
  apply List.ext_getElem
  · simp only [List.length_ofFn,sourceUintValuePayload,List.length_map]
  · intro i hi hj
    simp only [List.getElem_ofFn,sourceUintValuePayload,List.getElem_map,List.get_eq_getElem]

theorem sourceUintTable_input {E : Source.Env} (F : Source.Fr) (off : Nat)
    (vs : List (Source.Val E.layout (.int .u256))) : (sourceUintTable F off vs).input=F.cd := by rfl

theorem sourceUintTable_other {E : Source.Env} (F : Source.Fr) (off p : Nat)
    (vs : List (Source.Val E.layout (.int .u256))) (different : p≠off) :
    (sourceUintTable F off vs).objects p=none := by
  simp only [sourceUintTable,if_neg different]

/-- A complete write into the fresh object reuses Heap.set_alloc_self. -/
theorem overwrite_fresh_uints {H : HTy} (hp : Heap H) (xs ys : List PrimTy.uint.Denote)
    (valid : xs.length<2^256) (same : ys.length=xs.length)
    (bound : 0+ys.length≤(hp.alloc (R := .array (.prim .uint)) (⟨xs,valid⟩ : MObj H (.array (.prim .uint)))).1.len
      (hp.alloc (R := .array (.prim .uint)) (⟨xs,valid⟩ : MObj H (.array (.prim .uint)))).2 .dyn) :
    overwriteSlice (hp.alloc (R := .array (.prim .uint)) (⟨xs,valid⟩ : MObj H (.array (.prim .uint)))).1
      (hp.alloc (R := .array (.prim .uint)) (⟨xs,valid⟩ : MObj H (.array (.prim .uint)))).2 .dyn 0 ys bound=
      (hp.alloc (R := .array (.prim .uint)) (⟨ys,by rw [same];exact valid⟩ : MObj H (.array (.prim .uint)))).1 := by
  let old : MObj H (.array (.prim .uint)) := ⟨xs,valid⟩
  let new : MObj H (.array (.prim .uint)) := ⟨ys,by rw [same];exact valid⟩
  let ext := List.prefix_append H [RefTy.array (.prim .uint)]
  have initial : MObj.elems .dyn ((hp.alloc old).1.get (hp.alloc old).2)=xs := by
    rw [Heap.get_alloc,MObj.elems_wk,MObj.elems_dyn]
    exact List.map_id'' (fun _ => rfl) _
  have entire : replaceSlice xs 0 ys=ys := by
    simp only [replaceSlice,List.take_zero,List.nil_append,Nat.zero_add,same,List.drop_length,List.append_nil]
  have object : withElems .dyn ((hp.alloc old).1.get (hp.alloc old).2)
      (replaceSlice (MObj.elems .dyn ((hp.alloc old).1.get (hp.alloc old).2)) 0 ys)
      (replaceSlice_length _ _ _ bound)=MObj.wk ext (.array (.prim .uint)) new := by
    apply Subtype.ext
    change replaceSlice (MObj.elems .dyn ((hp.alloc old).1.get (hp.alloc old).2)) 0 ys=
      ys.map (MVal.wk ext (.prim .uint))
    rw [initial,entire]
    exact (List.map_id'' (fun _ => rfl) _).symm
  change (hp.alloc old).1.set (hp.alloc old).2 _=(hp.alloc new).1
  rw [object,Heap.set_alloc_self]

def checkedSourceUints {E : Source.Env} {H : HTy} {R : RefTy}
    (F : Source.Fr) (off len : Nat) (hp : Heap H) (dst : HRef H R)
    (a : ArrTy R (.prim .uint)) (dest : Nat) : Source.R (Option (Heap H)) := do
  let vs ← sourceCalldataUintValues E F off len
  pure (checkedCalldataUints (sourceUintTable F off vs) off hp dst a 0 len dest)

def checkedSourceFreshUints {E : Source.Env} {H : HTy}
    (F : Source.Fr) (off len : Nat) (hp : Heap H) (cap : len<2^256) :
    Source.R (Option (Heap (H++[RefTy.array (.prim .uint)]))) := do
  let vs ← sourceCalldataUintValues E F off len
  let zeros : MObj H (.array (.prim .uint)) :=
    ⟨List.replicate len (⟨0,by decide⟩ : PrimTy.uint.Denote),by rw [List.length_replicate];exact cap⟩
  let mid := hp.alloc zeros
  pure (checkedCalldataUints (sourceUintTable F off vs) off mid.1 mid.2 .dyn 0 len 0)

theorem checkedSourceFreshUints_error {E : Source.Env} {H : HTy}
    (F : Source.Fr) (off len : Nat) (hp : Heap H) (cap : len<2^256)
    (error : Source.Halt) (bad : sourceCalldataUintValues E F off len=.error error) :
    checkedSourceFreshUints (E := E) F off len hp cap=.error error := by
  simp only [checkedSourceFreshUints,bad,bind,Except.bind]

theorem checkedSourceFreshUints_some {E : Source.Env} {H : HTy}
    (F : Source.Fr) (off len : Nat) (hp : Heap H) (cap : len<2^256)
    (vs : List (Source.Val E.layout (.int .u256)))
    (decoded : sourceCalldataUintValues E F off len=.ok vs) :
    ∃ valid : (sourceUintValuePayload vs).length<2^256,
      let old : MObj H (.array (.prim .uint)) :=
        ⟨List.replicate len (⟨0,by decide⟩ : PrimTy.uint.Denote),by rw [List.length_replicate];exact cap⟩
      let new : MObj H (.array (.prim .uint)) := ⟨sourceUintValuePayload vs,valid⟩
      checkedCalldataUints (sourceUintTable F off vs) off (hp.alloc old).1 (hp.alloc old).2 .dyn 0 len 0=
        some (hp.alloc new).1 ∧
      checkedSourceFreshUints (E := E) F off len hp cap=.ok (some (hp.alloc new).1) := by
  have size : (sourceUintValuePayload vs).length=len := sourceCalldataUintValues_length decoded
  have valid : (sourceUintValuePayload vs).length<2^256 := by rw [size];exact cap
  refine ⟨valid,?_⟩
  dsimp only
  let old : MObj H (.array (.prim .uint)) :=
    ⟨List.replicate len (⟨0,by decide⟩ : PrimTy.uint.Denote),by rw [List.length_replicate];exact cap⟩
  let new : MObj H (.array (.prim .uint)) := ⟨sourceUintValuePayload vs,valid⟩
  have length : (hp.alloc old).1.len (hp.alloc old).2 .dyn=len := by
    simp only [Heap.len,Heap.get_alloc,MObj.elems_wk,MObj.elems_dyn,List.length_map]
    exact List.length_replicate
  have run : checkedCalldataUints (sourceUintTable F off vs) off (hp.alloc old).1 (hp.alloc old).2 .dyn 0 len 0=
      some (hp.alloc new).1 := by
    unfold checkedCalldataUints
    rw [sourceUintTable_payload]
    have hs : 0≤len ∧ len≤(sourceUintValuePayload vs).length := ⟨Nat.zero_le _,by rw [size];exact Nat.le_refl _⟩
    have hd : 0+(len-0)≤(hp.alloc old).1.len (hp.alloc old).2 .dyn := by
      rw [Nat.zero_add,Nat.sub_zero,length]
      exact Nat.le_refl _
    have take : ((sourceUintValuePayload vs).drop 0).take (len-0)=sourceUintValuePayload vs := by
      rw [List.drop_zero,Nat.sub_zero,←size,List.take_length]
    simp only [bind,Option.bind,dif_pos hs,dif_pos hd,take]
    congr 1
    exact overwrite_fresh_uints hp _ _ old.property (by rw [List.length_replicate,size]) _
  refine ⟨run,?_⟩
  simp only [checkedSourceFreshUints,decoded,bind,Except.bind,pure,Except.pure]
  exact congrArg Except.ok run

/-- Rejection of the existing destination is Option None, not a Source halt. -/
theorem checkedSourceUints_none_iff {E : Source.Env} {H : HTy} {R : RefTy}
    (F : Source.Fr) (off len : Nat) (hp : Heap H) (dst : HRef H R)
    (a : ArrTy R (.prim .uint)) (dest : Nat) (vs : List (Source.Val E.layout (.int .u256)))
    (decoded : sourceCalldataUintValues E F off len=.ok vs) :
    checkedSourceUints (E := E) F off len hp dst a dest=.ok none ↔ hp.len dst a<dest+len := by
  have size := sourceCalldataUintValues_length decoded
  have hs : 0≤len ∧ len≤(sourceUintValuePayload vs).length := ⟨Nat.zero_le _,by rw [size];exact Nat.le_refl _⟩
  simp only [checkedSourceUints,decoded,bind,Except.bind,pure,Except.pure,
    checkedCalldataUints,sourceUintTable_payload,Option.bind,dif_pos hs,Nat.sub_zero]
  by_cases hd : dest+len≤hp.len dst a
  · simp only [dif_pos hd,Except.ok.injEq,Option.some_ne_none,false_iff]
    omega
  · simp only [dif_neg hd,true_iff]
    omega
/-- The REAL Source conversion and checked zero-initialized transfer agree
on the reached payload heap; no final equality, transfer success or payload is
an input premise. Old objects and Source state frames follow the actual copy. -/
theorem source_cd_uint_checked_copy {E : Source.Env} {Γ : Source.RCtx} {H : HTy}
    (y : Source.EMState E Γ) (hp : Heap H) (address : Nat → Nat)
    (F : Source.Fr) (off len : Nat) (capacity : len<2^256)
    (SH : Source.HeapTy) (memOK : Source.MemOK E SH y) :
    match sourceCalldataUintValues E F off len with
    | .error error =>
      checkedSourceFreshUints (E := E) F off len hp capacity=.error error ∧
      (Source.cdToMem F (.array .memory (.int .u256) none) off len).run y=(.error error,y)
    | .ok vs => ∃ valid : (sourceUintValuePayload vs).length<2^256,
      let old : MObj H (.array (.prim .uint)) :=
        ⟨List.replicate len (⟨0,by decide⟩ : PrimTy.uint.Denote),by rw [List.length_replicate];exact capacity⟩
      let new : MObj H (.array (.prim .uint)) := ⟨sourceUintValuePayload vs,valid⟩
      let pair := hp.alloc new
      let ext := List.prefix_append H [RefTy.array (.prim .uint)]
      let address' := allocatedSourceAddress address H.length y.2.heap.next
      let z : Source.EMState E Γ :=
        (y.1,{y.2 with heap := (y.2.heap.alloc ⟨.array .memory (.int .u256) none,sourceUintMemory (sourceUintValuePayload vs)⟩).1})
      checkedCalldataUints (sourceUintTable F off vs) off (hp.alloc old).1 (hp.alloc old).2 .dyn 0 len 0=some pair.1 ∧
      checkedSourceFreshUints (E := E) F off len hp capacity=.ok (some pair.1) ∧
      (Source.cdToMem F (.array .memory (.int .u256) none) off len).run y=(.ok (.val (.memRef rfl y.2.heap.next)),z) ∧
      Heap.Keeps ext hp pair.1 ∧
      SourceUintMemoryAt z (address' pair.2.id) pair.1 pair.2 .dyn ∧ Source.MemOK E SH z ∧
      (∀ b obj,y.2.heap.get b=some obj → z.2.heap.get b=some obj ∧ b≠y.2.heap.next) ∧
      z.1=y.1 ∧ z.2.ex=y.2.ex ∧ z.2.events=y.2.events ∧ z.2.logs=y.2.logs ∧ z.2.fnLocals=y.2.fnLocals := by
  have source := source_cd_uint_copy y hp address F off len capacity SH memOK
  cases decoded : sourceCalldataUintValues E F off len with
  | error error =>
    rw [decoded] at source
    exact ⟨checkedSourceFreshUints_error F off len hp capacity error decoded,source⟩
  | ok vs =>
    rw [decoded] at source
    obtain ⟨valid,run,keep,new,mok,identity,sourceId,oldMap,separate,preserved,aliases,loc,ex,events,logs,fn⟩ := source
    obtain ⟨valid',direct,wrapped⟩ := checkedSourceFreshUints_some F off len hp capacity vs decoded
    exact ⟨valid,direct,wrapped,run,keep,new,mok,preserved,loc,ex,events,logs,fn⟩

/-- info: 'Solidity.Backend.MemoryOps.sourceUintTable_payload' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms sourceUintTable_payload
/-- info: 'Solidity.Backend.MemoryOps.sourceUintTable_input' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms sourceUintTable_input
/-- info: 'Solidity.Backend.MemoryOps.sourceUintTable_other' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms sourceUintTable_other
/-- info: 'Solidity.Backend.MemoryOps.overwrite_fresh_uints' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms overwrite_fresh_uints
/-- info: 'Solidity.Backend.MemoryOps.checkedSourceFreshUints_error' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms checkedSourceFreshUints_error
/-- info: 'Solidity.Backend.MemoryOps.checkedSourceFreshUints_some' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms checkedSourceFreshUints_some
/-- info: 'Solidity.Backend.MemoryOps.checkedSourceUints_none_iff' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms checkedSourceUints_none_iff
/-- info: 'Solidity.Backend.MemoryOps.source_cd_uint_checked_copy' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms source_cd_uint_checked_copy
end Solidity.Backend.MemoryOps
