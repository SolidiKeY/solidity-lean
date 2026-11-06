import Solidity.Backend.MemoryOps.SourceCalldataCopy
import Solidity.Semantics.AllocBytes

/-! A single immutable decoded-table observation of ACTUAL published Source
word decoding, followed by the existing checked heap transfer. This is not a
new ABI decoder/table for all offsets, constructor or copy evaluator. -/
namespace Solidity.Backend.MemoryOps

/-- Only the observed object is projected. Its input bytes are the actual
frame bytes; no assertion of ABI entry validity or other objects is made. -/
def sourceBoolTable {E : Source.Env} (F : Source.Fr) (off : Nat)
    (vs : List (Source.Val E.layout .bool)) : Source.Calldata E.layout :=
  { input := F.cd
    objects := fun p => if p=off then some ⟨.array .calldata .bool none,
      .array vs.length (fun _ h => nomatch h) (fun i => .val (vs.get i))⟩ else none }

theorem sourceBoolTable_payload {E : Source.Env} (F : Source.Fr) (off : Nat)
    (vs : List (Source.Val E.layout .bool)) :
    calldataBools (sourceBoolTable F off vs) off=some (sourceBoolValuePayload vs) := by
  unfold calldataBools sourceBoolTable
  dsimp only
  rw [if_pos rfl]
  change some (List.ofFn (fun i : Fin vs.length => calldataBool (.val (vs.get i)))) = _
  apply congrArg some
  apply List.ext_getElem
  · simp only [List.length_ofFn, sourceBoolValuePayload, List.length_map]
  · intro i hi hj
    simp only [List.getElem_ofFn, sourceBoolValuePayload, List.getElem_map,
      List.get_eq_getElem]

/-- Overwriting the complete fresh object consumes the existing checked slice
operation. Existing Heap.set_alloc_self supplies the reached heap identity. -/
theorem overwrite_fresh_bools {H : HTy} (hp : Heap H) (xs ys : List Bool)
    (valid : xs.length<2^256) (same : ys.length=xs.length)
    (bound : 0+ys.length≤(hp.alloc (R := .array (.prim .bool)) (⟨xs,valid⟩ : MObj H (.array (.prim .bool)))).1.len
      (hp.alloc (R := .array (.prim .bool)) (⟨xs,valid⟩ : MObj H (.array (.prim .bool)))).2 .dyn) :
    overwriteSlice (hp.alloc (R := .array (.prim .bool)) (⟨xs,valid⟩ : MObj H (.array (.prim .bool)))).1
      (hp.alloc (R := .array (.prim .bool)) (⟨xs,valid⟩ : MObj H (.array (.prim .bool)))).2 .dyn 0 ys bound=
      (hp.alloc (R := .array (.prim .bool)) (⟨ys,by rw [same];exact valid⟩ : MObj H (.array (.prim .bool)))).1 := by
  let old : MObj H (.array (.prim .bool)) := ⟨xs, valid⟩
  let new : MObj H (.array (.prim .bool)) := ⟨ys, by rw [same]; exact valid⟩
  let e := List.prefix_append H [RefTy.array (.prim .bool)]
  have initial : MObj.elems .dyn ((hp.alloc old).1.get (hp.alloc old).2) = xs := by
    rw [Heap.get_alloc, MObj.elems_wk, MObj.elems_dyn]
    exact List.map_id'' (fun _ => rfl) _
  have entire : replaceSlice xs 0 ys = ys := by
    simp only [replaceSlice, List.take_zero, List.nil_append, Nat.zero_add,
      same, List.drop_length, List.append_nil]
  have object : withElems .dyn ((hp.alloc old).1.get (hp.alloc old).2)
      (replaceSlice (MObj.elems .dyn ((hp.alloc old).1.get (hp.alloc old).2)) 0 ys)
      (replaceSlice_length _ _ _ bound) = MObj.wk e (.array (.prim .bool)) new := by
    apply Subtype.ext
    change replaceSlice (MObj.elems .dyn ((hp.alloc old).1.get (hp.alloc old).2)) 0 ys =
      ys.map (MVal.wk e (.prim .bool))
    rw [initial, entire]
    exact (List.map_id'' (fun _ => rfl) _).symm
  change (hp.alloc old).1.set (hp.alloc old).2 _ = (hp.alloc new).1
  rw [object, Heap.set_alloc_self]

/-- No payload input: decode the real frame, then invoke the actual checked
full-array transfer into an existing object. Option None is only this adapter's
capacity failure; it is not a Source halt or transaction rollback. -/
def checkedSourceBools {E : Source.Env} {H : HTy} {R : RefTy}
    (F : Source.Fr) (off len : Nat) (hp : Heap H) (dst : HRef H R)
    (a : ArrTy R (.prim .bool)) (dest : Nat) : Source.R (Option (Heap H)) := do
  let vs ← sourceCalldataBoolValues E F off len
  pure (checkedCalldataBools (sourceBoolTable F off vs) off hp dst a 0 len dest)

/-- Decode FIRST, allocate with the existing Heap.alloc, then fill its actual
fresh object with the existing checked operation. No suffix heap on failure. -/
def checkedSourceFreshBools {E : Source.Env} {H : HTy}
    (F : Source.Fr) (off len : Nat) (hp : Heap H) (cap : len<2^256) :
    Source.R (Option (Heap (H++[RefTy.array (.prim .bool)]))) := do
  let vs ← sourceCalldataBoolValues E F off len
  let zeros : MObj H (.array (.prim .bool)) := ⟨List.replicate len false,by rw [List.length_replicate];exact cap⟩
  let mid := hp.alloc zeros
  pure (checkedCalldataBools (sourceBoolTable F off vs) off mid.1 mid.2 .dyn 0 len 0)

/-- The single observed object retains the original raw input. -/
theorem sourceBoolTable_input {E : Source.Env} (F : Source.Fr) (off : Nat)
    (vs : List (Source.Val E.layout .bool)) : (sourceBoolTable F off vs).input=F.cd := by
  rfl

/-- A different offset has not been observed by this projection. -/
theorem sourceBoolTable_other {E : Source.Env} (F : Source.Fr) (off p : Nat)
    (vs : List (Source.Val E.layout .bool)) (different : p≠off) :
    (sourceBoolTable F off vs).objects p=none := by
  simp only [sourceBoolTable,if_neg different]

/-- Decode errors precede any allocation or checked transfer. -/
theorem checkedSourceFreshBools_error {E : Source.Env} {H : HTy}
    (F : Source.Fr) (off len : Nat) (hp : Heap H) (cap : len<2^256)
    (e : Source.Halt) (bad : sourceCalldataBoolValues E F off len=.error e) :
    checkedSourceFreshBools (E := E) F off len hp cap=.error e := by
  simp only [checkedSourceFreshBools,bad,bind,Except.bind]

/-- The real decoded payload exactly fills the genuinely fresh zero object.
The success trace names the reached allocation and actual checked operation. -/
theorem checkedSourceFreshBools_some {E : Source.Env} {H : HTy}
    (F : Source.Fr) (off len : Nat) (hp : Heap H) (cap : len<2^256)
    (vs : List (Source.Val E.layout .bool))
    (decoded : sourceCalldataBoolValues E F off len=.ok vs) :
    ∃ valid : (sourceBoolValuePayload vs).length<2^256,
      let old : MObj H (.array (.prim .bool)) := ⟨List.replicate len false, by rw [List.length_replicate];exact cap⟩
      let new : MObj H (.array (.prim .bool)) := ⟨sourceBoolValuePayload vs,valid⟩
      checkedCalldataBools (sourceBoolTable F off vs) off (hp.alloc old).1 (hp.alloc old).2 .dyn 0 len 0=
        some (hp.alloc new).1 ∧
      checkedSourceFreshBools (E := E) F off len hp cap=.ok (some (hp.alloc new).1) := by
  have size : (sourceBoolValuePayload vs).length=len := sourceCalldataBoolValues_length decoded
  have valid : (sourceBoolValuePayload vs).length<2^256 := by rw [size];exact cap
  refine ⟨valid,?_⟩
  dsimp only
  let old : MObj H (.array (.prim .bool)) := ⟨List.replicate len false, by rw [List.length_replicate];exact cap⟩
  let new : MObj H (.array (.prim .bool)) := ⟨sourceBoolValuePayload vs,valid⟩
  have length : (hp.alloc old).1.len (hp.alloc old).2 .dyn=len := by
    simp only [Heap.len,Heap.get_alloc,MObj.elems_wk,MObj.elems_dyn,List.length_map]
    exact List.length_replicate
  have run : checkedCalldataBools (sourceBoolTable F off vs) off (hp.alloc old).1 (hp.alloc old).2 .dyn 0 len 0=
      some (hp.alloc new).1 := by
    unfold checkedCalldataBools
    rw [sourceBoolTable_payload]
    have hs : 0≤len ∧ len≤(sourceBoolValuePayload vs).length := ⟨Nat.zero_le _, by rw [size];exact Nat.le_refl _⟩
    have hd : 0+(len-0)≤(hp.alloc old).1.len (hp.alloc old).2 .dyn := by
      rw [Nat.zero_add,Nat.sub_zero,length]
      exact Nat.le_refl _
    have take : ((sourceBoolValuePayload vs).drop 0).take (len-0)=sourceBoolValuePayload vs := by
      rw [List.drop_zero,Nat.sub_zero,←size,List.take_length]
    simp only [bind,Option.bind,dif_pos hs,dif_pos hd]
    simp only [take]
    congr 1
    exact overwrite_fresh_bools hp (List.replicate len false) (sourceBoolValuePayload vs) old.property
      (by rw [List.length_replicate,size]) _
  refine ⟨run,?_⟩
  simp only [checkedSourceFreshBools,decoded,bind,Except.bind,pure,Except.pure]
  exact congrArg Except.ok run

/-- A successful decoder followed by an insufficient EXISTING destination is
Option rejection, even though Source itself could allocate the copied array. -/
theorem checkedSourceBools_none_iff {E : Source.Env} {H : HTy} {R : RefTy}
    (F : Source.Fr) (off len : Nat) (hp : Heap H) (dst : HRef H R)
    (a : ArrTy R (.prim .bool)) (dest : Nat) (vs : List (Source.Val E.layout .bool))
    (decoded : sourceCalldataBoolValues E F off len=.ok vs) :
    checkedSourceBools (E := E) F off len hp dst a dest=.ok none ↔ hp.len dst a<dest+len := by
  have size := sourceCalldataBoolValues_length decoded
  have hs : 0≤len ∧ len≤(sourceBoolValuePayload vs).length := ⟨Nat.zero_le _,by rw [size];exact Nat.le_refl _⟩
  simp only [checkedSourceBools,decoded,bind,Except.bind,pure,Except.pure,
    checkedCalldataBools,sourceBoolTable_payload,Option.bind,dif_pos hs,Nat.sub_zero]
  by_cases hd : dest+len≤hp.len dst a
  · simp only [dif_pos hd,Except.ok.injEq,Option.some_ne_none,false_iff]
    omega
  · simp only [dif_neg hd,true_iff]
    omega

/-- Actual raw Source copy and actual checked transfer reach the SAME computed
fresh contents. The old named parent and selected child survive by the existing
allocation observer, not a final-correspondence premise. -/
theorem SourceBoolStructAt.checked_cd_bool_copy {E : Source.Env} {Γ : Source.RCtx} {H : HTy}
    {y : Source.EMState E Γ} {addr : Nat} {hp : Heap H} {r : HRef H (.struct s)}
    {address : Nat → Nat} {layout : SourceBoolStructLayout E dn s tag child}
    (hr : SourceBoolStructAt y addr hp r address layout)
    (F : Source.Fr) (off len : Nat) (capacity : len<2^256)
    (SH : Source.HeapTy) (memOK : Source.MemOK E SH y) :
    match sourceCalldataBoolValues E F off len with
    | .error e => checkedSourceFreshBools (E := E) F off len hp capacity=.error e ∧
        (Source.cdToMem F SourceBoolArrayTy off len).run y=(.error e,y)
    | .ok vs => ∃ valid : (sourceBoolValuePayload vs).length<2^256,
      let o : MObj H (.array (.prim .bool)) := ⟨sourceBoolValuePayload vs,valid⟩
      let pair := hp.alloc o
      let e := List.prefix_append H [RefTy.array (.prim .bool)]
      let address' := allocatedSourceAddress address H.length y.2.heap.next
      let z : Source.EMState E Γ :=
        (y.1,{y.2 with heap := (y.2.heap.alloc ⟨SourceBoolArrayTy,sourceBoolMemory (sourceBoolValuePayload vs)⟩).1})
      checkedSourceFreshBools (E := E) F off len hp capacity=.ok (some pair.1) ∧
      (Source.cdToMem F SourceBoolArrayTy off len).run y=(.ok (.val (.memRef rfl y.2.heap.next)),z) ∧
      Heap.Keeps e hp pair.1 ∧ SourceBoolStructAt z addr pair.1 (r.wk e) address' layout ∧
      SourceBoolMemoryAt z (address' pair.2.id) pair.1 pair.2 .dyn ∧ Source.MemOK E SH z ∧
      pair.2.id=H.length ∧ address' pair.2.id=y.2.heap.next ∧
      (∀ i,i<H.length → address' i=address i) ∧
      (∀ q : HRef H (.array (.prim .bool)),SourceBoolMemoryAt y (address q.id) hp q .dyn →
        SourceBoolMemoryAt z (address' (q.wk e).id) pair.1 (q.wk e) .dyn ∧ address q.id≠y.2.heap.next) ∧
      z.1=y.1 ∧ z.2.ex=y.2.ex ∧ z.2.events=y.2.events ∧ z.2.logs=y.2.logs ∧ z.2.fnLocals=y.2.fnLocals := by
  have copied := hr.cd_bool_copy F off len capacity SH memOK
  cases decoded : sourceCalldataBoolValues E F off len with
  | error err =>
    rw [decoded] at copied
    exact ⟨checkedSourceFreshBools_error F off len hp capacity err decoded,copied⟩
  | ok vs =>
    rw [decoded] at copied
    obtain ⟨valid,_,run⟩ := checkedSourceFreshBools_some F off len hp capacity vs decoded
    obtain ⟨_,sourceRun,keep,old,new,mok,fresh,freshAddress,oldAddress,_,_,_,aliases,loc,ex,ev,logs,fn⟩ := copied
    exact ⟨valid,run,sourceRun,keep,old,new,mok,fresh,freshAddress,oldAddress,aliases,loc,ex,ev,logs,fn⟩

/-- info: 'Solidity.Backend.MemoryOps.sourceBoolTable_payload' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms sourceBoolTable_payload
/-- info: 'Solidity.Backend.MemoryOps.overwrite_fresh_bools' depends on axioms: [propext, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms overwrite_fresh_bools
/-- info: 'Solidity.Backend.MemoryOps.sourceBoolTable_input' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms sourceBoolTable_input
/-- info: 'Solidity.Backend.MemoryOps.sourceBoolTable_other' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms sourceBoolTable_other
/-- info: 'Solidity.Backend.MemoryOps.checkedSourceFreshBools_error' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms checkedSourceFreshBools_error
/-- info: 'Solidity.Backend.MemoryOps.checkedSourceFreshBools_some' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms checkedSourceFreshBools_some
/-- info: 'Solidity.Backend.MemoryOps.checkedSourceBools_none_iff' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms checkedSourceBools_none_iff
/-- info: 'Solidity.Backend.MemoryOps.SourceBoolStructAt.checked_cd_bool_copy' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms SourceBoolStructAt.checked_cd_bool_copy
end Solidity.Backend.MemoryOps
