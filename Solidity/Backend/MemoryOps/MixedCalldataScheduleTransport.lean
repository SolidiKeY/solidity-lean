import Solidity.Backend.MemoryOps.MixedCalldataSchedules

namespace Solidity.Backend.MemoryOps
section
variable {D : Source.Layout} {H : HTy} {R Q : RefTy}
variable (c : Source.Calldata D) (off : Nat) (cu : Source.Calldata D) (uo : Nat)
variable (hp : Heap H) (r : HRef H R) (a : ArrTy R (.prim .bool)) (s t d : Nat)
variable (q : HRef H Q) (b : ArrTy Q (.prim .uint)) (u v f : Nat)

theorem checkedMixedCaptures_bool_source {n : Option Nat} {len : Nat}
    {hn : ∀ m, n=some m → m=len} {values : Fin len → Source.Data D .bool}
    (hc : DecodedArrayAt c off len hn values) (bs us : List SnapshotArgs) (out : Heap H)
    (ho : checkedMixedCaptures c off cu uo hp r a s t d q b u v f bs us=some out)
    (k : Nat) (hk : d ≤ captureOrigin bs k ∧ captureOrigin bs k < d+(t-s)) :
    ∃ value, (MObj.elems a (out.get r))[k]?=some value ∧
      DecodedArrayRead c off .bool n (s+(captureOrigin bs k-d)) (.val (.bool value)) := by
  obtain ⟨bm,ini,mid,hb,hu,hs,hsu⟩ := (checkedMixedCaptures_some c off cu uo hp r a s t d q b u v f bs us out).mp ho
  obtain ⟨value,hr,hsource⟩ := checkedCalldataBools_read hc hp r a s t d bm hb (captureOrigin bs k-d) (by omega)
  obtain ⟨pb,pu,hpb,hpu,hbr,hur⟩ := checkedMixedCaptures_read c off cu uo hp r a s t d q b u v f bs us out ho
  have he : pb=List.ofFn (fun i => calldataBool (values i)) := Option.some.inj (hpb.symm.trans (calldataBools_lookup hc))
  rw [checkedCalldataBools_elems hc hp r a s t d bm hb] at hr
  have hi : d+(captureOrigin bs k-d)=captureOrigin bs k := by omega
  rw [hi] at hr
  refine ⟨value,?_,hsource⟩
  rw [hbr k,he]
  exact hr

theorem checkedMixedCaptures_uint_source {n : Option Nat} {len : Nat}
    {hn : ∀ m, n=some m → m=len} {values : Fin len → Source.Data D (.int .u256)}
    (hc : DecodedArrayAt cu uo len hn values) (bs us : List SnapshotArgs) (out : Heap H)
    (ho : checkedMixedCaptures c off cu uo hp r a s t d q b u v f bs us=some out)
    (k : Nat) (hk : f ≤ captureOrigin us k ∧ captureOrigin us k < f+(v-u)) :
    ∃ value, (MObj.elems b (out.get q))[k]?=some value ∧
      DecodedArrayRead cu uo (.int .u256) n (u+(captureOrigin us k-f)) (.val (sourceUint value)) := by
  obtain ⟨bm,ini,mid,hb,hu,hs,hsu⟩ := (checkedMixedCaptures_some c off cu uo hp r a s t d q b u v f bs us out).mp ho
  obtain ⟨value,hr,hsource⟩ := checkedCalldataUints_read hc bm q b u v f ini hu (captureOrigin us k-f) (by omega)
  obtain ⟨pb,pu,hpb,hpu,hbr,hur⟩ := checkedMixedCaptures_read c off cu uo hp r a s t d q b u v f bs us out ho
  have he : pu=List.ofFn (fun i => calldataUint (values i)) := Option.some.inj (hpu.symm.trans (calldataUints_lookup hc))
  obtain ⟨pb0,hpb0,hbs,hbd,ebm⟩ := boolTransfer_result_lookup c off hp r a s t d bm hb
  have hframe : bm.get q=hp.get q := by
    rw [ebm,overwriteSlice_frame hp r q a d _ hbd (bool_uint_transfer_ne r a q b)]
  rw [checkedCalldataUints_elems hc bm q b u v f ini hu,hframe] at hr
  have hi : f+(captureOrigin us k-f)=captureOrigin us k := by omega
  rw [hi] at hr
  refine ⟨value,?_,hsource⟩
  rw [hur k,he]
  exact hr
end

section
variable {D : Source.Layout} {n n' : Option Nat} {c cu : Source.Calldata D} {off uo len len' : Nat}
variable {hn : ∀ m, n=some m → m=len} {hn' : ∀ m, n'=some m → m=len'}
variable {values : Fin len → Source.Data D .bool} {values' : Fin len' → Source.Data D (.int .u256)}
variable (hc : DecodedArrayAt c off len hn values) (hcu : DecodedArrayAt cu uo len' hn' values')

include hc hcu in
theorem checkedMixedCaptures_keeps {H H' : HTy} {R Q : RefTy} {hp : Heap H} {hp' : Heap H'}
    (e : H <+: H') (hk : Heap.Keeps e hp hp')
    (r : HRef H R) (a : ArrTy R (.prim .bool)) (s t d : Nat)
    (q : HRef H Q) (b : ArrTy Q (.prim .uint)) (u v f : Nat)
    (bs us : List SnapshotArgs) (out : Heap H)
    (ho : checkedMixedCaptures c off cu uo hp r a s t d q b u v f bs us=some out) :
    ∃ out', checkedMixedCaptures c off cu uo hp' (r.wk e) a s t d (q.wk e) b u v f bs us=some out' ∧ Heap.Keeps e out out' := by
  obtain ⟨bm,ini,mid,hb,hu,hs,hsu⟩ := (checkedMixedCaptures_some c off cu uo hp r a s t d q b u v f bs us out).mp ho
  have hi := (checkedBoolUintSequence_some_iff c off cu uo hp r a s t d q b u v f ini).mpr ⟨bm,hb,hu⟩
  obtain ⟨ini',hi',hk1⟩ := checkedBoolUintSequence_keeps hc hcu e hk r a s t d q b u v f ini hi
  obtain ⟨mid',hs',hk2⟩ := runCaptures_keeps e hk1 r a bs mid hs
  obtain ⟨out',hsu',hk3⟩ := runCaptures_keeps e hk2 q b us out hsu
  exact ⟨out',Option.bind_eq_some_iff.mpr ⟨ini',hi',Option.bind_eq_some_iff.mpr ⟨mid',hs',hsu'⟩⟩,hk3⟩
end

/-- Actual allocation after BOTH decoded calls, before the two reached-heap
schedules. Fresh own fields frame; their referenced descendants may change. -/
theorem checkedMixedCaptures_alloc {D : Source.Layout} {H : HTy} {R Q T : RefTy}
    (c : Source.Calldata D) (off : Nat) (cu : Source.Calldata D) (uo : Nat)
    (hp : Heap H) (r : HRef H R) (a : ArrTy R (.prim .bool)) (s t d : Nat)
    (q : HRef H Q) (b : ArrTy Q (.prim .uint)) (u v f : Nat)
    (bs us : List SnapshotArgs) (out : Heap H)
    (ho : checkedMixedCaptures c off cu uo hp r a s t d q b u v f bs us=some out) (obj : MObj H T) :
    let e := List.prefix_append H [T]
    ∃ ini mid' out', checkedBoolUintSequence c off cu uo hp r a s t d q b u v f=some ini ∧
      runCaptures (ini.alloc obj).1 (r.wk e) a bs=some mid' ∧
      runCaptures mid' (q.wk e) b us=some out' ∧ Heap.Keeps e out out' ∧
      out'.get (ini.alloc obj).2=(ini.alloc obj).1.get (ini.alloc obj).2 := by
  dsimp only
  obtain ⟨bm,ini,mid,hb,hu,hs,hsu⟩ := (checkedMixedCaptures_some c off cu uo hp r a s t d q b u v f bs us out).mp ho
  obtain ⟨mid',hs',hk1,hfresh⟩ := runCaptures_alloc ini obj r a bs mid hs
  obtain ⟨out',hsu',hk2⟩ := runCaptures_keeps _ hk1 q b us out hsu
  refine ⟨ini,mid',out',(checkedBoolUintSequence_some_iff c off cu uo hp r a s t d q b u v f ini).mpr ⟨bm,hb,hu⟩,hs',hsu',hk2,?_⟩
  exact (runCaptures_frame mid' out' (q.wk _) b us hsu' (ini.alloc obj).2 (old_ne_fresh ini obj q)).trans hfresh
/-- info: 'Solidity.Backend.MemoryOps.checkedMixedCaptures_bool_source' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms checkedMixedCaptures_bool_source
/-- info: 'Solidity.Backend.MemoryOps.checkedMixedCaptures_uint_source' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms checkedMixedCaptures_uint_source
/-- info: 'Solidity.Backend.MemoryOps.checkedMixedCaptures_keeps' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms checkedMixedCaptures_keeps
/-- info: 'Solidity.Backend.MemoryOps.checkedMixedCaptures_alloc' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms checkedMixedCaptures_alloc
end Solidity.Backend.MemoryOps
