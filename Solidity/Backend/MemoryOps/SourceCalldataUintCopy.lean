import Solidity.Backend.MemoryOps.SourceCalldataCopy
import Solidity.Backend.MemoryOps.SourceUintMemory

/-! Actual independent Source uint256 calldata-to-memory conversion and paired
existing intrinsic allocation. No decoder/allocator implementation, ABI entry
or emitted-copy certificate is introduced. -/
namespace Solidity.Backend.MemoryOps

def sourceCalldataUintValues (E : Source.Env) (F : Source.Fr) (off len : Nat) :
    Source.R (List (Source.Val E.layout (.int .u256))) :=
  (List.range len).mapM fun j => Source.decodeWord E.layout (Source.cdWordAt F (off+32*j)) (.int .u256)

def sourceUintValuePayload {D : Source.Layout} (vs : List (Source.Val D (.int .u256))) : List PrimTy.uint.Denote :=
  vs.map fun v => calldataUint (.val v)

theorem source_uint_value_array {D : Source.Layout} (vs : List (Source.Val D (.int .u256))) :
    (Source.Data.array (D := D) (l := .memory) (n := none) vs.length
      (fun _ h => nomatch h) (fun i => .val (vs.get i)))=
      sourceUintMemory (sourceUintValuePayload vs) := by
  have array_ext {m n : Nat} (h : m=n)
      (f : Fin m → Source.Data D (.int .u256)) (g : Fin n → Source.Data D (.int .u256))
      (agree : ∀ i,f i=g ⟨i.val,by omega⟩) :
      (Source.Data.array (l := .memory) (n := none) m (fun _ h => nomatch h) f)=
        Source.Data.array (l := .memory) (n := none) n (fun _ h => nomatch h) g := by
    subst n
    have same : f=g := funext agree
    rw [same]
  unfold sourceUintMemory
  apply array_ext (by simp only [sourceUintValuePayload,List.length_map])
  intro i
  simp only [sourceUintValuePayload,List.get_eq_getElem,Fin.getElem_fin,List.getElem_map]
  exact calldataUint_exact (.val vs[i])

theorem source_cd_uint_run {E : Source.Env} {Γ : Source.RCtx}
    (F : Source.Fr) (off len : Nat) (y : Source.EMState E Γ) :
    (Source.cdToMem F (.array .memory (.int .u256) none) off len).run y=
      match sourceCalldataUintValues E F off len with
      | .error e => (.error e,y)
      | .ok vs =>
        let xs := sourceUintValuePayload vs
        (.ok (.val (.memRef rfl y.2.heap.next)),
          (y.1,{y.2 with heap := (y.2.heap.alloc ⟨.array .memory (.int .u256) none,sourceUintMemory xs⟩).1})) := by
  simp only [Source.cdToMem,Source.STy.loc?,Option.some.injEq,reduceCtorEq,dite_false]
  rw [Source.Hoare.run_bind,source_mapM_lift_run]
  unfold sourceCalldataUintValues
  cases hd : (List.range len).mapM (fun j => Source.decodeWord E.layout
      (Source.cdWordAt F (off+32*j)) (.int .u256)) with
  | error e => rfl
  | ok vs =>
    simp only [Source.Hoare.run_bind,source_uint_value_array]
    rfl

theorem source_decode_mapM_length {α β : Type} (f : α → Source.R β) (xs : List α)
    (vs : List β) (h : xs.mapM f=.ok vs) : vs.length=xs.length := by
  induction xs generalizing vs with
  | nil => cases Except.ok.inj h;rfl
  | cons x xs ih =>
    rw [List.mapM_cons] at h
    cases hd : f x with
    | error e => simp only [hd,bind,Except.bind] at h;cases h
    | ok v =>
      simp only [hd,bind,Except.bind] at h
      cases ht : xs.mapM f with
      | error e => simp only [ht] at h;cases h
      | ok tail =>
        simp only [ht,pure,Except.pure] at h
        have same : v::tail=vs := Except.ok.inj h
        rw [←same]
        simp only [List.length_cons,ih tail ht]

theorem sourceCalldataUintValues_length {E : Source.Env} {F : Source.Fr} {off len : Nat}
    {vs : List (Source.Val E.layout (.int .u256))} (h : sourceCalldataUintValues E F off len=.ok vs) :
    (sourceUintValuePayload vs).length=len := by
  unfold sourceUintValuePayload
  rw [List.length_map]
  exact (source_decode_mapM_length _ (List.range len) vs h).trans List.length_range

theorem SourceUintMemoryAt.transport {E : Source.Env} {Γ : Source.RCtx} {H K : HTy}
    {y z : Source.EMState E Γ} {addr : Nat} {hp : Heap H} {hq : Heap K}
    {e : H <+: K} {R : RefTy} {r : HRef H R} {a : ArrTy R (.prim .uint)}
    (hr : SourceUintMemoryAt y addr hp r a) (hk : Heap.Keeps e hp hq)
    (hs : ∀ b obj,y.2.heap.get b=some obj → z.2.heap.get b=some obj) :
    SourceUintMemoryAt z addr hq (r.wk e) a := by
  unfold SourceUintMemoryAt
  rw [hk r,MObj.elems_wk,List.map_id'' (f := MVal.wk e (.prim .uint)) (fun _ => rfl)]
  exact hs addr _ hr

/-- The actual computed payload is the only source of the new object. All old
occupied Source cells and intrinsic objects are framed; unused map entries have
no imposed constraints. Capacity is intrinsic validity, not Source admission. -/
theorem source_cd_uint_copy {E : Source.Env} {Γ : Source.RCtx} {H : HTy}
    (y : Source.EMState E Γ) (hp : Heap H) (address : Nat → Nat)
    (F : Source.Fr) (off len : Nat) (capacity : len<2^256)
    (SH : Source.HeapTy) (memOK : Source.MemOK E SH y) :
    match sourceCalldataUintValues E F off len with
    | .error e => (Source.cdToMem F (.array .memory (.int .u256) none) off len).run y=(.error e,y)
    | .ok vs => ∃ valid : (sourceUintValuePayload vs).length<2^256,
      let o : MObj H (.array (.prim .uint)) := ⟨sourceUintValuePayload vs,valid⟩
      let pair := hp.alloc o
      let ext := List.prefix_append H [RefTy.array (.prim .uint)]
      let address' := allocatedSourceAddress address H.length y.2.heap.next
      let z : Source.EMState E Γ :=
        (y.1,{y.2 with heap := (y.2.heap.alloc ⟨.array .memory (.int .u256) none,sourceUintMemory (sourceUintValuePayload vs)⟩).1})
      (Source.cdToMem F (.array .memory (.int .u256) none) off len).run y=(.ok (.val (.memRef rfl y.2.heap.next)),z) ∧
      Heap.Keeps ext hp pair.1 ∧
      SourceUintMemoryAt z (address' pair.2.id) pair.1 pair.2 .dyn ∧ Source.MemOK E SH z ∧
      pair.2.id=H.length ∧ address' pair.2.id=y.2.heap.next ∧
      (∀ i,i<H.length → address' i=address i) ∧
      (∀ R (q : HRef H R),(q.wk ext).id≠pair.2.id) ∧
      (∀ b obj,y.2.heap.get b=some obj → z.2.heap.get b=some obj ∧ b≠y.2.heap.next) ∧
      (∀ R (q : HRef H R) (a : ArrTy R (.prim .uint)),
        SourceUintMemoryAt y (address q.id) hp q a →
        SourceUintMemoryAt z (address' (q.wk ext).id) pair.1 (q.wk ext) a) ∧
      z.1=y.1 ∧ z.2.ex=y.2.ex ∧ z.2.events=y.2.events ∧ z.2.logs=y.2.logs ∧ z.2.fnLocals=y.2.fnLocals := by
  cases hd : sourceCalldataUintValues E F off len with
  | error error =>
    have run := source_cd_uint_run F off len y
    rw [hd] at run
    exact run
  | ok vs =>
    have valid : (sourceUintValuePayload vs).length<2^256 := by
      rw [sourceCalldataUintValues_length hd]
      exact capacity
    refine ⟨valid,?_⟩
    dsimp only
    let o : MObj H (.array (.prim .uint)) := ⟨sourceUintValuePayload vs,valid⟩
    let ext := List.prefix_append H [RefTy.array (.prim .uint)]
    let z : Source.EMState E Γ :=
      (y.1,{y.2 with heap := (y.2.heap.alloc ⟨.array .memory (.int .u256) none,
        sourceUintMemory (sourceUintValuePayload vs)⟩).1})
    have occupied : ∀ b obj,y.2.heap.get b=some obj → b≠y.2.heap.next := by
      intro b obj hb same
      subst b
      have fresh := Source.Heap.alloc_fresh y.2.heap
        ⟨.array .memory (.int .u256) none,sourceUintMemory (sourceUintValuePayload vs)⟩
      change y.2.heap.get y.2.heap.next=none at fresh
      rw [fresh] at hb
      cases hb
    have preserved : ∀ b obj,y.2.heap.get b=some obj → z.2.heap.get b=some obj := by
      intro b obj hb
      exact (Source.Heap.alloc_other y.2.heap _ (occupied b obj hb)).trans hb
    have keeps : Heap.Keeps ext hp (hp.alloc o).1 := hp.keeps_alloc o
    have new : SourceUintMemoryAt z y.2.heap.next (hp.alloc o).1 (hp.alloc o).2 .dyn := by
      unfold SourceUintMemoryAt
      rw [hp.get_alloc o,MObj.elems_wk,List.map_id'' (f := MVal.wk ext (.prim .uint)) (fun _ => rfl)]
      rw [MObj.elems_dyn]
      exact Source.Heap.alloc_get y.2.heap _
    have mok := source_uint_alloc_memOK (E := E) (Γ := Γ) SH (sourceUintValuePayload vs) y memOK
    rw [source_uint_alloc y (sourceUintValuePayload vs)] at mok
    have run := source_cd_uint_run F off len y
    rw [hd] at run
    have oldAddress := allocatedSourceAddress_old address (H := H) y.2.heap.next
    refine ⟨run,keeps,?_,mok.1,rfl,?_,oldAddress,?_,?_,?_,rfl,rfl,rfl,rfl,rfl⟩
    · change SourceUintMemoryAt z (allocatedSourceAddress address H.length y.2.heap.next H.length) _ _ .dyn
      rw [allocatedSourceAddress,if_pos rfl]
      exact new
    · exact if_pos rfl
    · intro R q
      exact Nat.ne_of_lt q.id_lt
    · intro b obj hb
      exact ⟨preserved b obj hb,occupied b obj hb⟩
    · intro R q a hq
      change SourceUintMemoryAt z (allocatedSourceAddress address H.length y.2.heap.next q.id) _ _ a
      rw [oldAddress _ q.id_lt]
      exact hq.transport keeps preserved

/-- Unsupported genuine fixed Source target is a stuck conversion, not a
successful dynamic copy or an ABI bounds panic. No Source admission is added. -/
theorem source_cd_uint_fixed_stuck {E : Source.Env} {Γ : Source.RCtx}
    (F : Source.Fr) (off len n : Nat) (y : Source.EMState E Γ) :
    (Source.cdToMem F (.array .memory (.int .u256) (some n)) off len).run y=
      (.error (.stuck "calldata conversion"),y) := by
  rfl
/-- info: 'Solidity.Backend.MemoryOps.source_uint_value_array' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms source_uint_value_array
/-- info: 'Solidity.Backend.MemoryOps.source_cd_uint_run' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms source_cd_uint_run
/-- info: 'Solidity.Backend.MemoryOps.source_decode_mapM_length' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms source_decode_mapM_length
/-- info: 'Solidity.Backend.MemoryOps.sourceCalldataUintValues_length' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms sourceCalldataUintValues_length
/-- info: 'Solidity.Backend.MemoryOps.SourceUintMemoryAt.transport' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms SourceUintMemoryAt.transport
/-- info: 'Solidity.Backend.MemoryOps.source_cd_uint_copy' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms source_cd_uint_copy
/-- info: 'Solidity.Backend.MemoryOps.source_cd_uint_fixed_stuck' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms source_cd_uint_fixed_stuck
/-- Actual resolved implicit conversion in either existing pipeline. -/
def sourceUintCalldataCopy {E : Source.Env} {Γ : Source.RCtx}
    (i : Source.Idx Γ (.array .calldata (.int .u256) none)) :
    Source.RExpr E Γ (.array .memory (.int .u256) none) :=
  .conv (.local i) (.inl rfl)

theorem source_cd_uint_eval {E : Source.Env} {Γ : Source.RCtx}
    (G : Source.Glob E) (F : Source.Fr) (n : Nat) (y : Source.EMState E Γ)
    (i : Source.Idx Γ (.array .calldata (.int .u256) none)) (off len : Nat)
    (hi : y.1.get i=.cdRef rfl off len) :
    (Source.evalE G F (n+2) (sourceUintCalldataCopy i)).run y=
      (Source.cdToMem F (.array .memory (.int .u256) none) off len).run y := by
  rw [sourceUintCalldataCopy,Source.evalE,Source.Hoare.run_bind,source_local_value_run G F n y i _ hi]
  change (Source.convRV F (n+1) (.array .memory (.int .u256) none)
    (.val (.cdRef rfl off len) : Source.RVal E.layout (.array .calldata (.int .u256) none))).run y=_
  unfold Source.convRV
  rw [dif_neg (show (Source.STy.array .calldata (.int .u256) none)≠.array .memory (.int .u256) none from by intro h;cases h)]
  rfl

/-- info: 'Solidity.Backend.MemoryOps.source_cd_uint_eval' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms source_cd_uint_eval
/-- The existing raw helper pads missing words; this does not establish ABI
entry/tail admission. Runtime offsets and counts retain their existing scope. -/
theorem sourceCalldataUintValues_empty {E : Source.Env} (F : Source.Fr) (hcd : F.cd=[])
    (off len : Nat) : sourceCalldataUintValues E F off len=
      .ok (List.replicate len (sourceUint (D := E.layout) (⟨0,by decide⟩ : PrimTy.uint.Denote))) := by
  have zeros : ∀ k,Source.beValue (List.replicate k (0 : UInt8))=0 := by
    intro k
    unfold Source.beValue
    induction k with
    | zero => rfl
    | succ k ih =>
      rw [List.replicate_succ,List.foldl_cons]
      change (List.replicate k (0 : UInt8)).foldl (fun acc b => acc*256+b.toNat) (0*256+0)=0
      simpa only [Nat.zero_mul,Nat.zero_add] using ih
  have each : (fun j : Nat => Source.decodeWord E.layout (Source.cdWordAt F (off+32*j)) (.int .u256))=
      (fun _ => (.ok (sourceUint (D := E.layout) (⟨0,by decide⟩ : PrimTy.uint.Denote)) : Source.R (Source.Val E.layout (.int .u256)))) := by
    funext j
    simp only [Source.cdWordAt,hcd,List.drop_nil,Source.fitBytes,List.nil_append,List.take_replicate,Nat.min_self]
    rw [zeros]
    rfl
  have constant : ∀ is : List Nat,
      is.mapM (fun _ => (.ok (sourceUint (D := E.layout) (⟨0,by decide⟩ : PrimTy.uint.Denote)) : Source.R (Source.Val E.layout (.int .u256))))=
        .ok (List.replicate is.length (sourceUint (D := E.layout) (⟨0,by decide⟩ : PrimTy.uint.Denote))) := by
    intro is
    induction is with
    | nil => rfl
    | cons i is ih =>
      rw [List.mapM_cons]
      simp only [bind,Except.bind,ih,List.length_cons,List.replicate_succ]
      rfl
  unfold sourceCalldataUintValues
  rw [each,constant,List.length_range]

/-- info: 'Solidity.Backend.MemoryOps.sourceCalldataUintValues_empty' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms sourceCalldataUintValues_empty
end Solidity.Backend.MemoryOps
