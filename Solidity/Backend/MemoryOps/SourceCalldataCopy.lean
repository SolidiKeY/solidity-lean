import Solidity.Backend.MemoryOps.SourceStructGrowth
import Solidity.Backend.MemoryOps.CalldataTransfer
import Solidity.Source.Calldata

/-! Actual independent Source calldata-to-memory conversion. Existing decodeWord,
cdToMem, allocRef and intrinsic alloc are consumed; this is not another ABI
decoder, Source evaluator, constructor implementation or target compiler. -/
namespace Solidity.Backend.MemoryOps

/-- Run the existing elementary decoder in its declared left-to-right order. -/
def sourceCalldataBoolValues (E : Source.Env) (F : Source.Fr) (off len : Nat) :
    Source.R (List (Source.Val E.layout .bool)) :=
  (List.range len).mapM fun j => Source.decodeWord E.layout (Source.cdWordAt F (off+32*j)) .bool

/-- Eliminate actual typed decoded values; no payload or correctness relation
is supplied to the operation. -/
def sourceBoolValuePayload {D : Source.Layout} (vs : List (Source.Val D .bool)) : List Bool :=
  vs.map fun v => calldataBool (.val v)

/-- Lifting the published pure decoder cannot change the Source state, even
when a later element fails. This is ordinary List/Except composition only. -/
theorem source_mapM_lift_run {E : Source.Env} {Γ : Source.RCtx} {α β : Type}
    (f : α → Source.R β) (xs : List α) (y : Source.EMState E Γ) :
    (xs.mapM (fun x => Source.EM.lift (E := E) (Γ := Γ) (f x))).run y=
      (xs.mapM f,y) := by
  induction xs with
  | nil => rfl
  | cons x xs ih =>
    rw [List.mapM_cons,List.mapM_cons,Source.Hoare.run_bind]
    cases hx : f x with
    | error e => simp only [Source.EM.lift];rfl
    | ok v =>
      simp only [Source.EM.lift]
      change ((xs.mapM (fun x => Source.EM.lift (f x))) >>= fun vs => pure (v::vs)).run y=_
      rw [Source.Hoare.run_bind,ih]
      cases xs.mapM f <;> rfl

private theorem source_bool_array_ext (D : Source.Layout) {m n : Nat} (h : m=n)
    (f : Fin m → Source.Data D .bool) (g : Fin n → Source.Data D .bool)
    (agree : ∀ i,f i=g ⟨i.val,by omega⟩) :
    (Source.Data.array (D := D) (l := .memory) (n := none) m (fun _ h => nomatch h) f)=
      Source.Data.array (D := D) (l := .memory) (n := none) n (fun _ h => nomatch h) g := by
  subst n
  have same : f=g := funext agree
  rw [same]

/-- Exact equality of two views of the same published typed values. -/
theorem source_bool_value_array {D : Source.Layout} (vs : List (Source.Val D .bool)) :
    (Source.Data.array (D := D) (l := .memory) (n := none) vs.length
      (fun _ h => nomatch h) (fun i => .val (vs.get i)))=
      sourceBoolMemory (sourceBoolValuePayload vs) := by
  unfold sourceBoolMemory
  apply source_bool_array_ext D (by simp only [sourceBoolValuePayload,List.length_map])
  intro i
  simp only [sourceBoolValuePayload,List.get_eq_getElem,Fin.getElem_fin,List.getElem_map]
  exact calldataBool_exact (.val vs[i])

/-- The actual Source copy either fails before allocation, retaining its
actual input state, or allocates the actual decoded payload. No successful
copy, postheap or conversion agreement is a premise. -/
theorem source_cd_bool_run {E : Source.Env} {Γ : Source.RCtx}
    (F : Source.Fr) (off len : Nat) (y : Source.EMState E Γ) :
    (Source.cdToMem F (.array .memory .bool none) off len).run y=
      match sourceCalldataBoolValues E F off len with
      | .error e => (.error e,y)
      | .ok vs =>
        let bs := sourceBoolValuePayload vs
        (.ok (.val (.memRef rfl y.2.heap.next)),
          (y.1,{y.2 with heap := (y.2.heap.alloc ⟨SourceBoolArrayTy,sourceBoolMemory bs⟩).1})) := by
  simp only [Source.cdToMem,Source.STy.loc?,Option.some.injEq,reduceCtorEq,dite_false]
  rw [Source.Hoare.run_bind,source_mapM_lift_run]
  unfold sourceCalldataBoolValues
  cases hd : (List.range len).mapM (fun j => Source.decodeWord E.layout (Source.cdWordAt F (off+32*j)) .bool) with
  | error e => rfl
  | ok vs =>
    simp only [Source.Hoare.run_bind,source_bool_value_array]
    rfl

private theorem except_mapM_length {α β : Type} (f : α → Source.R β) (xs : List α) :
    ∀ vs,xs.mapM f=.ok vs → vs.length=xs.length := by
  induction xs with
  | nil => intro vs h;cases Except.ok.inj h;rfl
  | cons x xs ih =>
    intro vs h
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

/-- Successful traversal has exactly the runtime element count. -/
theorem sourceCalldataBoolValues_length {E : Source.Env} {F : Source.Fr} {off len : Nat}
    {vs : List (Source.Val E.layout .bool)} (h : sourceCalldataBoolValues E F off len=.ok vs) :
    (sourceBoolValuePayload vs).length=len := by
  unfold sourceBoolValuePayload
  rw [List.length_map]
  exact (except_mapM_length _ (List.range len) vs h).trans List.length_range

/-- Actual raw-input conversion followed by the already published paired
allocation observer. The result is classified by its COMPUTED decoder; there
is no supplied payload, desired successful run or postcorrespondence premise.
Capacity is existing intrinsic array validity, not Source admission. -/
theorem SourceBoolStructAt.cd_bool_copy {E : Source.Env} {Γ : Source.RCtx} {H : HTy}
    {y : Source.EMState E Γ} {addr : Nat} {hp : Heap H} {r : HRef H (.struct s)}
    {address : Nat → Nat} {layout : SourceBoolStructLayout E dn s tag child}
    (hr : SourceBoolStructAt y addr hp r address layout)
    (F : Source.Fr) (off len : Nat) (capacity : len<2^256)
    (SH : Source.HeapTy) (memOK : Source.MemOK E SH y) :
    match sourceCalldataBoolValues E F off len with
    | .error e => (Source.cdToMem F SourceBoolArrayTy off len).run y=(.error e,y)
    | .ok vs => ∃ valid : (sourceBoolValuePayload vs).length<2^256,
      let o : MObj H (.array (.prim .bool)) := ⟨sourceBoolValuePayload vs,valid⟩
      let pair := hp.alloc o
      let e := List.prefix_append H [RefTy.array (.prim .bool)]
      let address' := allocatedSourceAddress address H.length y.2.heap.next
      let z : Source.EMState E Γ :=
        (y.1,{y.2 with heap := (y.2.heap.alloc ⟨SourceBoolArrayTy,sourceBoolMemory (sourceBoolValuePayload vs)⟩).1})
      (Source.cdToMem F SourceBoolArrayTy off len).run y=(.ok (.val (.memRef rfl y.2.heap.next)),z) ∧
      Heap.Keeps e hp pair.1 ∧ SourceBoolStructAt z addr pair.1 (r.wk e) address' layout ∧
      SourceBoolMemoryAt z (address' pair.2.id) pair.1 pair.2 .dyn ∧ Source.MemOK E SH z ∧
      pair.2.id=H.length ∧ address' pair.2.id=y.2.heap.next ∧
      (∀ i,i<H.length → address' i=address i) ∧
      (∀ R (q : HRef H R),(q.wk e).id≠pair.2.id) ∧
      addr≠y.2.heap.next ∧ address (hp.field r layout.child_type).id≠y.2.heap.next ∧
      (∀ q : HRef H (.array (.prim .bool)),SourceBoolMemoryAt y (address q.id) hp q .dyn →
        SourceBoolMemoryAt z (address' (q.wk e).id) pair.1 (q.wk e) .dyn ∧ address q.id≠y.2.heap.next) ∧
      z.1=y.1 ∧ z.2.ex=y.2.ex ∧ z.2.events=y.2.events ∧ z.2.logs=y.2.logs ∧ z.2.fnLocals=y.2.fnLocals := by
  cases hd : sourceCalldataBoolValues E F off len with
  | error e =>
    have run := source_cd_bool_run F off len y
    rw [hd] at run
    exact run
  | ok vs =>
    have valid : (sourceBoolValuePayload vs).length<2^256 := by
      rw [sourceCalldataBoolValues_length hd]
      exact capacity
    refine ⟨valid,?_⟩
    dsimp only
    let o : MObj H (.array (.prim .bool)) := ⟨sourceBoolValuePayload vs,valid⟩
    obtain ⟨_,keep,old,new,mok,fresh,freshAddress,oldAddress,distinct,parentNe,childNe,aliases,loc,ex,ev,logs,fn⟩ :=
      hr.alloc_bool o SH memOK
    have run := source_cd_bool_run F off len y
    rw [hd] at run
    refine ⟨run,keep,?_,?_,?_,fresh,freshAddress,oldAddress,distinct,parentNe,childNe,?_,rfl,rfl,rfl,rfl,rfl⟩
    · simpa only [MObj.elems_dyn] using old
    · simpa only [MObj.elems_dyn] using new
    · simpa only [MObj.elems_dyn] using mok
    · simpa only [MObj.elems_dyn] using aliases

/-- Ordered prefix success and the actual first failed decoder call expose
real reached validation states. No Source allocation or suffix state is invented. -/
theorem source_cd_bool_first_error {E : Source.Env} {Γ : Source.RCtx}
    (F : Source.Fr) (off len : Nat) (y : Source.EMState E Γ)
    (acceptedIndices pendingIndices : List Nat) (i : Nat) (accepted : List (Source.Val E.layout .bool)) (e : Source.Halt)
    (order : List.range len=acceptedIndices++i::pendingIndices)
    (hp : acceptedIndices.mapM (fun j => Source.decodeWord E.layout (Source.cdWordAt F (off+32*j)) .bool)=.ok accepted)
    (bad : Source.decodeWord E.layout (Source.cdWordAt F (off+32*i)) .bool=.error e) :
    (acceptedIndices.mapM (fun j => Source.EM.lift (E := E) (Γ := Γ)
      (Source.decodeWord E.layout (Source.cdWordAt F (off+32*j)) .bool))).run y=(.ok accepted,y) ∧
    (Source.EM.lift (E := E) (Γ := Γ) (Source.decodeWord E.layout (Source.cdWordAt F (off+32*i)) .bool)).run y=(.error e,y) ∧
    (Source.cdToMem F SourceBoolArrayTy off len).run y=(.error e,y) := by
  have full : sourceCalldataBoolValues E F off len=.error e := by
    unfold sourceCalldataBoolValues
    rw [order,List.mapM_append,List.mapM_cons]
    simp only [hp,bad,bind,Except.bind]
  refine ⟨?_,?_,?_⟩
  · rw [source_mapM_lift_run,hp]
  · rw [bad];rfl
  · rw [source_cd_bool_run,full]

/-- The published helper zero-pads raw reads beyond the frame. This is not
ABI entry success: a positive-length empty frame need not pass cdTail. -/
theorem sourceCalldataBoolValues_empty {E : Source.Env} (F : Source.Fr) (hcd : F.cd=[])
    (off len : Nat) :
    sourceCalldataBoolValues E F off len=.ok (List.replicate len (Source.Val.bool false)) := by
  have zeros : ∀ k,Source.beValue (List.replicate k (0 : UInt8))=0 := by
    intro k
    unfold Source.beValue
    induction k with
    | zero => rfl
    | succ k ih =>
      rw [List.replicate_succ,List.foldl_cons]
      change (List.replicate k (0 : UInt8)).foldl (fun acc b => acc*256+b.toNat) (0*256+0)=0
      simpa only [Nat.zero_mul,Nat.zero_add] using ih
  have each : (fun j : Nat => Source.decodeWord E.layout (Source.cdWordAt F (off+32*j)) .bool)=
      (fun _ => (.ok (Source.Val.bool false) : Source.R (Source.Val E.layout .bool))) := by
    funext j
    simp only [Source.cdWordAt,hcd,List.drop_nil,Source.fitBytes,List.nil_append,List.take_replicate,Nat.min_self]
    rw [zeros]
    rfl
  have constant : ∀ is : List Nat,
      is.mapM (fun _ => (.ok (Source.Val.bool false) : Source.R (Source.Val E.layout .bool)))=
        .ok (List.replicate is.length (Source.Val.bool false)) := by
    intro is
    induction is with
    | nil => rfl
    | cons i is ih =>
      rw [List.mapM_cons]
      simp only [bind,Except.bind,ih,List.length_cons,List.replicate_succ]
      rfl
  unfold sourceCalldataBoolValues
  rw [each,constant,List.length_range]

/-- info: 'Solidity.Backend.MemoryOps.source_mapM_lift_run' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms source_mapM_lift_run
/-- info: 'Solidity.Backend.MemoryOps.source_bool_value_array' depends on axioms: [propext, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms source_bool_value_array
/-- info: 'Solidity.Backend.MemoryOps.source_cd_bool_run' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms source_cd_bool_run
/-- info: 'Solidity.Backend.MemoryOps.sourceCalldataBoolValues_length' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms sourceCalldataBoolValues_length
/-- info: 'Solidity.Backend.MemoryOps.SourceBoolStructAt.cd_bool_copy' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms SourceBoolStructAt.cd_bool_copy
/-- info: 'Solidity.Backend.MemoryOps.source_cd_bool_first_error' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms source_cd_bool_first_error
/-- info: 'Solidity.Backend.MemoryOps.sourceCalldataBoolValues_empty' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms sourceCalldataBoolValues_empty

/-- Actual resolved implicit calldata-to-memory conversion, with the existing
Source typing evidence; no new admission/profile rule. -/
def sourceBoolCalldataCopy {E : Source.Env} {Γ : Source.RCtx}
    (i : Source.Idx Γ (.array .calldata .bool none)) : Source.RExpr E Γ SourceBoolArrayTy :=
  .conv (.local i) (.inl rfl)

theorem source_cd_bool_eval {E : Source.Env} {Γ : Source.RCtx}
    (G : Source.Glob E) (F : Source.Fr) (n : Nat) (y : Source.EMState E Γ)
    (i : Source.Idx Γ (.array .calldata .bool none)) (off len : Nat)
    (hi : y.1.get i=.cdRef rfl off len) :
    (Source.evalE G F (n+2) (sourceBoolCalldataCopy i)).run y=
      (Source.cdToMem F SourceBoolArrayTy off len).run y := by
  rw [sourceBoolCalldataCopy,Source.evalE,Source.Hoare.run_bind,source_local_value_run G F n y i _ hi]
  change (Source.convRV F (n+1) (.array .memory .bool none) (.val (.cdRef rfl off len) : Source.RVal E.layout (.array .calldata .bool none))).run y=_
  unfold Source.convRV
  rw [dif_neg (show (Source.STy.array .calldata .bool none)≠.array .memory .bool none from by intro h;cases h)]
  rfl

/-- info: 'Solidity.Backend.MemoryOps.source_cd_bool_eval' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms source_cd_bool_eval


/-- Runtime-length zero-padded Source conversion; this is the helper's actual
semantics, not an assertion that empty calldata passes ABI entry checks. -/
theorem source_cd_bool_empty_run {E : Source.Env} {Γ : Source.RCtx}
    (F : Source.Fr) (hcd : F.cd=[]) (off len : Nat) (y : Source.EMState E Γ) :
    (Source.cdToMem F SourceBoolArrayTy off len).run y=
      (.ok (.val (.memRef rfl y.2.heap.next)),
        (y.1,{y.2 with heap := (y.2.heap.alloc ⟨SourceBoolArrayTy,sourceBoolMemory (List.replicate len false)⟩).1})) := by
  rw [source_cd_bool_run,sourceCalldataBoolValues_empty F hcd]
  simp only [sourceBoolValuePayload,List.map_replicate]
  rfl

/-- info: 'Solidity.Backend.MemoryOps.source_cd_bool_empty_run' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms source_cd_bool_empty_run

end Solidity.Backend.MemoryOps
