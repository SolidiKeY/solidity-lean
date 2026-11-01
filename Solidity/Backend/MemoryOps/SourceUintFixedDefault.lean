import Solidity.Backend.MemoryOps.SourceUintMemory
import Solidity.Backend.MemoryOps.SourceDeclaration
import Solidity.Evm.MemoryDefaultBuilder

/-! Genuine fixed Source uint defaults. Existing Data/Heap/typed fixed objects and
published fixed builders are used unchanged. Low-level zero-size facts do not
establish Source admission; the supported Source/word application is positive. -/
namespace Solidity.Backend.MemoryOps

/-- Typed conversion of an EXISTING intrinsic fixed object; no dynamic STy cast. -/
def sourceUintFixedObject {D : Source.Layout} {H : HTy} {n : Nat}
    (o : MObj H (.fixed (.prim .uint) n)) : Source.Data D (.array .memory (.int .u256) (some n)) :=
  .array n (fun _ h => by cases h;rfl) (fun i => .val (sourceUint (o.1[i.val]'(by rw [o.2];exact i.isLt))))

def SourceUintFixedAt {E : Source.Env} {Γ : Source.RCtx} {H : HTy} {n : Nat}
    (y : Source.EMState E Γ) (address : Nat) (hp : Heap H) (r : HRef H (.fixed (.prim .uint) n)) : Prop :=
  y.2.heap.get address=some ⟨.array .memory (.int .u256) (some n),sourceUintFixedObject (hp.get r)⟩

def sourceUintFixedZero {D : Source.Layout} (n : Nat) : Source.Data D (.array .memory (.int .u256) (some n)) :=
  .array n (fun _ h => by cases h;rfl) (fun _ => .val (sourceUint (PrimTy.dflt .uint)))

private theorem zero_uint_run {E : Source.Env} {Γ : Source.RCtx} (y : Source.EMState E Γ) (fuel : Nat) :
    (Source.zeroVal (E := E) (Γ := Γ) (fuel+1) (.int .u256)).run y=(.ok (sourceUint (PrimTy.dflt .uint)),y) := by
  rfl

/-- Actual recursive evaluator, at fuel parametrized by the declared length. -/
theorem source_uint_zeroElems_run {E : Source.Env} {Γ : Source.RCtx} (y : Source.EMState E Γ) (n : Nat) :
    (Source.zeroElems (E := E) (Γ := Γ) (n+1) (.int .u256) n).run y=
      (.ok (fun _ => Source.Data.val (D := E.layout) (sourceUint (PrimTy.dflt .uint))),y) := by
  induction n with
  | zero =>
    have hf : (Fin.elim0 : Fin 0 → Source.Data E.layout (.int .u256))=
        (fun _ => Source.Data.val (D := E.layout) (sourceUint (PrimTy.dflt .uint))) := by
      funext i;exact i.elim0
    change (Except.ok Fin.elim0,y)=_
    rw [hf]
  | succ n ih =>
    rw [Source.zeroElems,Source.Hoare.run_bind,zero_uint_run]
    change (Source.zeroElems (n+1) (.int .u256) n >>= fun f =>
      pure (Source.finCons (Source.Data.val (D := E.layout) (sourceUint (PrimTy.dflt .uint))) f)).run y=_
    rw [Source.Hoare.run_bind,ih]
    have hf : Source.finCons (Source.Data.val (D := E.layout) (sourceUint (PrimTy.dflt .uint)))
        (fun _ : Fin n => Source.Data.val (D := E.layout) (sourceUint (PrimTy.dflt .uint)))=
        (fun _ : Fin (n+1) => Source.Data.val (D := E.layout) (sourceUint (PrimTy.dflt .uint))) := by
      funext i
      unfold Source.finCons
      split <;> rfl
    change (Except.ok (Source.finCons _ _),y)=_
    rw [hf]

theorem source_uint_fixed_zeroData {E : Source.Env} {Γ : Source.RCtx} (y : Source.EMState E Γ) (n : Nat) :
    (Source.zeroData (E := E) (Γ := Γ) (n+2) (.array .memory (.int .u256) (some n))).run y=
      (.ok (sourceUintFixedZero n),y) := by
  rw [Source.zeroData,Source.Hoare.run_bind,source_uint_zeroElems_run]
  rfl

theorem source_uint_fixed_zeroVal {E : Source.Env} {Γ : Source.RCtx} (y : Source.EMState E Γ) (n : Nat) :
    (Source.zeroVal (E := E) (Γ := Γ) (n+3) (.array .memory (.int .u256) (some n))).run y=
      (.ok (.memRef rfl y.2.heap.next),
        (y.1,{y.2 with heap := (y.2.heap.alloc ⟨.array .memory (.int .u256) (some n),sourceUintFixedZero n⟩).1})) := by
  rw [Source.zeroVal]
  change (Source.zeroData (n+2) (.array .memory (.int .u256) (some n)) >>= fun x => Source.allocRef x).run y=_
  rw [Source.Hoare.run_bind,source_uint_fixed_zeroData]
  rfl

/-- Pointwise fixed conversion derives from actual intrinsic contents. -/
theorem sourceUintFixedObject_zero {D : Source.Layout} {H : HTy} {n : Nat}
    (o : MObj H (.fixed (.prim .uint) n)) (he : o.1=List.replicate n (PrimTy.dflt .uint)) :
    sourceUintFixedObject (D := D) o=sourceUintFixedZero n := by
  rcases o with ⟨xs,hxs⟩
  change xs=List.replicate n (PrimTy.dflt .uint) at he
  subst xs
  unfold sourceUintFixedObject sourceUintFixedZero
  congr 1
  funext i
  simp only [List.getElem_replicate]

/-- Supported POSITIVE fixed Source constructor, independently related to the
actual published intrinsic default. Neither successful execution nor postagreement
is assumed. This does not assert general Source type admission. -/
theorem source_uint_fixed_intrinsic {E : Source.Env} {Γ : Source.RCtx} {H : HTy}
    (y : Source.EMState E Γ) (hp : Heap H) (n : Nat) (_hn : 0<n) :
    let g := hp.allocDefault (.fixed (.prim .uint) n) rfl
    let z := ((Source.zeroVal (E := E) (Γ := Γ) (n+3) (.array .memory (.int .u256) (some n))).run y).2
    SourceUintFixedAt z y.2.heap.next g.heap g.val ∧
      MObj.elems .fixed (g.heap.get g.val)=List.replicate n (PrimTy.dflt .uint) ∧
      Heap.Keeps g.ext hp g.heap ∧ g.val.id=H.length := by
  dsimp only
  have he : MObj.elems .fixed ((hp.allocDefault (.fixed (.prim .uint) n) rfl).heap.get
      (hp.allocDefault (.fixed (.prim .uint) n) rfl).val)=List.replicate n (PrimTy.dflt .uint) := by
    rw [Evm.Memory.Objects.defaultFixed_copy]
    change MObj.elems .fixed ((hp.alloc (Evm.Memory.Objects.defaultFixed .uint n)).1.get
      (hp.alloc (Evm.Memory.Objects.defaultFixed .uint n)).2)=_
    rw [Heap.get_alloc,MObj.elems_wk,MObj.elems_fixed]
    simp only [Evm.Memory.Objects.defaultFixed,List.map_replicate]
    rfl
  refine ⟨?_,he,SVal.keeps_copyStToM _ rfl hp,?_⟩
  · unfold SourceUintFixedAt
    rw [source_uint_fixed_zeroVal,sourceUintFixedObject_zero _ (by simpa only [MObj.elems_fixed] using he)]
    exact Source.Heap.alloc_get _ _
  · rw [Evm.Memory.Objects.defaultFixed_copy]
    rfl

/-- Insufficient recursive fuel returns the actual unchanged state, even when
some primitive zeros have been computed. Primitive elements allocate no children. -/
theorem source_uint_zeroElems_timeout {E : Source.Env} {Γ : Source.RCtx}
    (y : Source.EMState E Γ) (fuel n : Nat) (hf : fuel≤n) :
    (Source.zeroElems (E := E) (Γ := Γ) fuel (.int .u256) n).run y=(.error .timeout,y) := by
  induction fuel generalizing n with
  | zero => cases n <;> rfl
  | succ fuel ih =>
    cases n with
    | zero => omega
    | succ n =>
      cases fuel with
      | zero => rfl
      | succ k =>
        rw [Source.zeroElems,Source.Hoare.run_bind,zero_uint_run]
        change (Source.zeroElems (k+1) (.int .u256) n >>= fun f =>
          pure (Source.finCons (Source.Data.val (D := E.layout) (sourceUint (PrimTy.dflt .uint))) f)).run y=_
        rw [Source.Hoare.run_bind,ih n (by omega)]

theorem source_uint_fixed_zeroData_timeout {E : Source.Env} {Γ : Source.RCtx}
    (y : Source.EMState E Γ) (fuel n : Nat) (hf : fuel≤n+1) :
    (Source.zeroData (E := E) (Γ := Γ) fuel (.array .memory (.int .u256) (some n))).run y=(.error .timeout,y) := by
  cases fuel with
  | zero => rfl
  | succ k => rw [Source.zeroData,Source.Hoare.run_bind,source_uint_zeroElems_timeout y k n (by omega)]

theorem source_uint_fixed_zeroVal_timeout {E : Source.Env} {Γ : Source.RCtx}
    (y : Source.EMState E Γ) (fuel n : Nat) (hf : fuel≤n+2) :
    (Source.zeroVal (E := E) (Γ := Γ) fuel (.array .memory (.int .u256) (some n))).run y=(.error .timeout,y) := by
  cases fuel with
  | zero => rfl
  | succ k =>
    rw [Source.zeroVal]
    change (Source.zeroData k (.array .memory (.int .u256) (some n)) >>= fun x => Source.allocRef x).run y=_
    rw [Source.Hoare.run_bind,source_uint_fixed_zeroData_timeout y k n (by omega)]

/-- Actual declared fixed length, including the dependent element-conversion
proof. This observer never identifies Source fixed and dynamic types. -/
theorem SourceUintFixedAt.read {E : Source.Env} {Γ : Source.RCtx} {H : HTy} {n : Nat}
    {y : Source.EMState E Γ} {address : Nat} {hp : Heap H} {r : HRef H (.fixed (.prim .uint) n)}
    (hr : SourceUintFixedAt y address hp r) (i : Nat) (hi : i<n) :
    (Source.memElem (E := E) (Γ := Γ) address i (.int .u256)).run y=
      (.ok (sourceUint ((hp.get r).1[i]'(by rw [(hp.get r).2];exact hi))),y) := by
  rw [Source.memElem,Source.Hoare.run_bind,source_heapObj_run y address _ hr]
  simp only [sourceUintFixedObject,hi,↓reduceDIte,Source.Data.asVal]
  rfl

theorem SourceUintFixedAt.bounds {E : Source.Env} {Γ : Source.RCtx} {H : HTy} {n : Nat}
    {y : Source.EMState E Γ} {address : Nat} {hp : Heap H} {r : HRef H (.fixed (.prim .uint) n)}
    (hr : SourceUintFixedAt y address hp r) (i : Nat) (hi : n≤i) :
    (Source.memElem (E := E) (Γ := Γ) address i (.int .u256)).run y=
      (.error (.revert (Source.panicData .index)),y) := by
  rw [Source.memElem,Source.Hoare.run_bind,source_heapObj_run y address _ hr]
  simp only [sourceUintFixedObject,show ¬i<n from Nat.not_lt.mpr hi,↓reduceDIte]
  rfl

theorem sourceUintFixedObject_wk {D : Source.Layout} {H K : HTy} {n : Nat} (ext : H.IsPrefix K)
    (o : MObj H (.fixed (.prim .uint) n)) :
    sourceUintFixedObject (D := D) (MObj.wk ext (.fixed (.prim .uint) n) o)=sourceUintFixedObject o := by
  unfold sourceUintFixedObject
  congr 1
  funext i
  simp only [MObj.wk,List.getElem_map,MVal.wk]

theorem SourceUintFixedAt.keeps {E : Source.Env} {Γ : Source.RCtx} {H K : HTy} {n : Nat}
    {y : Source.EMState E Γ} {address : Nat} {hp : Heap H} {hq : Heap K} {r : HRef H (.fixed (.prim .uint) n)}
    (hr : SourceUintFixedAt y address hp r) (ext : H.IsPrefix K) (hk : Heap.Keeps ext hp hq) :
    SourceUintFixedAt y address hq (r.wk ext) := by
  unfold SourceUintFixedAt at hr ⊢
  rw [hk r,sourceUintFixedObject_wk]
  exact hr

/-- Existing published Source invariant theorem, specialized without reproducing
its recursive constructors or asserting success as a premise. -/
theorem source_uint_fixed_memOK {E : Source.Env} {Γ : Source.RCtx} (SH : Source.HeapTy) (n : Nat) :
    Source.Hoare (Source.MemOK E SH)
      (Source.zeroVal (E := E) (Γ := Γ) (n+3) (.array .memory (.int .u256) (some n)))
      (fun v y => Source.MemOK E SH y ∧ v.RefOK E y.2.heap.ty) (fun _ y => Source.MemOK E SH y) :=
  (Source.zeroOK (E := E) (Γ := Γ) (n+3)).val SH _

/-- Actual Source declaration/context extension. The numeric fixed length stays
in the new local type, while the existing intrinsic builder supplies its root. -/
theorem source_uint_fixed_declaration {E : Source.Env} {Γ : Source.RCtx} {H : HTy}
    (G : Source.Glob E) (F : Source.Fr) (y : Source.EMState E Γ) (hp : Heap H)
    (n : Nat) (hn : 0<n) (SH : Source.HeapTy) (hmem : Source.MemOK E SH y) :
    let SA := Source.STy.array .memory (.int .u256) (some n)
    let g := hp.allocDefault (.fixed (.prim .uint) n) rfl
    let z : Source.EMState E Γ :=
      (y.1,{y.2 with heap := (y.2.heap.alloc ⟨SA,sourceUintFixedZero n⟩).1})
    (Source.execS G F (n+4) Γ.length none (.declVar SA : Source.RStmt E [] false .body Γ (SA::Γ)) y.1).run (.nil,y.2)=
      (.ok (.normal (.cons (.memRef rfl y.2.heap.next) z.1)),(.nil,z.2)) ∧
    SourceUintFixedAt (.cons (.memRef rfl y.2.heap.next : Source.Val E.layout SA) z.1,z.2) y.2.heap.next g.heap g.val ∧
    Source.MemOK E SH (.cons (.memRef rfl y.2.heap.next : Source.Val E.layout SA) z.1,z.2) := by
  dsimp only
  have hz := source_uint_fixed_zeroVal y n
  have hr := (source_uint_fixed_intrinsic y hp n hn).1
  rw [hz] at hr
  have hm := source_uint_fixed_memOK (E := E) (Γ := Γ) SH n y hmem
  rw [hz] at hm
  refine ⟨source_decl_statement_run G F (n+3) Γ.length y _ _ hz,hr,?_⟩
  refine ⟨⟨hm.1.1.1,?_⟩,hm.1.2⟩
  exact ⟨hm.2,hm.1.1.2⟩

/-- Old occupied Source addresses survive the ACTUAL allocation, independent of
an address-map injectivity premise. Older typed intrinsic objects survive by Keeps. -/
theorem source_uint_fixed_old_frame {E : Source.Env} {Γ : Source.RCtx} {H : HTy}
    (y : Source.EMState E Γ) (hp : Heap H) (n : Nat) (hn : 0<n) :
    let g := hp.allocDefault (.fixed (.prim .uint) n) rfl
    let z := ((Source.zeroVal (E := E) (Γ := Γ) (n+3) (.array .memory (.int .u256) (some n))).run y).2
    Heap.Keeps g.ext hp g.heap ∧
    (∀ {R : RefTy} (q : HRef H R),g.val.id≠(q.wk g.ext).id) ∧
    (∀ address,y.2.heap.get address≠none → y.2.heap.next≠address ∧ z.2.heap.get address=y.2.heap.get address) := by
  dsimp only
  have h := source_uint_fixed_intrinsic y hp n hn
  refine ⟨h.2.2.1,?_,?_⟩
  · intro R q
    rw [h.2.2.2]
    change H.length≠q.id
    have hq := q.id_lt
    omega
  · intro address ha
    have hne : address≠y.2.heap.next := by
      intro heq
      have hf := y.2.heap.alloc_fresh ⟨.array .memory (.int .u256) (some n),sourceUintFixedZero n⟩
      change y.2.heap.get y.2.heap.next=none at hf
      rw [←heq] at hf
      exact ha hf
    refine ⟨Ne.symm hne,?_⟩
    rw [source_uint_fixed_zeroVal,Source.Heap.alloc_other _ _ hne]

/-- Published headerless fixed builder applied to INITIAL full allocator/space
premises. The returned ownership certificate refers to the SAME actual intrinsic
default whose contents the independently executed Source constructor represents. -/
theorem source_uint_fixed_word {E : Source.Env} {Γ : Source.RCtx} {H : HTy}
    (y : Source.EMState E Γ) (hp : Heap H) (n : Nat) (hn : 0<n)
    (base : Nat → Fin Evm.W) (frame : Nat) (cursor : Fin Evm.W) (m : Evm.Machine)
    (ha : Evm.Memory.Objects.AllocatorRepr hp base frame cursor m)
    (hs : cursor.val+max 1 n<Evm.W) :
    let g := hp.allocDefault (.fixed (.prim .uint) n) rfl
    let z := ((Source.zeroVal (E := E) (Γ := Γ) (n+3) (.array .memory (.int .u256) (some n))).run y).2
    SourceUintFixedAt z y.2.heap.next g.heap g.val ∧
    Evm.Memory.Objects.DefaultBuildResult hp (.fixed (.prim .uint) n) rfl
      (Evm.Memory.Objects.DefaultBuilder.fixedPrimitive .uint n).code (max 1 n) base frame cursor m hs := by
  exact ⟨(source_uint_fixed_intrinsic y hp n hn).1,
    (Evm.Memory.Objects.DefaultBuilder.fixedPrimitive .uint n).correct hp base frame cursor m ha hs⟩

/-- Actual resolved fixed-array syntax, from initial local alignment and the
fixed observer, rather than an assumed selected pointer or output read. -/
theorem SourceUintFixedAt.eval_index {E : Source.Env} {Γ : Source.RCtx} {H : HTy} {n : Nat}
    {y : Source.EMState E Γ} {address : Nat} {hp : Heap H} {r : HRef H (.fixed (.prim .uint) n)}
    (hr : SourceUintFixedAt y address hp r) (G : Source.Glob E) (F : Source.Fr) (fuel : Nat)
    (root : Source.Idx Γ (.array .memory (.int .u256) (some n))) (index : Source.Idx Γ (.int .u256))
    (k : PrimTy.uint.Denote) (hroot : y.1.get root=.memRef rfl address)
    (hindex : y.1.get index=sourceUint k) (hk : k.1.toNat<n) :
    (Source.evalE G F (fuel+2) (.indexArray (.local root) (.local index) rfl)).run y=
      (.ok (.val (sourceUint ((hp.get r).1[k.1.toNat]'(by rw [(hp.get r).2];exact hk)))),y) := by
  rw [Source.evalE,Source.Hoare.run_bind,source_local_value_run G F fuel y root _ hroot]
  change ((Source.evalE G F (fuel+1) (.local index)) >>= fun v => Source.indexNat v >>= fun k =>
    Source.indexLoc F (.memRef rfl address : Source.Val E.layout (.array .memory (.int .u256) (some n))) k >>=
      fun loc => Source.readLoc F loc >>= fun v => pure (Source.RVal.val v)).run y=_
  rw [Source.Hoare.run_bind,source_local_value_run G F fuel y index _ hindex]
  change (Source.indexLoc F (.memRef rfl address : Source.Val E.layout (.array .memory (.int .u256) (some n))) k.1.toNat >>=
    fun loc => Source.readLoc F loc >>= fun v => pure (Source.RVal.val v)).run y=_
  have hi : (Source.indexLoc (E := E) (Γ := Γ) F
      (.memRef rfl address : Source.Val E.layout (.array .memory (.int .u256) (some n))) k.1.toNat).run y=
        (.ok (.mem address k.1.toNat),y) := by
    rw [Source.indexLoc,Source.Hoare.run_bind]
    change (if k.1.toNat<n then pure (Source.Loc.mem address k.1.toNat : Source.Loc E.layout Γ (.int .u256)) else Source.EM.lift (Source.panic .index)).run y=_
    rw [if_pos hk]
    rfl
  rw [Source.Hoare.run_bind,hi]
  change ((Source.readLoc (E := E) (Γ := Γ) F (.mem address k.1.toNat)) >>= fun v => pure (Source.RVal.val v)).run y=_
  have hread : (Source.readLoc (E := E) (Γ := Γ) F (.mem address k.1.toNat)).run y=
      (.ok (sourceUint ((hp.get r).1[k.1.toNat]'(by rw [(hp.get r).2];exact hk))),y) := hr.read _ hk
  rw [Source.Hoare.run_bind,hread]
  rfl

/-- info: 'Solidity.Backend.MemoryOps.source_uint_zeroElems_run' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms source_uint_zeroElems_run
/-- info: 'Solidity.Backend.MemoryOps.source_uint_fixed_zeroData' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms source_uint_fixed_zeroData
/-- info: 'Solidity.Backend.MemoryOps.source_uint_fixed_zeroVal' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms source_uint_fixed_zeroVal
/-- info: 'Solidity.Backend.MemoryOps.sourceUintFixedObject_zero' depends on axioms: [propext, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms sourceUintFixedObject_zero
/-- info: 'Solidity.Backend.MemoryOps.source_uint_fixed_intrinsic' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms source_uint_fixed_intrinsic
/-- info: 'Solidity.Backend.MemoryOps.source_uint_zeroElems_timeout' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms source_uint_zeroElems_timeout
/-- info: 'Solidity.Backend.MemoryOps.source_uint_fixed_zeroData_timeout' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms source_uint_fixed_zeroData_timeout
/-- info: 'Solidity.Backend.MemoryOps.source_uint_fixed_zeroVal_timeout' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms source_uint_fixed_zeroVal_timeout
/-- info: 'Solidity.Backend.MemoryOps.SourceUintFixedAt.read' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms SourceUintFixedAt.read
/-- info: 'Solidity.Backend.MemoryOps.SourceUintFixedAt.bounds' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms SourceUintFixedAt.bounds
/-- info: 'Solidity.Backend.MemoryOps.sourceUintFixedObject_wk' depends on axioms: [propext, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms sourceUintFixedObject_wk
/-- info: 'Solidity.Backend.MemoryOps.SourceUintFixedAt.keeps' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms SourceUintFixedAt.keeps
/-- info: 'Solidity.Backend.MemoryOps.source_uint_fixed_memOK' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms source_uint_fixed_memOK
/-- info: 'Solidity.Backend.MemoryOps.source_uint_fixed_declaration' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms source_uint_fixed_declaration
/-- info: 'Solidity.Backend.MemoryOps.source_uint_fixed_old_frame' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms source_uint_fixed_old_frame
/-- info: 'Solidity.Backend.MemoryOps.source_uint_fixed_word' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms source_uint_fixed_word
/-- info: 'Solidity.Backend.MemoryOps.SourceUintFixedAt.eval_index' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms SourceUintFixedAt.eval_index
end Solidity.Backend.MemoryOps
