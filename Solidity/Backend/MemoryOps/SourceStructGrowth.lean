import Solidity.Backend.MemoryOps.SourceDefault
import Solidity.Backend.MemoryOps.SourceStructDelete

/-! Paired REAL Source/intrinsic heap allocation for the existing finite named
struct observer. Old occupied Source cells, not all addresses, are framed.
No new allocator or address-injectivity hypothesis. Only the empty default
word corollary consumes an existing target allocation certificate. -/
namespace Solidity.Backend.MemoryOps
open Semantics

/-- Honest preservation of the actual occupied Source cell plus intrinsic Keeps. -/
theorem SourceBoolMemoryAt.transport {E : Source.Env} {Γ : Source.RCtx} {H H' : HTy}
    {y z : Source.EMState E Γ} {addr : Nat} {hp : Heap H} {hp' : Heap H'}
    {e : H <+: H'} {R : RefTy} {r : HRef H R} {a : ArrTy R (.prim .bool)}
    (hr : SourceBoolMemoryAt y addr hp r a) (hk : Heap.Keeps e hp hp')
    (hs : ∀ b obj, y.2.heap.get b=some obj → z.2.heap.get b=some obj) :
    SourceBoolMemoryAt z addr hp' (r.wk e) a := by
  unfold SourceBoolMemoryAt
  rw [hk r,MObj.elems_wk,List.map_id'' (f := MVal.wk e (.prim .bool)) (fun _ => rfl)]
  exact hs addr _ hr

/-- Old named fields and child contents transport; address agreement is required
only on valid OLD IDs. Source locals/world need not be constrained by this observer. -/
theorem SourceBoolStructAt.transport {E : Source.Env} {Γ : Source.RCtx} {H H' : HTy}
    {y z : Source.EMState E Γ} {addr : Nat} {hp : Heap H} {hp' : Heap H'}
    {e : H <+: H'} {r : HRef H (.struct s)} {address address' : Nat → Nat}
    {layout : SourceBoolStructLayout E dn s tag child}
    (hr : SourceBoolStructAt y addr hp r address layout) (hk : Heap.Keeps e hp hp')
    (hs : ∀ b obj, y.2.heap.get b=some obj → z.2.heap.get b=some obj)
    (ha : ∀ i, i<H.length → address' i=address i) :
    SourceBoolStructAt z addr hp' (r.wk e) address' layout := by
  have ht := hk.field r layout.tag_type
  have hc := hk.field r layout.child_type
  change hp'.field (r.wk e) layout.tag_type=hp.field r layout.tag_type at ht
  change hp'.field (r.wk e) layout.child_type=(hp.field r layout.child_type).wk e at hc
  refine ⟨?_,?_⟩
  · rw [ht,hc]
    change z.2.heap.get addr=some ⟨.struct .memory dn,sourceBoolStructData dn layout.source_types
      (hp.field r layout.tag_type) (address' (hp.field r layout.child_type).id)⟩
    rw [ha _ (hp.field r layout.child_type).id_lt]
    exact hs addr _ hr.parent
  · rw [hc]
    change SourceBoolMemoryAt z (address' (hp.field r layout.child_type).id) hp'
      ((hp.field r layout.child_type).wk e) .dyn
    rw [ha _ (hp.field r layout.child_type).id_lt]
    exact hr.leaf.transport hk hs

/-- Extend only the genuinely fresh intrinsic identity; all other entries are
unchanged, with no condition imposed on unused old address-map entries. -/
def allocatedSourceAddress (old : Nat → Nat) (freshId freshAddress : Nat) : Nat → Nat :=
  fun i => if i=freshId then freshAddress else old i

theorem allocatedSourceAddress_old (old : Nat → Nat) {H : HTy} (fresh : Nat)
    (i : Nat) (hi : i<H.length) : allocatedSourceAddress old H.length fresh i=old i := by
  unfold allocatedSourceAddress
  rw [if_neg (Nat.ne_of_lt hi)]

/-- The actual existing allocators produce the extension, old observations,
fresh relation and MemOK. Freshness follows occupied cells and real alloc_get.
The supplied intrinsic object has its existing intrinsic length validity. -/
theorem SourceBoolStructAt.alloc_bool {E : Source.Env} {Γ : Source.RCtx} {H : HTy}
    {y : Source.EMState E Γ} {addr : Nat} {hp : Heap H} {r : HRef H (.struct s)}
    {address : Nat → Nat} {layout : SourceBoolStructLayout E dn s tag child}
    (hr : SourceBoolStructAt y addr hp r address layout)
    (o : MObj H (.array (.prim .bool))) (SH : Source.HeapTy) (hm : Source.MemOK E SH y) :
    let xs := MObj.elems .dyn o
    let z : Source.EMState E Γ := (y.1,{y.2 with heap := (y.2.heap.alloc ⟨SourceBoolArrayTy,sourceBoolMemory xs⟩).1})
    let h := hp.alloc o
    let e := List.prefix_append H [RefTy.array (.prim .bool)]
    let address' := allocatedSourceAddress address H.length y.2.heap.next
    (Source.allocRef (E := E) (Γ := Γ) (sourceBoolMemory xs)).run y=(.ok (.memRef rfl y.2.heap.next),z) ∧
    Heap.Keeps e hp h.1 ∧
    SourceBoolStructAt z addr h.1 (r.wk e) address' layout ∧
    SourceBoolMemoryAt z (address' h.2.id) h.1 h.2 .dyn ∧ Source.MemOK E SH z ∧
    h.2.id=H.length ∧ address' h.2.id=y.2.heap.next ∧
    (∀ i, i<H.length → address' i=address i) ∧
    (∀ R (q : HRef H R), (q.wk e).id≠h.2.id) ∧
    addr≠y.2.heap.next ∧ address (hp.field r layout.child_type).id≠y.2.heap.next ∧
    (∀ q : HRef H (.array (.prim .bool)),SourceBoolMemoryAt y (address q.id) hp q .dyn →
      SourceBoolMemoryAt z (address' (q.wk e).id) h.1 (q.wk e) .dyn ∧ address q.id≠y.2.heap.next) ∧
    z.1=y.1 ∧ z.2.ex=y.2.ex ∧ z.2.events=y.2.events ∧ z.2.logs=y.2.logs ∧ z.2.fnLocals=y.2.fnLocals := by
  dsimp only
  let xs := MObj.elems .dyn o
  let z : Source.EMState E Γ := (y.1,{y.2 with heap := (y.2.heap.alloc ⟨SourceBoolArrayTy,sourceBoolMemory xs⟩).1})
  have hs : ∀ b obj, y.2.heap.get b=some obj → z.2.heap.get b=some obj := by
    intro b obj hb
    have hn : b≠y.2.heap.next := by
      intro he
      subst b
      have hf := Source.Heap.alloc_fresh y.2.heap ⟨SourceBoolArrayTy,sourceBoolMemory xs⟩
      change y.2.heap.get y.2.heap.next=none at hf
      rw [hf] at hb
      cases hb
    exact (Source.Heap.alloc_other y.2.heap _ hn).trans hb
  have hn : ∀ b obj, y.2.heap.get b=some obj → b≠y.2.heap.next := by
    intro b obj hb he
    subst b
    have hf := Source.Heap.alloc_fresh y.2.heap ⟨SourceBoolArrayTy,sourceBoolMemory xs⟩
    change y.2.heap.get y.2.heap.next=none at hf
    rw [hf] at hb
    cases hb
  have hk : Heap.Keeps (List.prefix_append H [RefTy.array (.prim .bool)]) hp (hp.alloc o).1 := hp.keeps_alloc o
  have ha := allocatedSourceAddress_old address (H := H) y.2.heap.next
  have hnew : SourceBoolMemoryAt z y.2.heap.next (hp.alloc o).1 (hp.alloc o).2 .dyn := by
    unfold SourceBoolMemoryAt
    rw [hp.get_alloc o,MObj.elems_wk,List.map_id'' (f := MVal.wk (List.prefix_append H [RefTy.array (.prim .bool)]) (.prim .bool)) (fun _ => rfl)]
    exact Source.Heap.alloc_get y.2.heap _
  have hmk := source_bool_alloc_memOK (E := E) (Γ := Γ) SH xs y hm
  rw [source_bool_alloc y xs] at hmk
  refine ⟨source_bool_alloc y xs,hk,hr.transport hk hs ha,?_,hmk.1,rfl,?_,ha,?_,hn _ _ hr.parent,hn _ _ hr.leaf,?_,rfl,rfl,rfl,rfl,rfl⟩
  · change SourceBoolMemoryAt z (allocatedSourceAddress address H.length y.2.heap.next H.length) (hp.alloc o).1 (hp.alloc o).2 .dyn
    rw [allocatedSourceAddress,if_pos rfl]
    exact hnew
  · exact if_pos rfl
  · intro R q
    exact Nat.ne_of_lt q.id_lt
  · intro q hq
    refine ⟨?_,hn _ _ hq⟩
    change SourceBoolMemoryAt z (allocatedSourceAddress address H.length y.2.heap.next q.id) (hp.alloc o).1 (q.wk _) .dyn
    rw [ha _ q.id_lt]
    exact hq.transport hk hs

/-- Actual allocation, actual existing field write, then resolved member-child
DELETE at the reached fresh child. No target allocation/code or Source new-expression
claim is made: the allocation stage is exactly published Source.allocRef. -/
theorem SourceBoolStructAt.alloc_select_delete {E : Source.Env} {Γ : Source.RCtx} {H : HTy}
    {y : Source.EMState E Γ} {addr : Nat} {hp : Heap H} {r : HRef H (.struct s)}
    {address : Nat → Nat} {layout : SourceBoolStructLayout E dn s tag child}
    (hr : SourceBoolStructAt y addr hp r address layout)
    (o : MObj H (.array (.prim .bool))) (SH : Source.HeapTy) (hm : Source.MemOK E SH y)
    (G : Source.Glob E) (F : Source.Fr) (n : Nat)
    (root : Source.Idx Γ (.struct .memory dn)) (i : Source.Idx Γ (.int .u256)) (k : PrimTy.uint.Denote)
    (hroot : y.1.get root=.memRef rfl addr) (hi : y.1.get i=sourceUint k)
    (hk : k.1.toNat<(MObj.elems .dyn o).length) :
    let h := hp.alloc o
    let e := List.prefix_append H [RefTy.array (.prim .bool)]
    let address' := allocatedSourceAddress address H.length y.2.heap.next
    let rr := r.wk e
    let selected := h.1.setField rr layout.child_type h.2
    ∃ (z w v : Source.EMState E Γ) (out : Heap (H++[RefTy.array (.prim .bool)])),
      (Source.allocRef (E := E) (Γ := Γ) (sourceBoolMemory (MObj.elems .dyn o))).run y=
        (.ok (.memRef rfl y.2.heap.next),z) ∧
      (Source.writeLoc (E := E) (Γ := Γ) F n (.mem (τ := SourceBoolArrayTy) addr 1)
        (.memRef rfl (address' h.2.id))).run z=(.ok (),w) ∧
      (Source.evalE G F (n+4) (sourceStructChildDelete layout root i)).run w=(.ok Source.RVal.unit,v) ∧
      selected.writeAddr (.index h.2 .dyn k) (PrimTy.dflt .bool)=some out ∧
      SourceBoolStructAt z addr h.1 rr address' layout ∧
      SourceBoolStructAt w addr selected rr address' layout ∧
      SourceBoolStructAt v addr out rr address' layout ∧
      Source.MemOK E SH z ∧ Source.MemOK E SH w ∧ Source.MemOK E SH v ∧
      w.1=y.1 ∧ v.1=y.1 ∧ selected.field rr layout.child_type=h.2 ∧
      selected.len h.2 .dyn=(MObj.elems .dyn o).length ∧ out.get rr=selected.get rr ∧
      (∀ q : HRef H (.array (.prim .bool)),SourceBoolMemoryAt y (address q.id) hp q .dyn →
        SourceBoolMemoryAt w (address' (q.wk e).id) selected (q.wk e) .dyn ∧
        SourceBoolMemoryAt v (address' (q.wk e).id) out (q.wk e) .dyn) := by
  dsimp only
  obtain ⟨ha,hkeep,hrz,hfresh,hmz,hid,haddr,hold,hneq,hpa,hca,halias,hlocal,heffects⟩ := hr.alloc_bool o SH hm
  let z : Source.EMState E Γ := (y.1,{y.2 with heap := (y.2.heap.alloc ⟨SourceBoolArrayTy,sourceBoolMemory (MObj.elems .dyn o)⟩).1})
  let rr := r.wk (List.prefix_append H [RefTy.array (.prim .bool)])
  let selected := (hp.alloc o).1.setField rr layout.child_type (hp.alloc o).2
  obtain ⟨w,hw,hrw,hmw,hlw,htag,hsel,hchildren,hsource,heff⟩ := hrz.write_reference (hp.alloc o).2 hfresh F n SH hmz
  have hlen : selected.len (hp.alloc o).2 .dyn=(MObj.elems .dyn o).length := by
    unfold Heap.len
    rw [hchildren,hp.get_alloc o,MObj.elems_wk,List.length_map]
  have hk' : k.1.toNat<selected.len (selected.field rr layout.child_type) .dyn := by rw [hsel,hlen];exact hk
  obtain ⟨out,v,hwrite,hwv,hrv,hmv,hlv,hparent,hother,hsourceframe,heffv⟩ := hrw.write_child F (n+3) k false hk' SH hmw
  have hd : (Source.evalE G F (n+4) (sourceStructChildDelete layout root i)).run w=(.ok Source.RVal.unit,v) := by
    rw [sourceStructChildDelete,Source.evalE,Source.Hoare.run_bind,
      hrw.eval_child_loc G F n root i k (by rw [hlw,hlocal];exact hroot) (by rw [hlw,hlocal];exact hi) hk']
    have hdloc : (Source.deleteLoc (E := E) (Γ := Γ) F (n+3) (τ := .bool)
      (.mem ((allocatedSourceAddress address H.length y.2.heap.next) (selected.field rr layout.child_type).id) k.1.toNat)).run w=(.ok (),v) := hwv
    change (Source.deleteLoc F (n+3) (τ := .bool)
      (.mem ((allocatedSourceAddress address H.length y.2.heap.next) (selected.field rr layout.child_type).id) k.1.toNat) >>= fun _ => pure Source.RVal.unit).run w=_
    rw [Source.Hoare.run_bind,hdloc]
    rfl
  rw [hsel] at hwrite hother hsourceframe
  refine ⟨z,w,v,out,ha,hw,hd,hwrite,hrz,hrw,hrv,hmz,hmw,hmv,hlw.trans hlocal,
    hlv.trans (hlw.trans hlocal),hsel,hlen,hparent,?_⟩
  intro q hq
  have hqw := hsource _ (halias q hq).1
  refine ⟨hqw,?_⟩
  unfold SourceBoolMemoryAt
  have hqn : (allocatedSourceAddress address H.length y.2.heap.next) (q.wk (List.prefix_append H [RefTy.array (.prim .bool)])).id≠
      (allocatedSourceAddress address H.length y.2.heap.next) (hp.alloc o).2.id := by
    change (allocatedSourceAddress address H.length y.2.heap.next) q.id≠_
    rw [hold _ q.id_lt,haddr]
    exact (halias q hq).2
  rw [hsourceframe _ hqn,hother _ (Ne.symm (hneq _ q))]
  exact hqw


/-- Supported EMPTY-default word application. The named old observer is
transported through actual Source default/State.allocPush/word allocation. All
initial allocator/space premises remain explicit; no nonempty/all-profile compiler. -/
theorem SourceBoolStructAt.default_word_growth {E : Source.Env} {Γ : Source.RCtx} {C : Contract} {Δ : Ctx}
    {y : Source.EMState E Γ} {addr : Nat} (σ : State C Δ) (r : HRef σ.H (.struct s))
    (address : Nat → Nat) (layout : SourceBoolStructLayout E dn s tag child)
    (hr : SourceBoolStructAt y addr σ.heap r address layout) (fuel : Nat)
    (SH : Source.HeapTy) (hmem : Source.MemOK E SH y)
    {L b frame : Nat} {F : Evm.Frag Δ} {base : Nat → Fin Evm.W} {cursor : Fin Evm.W} {m : Evm.Machine}
    (hm : Evm.Memory.StateRepr L b frame F σ base m)
    (ha : Evm.Memory.StructAllocatorRepr σ.heap base frame cursor m) (hb : 0<b)
    (hspace : cursor.val+1<Evm.W) (hcap : b+(Δ.length+1)≤frame) :
    let o := Evm.Memory.defaultArray (H := σ.H) .bool ⟨0,Evm.W_pos⟩
    let σ' := σ.allocPush o
    let r' := (σ.alloc o).2
    let e := List.prefix_append σ.H [RefTy.array (.prim .bool)]
    let address' := allocatedSourceAddress address σ.H.length y.2.heap.next
    let base' := Evm.upd base σ.H.length cursor
    let m' := Evm.Memory.writeMachine (Evm.Memory.allocateMachine m cursor ⟨0,Evm.W_pos⟩)
      (Evm.cell (b+Δ.length)) (.val cursor)
    ∃ z : Source.EMState E Γ,
      (Source.zeroVal (E := E) (Γ := Γ) (fuel+2) SourceBoolArrayTy).run y=(.ok (.memRef rfl y.2.heap.next),z) ∧
      (Source.allocRef (E := E) (Γ := Γ) (sourceBoolMemory [])).run y=(.ok (.memRef rfl y.2.heap.next),z) ∧
      TRun.declMem (.array (.prim .bool)) none rfl σ=.ok ⟨σ',e⟩ ∧
      Evm.run (Evm.Memory.declareNewCode b (.lit 0 rfl : Simple C Δ .uint)) m=.ok m' 0 ∧
      SourceBoolStructAt z addr σ'.heap (r.wk e) address' layout ∧
      SourceBoolMemoryAt z y.2.heap.next σ'.heap r' .dyn ∧ Source.MemOK E SH z ∧
      Evm.Memory.StateRepr L b frame (F.push (.mem (.array (.prim .bool))) .ok) σ' base' m' ∧
      Evm.Memory.StructAllocatorRepr σ'.heap base' frame ⟨cursor.val+1,hspace⟩ m' ∧
      m'.stack=m.stack ∧ r'.id=σ.H.length := by
  dsimp only
  obtain ⟨z,hz,hd,hc,hfresh,hm',ha',hstack,hid⟩ := source_bool_default_word y fuel σ hm ha hb hspace hcap
  obtain ⟨halloc,hkeep,hstruct,hnew,hmem',tail⟩ := hr.alloc_bool
    (Evm.Memory.defaultArray (H := σ.H) .bool ⟨0,Evm.W_pos⟩) SH hmem
  simp only [MObj.elems_dyn,Evm.Memory.defaultArray,List.replicate_zero] at halloc hstruct hmem'
  have he : (Source.allocRef (E := E) (Γ := Γ) (sourceBoolMemory [])).run y=
      (Source.zeroVal (E := E) (Γ := Γ) (fuel+2) SourceBoolArrayTy).run y :=
    (source_bool_alloc y []).trans (source_bool_default_run y fuel).symm
  have hzid := congrArg Prod.snd (halloc.symm.trans (he.trans hz))
  change (y.1,{y.2 with heap := (y.2.heap.alloc ⟨SourceBoolArrayTy,sourceBoolMemory []⟩).1})=z at hzid
  rw [hzid] at hstruct hmem'
  exact ⟨z,hz,he.trans hz,hd,hc,hstruct,hfresh,hmem',hm',ha',hstack,hid⟩

/-- info: 'Solidity.Backend.MemoryOps.SourceBoolMemoryAt.transport' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms SourceBoolMemoryAt.transport

/-- info: 'Solidity.Backend.MemoryOps.SourceBoolStructAt.transport' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms SourceBoolStructAt.transport

/-- info: 'Solidity.Backend.MemoryOps.allocatedSourceAddress_old' does not depend on any axioms -/
#guard_msgs (whitespace := lax) in #print axioms allocatedSourceAddress_old

/-- info: 'Solidity.Backend.MemoryOps.SourceBoolStructAt.alloc_bool' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms SourceBoolStructAt.alloc_bool

/-- info: 'Solidity.Backend.MemoryOps.SourceBoolStructAt.alloc_select_delete' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms SourceBoolStructAt.alloc_select_delete

/-- info: 'Solidity.Backend.MemoryOps.SourceBoolStructAt.default_word_growth' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms SourceBoolStructAt.default_word_growth

end Solidity.Backend.MemoryOps
