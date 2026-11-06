import Solidity.Backend.MemoryOps.SourceUintFixedAssignment
import Solidity.Backend.MemoryOps.SourceUintCompound

/-! Genuine fixed uint Source compound syntax. The actual old cell is obtained
from INITIAL typed fixed correspondence; published arithmetic is reused read-only.
Success may be checked or unchecked in-range; overflow is checked-only. -/
namespace Solidity.Backend.MemoryOps

def sourceUintFixedIndexedAdd {E : Source.Env} {Γ : Source.RCtx} {N : Nat}
    (root : Source.Idx Γ (.array .memory (.int .u256) (some N)))
    (index rhs : Source.Idx Γ (.int .u256)) : Source.RExpr E Γ (.int .u256) :=
  .compound .add (.indexArray (.local root) (by decide) (.local index) rfl) (.local rhs) (by rfl)

/-- The old value is read from INITIAL represented contents, not supplied as an
arithmetic/output oracle; every write and postrelation follows from that read. -/
theorem SourceUintFixedAt.compound_add {E : Source.Env} {Γ : Source.RCtx} {N : Nat} {H : HTy}
    {y : Source.EMState E Γ} {address : Nat} {hp : Heap H} {r : HRef H (.fixed (.prim .uint) N)}
    (hr : SourceUintFixedAt y address hp r)
    (G : Source.Glob E) (F : Source.Fr) (n : Nat)
    (root : Source.Idx Γ (.array .memory (.int .u256) (some N)))
    (index rhs : Source.Idx Γ (.int .u256)) (k value : PrimTy.uint.Denote)
    (hroot : y.1.get root=.memRef rfl address) (hindex : y.1.get index=sourceUint k)
    (hrhs : y.1.get rhs=sourceUint value) (hk : k.1.toNat<hp.len r .fixed)
    (hadd : PrimTy.uint.inRange ((MObj.elems .fixed (hp.get r))[k.1.toNat].1+value.1)=true) :
    ∃ (out : Heap H) (z : Source.EMState E Γ),
      hp.writeAddr (.index r .fixed k) ⟨(MObj.elems .fixed (hp.get r))[k.1.toNat].1+value.1,hadd⟩=some out ∧
      (Source.writeLoc (E := E) (Γ := Γ) F (n+2) (.mem address k.1.toNat)
        (sourceUint ⟨(MObj.elems .fixed (hp.get r))[k.1.toNat].1+value.1,hadd⟩)).run y=(.ok (),z) ∧
      (Source.evalE G F (n+3) (sourceUintFixedIndexedAdd root index rhs)).run y=
        (.ok (.val (sourceUint ⟨(MObj.elems .fixed (hp.get r))[k.1.toNat].1+value.1,hadd⟩)),z) ∧
      SourceUintFixedAt z address out r ∧ z.1=y.1 := by
  have hkn : k.1.toNat<N := by simpa only [Heap.len,MObj.elems_fixed,(hp.get r).2] using hk
  let old := (MObj.elems .fixed (hp.get r))[k.1.toNat]
  let new : PrimTy.uint.Denote := ⟨old.1+value.1,hadd⟩
  obtain ⟨out,z,hw,hs,hr'⟩ := hr.write_addr F (n+2) k new hkn
  have hold : (Source.readLoc (E := E) (Γ := Γ) F (.mem address k.1.toNat)).run y=(.ok (sourceUint old),y) := by
    simpa only [Source.readLoc,old,MObj.elems_fixed] using hr.read k.1.toNat hkn
  have hbin := (source_uint_add (D := E.layout) F.checked old value hadd).1
  have he : (Source.evalE G F (n+3) (sourceUintFixedIndexedAdd root index rhs)).run y=(.ok (.val (sourceUint new)),z) := by
    rw [sourceUintFixedIndexedAdd,Source.evalE,Source.Hoare.run_bind,source_local_value_run G F (n+1) y rhs _ hrhs]
    simp only [Source.Hoare.run_bind]
    rw [hr.eval_index_loc G F n root index k hroot hindex hkn]
    simp only [Source.Hoare.run_bind]
    rw [hold]
    simp only [Source.Hoare.run_bind]
    simp only [Source.AssignOp.kind?]
    change ((Source.convRV F (n+2) (.int .u256) (.val (sourceUint value))) >>= fun v =>
      Source.EM.lift (Source.binVal F.checked .add (sourceUint old) (sourceUint value)) >>= fun new =>
      Source.writeLoc F (n+2) (.mem address k.1.toNat) new >>= fun _ => pure (Source.RVal.val new)).run y=_
    simp only [Source.convRV,↓reduceDIte]
    rw [Source.Hoare.run_bind]
    change ((Source.EM.lift (Source.binVal F.checked .add (sourceUint old) (sourceUint value))) >>= fun new =>
      Source.writeLoc F (n+2) (.mem address k.1.toNat) new >>= fun _ => pure (Source.RVal.val new)).run y=_
    rw [hbin]
    change ((Source.writeLoc F (n+2) (.mem address k.1.toNat) (sourceUint new)) >>= fun _ => pure (Source.RVal.val (sourceUint new))).run y=_
    rw [Source.Hoare.run_bind,hs]
    rfl
  exact ⟨out,z,hw,hs,he,hr',(hr.write_frames F (n+2) k new hkn hw hs).1⟩

/-- Checked overflow executes the actual resolved Source expression and stops
before the write. This is separate from unchecked wrapping and target outcomes. -/
theorem SourceUintFixedAt.compound_add_overflow {E : Source.Env} {Γ : Source.RCtx} {N : Nat} {H : HTy}
    {y : Source.EMState E Γ} {address : Nat} {hp : Heap H} {r : HRef H (.fixed (.prim .uint) N)}
    (hr : SourceUintFixedAt y address hp r)
    (G : Source.Glob E) (F : Source.Fr) (n : Nat) (hc : F.checked=true)
    (root : Source.Idx Γ (.array .memory (.int .u256) (some N)))
    (index rhs : Source.Idx Γ (.int .u256)) (k value : PrimTy.uint.Denote)
    (hroot : y.1.get root=.memRef rfl address) (hindex : y.1.get index=sourceUint k)
    (hrhs : y.1.get rhs=sourceUint value) (hk : k.1.toNat<hp.len r .fixed)
    (hbad : PrimTy.uint.inRange ((MObj.elems .fixed (hp.get r))[k.1.toNat].1+value.1)≠true) :
    (Source.evalE G F (n+3) (sourceUintFixedIndexedAdd root index rhs)).run y=
      (.error (.revert (Source.panicData .arithmetic)),y) := by
  have hkn : k.1.toNat<N := by simpa only [Heap.len,MObj.elems_fixed,(hp.get r).2] using hk
  let old := (MObj.elems .fixed (hp.get r))[k.1.toNat]
  have hold : (Source.readLoc (E := E) (Γ := Γ) F (.mem address k.1.toNat)).run y=(.ok (sourceUint old),y) := by
    simpa only [Source.readLoc,old,MObj.elems_fixed] using hr.read k.1.toNat hkn
  have hbin := (source_uint_add_overflow (D := E.layout) old value hbad).1
  rw [sourceUintFixedIndexedAdd,Source.evalE,Source.Hoare.run_bind,source_local_value_run G F (n+1) y rhs _ hrhs]
  simp only [Source.Hoare.run_bind]
  rw [hr.eval_index_loc G F n root index k hroot hindex hkn]
  simp only [Source.Hoare.run_bind]
  rw [hold]
  simp only [Source.Hoare.run_bind,Source.AssignOp.kind?]
  have hconv : (Source.convRV (E := E) (Γ := Γ) F (n+2) (.int .u256) (.val (sourceUint value))).run y=
      (.ok (.val (sourceUint value)),y) := by rfl
  have hget : (Source.getV (E := E) (Γ := Γ) (.val (sourceUint value) : Source.RVal E.layout (.int .u256))).run y=
      (.ok (sourceUint value),y) := rfl
  simp only [hconv,hget,Source.AssignOp.binOp]
  rw [hc,hbin]
  rfl

theorem SourceUintFixedAt.compound_add_bounds {E : Source.Env} {Γ : Source.RCtx} {H : HTy} {N : Nat}
    {y : Source.EMState E Γ} {address : Nat} {hp : Heap H} {r : HRef H (.fixed (.prim .uint) N)}
    (hr : SourceUintFixedAt y address hp r) (G : Source.Glob E) (F : Source.Fr) (fuel : Nat)
    (root : Source.Idx Γ (.array .memory (.int .u256) (some N))) (index rhs : Source.Idx Γ (.int .u256))
    (k value : PrimTy.uint.Denote) (hroot : y.1.get root=.memRef rfl address)
    (hi : y.1.get index=sourceUint k) (hv : y.1.get rhs=sourceUint value) (hk : N≤k.1.toNat) :
    (Source.evalE G F (fuel+3) (sourceUintFixedIndexedAdd root index rhs)).run y=
      (.error (.revert (Source.panicData .index)),y) := by
  rw [sourceUintFixedIndexedAdd,Source.evalE,Source.Hoare.run_bind,source_local_value_run G F (fuel+1) y rhs _ hv]
  simp only [Source.Hoare.run_bind]
  rw [hr.eval_index_bounds G F fuel root index k hroot hi hk]

theorem source_uint_fixed_add_timeout {E : Source.Env} {Γ : Source.RCtx} {N : Nat}
    (G : Source.Glob E) (F : Source.Fr) (y : Source.EMState E Γ)
    (root : Source.Idx Γ (.array .memory (.int .u256) (some N))) (index rhs : Source.Idx Γ (.int .u256)) :
    (Source.evalE G F 2 (sourceUintFixedIndexedAdd root index rhs)).run y=(.error .timeout,y) := by rfl

/-- info: 'Solidity.Backend.MemoryOps.SourceUintFixedAt.compound_add' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms SourceUintFixedAt.compound_add
/-- info: 'Solidity.Backend.MemoryOps.SourceUintFixedAt.compound_add_overflow' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms SourceUintFixedAt.compound_add_overflow
/-- info: 'Solidity.Backend.MemoryOps.SourceUintFixedAt.compound_add_bounds' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms SourceUintFixedAt.compound_add_bounds
/-- info: 'Solidity.Backend.MemoryOps.source_uint_fixed_add_timeout' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms source_uint_fixed_add_timeout
end Solidity.Backend.MemoryOps
