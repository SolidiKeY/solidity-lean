import Solidity.Backend.CalldataPackets.RawUint.Execution
import Solidity.Backend.MemoryOps.SourceCalldataUintDelete

/-! Byte-derived specialization of the existing actual Source Items copy/bind
and numeric deletion. Scalar decoding comes from the published RawUint packet.
Standalone copies zero-pad short input: entry guarding remains a separate
cdTail operation, not an invented standalone-copy refusal. -/
namespace Solidity.Backend.MemoryOps

/-- Total uint decoding, derived from the published scalar decoder. This
removes the impossible decoder-error branch without assuming a decoded list. -/
theorem source_cd_uint_values_raw (E : Source.Env) (F : Source.Fr) (off len : Nat) :
    sourceCalldataUintValues E F off len=
      .ok ((CalldataPackets.RawUint.payload F off len).map (sourceUint (D := E.layout))) := by
  first
  | solve | rfl | simp only [] | omega
  | simp only [sourceCalldataUintValues,CalldataPackets.RawUint.payload,List.map_map,
      Function.comp_def,CalldataPackets.RawUint.decode_uint]
    exact List.mapM_pure (m := Except Source.Halt) (l := List.range len)
      (f := fun j => sourceUint (D := E.layout) (CalldataPackets.RawUint.wordValue (Source.cdWordAt F (off+32*j))))


/-- The Source/intrinsic conversion retains every canonical uint256 value. -/
theorem source_uint_payload_sourceUint {D : Source.Layout} (xs : List PrimTy.uint.Denote) :
    sourceUintValuePayload (xs.map (sourceUint (D := D)))=xs := by
  first
  | solve | rfl | simp only [] | omega
  | simp only [sourceUintValuePayload,List.map_map,Function.comp_def,calldataUint_sourceUint]
    exact List.map_id xs

/-- Actual byte-derived copy/bind then reached in-bounds deletion, with the existing full Source Items execution, intrinsic write and old-object frames. -/
theorem source_raw_uint_bind_delete {E : Source.Env} {Γ : Source.RCtx} {H : HTy}
    (y : Source.EMState E Γ) (hp : Heap H) (G : Source.Glob E) (F : Source.Fr)
    (fuel nps : Nat) (dst : Source.Idx Γ SourceUintArrayTy)
    (src : Source.Idx Γ (.array .calldata (.int .u256) none))
    (index : Source.Idx Γ (.int .u256)) (off len : Nat) (k : PrimTy.uint.Denote)
    (hsrc : y.1.get src=.cdRef rfl off len) (hi : y.1.get index=sourceUint k)
    (bound : k.1.toNat<len) (cap : len<2^256)
    (SH : Source.HeapTy) (hm : Source.MemOK E SH y) :
    ∃ valid : (CalldataPackets.RawUint.payload F off len).length<2^256,
      let pair := hp.alloc (R := .array (.prim .uint))
        (⟨CalldataPackets.RawUint.payload F off len,valid⟩ : MObj H (.array (.prim .uint)))
      let ext := List.prefix_append H [RefTy.array (.prim .uint)]
      let mid : Source.EMState E Γ :=
        (y.1.set dst (.memRef rfl y.2.heap.next),
          {y.2 with heap := (y.2.heap.alloc ⟨SourceUintArrayTy,sourceUintMemory (CalldataPackets.RawUint.payload F off len)⟩).1})
      ∃ (out : Heap (H++[RefTy.array (.prim .uint)])) (z : Source.EMState E Γ),
        (Source.evalE G F (fuel+4) (sourceUintCalldataBind dst src)).run y=(.ok (.val (.memRef rfl y.2.heap.next)),mid) ∧
        (Source.evalE G F (fuel+3) (sourceUintIndexedDelete dst index)).run mid=(.ok Source.RVal.unit,z) ∧
        (Source.execItems G F (fuel+6) nps none
          (.stmt (.expr (sourceUintCalldataBind dst src)) (.stmt (.expr (sourceUintIndexedDelete dst index)) .nil) :
            Source.RItems E [] false .body Γ Γ) y.1).run (.nil,y.2)=(.ok (.normal z.1),(.nil,z.2)) ∧
        checkedSourceFreshUints (E := E) F off len hp cap=.ok (some pair.1) ∧
        pair.1.writeAddr (.index pair.2 .dyn k) (PrimTy.dflt .uint)=some out ∧
        SourceUintMemoryAt z y.2.heap.next out pair.2 .dyn ∧ Source.MemOK E SH z ∧
        Heap.Keeps ext hp out ∧ MObj.elems .dyn (out.get pair.2)=(CalldataPackets.RawUint.payload F off len).set k.1.toNat (PrimTy.dflt .uint) ∧
        (∀ b obj,y.2.heap.get b=some obj → z.2.heap.get b=some obj) ∧
        z.1=mid.1 ∧ z.2.ex=y.2.ex ∧ z.2.events=y.2.events ∧ z.2.logs=y.2.logs ∧ z.2.fnLocals=y.2.fnLocals := by
  first
  | solve | rfl | simp only [] | omega
  | simpa only [source_cd_uint_values_raw,source_uint_payload_sourceUint] using
      source_cd_uint_bind_delete y hp G F fuel nps dst src index off len k hsrc hi bound cap SH hm

/-- Actual byte-derived successful copy/bind prefix then exact fresh-root bounds rejection. The outcome retains the reached Source globals; no suffix heap, transaction rollback or target panic payload is asserted. -/
theorem source_raw_uint_bind_delete_bounds {E : Source.Env} {Γ : Source.RCtx} {H : HTy}
    (y : Source.EMState E Γ) (hp : Heap H) (G : Source.Glob E) (F : Source.Fr)
    (fuel nps : Nat) (dst : Source.Idx Γ SourceUintArrayTy)
    (src : Source.Idx Γ (.array .calldata (.int .u256) none))
    (index : Source.Idx Γ (.int .u256)) (off len : Nat) (k : PrimTy.uint.Denote)
    (hsrc : y.1.get src=.cdRef rfl off len) (hi : y.1.get index=sourceUint k)
    (bound : len≤k.1.toNat) (cap : len<2^256)
    (SH : Source.HeapTy) (hm : Source.MemOK E SH y) :
    ∃ valid : (CalldataPackets.RawUint.payload F off len).length<2^256,
      let pair := hp.alloc (R := .array (.prim .uint))
        (⟨CalldataPackets.RawUint.payload F off len,valid⟩ : MObj H (.array (.prim .uint)))
      let mid : Source.EMState E Γ :=
        (y.1.set dst (.memRef rfl y.2.heap.next),
          {y.2 with heap := (y.2.heap.alloc ⟨SourceUintArrayTy,sourceUintMemory (CalldataPackets.RawUint.payload F off len)⟩).1})
      (Source.evalE G F (fuel+4) (sourceUintCalldataBind dst src)).run y=(.ok (.val (.memRef rfl y.2.heap.next)),mid) ∧
      (Source.evalE G F (fuel+3) (sourceUintIndexedDelete dst index)).run mid=
        (.error (.revert (Source.panicData .index)),mid) ∧
      (Source.execItems G F (fuel+6) nps none
        (.stmt (.expr (sourceUintCalldataBind dst src)) (.stmt (.expr (sourceUintIndexedDelete dst index)) .nil) :
          Source.RItems E [] false .body Γ Γ) y.1).run (.nil,y.2)=
        (.error (.revert (Source.panicData .index)),(.nil,mid.2)) ∧
      checkedSourceFreshUints (E := E) F off len hp cap=.ok (some pair.1) ∧
      pair.1.writeAddr (.index pair.2 .dyn k) (PrimTy.dflt .uint)=none ∧
      SourceUintMemoryAt mid y.2.heap.next pair.1 pair.2 .dyn ∧ Source.MemOK E SH mid ∧
      Heap.Keeps (List.prefix_append H [RefTy.array (.prim .uint)]) hp pair.1 ∧
      (∀ b obj,y.2.heap.get b=some obj → mid.2.heap.get b=some obj) := by
  first
  | solve | rfl | simp only [] | omega
  | simpa only [source_cd_uint_values_raw,source_uint_payload_sourceUint] using
      source_cd_uint_bind_delete_bounds y hp G F fuel nps dst src index off len k hsrc hi bound cap SH hm

/-- info: 'Solidity.Backend.MemoryOps.source_cd_uint_values_raw' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms source_cd_uint_values_raw
/-- info: 'Solidity.Backend.MemoryOps.source_uint_payload_sourceUint' depends on axioms: [propext, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms source_uint_payload_sourceUint
/-- info: 'Solidity.Backend.MemoryOps.source_raw_uint_bind_delete' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms source_raw_uint_bind_delete
/-- info: 'Solidity.Backend.MemoryOps.source_raw_uint_bind_delete_bounds' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms source_raw_uint_bind_delete_bounds
end Solidity.Backend.MemoryOps
