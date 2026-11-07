import Solidity.Backend.MemoryOps.SourceRawUintDelete

/-! Actual cdTail guarding followed by the existing Source Items copy/bind/delete.
The initial typed view is explicitly aligned to the byte-derived tail. This
adapter does not construct an ABI argument environment or prove its lowering. -/
namespace Solidity.Backend.MemoryOps

/-- Existing guard and Items operations composed in their actual order. The
argument environment is an input; the guard does not secretly create locals. -/
def sourceGuardedUintDelete {E : Source.Env} {Γ : Source.RCtx}
    (G : Source.Glob E) (F : Source.Fr) (fuel nps : Nat)
    (dst : Source.Idx Γ SourceUintArrayTy)
    (src : Source.Idx Γ (.array .calldata (.int .u256) none))
    (index : Source.Idx Γ (.int .u256)) (data : List UInt8) (entry : Nat)
    (locals : Source.Locals E.layout Γ) : Source.EM E [] (Source.Out E.layout Γ Γ) :=
  Source.EM.lift (Source.cdTail data entry 32) >>= fun _ =>
    Source.execItems G F (fuel+6) nps none
      (.stmt (.expr (sourceUintCalldataBind dst src)) (.stmt (.expr (sourceUintIndexedDelete dst index)) .nil) :
        Source.RItems E [] false .body Γ Γ) locals

/-- The actual published guard succeeds from byte bounds, not a supplied run. -/
theorem source_uint_entry_tail (data : List UInt8) (entry : Nat)
    (small : Source.wordAt (data.drop (Source.wordAt data entry)) 0<2^64)
    (span : Source.wordAt data entry+32+32*Source.wordAt (data.drop (Source.wordAt data entry)) 0≤data.length) :
    Source.cdTail data entry 32=.ok (4+Source.wordAt data entry+32,
      Source.wordAt (data.drop (Source.wordAt data entry)) 0) := by
  first
  | solve | rfl | simp only [] | omega
  | have head : ¬data.length<Source.wordAt data entry+32 := by omega
    simp only [Source.cdTail,if_neg head,if_neg (Nat.not_le.mpr small),if_pos span,pure,Except.pure]

/-- All entry refusals occur BEFORE Items, with the original Source globals.
The conditions describe actual bytes; no failure execution is a premise. -/
theorem source_guarded_uint_delete_refusal {E : Source.Env} {Γ : Source.RCtx}
    (G : Source.Glob E) (F : Source.Fr) (fuel nps : Nat)
    (dst : Source.Idx Γ SourceUintArrayTy) (src : Source.Idx Γ (.array .calldata (.int .u256) none))
    (index : Source.Idx Γ (.int .u256)) (data : List UInt8) (entry : Nat)
    (y : Source.EMState E Γ)
    (bad : data.length<Source.wordAt data entry+32 ∨
      2^64≤Source.wordAt (data.drop (Source.wordAt data entry)) 0 ∨
      data.length<Source.wordAt data entry+32+32*Source.wordAt (data.drop (Source.wordAt data entry)) 0) :
    (sourceGuardedUintDelete G F fuel nps dst src index data entry y.1).run (.nil,y.2)=
      (.error (.revert []),(.nil,y.2)) := by
  first
  | solve | rfl | simp only [] | omega
  | have refused : Source.cdTail data entry 32=.error (.revert []) := by
      by_cases head : data.length<Source.wordAt data entry+32
      · exact CalldataPackets.RawUint.entry_short_head data entry head
      · by_cases large : 2^64≤Source.wordAt (data.drop (Source.wordAt data entry)) 0
        · exact CalldataPackets.RawUint.entry_large_length data entry head large
        · exact CalldataPackets.RawUint.entry_short_elements data entry head large (by omega)
    rw [sourceGuardedUintDelete,refused]
    rfl

/-- Byte-derived valid entry followed by the actual Items consumer; the
view/frame alignments remain INITIAL premises, never desired postrelations. -/
theorem source_guarded_uint_bind_delete {E : Source.Env} {Γ : Source.RCtx} {H : HTy}
    (y : Source.EMState E Γ) (hp : Heap H) (G : Source.Glob E) (F : Source.Fr)
    (fuel nps : Nat) (dst : Source.Idx Γ SourceUintArrayTy)
    (src : Source.Idx Γ (.array .calldata (.int .u256) none)) (index : Source.Idx Γ (.int .u256))
    (selector data : List UInt8) (four : selector.length=4) (binding : F.cd=selector++data)
    (entry : Nat) (k : PrimTy.uint.Denote)
    (hsrc : y.1.get src=.cdRef rfl (4+Source.wordAt data entry+32) (Source.wordAt (data.drop (Source.wordAt data entry)) 0)) (hi : y.1.get index=sourceUint k)
    (small : (Source.wordAt (data.drop (Source.wordAt data entry)) 0)<2^64)
    (span : Source.wordAt data entry+32+32*(Source.wordAt (data.drop (Source.wordAt data entry)) 0)≤data.length)
    (bound : k.1.toNat<(Source.wordAt (data.drop (Source.wordAt data entry)) 0)) (SH : Source.HeapTy) (hm : Source.MemOK E SH y) :
    Source.cdTail data entry 32=.ok ((4+Source.wordAt data entry+32),(Source.wordAt (data.drop (Source.wordAt data entry)) 0)) ∧
    ∃ valid : (CalldataPackets.RawUint.dataPayload data (Source.wordAt data entry+32) (Source.wordAt (data.drop (Source.wordAt data entry)) 0)).length<2^256,
      let pair := hp.alloc (R := .array (.prim .uint))
        (⟨CalldataPackets.RawUint.dataPayload data (Source.wordAt data entry+32) (Source.wordAt (data.drop (Source.wordAt data entry)) 0),valid⟩ : MObj H (.array (.prim .uint)))
      let ext := List.prefix_append H [RefTy.array (.prim .uint)]
      let mid : Source.EMState E Γ :=
        (y.1.set dst (.memRef rfl y.2.heap.next),
          {y.2 with heap := (y.2.heap.alloc ⟨SourceUintArrayTy,sourceUintMemory (CalldataPackets.RawUint.dataPayload data (Source.wordAt data entry+32) (Source.wordAt (data.drop (Source.wordAt data entry)) 0))⟩).1})
      ∃ (out : Heap (H++[RefTy.array (.prim .uint)])) (z : Source.EMState E Γ),
        (Source.evalE G F (fuel+4) (sourceUintCalldataBind dst src)).run y=(.ok (.val (.memRef rfl y.2.heap.next)),mid) ∧
        (Source.evalE G F (fuel+3) (sourceUintIndexedDelete dst index)).run mid=(.ok Source.RVal.unit,z) ∧
        (Source.execItems G F (fuel+6) nps none
          (.stmt (.expr (sourceUintCalldataBind dst src)) (.stmt (.expr (sourceUintIndexedDelete dst index)) .nil) :
            Source.RItems E [] false .body Γ Γ) y.1).run (.nil,y.2)=(.ok (.normal z.1),(.nil,z.2)) ∧
        checkedSourceFreshUints (E := E) F (4+Source.wordAt data entry+32) (Source.wordAt (data.drop (Source.wordAt data entry)) 0) hp (Nat.lt_trans small (by decide : 2^64<2^256))=.ok (some pair.1) ∧
        pair.1.writeAddr (.index pair.2 .dyn k) (PrimTy.dflt .uint)=some out ∧
        SourceUintMemoryAt z y.2.heap.next out pair.2 .dyn ∧ Source.MemOK E SH z ∧
        Heap.Keeps ext hp out ∧ MObj.elems .dyn (out.get pair.2)=(CalldataPackets.RawUint.dataPayload data (Source.wordAt data entry+32) (Source.wordAt (data.drop (Source.wordAt data entry)) 0)).set k.1.toNat (PrimTy.dflt .uint) ∧
        (∀ b obj,y.2.heap.get b=some obj → z.2.heap.get b=some obj) ∧
        z.1=mid.1 ∧ z.2.ex=y.2.ex ∧ z.2.events=y.2.events ∧ z.2.logs=y.2.logs ∧ z.2.fnLocals=y.2.fnLocals ∧
        (sourceGuardedUintDelete G F fuel nps dst src index data entry y.1).run (.nil,y.2)=(.ok (.normal z.1),(.nil,z.2)) := by
  first
  | solve | rfl | simp only [] | omega
  | have tail := source_uint_entry_tail data entry small span
    have cap : (Source.wordAt (data.drop (Source.wordAt data entry)) 0)<2^256 := Nat.lt_trans small (by decide)
    have bytes : CalldataPackets.RawUint.payload F (4+Source.wordAt data entry+32) (Source.wordAt (data.drop (Source.wordAt data entry)) 0)=
        CalldataPackets.RawUint.dataPayload data (Source.wordAt data entry+32) (Source.wordAt (data.drop (Source.wordAt data entry)) 0) := by
      simpa only [Nat.add_assoc] using CalldataPackets.RawUint.payload_frame F selector data four binding (Source.wordAt data entry+32) (Source.wordAt (data.drop (Source.wordAt data entry)) 0)
    have result := source_raw_uint_bind_delete y hp G F fuel nps dst src index (4+Source.wordAt data entry+32) (Source.wordAt (data.drop (Source.wordAt data entry)) 0) k hsrc hi bound cap SH hm
    rw [bytes] at result
    obtain ⟨valid,out,z,first,second,program,adapter,write,fresh,mok,keep,values,occupied,locals,ex,events,logs,fn⟩ := result
    refine ⟨tail,valid,out,z,first,second,program,adapter,write,fresh,mok,keep,values,occupied,locals,ex,events,logs,fn,?_⟩
    rw [sourceGuardedUintDelete,tail]
    exact program

/-- Byte-derived valid entry followed by the actual Items consumer; the
view/frame alignments remain INITIAL premises, never desired postrelations. -/
theorem source_guarded_uint_bind_delete_bounds {E : Source.Env} {Γ : Source.RCtx} {H : HTy}
    (y : Source.EMState E Γ) (hp : Heap H) (G : Source.Glob E) (F : Source.Fr)
    (fuel nps : Nat) (dst : Source.Idx Γ SourceUintArrayTy)
    (src : Source.Idx Γ (.array .calldata (.int .u256) none)) (index : Source.Idx Γ (.int .u256))
    (selector data : List UInt8) (four : selector.length=4) (binding : F.cd=selector++data)
    (entry : Nat) (k : PrimTy.uint.Denote)
    (hsrc : y.1.get src=.cdRef rfl (4+Source.wordAt data entry+32) (Source.wordAt (data.drop (Source.wordAt data entry)) 0)) (hi : y.1.get index=sourceUint k)
    (small : (Source.wordAt (data.drop (Source.wordAt data entry)) 0)<2^64)
    (span : Source.wordAt data entry+32+32*(Source.wordAt (data.drop (Source.wordAt data entry)) 0)≤data.length)
    (bound : (Source.wordAt (data.drop (Source.wordAt data entry)) 0)≤k.1.toNat) (SH : Source.HeapTy) (hm : Source.MemOK E SH y) :
    Source.cdTail data entry 32=.ok ((4+Source.wordAt data entry+32),(Source.wordAt (data.drop (Source.wordAt data entry)) 0)) ∧
    ∃ valid : (CalldataPackets.RawUint.dataPayload data (Source.wordAt data entry+32) (Source.wordAt (data.drop (Source.wordAt data entry)) 0)).length<2^256,
      let pair := hp.alloc (R := .array (.prim .uint))
        (⟨CalldataPackets.RawUint.dataPayload data (Source.wordAt data entry+32) (Source.wordAt (data.drop (Source.wordAt data entry)) 0),valid⟩ : MObj H (.array (.prim .uint)))
      let mid : Source.EMState E Γ :=
        (y.1.set dst (.memRef rfl y.2.heap.next),
          {y.2 with heap := (y.2.heap.alloc ⟨SourceUintArrayTy,sourceUintMemory (CalldataPackets.RawUint.dataPayload data (Source.wordAt data entry+32) (Source.wordAt (data.drop (Source.wordAt data entry)) 0))⟩).1})
      (Source.evalE G F (fuel+4) (sourceUintCalldataBind dst src)).run y=(.ok (.val (.memRef rfl y.2.heap.next)),mid) ∧
      (Source.evalE G F (fuel+3) (sourceUintIndexedDelete dst index)).run mid=
        (.error (.revert (Source.panicData .index)),mid) ∧
      (Source.execItems G F (fuel+6) nps none
        (.stmt (.expr (sourceUintCalldataBind dst src)) (.stmt (.expr (sourceUintIndexedDelete dst index)) .nil) :
          Source.RItems E [] false .body Γ Γ) y.1).run (.nil,y.2)=
        (.error (.revert (Source.panicData .index)),(.nil,mid.2)) ∧
      checkedSourceFreshUints (E := E) F (4+Source.wordAt data entry+32) (Source.wordAt (data.drop (Source.wordAt data entry)) 0) hp (Nat.lt_trans small (by decide : 2^64<2^256))=.ok (some pair.1) ∧
      pair.1.writeAddr (.index pair.2 .dyn k) (PrimTy.dflt .uint)=none ∧
      SourceUintMemoryAt mid y.2.heap.next pair.1 pair.2 .dyn ∧ Source.MemOK E SH mid ∧
      Heap.Keeps (List.prefix_append H [RefTy.array (.prim .uint)]) hp pair.1 ∧
      (∀ b obj,y.2.heap.get b=some obj → mid.2.heap.get b=some obj) ∧
        (sourceGuardedUintDelete G F fuel nps dst src index data entry y.1).run (.nil,y.2)=(.error (.revert (Source.panicData .index)),(.nil,mid.2)) := by
  first
  | solve | rfl | simp only [] | omega
  | have tail := source_uint_entry_tail data entry small span
    have cap : (Source.wordAt (data.drop (Source.wordAt data entry)) 0)<2^256 := Nat.lt_trans small (by decide)
    have bytes : CalldataPackets.RawUint.payload F (4+Source.wordAt data entry+32) (Source.wordAt (data.drop (Source.wordAt data entry)) 0)=
        CalldataPackets.RawUint.dataPayload data (Source.wordAt data entry+32) (Source.wordAt (data.drop (Source.wordAt data entry)) 0) := by
      simpa only [Nat.add_assoc] using CalldataPackets.RawUint.payload_frame F selector data four binding (Source.wordAt data entry+32) (Source.wordAt (data.drop (Source.wordAt data entry)) 0)
    have result := source_raw_uint_bind_delete_bounds y hp G F fuel nps dst src index (4+Source.wordAt data entry+32) (Source.wordAt (data.drop (Source.wordAt data entry)) 0) k hsrc hi bound cap SH hm
    rw [bytes] at result
    obtain ⟨valid,first,second,program,adapter,write,fresh,mok,keep,occupied⟩ := result
    refine ⟨tail,valid,first,second,program,adapter,write,fresh,mok,keep,occupied,?_⟩
    rw [sourceGuardedUintDelete,tail]
    exact program

/-- info: 'Solidity.Backend.MemoryOps.source_uint_entry_tail' depends on axioms: [propext, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms source_uint_entry_tail
/-- info: 'Solidity.Backend.MemoryOps.source_guarded_uint_delete_refusal' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms source_guarded_uint_delete_refusal
/-- info: 'Solidity.Backend.MemoryOps.source_guarded_uint_bind_delete' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms source_guarded_uint_bind_delete
/-- info: 'Solidity.Backend.MemoryOps.source_guarded_uint_bind_delete_bounds' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms source_guarded_uint_bind_delete_bounds
end Solidity.Backend.MemoryOps
