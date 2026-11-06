import Solidity.Backend.MemoryOps.SourceCalldataCopy

/-! Raw Boolean calldata validation against the existing independent Source
copy operation. Values are derived from the actual frame bytes. No decoder,
Source evaluator, entry guard, allocator or target compiler is defined here. -/
namespace Solidity.Backend.MemoryOps

def rawBoolPayload (F : Source.Fr) (off len : Nat) : List Bool :=
  (List.range len).map fun j => decide (Source.cdWordAt F (off+32*j)=1)

/-- Canonicality is a fact about the actual bytes, not an assumed decode run. -/
theorem decode_raw_bool (D : Source.Layout) (w : Nat) (canonical : w=0 ∨ w=1) :
    Source.decodeWord D w .bool=.ok (.bool (decide (w=1))) := by
  first
  | solve | simp only [] | omega
  | rcases canonical with h|h <;> subst w <;> rfl

theorem raw_bool_indices (D : Source.Layout) (F : Source.Fr) (off : Nat) (indices : List Nat)
    (canonical : ∀ j,j∈indices → Source.cdWordAt F (off+32*j)=0 ∨ Source.cdWordAt F (off+32*j)=1) :
    indices.mapM (fun j => Source.decodeWord D (Source.cdWordAt F (off+32*j)) .bool)=
      .ok (indices.map fun j => Source.Val.bool (D := D) (decide (Source.cdWordAt F (off+32*j)=1))) := by
  first
  | solve | simp only [] | omega
  | induction indices with
    | nil => rfl
    | cons j js ih =>
      rw [List.mapM_cons,decode_raw_bool D _ (canonical j (by exact List.mem_cons_self))]
      have rest := ih (fun k hk => canonical k (List.mem_cons_of_mem j hk))
      simp only [bind,Except.bind,rest,List.map_cons]
      rfl

/-- All elements are decoded from bytes before the one actual fresh allocation.
Runtime length and input byte length are unrestricted by this standalone law. -/
theorem source_raw_bool_copy {E : Source.Env} {Γ : Source.RCtx}
    (F : Source.Fr) (off len : Nat) (y : Source.EMState E Γ)
    (canonical : ∀ j,j<len → Source.cdWordAt F (off+32*j)=0 ∨ Source.cdWordAt F (off+32*j)=1) :
    (Source.cdToMem F SourceBoolArrayTy off len).run y=
      (.ok (.val (.memRef rfl y.2.heap.next)),
        (y.1,{y.2 with heap := (y.2.heap.alloc ⟨SourceBoolArrayTy,sourceBoolMemory (rawBoolPayload F off len)⟩).1})) := by
  first
  | solve | simp only [] | omega
  | have decoded := raw_bool_indices E.layout F off (List.range len)
        (fun j hj => canonical j (List.mem_range.mp hj))
    rw [source_cd_bool_run]
    change (List.range len).mapM _=_ at decoded
    unfold sourceCalldataBoolValues
    rw [decoded]
    simp only [sourceBoolValuePayload,rawBoolPayload,List.map_map,Function.comp_def,calldataBool]

/-- The actual successful copy derives every old-object/local/world frame. -/
theorem source_raw_bool_copy_frames {E : Source.Env} {Γ : Source.RCtx}
    (F : Source.Fr) (off len : Nat) (y : Source.EMState E Γ)
    (canonical : ∀ j,j<len → Source.cdWordAt F (off+32*j)=0 ∨ Source.cdWordAt F (off+32*j)=1) :
    let z := (Source.cdToMem F SourceBoolArrayTy off len).run y |>.2
    z.2.heap.get y.2.heap.next=some ⟨SourceBoolArrayTy,sourceBoolMemory (rawBoolPayload F off len)⟩ ∧
    z.2.heap.next=y.2.heap.next+1 ∧
    (∀ a,a≠y.2.heap.next → z.2.heap.get a=y.2.heap.get a) ∧
    z.1=y.1 ∧ {z.2 with heap := y.2.heap}=y.2 := by
  first
  | solve | simp only [] | omega
  | rw [source_raw_bool_copy F off len y canonical]
    refine ⟨Source.Heap.alloc_get _ _,rfl,fun a ha => Source.Heap.alloc_other _ _ ha,rfl,?_⟩
    cases y.2
    rfl

/-- A material accepted prefix is derived from raw words. The first invalid
raw Boolean word then rejects before allocation, retaining the actual state. -/
theorem source_raw_bool_copy_first_error {E : Source.Env} {Γ : Source.RCtx}
    (F : Source.Fr) (off len : Nat) (y : Source.EMState E Γ) (acceptedIndices pending : List Nat) (i : Nat)
    (order : List.range len=acceptedIndices++i::pending)
    (canonical : ∀ j,j∈acceptedIndices → Source.cdWordAt F (off+32*j)=0 ∨ Source.cdWordAt F (off+32*j)=1)
    (invalid : 1<Source.cdWordAt F (off+32*i)) :
    let accepted := acceptedIndices.map fun j => Source.Val.bool (D := E.layout) (decide (Source.cdWordAt F (off+32*j)=1))
    (acceptedIndices.mapM (fun j => Source.EM.lift (E := E) (Γ := Γ)
      (Source.decodeWord E.layout (Source.cdWordAt F (off+32*j)) .bool))).run y=(.ok accepted,y) ∧
    (Source.EM.lift (E := E) (Γ := Γ) (Source.decodeWord E.layout (Source.cdWordAt F (off+32*i)) .bool)).run y=
      (.error (.revert []),y) ∧
    (Source.cdToMem F SourceBoolArrayTy off len).run y=(.error (.revert []),y) := by
  first
  | solve | simp only [] | omega
  | have bad : Source.decodeWord E.layout (Source.cdWordAt F (off+32*i)) .bool=.error (.revert []) := by
      simp only [Source.decodeWord,Source.decodeElemWord,if_neg (by omega : Source.cdWordAt F (off+32*i)≠0),
        if_neg (by omega : Source.cdWordAt F (off+32*i)≠1)]
    exact source_cd_bool_first_error F off len y acceptedIndices pending i _ (.revert []) order
      (raw_bool_indices E.layout F off acceptedIndices canonical) bad

/-- info: 'Solidity.Backend.MemoryOps.decode_raw_bool' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms decode_raw_bool
/-- info: 'Solidity.Backend.MemoryOps.raw_bool_indices' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms raw_bool_indices
/-- info: 'Solidity.Backend.MemoryOps.source_raw_bool_copy' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms source_raw_bool_copy
/-- info: 'Solidity.Backend.MemoryOps.source_raw_bool_copy_frames' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms source_raw_bool_copy_frames
/-- info: 'Solidity.Backend.MemoryOps.source_raw_bool_copy_first_error' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms source_raw_bool_copy_first_error
end Solidity.Backend.MemoryOps
