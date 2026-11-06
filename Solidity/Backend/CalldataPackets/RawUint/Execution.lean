import Solidity.Backend.MemoryOps.SourceCalldataCopy
import Solidity.Backend.MemoryOps.SourceUintMemory
import Solidity.Yul.Views.ScalarCodecs

/-! Raw uint256 copying through the published Source operations. Payloads are
computed from bytes, not supplied as a success or representation premise.
Standalone copies pad missing bytes; dynamic-entry refusal belongs to cdTail. -/
namespace Solidity.Backend.CalldataPackets.RawUint
open Solidity.Backend.MemoryOps

abbrev ArrayTy : Source.STy := .array .memory (.int .u256) none

def wordValue (w : Nat) : PrimTy.uint.Denote := Evm.Memory.indexValue (Source.toWord w)

def payload (F : Source.Fr) (off len : Nat) : List PrimTy.uint.Denote :=
  (List.range len).map fun j => wordValue (Source.cdWordAt F (off+32*j))

theorem payload_length (F : Source.Fr) (off len : Nat) : (payload F off len).length=len := by
  simp only [payload,List.length_map,List.length_range]

theorem decode_uint (D : Source.Layout) (w : Nat) :
    Source.decodeWord D w (.int .u256)=.ok (sourceUint (wordValue w)) := by
  have hr : Source.IntTy.u256.lo ≤ ((Source.toWord w).val : Int) ∧
      ((Source.toWord w).val : Int) ≤ Source.IntTy.u256.hi := by
    have bound : (Source.toWord w).val < 2^256 := (Source.toWord w).isLt
    change 0 ≤ ((Source.toWord w).val : Int) ∧
      ((Source.toWord w).val : Int) ≤ ((2^256-1 : Nat) : Int)
    omega
  have rd : Source.readInt .u256 (Source.toWord w)=some ((Source.toWord w).val : Int) := by
    change (if Source.IntTy.u256.lo ≤ ((Source.toWord w).val : Int) ∧
      ((Source.toWord w).val : Int) ≤ Source.IntTy.u256.hi then
      some ((Source.toWord w).val : Int) else none)=_
    exact if_pos hr
  change (match Source.readInt .u256 (Source.toWord w) with
    | some v => Source.mkInt Source.IntTy.u256 v
    | none => .error (.revert []))=_
  rw [rd]
  change Source.mkInt Source.IntTy.u256 ((Source.toWord w).val : Int)=_
  rw [Source.mkInt,dif_pos hr]
  rfl

/-- The 32-byte reader is bounded even when its requested offset is beyond EOF. -/
theorem raw_word_bound (F : Source.Fr) (off : Nat) : Source.cdWordAt F off < 2^256 := by
  have bound : Source.beValue (Source.fitBytes 32 (F.cd.drop off)) <
      256^(Source.fitBytes 32 (F.cd.drop off)).length :=
    Yul.Views.scalar_beValue_bound _
  rw [Source.fitBytes_length] at bound
  exact bound

theorem raw_value_exact (F : Source.Fr) (off : Nat) :
    (wordValue (Source.cdWordAt F off)).val=(Source.cdWordAt F off : Int) := by
  change ((Source.cdWordAt F off % 2^256 : Nat) : Int)=_
  rw [Nat.mod_eq_of_lt (raw_word_bound F off)]

private theorem decode_indices (D : Source.Layout) (F : Source.Fr) (off : Nat)
    (indices : List Nat) :
    indices.mapM (fun j => Source.decodeWord D (Source.cdWordAt F (off+32*j)) (.int .u256))=
      .ok (indices.map fun j => sourceUint (D := D) (wordValue (Source.cdWordAt F (off+32*j)))) := by
  induction indices with
  | nil => rfl
  | cons j js ih =>
    rw [List.mapM_cons,decode_uint]
    simp only [bind,Except.bind,ih,List.map_cons]
    rfl

private theorem uint_array_ext (D : Source.Layout) {m n : Nat} (h : m=n)
    (f : Fin m → Source.Data D (.int .u256)) (g : Fin n → Source.Data D (.int .u256))
    (agree : ∀ i,f i=g ⟨i.val,by omega⟩) :
    (Source.Data.array (D := D) (l := .memory) (n := none) m (fun _ h => nomatch h) f)=
      Source.Data.array (D := D) (l := .memory) (n := none) n (fun _ h => nomatch h) g := by
  subst n
  have same : f=g := funext agree
  rw [same]

private theorem uint_array_values {D : Source.Layout} (xs : List PrimTy.uint.Denote) :
    (Source.Data.array (D := D) (l := .memory) (n := none)
      (xs.map (sourceUint (D := D))).length (fun _ h => nomatch h)
      (fun i => .val ((xs.map (sourceUint (D := D))).get i)))=sourceUintMemory xs := by
  unfold sourceUintMemory
  apply uint_array_ext D (by simp only [List.length_map])
  intro i
  simp only [List.get_eq_getElem,List.getElem_map,Fin.getElem_fin]

/-- Exact Source allocation for all runtime lengths and all raw input frames.
No byte-span bound is imposed on this standalone helper. -/
theorem copy_run {E : Source.Env} {Γ : Source.RCtx}
    (F : Source.Fr) (off len : Nat) (y : Source.EMState E Γ) :
    (Source.cdToMem F ArrayTy off len).run y=
      (.ok (.val (.memRef rfl y.2.heap.next)),
        (y.1,{y.2 with heap := (y.2.heap.alloc
          ⟨ArrayTy,sourceUintMemory (payload F off len)⟩).1})) := by
  simp only [Source.cdToMem,ArrayTy,Source.STy.loc?,Option.some.injEq,reduceCtorEq,dite_false]
  rw [Source.Hoare.run_bind,source_mapM_lift_run,decode_indices]
  have same : ((List.range len).map fun j => sourceUint (D := E.layout)
      (wordValue (Source.cdWordAt F (off+32*j))))=
      (payload F off len).map (sourceUint (D := E.layout)) := by
    simp only [payload,List.map_map,Function.comp_def]
  rw [same]
  simp only [Source.Hoare.run_bind,uint_array_values]
  rfl

/-- Allocation leaves every old heap address and all other Source state intact. -/
theorem copy_observations {E : Source.Env} {Γ : Source.RCtx}
    (F : Source.Fr) (off len : Nat) (y : Source.EMState E Γ) :
    let z := (Source.cdToMem F ArrayTy off len).run y |>.2
    z.2.heap.get y.2.heap.next=some ⟨ArrayTy,sourceUintMemory (payload F off len)⟩ ∧
    z.2.heap.next=y.2.heap.next+1 ∧
    (∀ a,a≠y.2.heap.next → z.2.heap.get a=y.2.heap.get a) ∧
    z.1=y.1 ∧ {z.2 with heap := y.2.heap}=y.2 := by
  rw [copy_run]
  dsimp only
  refine ⟨Source.Heap.alloc_get _ _,rfl,?_,rfl,?_⟩
  · intro a different
    exact Source.Heap.alloc_other _ _ different
  · cases y.2
    rfl

/-- The dynamic entry guard and copy are the existing operations, in order. -/
theorem guarded_run {E : Source.Env} {Γ : Source.RCtx}
    (data : List UInt8) (i : Nat) (F : Source.Fr) (y : Source.EMState E Γ) :
    ((Source.EM.lift (Source.cdTail data i 32)) >>= fun p =>
      Source.cdToMem F ArrayTy p.1 p.2).run y=
      match Source.cdTail data i 32 with
      | .error e => (.error e,y)
      | .ok (off,len) =>
        (.ok (.val (.memRef rfl y.2.heap.next)),
          (y.1,{y.2 with heap := (y.2.heap.alloc
            ⟨ArrayTy,sourceUintMemory (payload F off len)⟩).1})) := by
  rw [Source.Hoare.run_bind]
  cases h : Source.cdTail data i 32 with
  | error e => simp only [Source.EM.lift];rfl
  | ok p =>
    simp only [Source.EM.lift]
    exact copy_run F p.1 p.2 y

/-- First guard: a missing length word is an empty-data revert. -/
theorem entry_short_head (data : List UInt8) (i : Nat)
    (short : data.length<Source.wordAt data i+32) :
    Source.cdTail data i 32=.error (.revert []) := by
  simp only [Source.cdTail,if_pos short]

/-- Allocation-size refusal precedes the element-span check, with the actual
calldata-entry empty-data revert (not the memory-decoder allocation panic). -/
theorem entry_large_length (data : List UInt8) (i : Nat)
    (head : ¬data.length<Source.wordAt data i+32)
    (large : 2^64 ≤ Source.wordAt (data.drop (Source.wordAt data i)) 0) :
    Source.cdTail data i 32=.error (.revert []) := by
  simp only [Source.cdTail,if_neg head,if_pos large]

/-- Truncated elements fail at the published entry span guard. -/
theorem entry_short_elements (data : List UInt8) (i : Nat)
    (head : ¬data.length<Source.wordAt data i+32)
    (small : ¬2^64 ≤ Source.wordAt (data.drop (Source.wordAt data i)) 0)
    (short : ¬Source.wordAt data i+32+32*Source.wordAt (data.drop (Source.wordAt data i)) 0≤data.length) :
    Source.cdTail data i 32=.error (.revert []) := by
  simp only [Source.cdTail,if_neg head,if_neg small,if_neg short]


/-- Raw argument bytes after the four-byte selector; not an ABI encoder. -/
def dataPayload (data : List UInt8) (off len : Nat) : List PrimTy.uint.Denote :=
  (List.range len).map fun j => wordValue
    (Source.beValue (Source.fitBytes 32 (data.drop (off+32*j))))

theorem payload_frame (F : Source.Fr) (selectorBytes data : List UInt8) (four : selectorBytes.length=4)
    (binding : F.cd=selectorBytes++data) (off len : Nat) :
    payload F (4+off) len=dataPayload data off len := by
  unfold payload dataPayload
  apply List.map_congr_left
  intro j hj
  unfold Source.cdWordAt
  rw [binding,Nat.add_assoc,←four,List.drop_length_add_append]

/-- Complete ordered entry+copy outcome under the actual frame byte binding.
All three guard failures preserve the initial state; success allocates values
computed from precisely these argument bytes. -/
theorem guarded_frame_run {E : Source.Env} {Γ : Source.RCtx}
    (F : Source.Fr) (selectorBytes data : List UInt8) (four : selectorBytes.length=4)
    (binding : F.cd=selectorBytes++data) (i : Nat) (y : Source.EMState E Γ) :
    ((Source.EM.lift (Source.cdTail data i 32)) >>= fun p =>
      Source.cdToMem F ArrayTy p.1 p.2).run y=
      let off := Source.wordAt data i
      let len := Source.wordAt (data.drop off) 0
      if data.length<off+32 then (.error (.revert []),y)
      else if 2^64≤len then (.error (.revert []),y)
      else if off+32+32*len≤data.length then
        (.ok (.val (.memRef rfl y.2.heap.next)),
          (y.1,{y.2 with heap := (y.2.heap.alloc
            ⟨ArrayTy,sourceUintMemory (dataPayload data (off+32) len)⟩).1}))
      else (.error (.revert []),y) := by
  rw [guarded_run]
  dsimp only
  by_cases head : data.length<Source.wordAt data i+32
  · simp only [Source.cdTail,if_pos head]
  · by_cases large : 2^64≤Source.wordAt (data.drop (Source.wordAt data i)) 0
    · simp only [Source.cdTail,if_neg head,if_pos large]
    · by_cases span : Source.wordAt data i+32+32*Source.wordAt (data.drop (Source.wordAt data i)) 0≤data.length
      · simp only [Source.cdTail,if_neg head,if_neg large,if_pos span,pure,Except.pure]
        rw [Nat.add_assoc,payload_frame F selectorBytes data four binding]
      · simp only [Source.cdTail,if_neg head,if_neg large,if_neg span]

/-- The real resolved implicit conversion, with no target compiler assumed. -/
def copyExpr {E : Source.Env} {Γ : Source.RCtx}
    (i : Source.Idx Γ (.array .calldata (.int .u256) none)) : Source.RExpr E Γ ArrayTy :=
  .conv (.local i) (.inl rfl)

theorem eval_copy {E : Source.Env} {Γ : Source.RCtx}
    (G : Source.Glob E) (F : Source.Fr) (n : Nat) (y : Source.EMState E Γ)
    (i : Source.Idx Γ (.array .calldata (.int .u256) none)) (off len : Nat)
    (localRef : y.1.get i=.cdRef rfl off len) :
    (Source.evalE G F (n+2) (copyExpr i)).run y=
      (.ok (.val (.memRef rfl y.2.heap.next)),
        (y.1,{y.2 with heap := (y.2.heap.alloc
          ⟨ArrayTy,sourceUintMemory (payload F off len)⟩).1})) := by
  rw [copyExpr,Source.evalE,Source.Hoare.run_bind,source_local_value_run G F n y i _ localRef]
  change (Source.convRV F (n+1) ArrayTy
    (.val (.cdRef rfl off len) : Source.RVal E.layout (.array .calldata (.int .u256) none))).run y=_
  unfold Source.convRV
  rw [dif_neg (show (Source.STy.array .calldata (.int .u256) none)≠ArrayTy from by intro h;cases h)]
  exact copy_run F off len y

/-- A structural decoded table whose contents are DERIVED from raw bytes.
This representation does not assert native execution or entry admission. -/
def table {D : Source.Layout} (F : Source.Fr) (off len : Nat) : Source.Calldata D :=
  { input := F.cd
    objects := fun k => if k=off then some
      ⟨.array .calldata (.int .u256) none,
        .array (payload F off len).length (fun _ h => nomatch h)
          (fun i => .val (sourceUint ((payload F off len)[i])))⟩ else none }

theorem table_uints {D : Source.Layout} (F : Source.Fr) (off len : Nat) :
    calldataUints (D := D) (table F off len) off=some (payload F off len) := by
  unfold calldataUints table
  simp only []
  change some (List.ofFn (fun i : Fin (payload F off len).length => calldataUint
    (Source.Data.val (sourceUint (D := D) (payload F off len)[i]))))=_
  rw [calldataUint_values]

/-- Existing intrinsic checked transfer consumes the same raw-derived values.
Bounds are operation-side slice/destination validity, not decoded payloads. -/
theorem transfer {D : Source.Layout} {H : HTy} {R : RefTy}
    (F : Source.Fr) (off len : Nat) (hp : Heap H) (dst : HRef H R)
    (a : ArrTy R (.prim .uint)) (start stop offset : Nat)
    (bounds : SliceBounds len start stop) (fits : offset+(stop-start)≤hp.len dst a) :
    checkedCalldataUints (D := D) (table F off len) off hp dst a start stop offset=
      some (overwriteSlice hp dst a offset
        (((payload F off len).drop start).take (stop-start))
        (by rw [(show SliceBounds (payload F off len).length start stop from
          by simpa only [payload_length] using bounds).length];exact fits)) := by
  unfold checkedCalldataUints
  rw [table_uints]
  simp only [Bind.bind,Option.bind,payload_length,
    dif_pos (show start≤stop ∧ stop≤len from ⟨bounds.ordered,bounds.bounded⟩),dif_pos fits]

/-- info: 'Solidity.Backend.CalldataPackets.RawUint.decode_uint' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms decode_uint
/-- info: 'Solidity.Backend.CalldataPackets.RawUint.raw_word_bound' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms raw_word_bound
/-- info: 'Solidity.Backend.CalldataPackets.RawUint.raw_value_exact' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms raw_value_exact
/-- info: 'Solidity.Backend.CalldataPackets.RawUint.copy_run' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms copy_run
/-- info: 'Solidity.Backend.CalldataPackets.RawUint.copy_observations' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms copy_observations
/-- info: 'Solidity.Backend.CalldataPackets.RawUint.guarded_frame_run' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms guarded_frame_run
/-- info: 'Solidity.Backend.CalldataPackets.RawUint.eval_copy' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms eval_copy
/-- info: 'Solidity.Backend.CalldataPackets.RawUint.table_uints' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms table_uints
/-- info: 'Solidity.Backend.CalldataPackets.RawUint.transfer' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms transfer
end Solidity.Backend.CalldataPackets.RawUint
