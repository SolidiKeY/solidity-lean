import Solidity.Backend.MemoryOps.SourceRawBoolEntry

/-!
# Raw bool calldata-to-memory packet

Validation and payload are computed from actual zero-padded calldata words.
The existing Source decoder, copy, allocator and entry guard execute unchanged.
This packet proves their complete outcome, including dirty-word rejection before
allocation. It does not establish native byte-memory, gas or compiler adequacy.
-/
namespace Solidity.Backend.CalldataPackets.RawBool
open Solidity.Backend.MemoryOps

abbrev ArrayTy : Source.STy := .array .memory .bool none

def canonicalWord (w : Nat) : Bool := decide (w=0 ∨ w=1)

def valid (F : Source.Fr) (off len : Nat) : Bool :=
  (List.range len).all fun j => canonicalWord (Source.cdWordAt F (off+32*j))

def payload (F : Source.Fr) (off len : Nat) : List Bool := rawBoolPayload F off len

theorem payload_length (F : Source.Fr) (off len : Nat) : (payload F off len).length=len := by
  simp only [payload,rawBoolPayload,List.length_map,List.length_range]

theorem valid_iff (F : Source.Fr) (off len : Nat) : valid F off len=true ↔
    ∀ j,j<len → Source.cdWordAt F (off+32*j)=0 ∨ Source.cdWordAt F (off+32*j)=1 := by
  simp only [valid,List.all_eq_true,canonicalWord,decide_eq_true_eq,List.mem_range]

/-- Exact 0/1 validation; every other raw natural word reverts, without masking. -/
theorem decode_bool (D : Source.Layout) (w : Nat) :
    Source.decodeWord D w .bool=
      if canonicalWord w then .ok (.bool (decide (w=1))) else .error (.revert []) := by
  by_cases zero : w=0
  · subst w; rfl
  · by_cases one : w=1
    · subst w; rfl
    · have bad : canonicalWord w=false := decide_eq_false (by omega)
      simp only [Source.decodeWord,Source.decodeElemWord,if_neg zero,if_neg one,bad,
        Bool.false_eq_true,if_false]

private theorem decode_indices (D : Source.Layout) (F : Source.Fr) (off : Nat)
    (indices : List Nat) :
    indices.mapM (fun j => Source.decodeWord D (Source.cdWordAt F (off+32*j)) .bool)=
      if indices.all (fun j => canonicalWord (Source.cdWordAt F (off+32*j))) then
        .ok (indices.map fun j => Source.Val.bool (D := D) (decide (Source.cdWordAt F (off+32*j)=1)))
      else .error (.revert []) := by
  induction indices with
  | nil => rfl
  | cons j js ih =>
      rw [List.mapM_cons,decode_bool,List.all_cons]
      cases head : canonicalWord (Source.cdWordAt F (off+32*j)) <;>
        cases tail : js.all (fun j => canonicalWord (Source.cdWordAt F (off+32*j))) <;>
        simp only [tail,ih,Bool.false_and,Bool.true_and,Bool.false_eq_true,
          if_false,if_true,List.map_cons,bind,Except.bind,pure,Except.pure]

/-- Unconditional classification of the actual Source copy. Validation is a
computed test, never a supplied successful decoder/copy or postheap premise. -/
theorem copy_run {E : Source.Env} {Γ : Source.RCtx}
    (F : Source.Fr) (off len : Nat) (y : Source.EMState E Γ) :
    (Source.cdToMem F ArrayTy off len).run y=
      if valid F off len then
        (.ok (.val (.memRef rfl y.2.heap.next)),
          (y.1,{y.2 with heap := (y.2.heap.alloc
            ⟨ArrayTy,sourceBoolMemory (payload F off len)⟩).1}))
      else (.error (.revert []),y) := by
  by_cases accepted : valid F off len=true
  · rw [if_pos accepted]
    exact source_raw_bool_copy F off len y ((valid_iff F off len).mp accepted)
  · have rejected : sourceCalldataBoolValues E F off len=.error (.revert []) := by
      unfold sourceCalldataBoolValues
      rw [decode_indices]
      exact if_neg accepted
    rw [if_neg accepted,source_cd_bool_run,rejected]

/-- Any dirty raw element forces the computed validator to fail. -/
theorem dirty_at (F : Source.Fr) (off len i : Nat) (inside : i<len)
    (dirty : 1<Source.cdWordAt F (off+32*i)) : valid F off len=false := by
  cases h : valid F off len with
  | false => rfl
  | true =>
      have canonical := (valid_iff F off len).mp h i inside
      omega

/-- Dirty input preserves the complete state, including nonempty old heaps. -/
theorem copy_dirty {E : Source.Env} {Γ : Source.RCtx}
    (F : Source.Fr) (off len : Nat) (y : Source.EMState E Γ)
    (dirty : valid F off len=false) :
    (Source.cdToMem F ArrayTy off len).run y=(.error (.revert []),y) := by
  rw [copy_run,dirty]
  rfl

/-- Successful allocation frames old addresses and every non-heap observation. -/
theorem copy_observations {E : Source.Env} {Γ : Source.RCtx}
    (F : Source.Fr) (off len : Nat) (y : Source.EMState E Γ) :
    let z := (Source.cdToMem F ArrayTy off len).run y |>.2
    (∀ a,a≠y.2.heap.next → z.2.heap.get a=y.2.heap.get a) ∧
    z.1=y.1 ∧ {z.2 with heap := y.2.heap}=y.2 := by
  rw [copy_run]
  split
  · refine ⟨fun a different => Source.Heap.alloc_other _ _ different,rfl,?_⟩
    cases y.2
    rfl
  · exact ⟨fun _ _ => rfl,rfl,rfl⟩

/-- The existing entry guard runs before validation; both failure phases retain
state. Standalone copy is deliberately not given an entry-span restriction. -/
theorem guarded_run {E : Source.Env} {Γ : Source.RCtx}
    (data : List UInt8) (i : Nat) (F : Source.Fr) (y : Source.EMState E Γ) :
    ((Source.EM.lift (Source.cdTail data i 32)) >>= fun p =>
      Source.cdToMem F ArrayTy p.1 p.2).run y=
      match Source.cdTail data i 32 with
      | .error e => (.error e,y)
      | .ok (off,len) =>
        if valid F off len then
          (.ok (.val (.memRef rfl y.2.heap.next)),
            (y.1,{y.2 with heap := (y.2.heap.alloc
              ⟨ArrayTy,sourceBoolMemory (payload F off len)⟩).1}))
        else (.error (.revert []),y) := by
  rw [source_raw_bool_guarded_run]
  cases h : Source.cdTail data i 32 with
  | error e => rfl
  | ok p => exact copy_run F p.1 p.2 y

def dataValid (data : List UInt8) (off len : Nat) : Bool :=
  (List.range len).all fun j => canonicalWord
    (Source.beValue (Source.fitBytes 32 (data.drop (off+32*j))))

def dataPayload (data : List UInt8) (off len : Nat) : List Bool :=
  (List.range len).map fun j => decide
    (Source.beValue (Source.fitBytes 32 (data.drop (off+32*j)))=1)

theorem valid_frame (F : Source.Fr) (selectorBytes data : List UInt8)
    (four : selectorBytes.length=4) (binding : F.cd=selectorBytes++data) (off len : Nat) :
    valid F (4+off) len=dataValid data off len := by
  unfold valid dataValid
  have same : (fun j => canonicalWord (Source.cdWordAt F (4+off+32*j)))=
      (fun j => canonicalWord (Source.beValue (Source.fitBytes 32 (data.drop (off+32*j))))) := by
    funext j
    rw [raw_bool_frame_word F selectorBytes data four binding]
  rw [same]

theorem payload_frame (F : Source.Fr) (selectorBytes data : List UInt8)
    (four : selectorBytes.length=4) (binding : F.cd=selectorBytes++data) (off len : Nat) :
    payload F (4+off) len=dataPayload data off len := by
  unfold payload rawBoolPayload dataPayload
  apply List.map_congr_left
  intro j hj
  rw [raw_bool_frame_word F selectorBytes data four binding]

/-- Complete ordered entry+copy result, from the actual argument bytes. -/
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
        if dataValid data (off+32) len then
          (.ok (.val (.memRef rfl y.2.heap.next)),
            (y.1,{y.2 with heap := (y.2.heap.alloc
              ⟨ArrayTy,sourceBoolMemory (dataPayload data (off+32) len)⟩).1}))
        else (.error (.revert []),y)
      else (.error (.revert []),y) := by
  rw [guarded_run]
  dsimp only
  by_cases head : data.length<Source.wordAt data i+32
  · simp only [Source.cdTail,if_pos head]
  · by_cases large : 2^64≤Source.wordAt (data.drop (Source.wordAt data i)) 0
    · simp only [Source.cdTail,if_neg head,if_pos large]
    · by_cases span : Source.wordAt data i+32+32*Source.wordAt (data.drop (Source.wordAt data i)) 0≤data.length
      · simp only [Source.cdTail,if_neg head,if_neg large,if_pos span,pure,Except.pure]
        rw [Nat.add_assoc,valid_frame F selectorBytes data four binding,
          payload_frame F selectorBytes data four binding]
      · simp only [Source.cdTail,if_neg head,if_neg large,if_neg span]

/-- Actual resolved implicit conversion, with validation still computed. -/
def copyExpr {E : Source.Env} {Γ : Source.RCtx}
    (i : Source.Idx Γ (.array .calldata .bool none)) : Source.RExpr E Γ ArrayTy :=
  .conv (.local i) (.inl rfl)

theorem eval_copy {E : Source.Env} {Γ : Source.RCtx}
    (G : Source.Glob E) (F : Source.Fr) (n : Nat) (y : Source.EMState E Γ)
    (i : Source.Idx Γ (.array .calldata .bool none)) (off len : Nat)
    (localRef : y.1.get i=.cdRef rfl off len) :
    (Source.evalE G F (n+2) (copyExpr i)).run y=
      if valid F off len then
        (.ok (.val (.memRef rfl y.2.heap.next)),
          (y.1,{y.2 with heap := (y.2.heap.alloc
            ⟨ArrayTy,sourceBoolMemory (payload F off len)⟩).1}))
      else (.error (.revert []),y) := by
  rw [copyExpr,Source.evalE,Source.Hoare.run_bind,source_local_value_run G F n y i _ localRef]
  change (Source.convRV F (n+1) ArrayTy
    (.val (.cdRef rfl off len) : Source.RVal E.layout (.array .calldata .bool none))).run y=_
  unfold Source.convRV
  rw [dif_neg (show (Source.STy.array .calldata .bool none)≠ArrayTy from by intro h;cases h)]
  exact copy_run F off len y

/-- The decoded-table view exists only after actual raw validation succeeds. -/
def table {D : Source.Layout} (F : Source.Fr) (off len : Nat) : Source.Calldata D :=
  { input := F.cd
    objects := fun k => if k=off then
      if valid F off len then some
        ⟨.array .calldata .bool none,
          .array (payload F off len).length (fun _ h => nomatch h)
            (fun i => .val (.bool ((payload F off len)[i])))⟩
      else none
    else none }

theorem table_bools {D : Source.Layout} (F : Source.Fr) (off len : Nat) :
    calldataBools (D := D) (table F off len) off=
      if valid F off len then some (payload F off len) else none := by
  unfold calldataBools table
  dsimp only
  rw [if_pos rfl]
  by_cases accepted : valid F off len=true
  · rw [if_pos accepted,if_pos accepted]
    change some (List.ofFn (fun i : Fin (payload F off len).length => (payload F off len)[i]))=_
    congr 1
    apply List.ext_getElem
    · exact List.length_ofFn
    · intro i hi hj
      simp only [List.getElem_ofFn,Fin.getElem_fin]
  · rw [if_neg accepted,if_neg accepted]

/-- Existing checked transfer consumes the same computed validation/payload.
Slice/destination bounds are operation-side validity, not assumed decoding. -/
theorem transfer {D : Source.Layout} {H : HTy} {R : RefTy}
    (F : Source.Fr) (off len : Nat) (hp : Heap H) (dst : HRef H R)
    (a : ArrTy R (.prim .bool)) (start stop offset : Nat)
    (bounds : SliceBounds len start stop) (fits : offset+(stop-start)≤hp.len dst a) :
    checkedCalldataBools (D := D) (table F off len) off hp dst a start stop offset=
      if valid F off len then
        some (overwriteSlice hp dst a offset
          (((payload F off len).drop start).take (stop-start))
          (by rw [(show SliceBounds (payload F off len).length start stop from
            by simpa only [payload_length] using bounds).length];exact fits))
      else none := by
  unfold checkedCalldataBools
  rw [table_bools]
  by_cases accepted : valid F off len=true
  · simp only [if_pos accepted,Bind.bind,Option.bind,payload_length,
      dif_pos (show start≤stop ∧ stop≤len from ⟨bounds.ordered,bounds.bounded⟩),dif_pos fits]
  · simp only [if_neg accepted,Bind.bind,Option.bind]


/-- info: 'Solidity.Backend.CalldataPackets.RawBool.payload_length' depends on axioms: [propext] -/
#guard_msgs in
#print axioms payload_length
/-- info: 'Solidity.Backend.CalldataPackets.RawBool.valid_iff' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms valid_iff
/-- info: 'Solidity.Backend.CalldataPackets.RawBool.decode_bool' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms decode_bool
/-- info: '_private.Solidity.Backend.CalldataPackets.RawBool.Execution.0.Solidity.Backend.CalldataPackets.RawBool.decode_indices' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms decode_indices
/-- info: 'Solidity.Backend.CalldataPackets.RawBool.copy_run' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms copy_run
/-- info: 'Solidity.Backend.CalldataPackets.RawBool.dirty_at' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms dirty_at
/-- info: 'Solidity.Backend.CalldataPackets.RawBool.copy_dirty' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms copy_dirty
/-- info: 'Solidity.Backend.CalldataPackets.RawBool.copy_observations' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms copy_observations
/-- info: 'Solidity.Backend.CalldataPackets.RawBool.guarded_run' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms guarded_run
/-- info: 'Solidity.Backend.CalldataPackets.RawBool.valid_frame' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms valid_frame
/-- info: 'Solidity.Backend.CalldataPackets.RawBool.payload_frame' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms payload_frame
/-- info: 'Solidity.Backend.CalldataPackets.RawBool.guarded_frame_run' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms guarded_frame_run
/-- info: 'Solidity.Backend.CalldataPackets.RawBool.eval_copy' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms eval_copy
/-- info: 'Solidity.Backend.CalldataPackets.RawBool.table_bools' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms table_bools
/-- info: 'Solidity.Backend.CalldataPackets.RawBool.transfer' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms transfer

end Solidity.Backend.CalldataPackets.RawBool
