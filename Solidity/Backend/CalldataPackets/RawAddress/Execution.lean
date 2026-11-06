import Solidity.Source.Eval
import Solidity.Source.Hoare

/-! Raw address-array calldata copying through the existing Source decoder and
allocator. Payloads are computed from raw frame bytes. Dirty high bits revert
before allocation, including a dirty element following a valid prefix.
This packet does not claim compiler/EVM or physical-memory adequacy. -/
namespace Solidity.Backend.CalldataPackets.RawAddress

abbrev ArrayTy (payable : Bool) : Source.STy := .array .memory (.address payable) none

/-- Typed values derived by the published decoder, never a supplied payload. -/
def payload (D : Source.Layout) (payable : Bool) (F : Source.Fr) (off len : Nat) :
    Source.R (List (Source.Val D (.address payable))) :=
  (List.range len).mapM fun j => Source.decodeWord D (Source.cdWordAt F (off+32*j)) (.address payable)

def memory {D : Source.Layout} {payable : Bool}
    (xs : List (Source.Val D (.address payable))) : Source.Data D (ArrayTy payable) :=
  .array xs.length (fun _ h => nomatch h) (fun i => .val (xs.get i))

theorem decode_clean (D : Source.Layout) (payable : Bool) (w : Nat) (h : w<2^160) :
    Source.decodeWord D w (.address payable)=.ok (.address ⟨w,h⟩) := by
  simp only [Source.decodeWord,Source.decodeElemWord,dif_pos h,pure,Except.pure]

theorem decode_dirty (D : Source.Layout) (payable : Bool) (w : Nat) (h : 2^160≤w) :
    Source.decodeWord D w (.address payable)=.error (.revert []) := by
  simp only [Source.decodeWord,Source.decodeElemWord,dif_neg (Nat.not_lt.mpr h)]

-- Same elementary List/Except lifting argument as the template's published
-- source_mapM_lift_run. Kept private to avoid importing the unrelated memory
-- transfer/representation closure; this defines no Source operation.
private theorem mapM_lift_run {E : Source.Env} {Γ : Source.RCtx} {α β : Type}
    (f : α → Source.R β) (xs : List α) (y : Source.EMState E Γ) :
    (xs.mapM (fun x => Source.EM.lift (E := E) (Γ := Γ) (f x))).run y=(xs.mapM f,y) := by
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

/-- Complete outcome for every raw frame, offset, length and payable flag.
The error branch preserves the entire initial state, even after valid elements. -/
theorem copy_run {E : Source.Env} {Γ : Source.RCtx}
    (payable : Bool) (F : Source.Fr) (off len : Nat) (y : Source.EMState E Γ) :
    (Source.cdToMem F (ArrayTy payable) off len).run y=
      match payload E.layout payable F off len with
      | .error e => (.error e,y)
      | .ok xs =>
        (.ok (.val (.memRef rfl y.2.heap.next)),
          (y.1,{y.2 with heap := (y.2.heap.alloc ⟨ArrayTy payable,memory xs⟩).1})) := by
  simp only [Source.cdToMem,ArrayTy,Source.STy.loc?,Option.some.injEq,reduceCtorEq,dite_false]
  rw [Source.Hoare.run_bind,mapM_lift_run]
  unfold payload
  cases hd : (List.range len).mapM (fun j => Source.decodeWord E.layout
      (Source.cdWordAt F (off+32*j)) (.address payable)) with
  | error e => rfl
  | ok xs =>
    simp only [Source.Hoare.run_bind]
    rfl

/-- Every failure, including high-bit validation, leaves old allocations intact. -/
theorem copy_error {E : Source.Env} {Γ : Source.RCtx}
    (payable : Bool) (F : Source.Fr) (off len : Nat) (y : Source.EMState E Γ)
    (h : payload E.layout payable F off len=.error (.revert [])) :
    (Source.cdToMem F (ArrayTy payable) off len).run y=(.error (.revert []),y) := by
  rw [copy_run,h]

private theorem dirty_indices (D : Source.Layout) (payable : Bool) (F : Source.Fr) (off : Nat)
    (indices : List Nat) (dirty : ∃ j ∈ indices,2^160≤Source.cdWordAt F (off+32*j)) :
    indices.mapM (fun j => Source.decodeWord D (Source.cdWordAt F (off+32*j)) (.address payable))=
      .error (.revert []) := by
  revert dirty
  induction indices with
  | nil => intro dirty;rcases dirty with ⟨j,hj,_⟩;cases hj
  | cons j js ih =>
    intro dirty
    by_cases h : Source.cdWordAt F (off+32*j)<2^160
    · rw [List.mapM_cons,decode_clean D payable _ h]
      have tail : ∃ k ∈ js,2^160≤Source.cdWordAt F (off+32*k) := by
        rcases dirty with ⟨k,hk,hd⟩
        rcases List.mem_cons.mp hk with same | member
        · subst k;omega
        · exact ⟨k,member,hd⟩
      simp only [bind,Except.bind,ih tail]
    · rw [List.mapM_cons,decode_dirty D payable _ (Nat.le_of_not_gt h)]
      rfl

/-- A dirty word at ANY selected position reverts without allocating a prefix. -/
theorem copy_dirty {E : Source.Env} {Γ : Source.RCtx}
    (payable : Bool) (F : Source.Fr) (off len : Nat) (y : Source.EMState E Γ)
    (j : Nat) (within : j<len) (dirty : 2^160≤Source.cdWordAt F (off+32*j)) :
    (Source.cdToMem F (ArrayTy payable) off len).run y=(.error (.revert []),y) := by
  apply copy_error
  exact dirty_indices E.layout payable F off (List.range len)
    ⟨j,List.mem_range.mpr within,dirty⟩

/-- Success allocates once, preserves every old address and all other state.
The successful result is the computed raw decoder, not a representation premise. -/
theorem copy_observations {E : Source.Env} {Γ : Source.RCtx}
    (payable : Bool) (F : Source.Fr) (off len : Nat) (y : Source.EMState E Γ)
    (xs : List (Source.Val E.layout (.address payable)))
    (h : payload E.layout payable F off len=.ok xs) :
    let z := (Source.cdToMem F (ArrayTy payable) off len).run y |>.2
    z.2.heap.get y.2.heap.next=some ⟨ArrayTy payable,memory xs⟩ ∧
    z.2.heap.next=y.2.heap.next+1 ∧
    (∀ a,a≠y.2.heap.next → z.2.heap.get a=y.2.heap.get a) ∧
    z.1=y.1 ∧ {z.2 with heap := y.2.heap}=y.2 := by
  rw [copy_run,h]
  dsimp only
  refine ⟨Source.Heap.alloc_get _ _,rfl,?_,rfl,?_⟩
  · intro a different
    exact Source.Heap.alloc_other _ _ different
  · cases y.2
    rfl

/-- Existing entry guards precede validation and allocation. -/
theorem guarded_run {E : Source.Env} {Γ : Source.RCtx}
    (payable : Bool) (data : List UInt8) (i : Nat) (F : Source.Fr) (y : Source.EMState E Γ) :
    ((Source.EM.lift (Source.cdTail data i 32)) >>= fun p =>
      Source.cdToMem F (ArrayTy payable) p.1 p.2).run y=
      match Source.cdTail data i 32 with
      | .error e => (.error e,y)
      | .ok (off,len) =>
        match payload E.layout payable F off len with
        | .error e => (.error e,y)
        | .ok xs =>
          (.ok (.val (.memRef rfl y.2.heap.next)),
            (y.1,{y.2 with heap := (y.2.heap.alloc ⟨ArrayTy payable,memory xs⟩).1})) := by
  rw [Source.Hoare.run_bind]
  cases h : Source.cdTail data i 32 with
  | error e => simp only [Source.EM.lift];rfl
  | ok p =>
    simp only [Source.EM.lift]
    exact copy_run payable F p.1 p.2 y

/-- No unused words are validated; the zero-length copy allocates an empty array. -/
theorem copy_zero {E : Source.Env} {Γ : Source.RCtx}
    (payable : Bool) (F : Source.Fr) (off : Nat) (y : Source.EMState E Γ) :
    (Source.cdToMem F (ArrayTy payable) off 0).run y=
      (.ok (.val (.memRef rfl y.2.heap.next)),
        (y.1,{y.2 with heap := (y.2.heap.alloc ⟨ArrayTy payable,memory []⟩).1})) := by
  rw [copy_run]
  rfl

/-- Raw argument bytes, excluding the selector, with the same decoder. -/
def dataPayload (D : Source.Layout) (payable : Bool) (data : List UInt8) (off len : Nat) :
    Source.R (List (Source.Val D (.address payable))) :=
  (List.range len).mapM fun j => Source.decodeWord D
    (Source.beValue (Source.fitBytes 32 (data.drop (off+32*j)))) (.address payable)

theorem payload_frame (D : Source.Layout) (payable : Bool) (F : Source.Fr)
    (selectorBytes data : List UInt8) (four : selectorBytes.length=4)
    (binding : F.cd=selectorBytes++data) (off len : Nat) :
    payload D payable F (4+off) len=dataPayload D payable data off len := by
  unfold payload dataPayload
  apply congrArg (fun f : Nat → Source.R (Source.Val D (.address payable)) => (List.range len).mapM f)
  funext j
  unfold Source.cdWordAt
  rw [binding,Nat.add_assoc,←four,List.drop_length_add_append]

/-- Same-input entry and copy: the frame is tied to selector plus argument bytes.
The original three entry guards retain their order; then every element validates. -/
theorem guarded_frame_run {E : Source.Env} {Γ : Source.RCtx}
    (payable : Bool) (F : Source.Fr) (selectorBytes data : List UInt8)
    (four : selectorBytes.length=4) (binding : F.cd=selectorBytes++data)
    (i : Nat) (y : Source.EMState E Γ) :
    ((Source.EM.lift (Source.cdTail data i 32)) >>= fun p =>
      Source.cdToMem F (ArrayTy payable) p.1 p.2).run y=
      let off := Source.wordAt data i
      let len := Source.wordAt (data.drop off) 0
      if data.length<off+32 then (.error (.revert []),y)
      else if 2^64≤len then (.error (.revert []),y)
      else if off+32+32*len≤data.length then
        match dataPayload E.layout payable data (off+32) len with
        | .error e => (.error e,y)
        | .ok xs =>
          (.ok (.val (.memRef rfl y.2.heap.next)),
            (y.1,{y.2 with heap := (y.2.heap.alloc ⟨ArrayTy payable,memory xs⟩).1}))
      else (.error (.revert []),y) := by
  rw [guarded_run]
  dsimp only
  by_cases head : data.length<Source.wordAt data i+32
  · simp only [Source.cdTail,if_pos head]
  · by_cases large : 2^64≤Source.wordAt (data.drop (Source.wordAt data i)) 0
    · simp only [Source.cdTail,if_neg head,if_pos large]
    · by_cases span : Source.wordAt data i+32+32*Source.wordAt (data.drop (Source.wordAt data i)) 0≤data.length
      · simp only [Source.cdTail,if_neg head,if_neg large,if_pos span,pure,Except.pure]
        rw [Nat.add_assoc,payload_frame E.layout payable F selectorBytes data four binding]
        cases dataPayload E.layout payable data (Source.wordAt data i+32)
          (Source.wordAt (data.drop (Source.wordAt data i)) 0) <;> rfl
      · simp only [Source.cdTail,if_neg head,if_neg large,if_neg span]

/-- The existing resolved implicit calldata-to-memory conversion. -/
def copyExpr {E : Source.Env} {Γ : Source.RCtx} (payable : Bool)
    (i : Source.Idx Γ (.array .calldata (.address payable) none)) : Source.RExpr E Γ (ArrayTy payable) :=
  .conv (.local i) (.inl (by cases payable <;> rfl))

theorem eval_copy {E : Source.Env} {Γ : Source.RCtx}
    (payable : Bool) (G : Source.Glob E) (F : Source.Fr) (n : Nat) (y : Source.EMState E Γ)
    (i : Source.Idx Γ (.array .calldata (.address payable) none)) (off len : Nat)
    (localRef : y.1.get i=.cdRef rfl off len) :
    (Source.evalE G F (n+2) (copyExpr payable i)).run y=
      (Source.cdToMem F (ArrayTy payable) off len).run y := by
  rw [copyExpr,Source.evalE,Source.Hoare.run_bind]
  have local_run : (Source.evalE G F (n+1) (.local i)).run y=
      (.ok (.val (.cdRef rfl off len)),y) := by
    rw [Source.evalE,Source.Hoare.run_bind]
    rw [show (Source.EM.locals (E := E) (Γ := Γ)).run y=(.ok y.1,y) from rfl]
    change (Except.ok (Source.RVal.val (y.1.get i)),y)=_
    rw [localRef]
  rw [local_run]
  change (Source.convRV F (n+1) (ArrayTy payable)
    (.val (.cdRef rfl off len) : Source.RVal E.layout (.array .calldata (.address payable) none))).run y=_
  unfold Source.convRV
  rw [dif_neg (show (Source.STy.array .calldata (.address payable) none)≠ArrayTy payable from by intro h;cases h)]
  rfl

#print axioms payload_frame
#print axioms guarded_frame_run
#print axioms eval_copy
#print axioms decode_clean
#print axioms decode_dirty
#print axioms copy_run
#print axioms copy_dirty
#print axioms copy_error
#print axioms copy_observations
#print axioms guarded_run
#print axioms copy_zero
end Solidity.Backend.CalldataPackets.RawAddress
