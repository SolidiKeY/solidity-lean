import Solidity.Backend.CalldataPackets.RawBytesN.Interface

/-! Exact Source calldata-to-memory execution, with validation before allocation. -/
namespace Solidity.Backend.CalldataPackets.RawBytesN
open Solidity.Backend.MemoryOps

theorem decode_word (D : Source.Layout) (n : Nat) (h : 1 ≤ n ∧ n ≤ 32) (w : Nat) :
    Source.decodeWord D w (.fixedBytes n h) =
      if (Source.natBytes 32 w).drop n = List.replicate (32-n) 0 then
        .ok (Source.mkBytes (n := n) (h := h) (Source.natBytes 32 w))
      else .error (.revert []) := by rfl

def certificate (D : Source.Layout) (n : Nat) (h : 1 ≤ n ∧ n ≤ 32) :
    DecodeCertificate D n h := ⟨decode_word D n h⟩

theorem dirty_revert (D : Source.Layout) (n : Nat) (h : 1 ≤ n ∧ n ≤ 32) (w : Nat)
    (dirty : (Source.natBytes 32 w).drop n ≠ List.replicate (32-n) 0) :
    Source.decodeWord D w (.fixedBytes n h)=.error (.revert []) := by
  rw [decode_word,if_neg dirty]

/-- Total outcome: raw-byte decoding either reverts without allocation or
allocates precisely the actual decoded values. No successful run is assumed. -/
theorem copy_run {E : Source.Env} {Γ : Source.RCtx} (n : Nat) (h : 1 ≤ n ∧ n ≤ 32)
    (F : Source.Fr) (off len : Nat) (y : Source.EMState E Γ) :
    (Source.cdToMem F (ArrayTy n h) off len).run y =
      match decoded E.layout n h F off len with
      | .error e => (.error e,y)
      | .ok vs => (.ok (.val (.memRef rfl y.2.heap.next)),
          (y.1,{y.2 with heap := (y.2.heap.alloc ⟨ArrayTy n h,memory vs⟩).1})) := by
  simp only [Source.cdToMem,ArrayTy,Source.STy.loc?,Option.some.injEq,reduceCtorEq,dite_false]
  rw [Source.Hoare.run_bind,source_mapM_lift_run]
  unfold decoded
  cases (List.range len).mapM (fun j =>
    Source.decodeWord E.layout (Source.cdWordAt F (off+32*j)) (.fixedBytes n h)) <;> rfl

/-- Allocation preserves every address other than heap.next and all non-heap state; on any
validation failure the entire state is unchanged. -/
theorem copy_observations {E : Source.Env} {Γ : Source.RCtx}
    (n : Nat) (h : 1 ≤ n ∧ n ≤ 32) (F : Source.Fr) (off len : Nat)
    (y : Source.EMState E Γ) :
    match decoded E.layout n h F off len with
    | .error e => (Source.cdToMem F (ArrayTy n h) off len).run y=(.error e,y)
    | .ok vs =>
      let z := (Source.cdToMem F (ArrayTy n h) off len).run y |>.2
      z.2.heap.get y.2.heap.next=some ⟨ArrayTy n h,memory vs⟩ ∧
      z.2.heap.next=y.2.heap.next+1 ∧
      (∀ a,a≠y.2.heap.next → z.2.heap.get a=y.2.heap.get a) ∧
      z.1=y.1 ∧ {z.2 with heap := y.2.heap}=y.2 := by
  cases hd : decoded E.layout n h F off len with
  | error e => rw [copy_run,hd]
  | ok vs =>
    rw [copy_run,hd]
    dsimp only
    refine ⟨Source.Heap.alloc_get _ _,rfl,?_,rfl,?_⟩
    · intro a different
      exact Source.Heap.alloc_other _ _ different
    · cases y.2
      rfl

/-- Dynamic-entry guard is evaluated before decoding or allocation. -/
theorem guarded_run {E : Source.Env} {Γ : Source.RCtx} (n : Nat) (h : 1 ≤ n ∧ n ≤ 32)
    (data : List UInt8) (i : Nat) (F : Source.Fr) (y : Source.EMState E Γ) :
    ((Source.EM.lift (Source.cdTail data i 32)) >>= fun p =>
      Source.cdToMem F (ArrayTy n h) p.1 p.2).run y =
    match Source.cdTail data i 32 with
    | .error e => (.error e,y)
    | .ok (off,len) =>
      match decoded E.layout n h F off len with
      | .error e => (.error e,y)
      | .ok vs => (.ok (.val (.memRef rfl y.2.heap.next)),
          (y.1,{y.2 with heap := (y.2.heap.alloc ⟨ArrayTy n h,memory vs⟩).1})) := by
  rw [Source.Hoare.run_bind]
  cases hd : Source.cdTail data i 32 with
  | error e => simp only [Source.EM.lift];rfl
  | ok p => simp only [Source.EM.lift];exact copy_run n h F p.1 p.2 y

/-- Decode the argument bytes themselves, independently of selector storage. -/
def dataDecoded (D : Source.Layout) (n : Nat) (h : 1 ≤ n ∧ n ≤ 32)
    (data : List UInt8) (off len : Nat) : Source.R (List (Source.Val D (.fixedBytes n h))) :=
  (List.range len).mapM fun j => Source.decodeWord D
    (Source.beValue (Source.fitBytes 32 (data.drop (off+32*j)))) (.fixedBytes n h)

theorem decoded_frame (D : Source.Layout) (n : Nat) (h : 1 ≤ n ∧ n ≤ 32)
    (F : Source.Fr) (selectorBytes data : List UInt8) (four : selectorBytes.length=4)
    (binding : F.cd=selectorBytes++data) (off len : Nat) :
    decoded D n h F (4+off) len=dataDecoded D n h data off len := by
  have reader : (fun j => Source.cdWordAt F (4+off+32*j)) =
      (fun j => Source.beValue (Source.fitBytes 32 (data.drop (off+32*j)))) := by
    funext j
    unfold Source.cdWordAt
    rw [binding,Nat.add_assoc,←four,List.drop_length_add_append]
  have each : (fun j => Source.decodeWord D (Source.cdWordAt F (4+off+32*j)) (.fixedBytes n h)) =
      (fun j => Source.decodeWord D
        (Source.beValue (Source.fitBytes 32 (data.drop (off+32*j)))) (.fixedBytes n h)) := by
    funext j
    exact congrArg (fun w => Source.decodeWord D w (.fixedBytes n h)) (congrFun reader j)
  exact congrArg (fun f => (List.range len).mapM f) each

/-- All three entry refusals and per-element low-byte validation, bound to
exactly the same frame bytes; every failure retains the complete input state. -/
theorem guarded_frame_run {E : Source.Env} {Γ : Source.RCtx}
    (n : Nat) (h : 1 ≤ n ∧ n ≤ 32)
    (F : Source.Fr) (selectorBytes data : List UInt8) (four : selectorBytes.length=4)
    (binding : F.cd=selectorBytes++data) (i : Nat) (y : Source.EMState E Γ) :
    ((Source.EM.lift (Source.cdTail data i 32)) >>= fun p =>
      Source.cdToMem F (ArrayTy n h) p.1 p.2).run y=
      let off := Source.wordAt data i
      let len := Source.wordAt (data.drop off) 0
      if data.length<off+32 then (.error (.revert []),y)
      else if 2^64≤len then (.error (.revert []),y)
      else if off+32+32*len≤data.length then
        match dataDecoded E.layout n h data (off+32) len with
        | .error e => (.error e,y)
        | .ok vs => (.ok (.val (.memRef rfl y.2.heap.next)),
            (y.1,{y.2 with heap := (y.2.heap.alloc ⟨ArrayTy n h,memory vs⟩).1}))
      else (.error (.revert []),y) := by
  rw [guarded_run]
  dsimp only
  by_cases head : data.length<Source.wordAt data i+32
  · simp only [Source.cdTail,if_pos head]
  · by_cases large : 2^64≤Source.wordAt (data.drop (Source.wordAt data i)) 0
    · simp only [Source.cdTail,if_neg head,if_pos large]
    · by_cases span : Source.wordAt data i+32+32*Source.wordAt (data.drop (Source.wordAt data i)) 0≤data.length
      · simp only [Source.cdTail,if_neg head,if_neg large,if_pos span,pure,Except.pure]
        rw [Nat.add_assoc,decoded_frame E.layout n h F selectorBytes data four binding]
        rfl
      · simp only [Source.cdTail,if_neg head,if_neg large,if_neg span]

#print axioms decode_word
#print axioms copy_run
#print axioms copy_observations
#print axioms guarded_run
#print axioms guarded_frame_run
end Solidity.Backend.CalldataPackets.RawBytesN
