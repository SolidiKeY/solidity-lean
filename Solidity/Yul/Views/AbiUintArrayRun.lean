import Solidity.Yul.Views.AbiUintArrayData

namespace Solidity.Yul.Views

/-- Actual ABI dynamic uint256 array producer. All guards are the owner's
existing byte/length checks, in their original order. No new alignment/cap. -/
theorem abiUintArray_run {E Γ} (s : Source.EMState E Γ) (input : Roadmap.Bytes) (head : Nat)
    (header : abiArrayOffset input head+32≤input.length)
    (small : abiArrayLength input head<2^64)
    (payload : abiArrayOffset input head+32+32*abiArrayLength input head≤input.length) :
    (Source.decodeArg input head (.array .memory (.int Source.IntTy.u256) none)).run s=
      (.ok (Source.Val.memRef rfl s.2.heap.next),
        objectAllocatedState s (abiUintArrayData E.layout (abiArrayPayload input head) (abiArrayLength input head))) := by
  dsimp only [abiArrayOffset,abiArrayLength] at *
  have first : ¬input.length<Source.wordAt input head+32 := Nat.not_lt.mpr header
  have second : ¬2^64≤Source.wordAt (input.drop (Source.wordAt input head)) 0 := Nat.not_le.mpr small
  simp only [Source.decodeArg,Source.STy.isValueTy,ite_true,if_neg first,if_neg second,if_pos payload]
  change (do
    let xs ← ((List.range (abiArrayLength input head)).mapM (fun j =>
      (Source.EM.lift (Source.decodeWord E.layout (Source.wordAt (abiArrayPayload input head) j) (.int Source.IntTy.u256)) :
        Source.EM E Γ (Source.Val E.layout (.int Source.IntTy.u256)))))
    Source.allocRef (Source.Data.array (l := .memory) (n := none) xs.length (fun _ h => nomatch h)
      (fun i => Source.Data.val (xs.get i)))).run s= _
  rw [abiUintValues_mapM]
  change (Source.allocRef (abiUintArrayData E.layout (abiArrayPayload input head) (abiArrayLength input head))).run s= _
  exact objectAllocRef_run s _ rfl

/-- The actual owner MemOK is preserved for EVERY original heap typing; no
result-state safety law is a caller premise. Scalars need no child heap. -/
theorem abiUintArray_alloc_MemOK {E Γ} (H : Source.HeapTy) (s : Source.EMState E Γ)
    (input : Roadmap.Bytes) (head : Nat) (ok : Source.MemOK E H s) :
    Source.MemOK E H (objectAllocatedState s
      (abiUintArrayData E.layout (abiArrayPayload input head) (abiArrayLength input head))) :=
  (objectAllocRef_MemOK H s (abiUintArrayData E.layout (abiArrayPayload input head) (abiArrayLength input head))
    rfl True.intro (abiUintArrayData_inner (E := E) _ _)
    (abiUintArrayData_valid E s.2.heap.ty _ _) ok).1

/-- Short length header reverts before inspecting the length or allocating. -/
theorem abiUintArray_missing_header {E Γ} (s : Source.EMState E Γ) (input : Roadmap.Bytes) (head : Nat)
    (missing : input.length<abiArrayOffset input head+32) :
    (Source.decodeArg input head (.array .memory (.int Source.IntTy.u256) none)).run s=(.error (.revert []),s) := by
  dsimp only [abiArrayOffset,abiArrayLength] at *
  simp only [Source.decodeArg,Source.STy.isValueTy,ite_true,if_pos missing]
  rfl

/-- Owner allocation Panic0x41 takes precedence over payload bounds. -/
theorem abiUintArray_oversized {E Γ} (s : Source.EMState E Γ) (input : Roadmap.Bytes) (head : Nat)
    (header : abiArrayOffset input head+32≤input.length) (large : 2^64≤abiArrayLength input head) :
    (Source.decodeArg input head (.array .memory (.int Source.IntTy.u256) none)).run s=
      (.error (.revert (Source.panicData .alloc)),s) := by
  dsimp only [abiArrayOffset,abiArrayLength] at *
  have first : ¬input.length<Source.wordAt input head+32 := Nat.not_lt.mpr header
  simp only [Source.decodeArg,Source.STy.isValueTy,ite_true,if_neg first,if_pos large]
  rfl

/-- Complete payload failure is also before array allocation. -/
theorem abiUintArray_short_payload {E Γ} (s : Source.EMState E Γ) (input : Roadmap.Bytes) (head : Nat)
    (header : abiArrayOffset input head+32≤input.length) (small : abiArrayLength input head<2^64)
    (short : input.length<abiArrayOffset input head+32+32*abiArrayLength input head) :
    (Source.decodeArg input head (.array .memory (.int Source.IntTy.u256) none)).run s=(.error (.revert []),s) := by
  dsimp only [abiArrayOffset,abiArrayLength] at *
  have first : ¬input.length<Source.wordAt input head+32 := Nat.not_lt.mpr header
  have second : ¬2^64≤Source.wordAt (input.drop (Source.wordAt input head)) 0 := Nat.not_le.mpr small
  have third : ¬Source.wordAt input head+32+32*Source.wordAt (input.drop (Source.wordAt input head)) 0≤input.length := Nat.not_le.mpr short
  simp only [Source.decodeArg,Source.STy.isValueTy,ite_true,if_neg first,if_neg second,if_neg third]
  rfl

/-- Exact reuse of the already constructed typed physical allocation API;
this is an actual source run equality, not a supplied adequacy interface. -/
theorem abiUintArray_eval_alloc {E Γ} (s : Source.EMState E Γ) (input : Roadmap.Bytes) (head : Nat)
    (header : abiArrayOffset input head+32≤input.length)
    (small : abiArrayLength input head<2^64)
    (payload : abiArrayOffset input head+32+32*abiArrayLength input head≤input.length) :
    (Source.decodeArg input head (.array .memory (.int Source.IntTy.u256) none)).run s=
      (Source.allocRef (abiUintArrayData E.layout (abiArrayPayload input head) (abiArrayLength input head))).run s := by
  rw [abiUintArray_run s input head header small payload,objectAllocRef_run _ _ rfl]

end Solidity.Yul.Views
