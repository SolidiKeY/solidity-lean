import Solidity.Evm.TryPanicSourceBodyImage

/-! Existing Prog execution of the H8 normalized generic body. Only the two
single-operation glue goals in TERRA-TODO remain parameters here; no desired
reply, Xi result, source frame or whole-body execution is assumed. -/
namespace Solidity.Evm.TryPanicSourceExecution
open TryByteImage TryPanicProducer TryPanicCarrier TryPanicSourceBody TryPanicSourceBodyImage
variable {C : Contract}

/-- Lift the pending single-step sequencing glue through the existing cons. -/
theorem cons_put (glue : PutThen (C := C)) (σ : State C Input)
    (o : MObj σ.H bytesR) (i : Fin 96) (b : UInt8) (k : Prog C Buffer Buffer)
    (length : o.1.length = (TEnv.get sizeSlot σ.env).val.toNat) :
    (Prog.cons (put i b) k).runR (σ.allocPush o) =
      k.runR (σ.allocPush (clipped o i b))  := by
  simpa only [clipped] using (glue σ o i b k.runR length)

/-- Existing raw-memory read of the SAME concrete allocated byte object. -/
theorem raw_bytes (σ : State C Input) (bs : List UInt8) (bound : bs.length < 2^256) :
    rawTail.runR (σ.allocPush (bytesObj σ.H bs bound)) = .error (THalt.ofData bs) := by
  change TRun.seq (TRun.revertData [.mem .raw .here]) TRun.nil
    (σ.allocPush (bytesObj σ.H bs bound)) = _
  rw [TRun.seq, TRun.revertData_mem (σ.allocPush (bytesObj σ.H bs bound)) .raw .here
      (σ.alloc (bytesObj σ.H bs bound)).2 rfl, captureBytes_read]

/-- The actual newly allocated image object is read by raw-memory revert. -/
theorem raw_image (σ : State C Input) (n : Nat) (hn : n < 2^256) :
    rawTail.runR (σ.allocPush (imageObj σ.H n hn)) =
      .error (THalt.ofData (TryPanicSourceBytes.bytesAt n)) := by
  rw [image_eq]
  exact raw_bytes σ _ _

/-- Six actual checked conditional writes, not an assumed final object. -/
theorem contents_halt (glue : PutThen (C := C)) (σ : State C Input) :
    contents.runR (σ.allocPush (zerosObj σ.H (TEnv.get sizeSlot σ.env).val.toNat (input_bound σ))) =
      .error (THalt.ofData (TryPanicSourceBytes.bytesAt (TEnv.get sizeSlot σ.env).val.toNat)) := by
  simp only [contents, cons_put glue σ, clipped_length, zeros_length]
  exact raw_image σ (TEnv.get sizeSlot σ.env).val.toNat (input_bound σ)

/-- Allocate at the SAME local parameter, compose the proved contents, and
propagate the real revert through allocation sequencing. -/
theorem allocated_halt (glue : PutThen (C := C)) (allocation : AllocateRun (C := C))
    (σ : State C Input) :
    allocated.runR σ =
      .error (THalt.ofData (TryPanicSourceBytes.bytesAt (TEnv.get sizeSlot σ.env).val.toNat)) := by
  change TRun.seq (TRun.declMem bytesR (some (.newArr (.local sizeSlot) rfl)) rfl)
    contents.runR σ = _
  simp only [TRun.seq, allocation σ, contents_halt glue σ, Except.map]

/-- No normal source Out or successful child certificate is an input. -/
theorem body_halt (glue : PutThen (C := C)) (allocation : AllocateRun (C := C))
    (σ : State C Input) :
    body.runR σ =
      .error (THalt.ofData (TryPanicSourceBytes.bytesAt (TEnv.get sizeSlot σ.env).val.toNat)) := by
  change TRun.seq (TRun.block (.push .refl) allocated.runR) TRun.nil σ = _
  simp only [TRun.seq, TRun.block, allocated_halt glue allocation σ, Except.map]

/-- Generic body realization reduces to ONLY the two named routine primitive
adapters, not to an assumed whole-body run or selected reply. -/
theorem realizes (glue : PutThen (C := C)) (allocation : AllocateRun (C := C)) :
    TryPanicSourceControl.BodyRealizes (body (C := C)) :=
  (TryPanicSourceBytes.realizes_iff body).2 (body_halt glue allocation)

/-- Original c-argument normalization and actual terminal Return94 now consume
the generic body equation. This remains proof-only source control: compiled
return, installation and same-invocation provenance are separate obligations. -/
theorem caller_return (glue : PutThen (C := C)) (allocation : AllocateRun (C := C))
    (σ : State C TryPanicSourceControl.Caller) (key : FrameKey)
    (nonzero : σ.tx.selfAddress.val ≠ 0) :
    Stmt.run σ (TryPanicSourceControl.caller body) =
      .ok ⟨σ.setLocal .here codeWord, List.prefix_refl _⟩ :=
  TryPanicSourceControl.caller_at36 body (realizes glue allocation) σ key nonzero

/-- Consume the SAME completed original ThreeOp finite plan. No final byte
identity, chosen reply or whole-body successful-run premise is added. -/
theorem completed (glue : PutThen (C := C)) (allocation : AllocateRun (C := C))
    (σ : State C Input) (key : FrameKey) (K : Nat)
    (aligned : ∃ k, K = k*32) (large : 96 ≤ K)
    (μ final : FrameMem C Input) (bytes : List UInt8)
    (entry : TryPanicSourceFrame.FiniteEntry σ key K aligned large μ)
    (run : TryPanicSourcePlan.BodyCompletedAt TryPanicSourcePlan.originalOps μ final bytes) :
    body.runR σ = .error (THalt.ofData bytes) :=
  TryPanicSourceControl.body_completed body (realizes glue allocation)
    σ key K aligned large μ final bytes entry run

/-- Actual empty argument produces bare revert, unlike carrier36. -/
theorem empty_body (glue : PutThen (C := C)) (allocation : AllocateRun (C := C))
    (σ : State C Input) : body.runR (σ.withEnv (zero, ())) = .error .revert :=
  body_halt glue allocation (σ.withEnv (zero, ()))

theorem differs_at_zero (glue : PutThen (C := C)) (allocation : AllocateRun (C := C))
    (σ : State C Input) :
    body.runR (σ.withEnv (zero, ())) ≠ carrier36.runR (σ.withEnv (zero, ())) := by
  rw [empty_body glue allocation]
  have fixed : carrier36.runR (σ.withEnv (zero, ())) =
      .error (THalt.ofData computed36) := TryPanicCarrier.carrier36_halt _
  rw [fixed]
  have raw : THalt.ofData computed36 = .revertWith computed36 := by
    rw [computed36_panic]
    rfl
  rw [raw]
  intro impossible
  cases impossible

end Solidity.Evm.TryPanicSourceExecution
