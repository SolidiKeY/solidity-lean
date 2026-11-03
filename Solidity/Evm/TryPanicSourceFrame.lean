import Solidity.Evm.TryPanicSourcePlan

/-! Conditional finite-entry interpretation. Capacity is a pure witness, not a
source domain, gas bound, source-to-Prog realization or compiled-entry theorem. -/
namespace Solidity.Evm.TryPanicSourceFrame
open TryByteImage TryPanicProducer TryPanicSourcePlan
variable {C : Contract}

def freshK (σ : State C Input) (key : FrameKey) (K : Nat)
    (aligned : ∃ k, K = k*32) : FrameMem C Input :=
  { st := σ, key := key, scalar := scalarInput, capacity := K, aligned := aligned
    data := fun _ => 0, highWaterWords := 0, resident := by omega
    zeroAbove := by intros; rfl }

def at64K (K : Nat) (large : 96 ≤ K) : WordSpan K :=
  ⟨⟨64,rfl⟩,by change 64+32 ≤ K; omega⟩

/-- The modeled prologue is explicit and separate from the source body. -/
def entryK (σ : State C Input) (key : FrameKey) (K : Nat)
    (aligned : ∃ k, K = k*32) (large : 96 ≤ K) : FrameMem C Input :=
  store32 (freshK σ key K aligned) (at64K K large) freeWord

def imageK (σ : State C Input) (key : FrameKey) (K : Nat)
    (aligned : ∃ k, K = k*32) (large : 96 ≤ K) : FrameMem C Input :=
  originalImage (entryK σ key K aligned large) (by change 36 ≤ K; omega)

/-- Conditional initialization requires the actual whole modeled frame. It
contains no outcome, gas meter, compiler success or source-body certificate. -/
def FiniteEntry (σ : State C Input) (key : FrameKey) (K : Nat)
    (aligned : ∃ k, K = k*32) (large : 96 ≤ K) (μ : FrameMem C Input) : Prop :=
  μ = entryK σ key K aligned large

theorem entry_inhabited (σ : State C Input) (key : FrameKey) (K : Nat)
    (aligned : ∃ k, K = k*32) (large : 96 ≤ K) :
    FiniteEntry σ key K aligned large (entryK σ key K aligned large) := rfl

def dataK (σ : State C Input) (key : FrameKey) (K : Nat)
    (aligned : ∃ k, K = k*32) (large : 96 ≤ K)
    (fits : (TEnv.get sizeSlot σ.env).val.toNat ≤ K) : List UInt8 :=
  snapshot (imageK σ key K aligned large)
    (actualRange (entryK σ key K aligned large) fits)

theorem completed_generic (σ : State C Input) (key : FrameKey) (K : Nat)
    (aligned : ∃ k, K = k*32) (large : 96 ≤ K)
    (fits : (TEnv.get sizeSlot σ.env).val.toNat ≤ K) :
    BodyCompletedAt originalOps (entryK σ key K aligned large)
      (imageK σ key K aligned large) (dataK σ key K aligned large fits) :=
  original_completed _ _ fits

theorem data_length (σ : State C Input) (key : FrameKey) (K : Nat)
    (aligned : ∃ k, K = k*32) (large : 96 ≤ K)
    (fits : (TEnv.get sizeSlot σ.env).val.toNat ≤ K) :
    (dataK σ key K aligned large fits).length = (TEnv.get sizeSlot σ.env).val.toNat := by
  rw [dataK,snapshot_length]
  rfl

/-- Readback is factored at an abstract length to avoid reducing large lists. -/
theorem data_get (σ : State C Input) (key : FrameKey) (K : Nat)
    (aligned : ∃ k, K = k*32) (large : 96 ≤ K)
    (fits : (TEnv.get sizeSlot σ.env).val.toNat ≤ K) (i : Nat)
    (hi : i < (dataK σ key K aligned large fits).length) :
    (dataK σ key K aligned large fits)[i] =
      (imageK σ key K aligned large).data ⟨i, by change i < K; rw [data_length] at hi; omega⟩ := by
  change (snapshot (imageK σ key K aligned large)
    (actualRange (entryK σ key K aligned large) fits))[i] = _
  rw [snapshot_get]
  simp only [actualRange,zero,Int.reduceToNat,Nat.zero_add]

theorem image_frame (σ : State C Input) (key : FrameKey) (K : Nat)
    (aligned : ∃ k, K = k*32) (large : 96 ≤ K) :
    (imageK σ key K aligned large).st = σ ∧
    (imageK σ key K aligned large).key = key ∧
    (imageK σ key K aligned large).capacity = K ∧
    (imageK σ key K aligned large).highWaterWords = 3 := by
  refine ⟨rfl,rfl,rfl,?_⟩
  change max (max (max 0 ((64+32+31)/32)) ((0+32+31)/32)) ((4+32+31)/32) = 3
  decide

/-- Generic-capacity reduction at this invocation only. No global f=carrier36. -/
theorem data36_computed (σ : State C Input) (key : FrameKey) (K : Nat)
    (aligned : ∃ k, K = k*32) (large : 96 ≤ K)
    (size : TEnv.get sizeSlot σ.env = size36)
    (fits : (TEnv.get sizeSlot σ.env).val.toNat ≤ K) :
    dataK σ key K aligned large fits = computed36 := by
  apply List.ext_getElem
  · rw [data_length,computed36_length,size]
    rfl
  · intro i hi hj
    change (snapshot (imageK σ key K aligned large)
      (actualRange (entryK σ key K aligned large) fits))[i] = computed36[i]
    rw [snapshot_get]
    simp only [computed36,List.getElem_ofFn,imageK,originalImage,writePair,originalOps,entryK,
      store32,freshK,at64K,actualRange,zero,Int.reduceToNat,Nat.reduceAdd,
      Nat.zero_add,Nat.sub_zero]

theorem data_bound (σ : State C Input) (key : FrameKey) (K : Nat)
    (aligned : ∃ k, K = k*32) (large : 96 ≤ K)
    (fits : (TEnv.get sizeSlot σ.env).val.toNat ≤ K) :
    (dataK σ key K aligned large fits).length < 2^256 := by
  rw [data_length]
  have intrinsic : PrimTy.uint.inRange (TEnv.get sizeSlot σ.env).val = true :=
    (TEnv.get sizeSlot σ.env).property
  simp only [PrimTy.inRange,decide_eq_true_eq] at intrinsic
  omega

/-- Both typed halt results are proved independently in their actual contexts.
This is neither full normal Out equality nor a source-to-TRun realization. -/
theorem materialized_and_carrier36 (σ : State C Input) (key : FrameKey) (K : Nat)
    (aligned : ∃ k, K = k*32) (large : 96 ≤ K)
    (size : TEnv.get sizeSlot σ.env = size36)
    (fits : (TEnv.get sizeSlot σ.env).val.toNat ≤ K) :
    bytesHalt (dataK σ key K aligned large fits) (data_bound σ key K aligned large fits) σ = .error (THalt.ofData computed36) ∧
    Prog.run σ TryPanicCarrier.carrier36 = .error (THalt.ofData computed36) := by
  constructor
  · calc
      bytesHalt (dataK σ key K aligned large fits) (data_bound σ key K aligned large fits) σ =
          .error (THalt.ofData (dataK σ key K aligned large fits)) := bytesHalt_exact _ _ _
      _ = .error (THalt.ofData computed36) := by rw [data36_computed σ key K aligned large size fits]
  · exact TryPanicCarrier.carrier36_halt σ

theorem initialized_word (σ : State C Input) (key : FrameKey) (K : Nat)
    (aligned : ∃ k, K = k*32) (large : 96 ≤ K) :
    (imageK σ key K aligned large).data ⟨95,by change 95 < K; omega⟩ = 128 := by
  simp only [imageK,originalImage,writePair,originalOps,entryK,store32,freshK,
    at64K,zero,Int.reduceToNat,Nat.reduceAdd]
  rfl

/-- Consume the whole finite-entry relation instead of assuming an unrelated
image or final result. The local36 equality is scoped to this invocation. -/
theorem finite_entry36 (σ : State C Input) (key : FrameKey) (K : Nat)
    (aligned : ∃ k, K = k*32) (large : 96 ≤ K) (μ : FrameMem C Input)
    (init : FiniteEntry σ key K aligned large μ)
    (size : TEnv.get sizeSlot σ.env = size36) :
    ∃ final : FrameMem C Input,
      BodyCompletedAt originalOps μ final computed36 ∧
      final.st = σ ∧ final.key = key ∧ final.capacity = K := by
  have fits : (TEnv.get sizeSlot σ.env).val.toNat ≤ K := by
    rw [size]
    change 36 ≤ K
    omega
  cases init
  refine ⟨imageK σ key K aligned large, ?_, rfl, rfl, rfl⟩
  have completed : BodyCompletedAt originalOps (entryK σ key K aligned large)
      (imageK σ key K aligned large) (dataK σ key K aligned large fits) :=
    completed_generic σ key K aligned large fits
  rw [data36_computed σ key K aligned large size fits] at completed
  exact completed

/-- Literal-valued entry without constraining the function-wide plan or the
arbitrary caller heap, storage, transaction or net. Argument evaluation is
connected separately by evaluated_literal36 below. -/
theorem literal_entry36 {Γ : Ctx} (σ : State C Γ) (key : FrameKey) (K : Nat)
    (aligned : ∃ k, K = k*32) (large : 96 ≤ K) :
    ∃ final : FrameMem C Input,
      BodyCompletedAt originalOps
        (entryK (σ.withEnv (Δ := Input) (size36, ())) key K aligned large)
        final computed36 ∧
      final.st = σ.withEnv (Δ := Input) (size36, ()) ∧
      final.key = key ∧ final.capacity = K :=
  finite_entry36 _ key K aligned large _ rfl rfl

/-- A client of the actual published literal Args evaluation, not an assumed
argument or child result. Empty return entry preserves this same environment. -/
theorem evaluated_literal36 {Γ : Ctx} (σ : State C Γ) (key : FrameKey) (K : Nat)
    (aligned : ∃ k, K = k*32) (large : 96 ≤ K) :
    ∃ values : TEnv C σ.H Input,
      Args.evalT σ TryPanicCarrier.args36 = .ok values ∧
      ∃ final : FrameMem C Input,
        BodyCompletedAt originalOps (entryK (σ.withEnv values) key K aligned large)
          final computed36 ∧ final.st = σ.withEnv values ∧
          final.key = key ∧ final.capacity = K := by
  refine ⟨(size36, ()), TryPanicCarrier.args36_eval σ, ?_⟩
  exact literal_entry36 σ key K aligned large

end Solidity.Evm.TryPanicSourceFrame
