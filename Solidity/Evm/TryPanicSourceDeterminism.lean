import Solidity.Evm.TryPanicSourceFrame

/-! Inversion for the existing H8 finite completed branch. No target execution,
source admission, vendor law or resource outcome is added. -/
namespace Solidity.Evm.TryPanicSourceDeterminism
open TryByteImage TryPanicProducer TryPanicSourcePlan TryPanicSourceFrame
variable {C : Contract}

/-- Every completed derivation determines its bounds and actual final image.
No independently selected image, reply or successful execution is a premise. -/
theorem completed_exact {μ final : FrameMem C Input} {bytes : List UInt8}
    (d : BodyCompletedAt originalOps μ final bytes) :
    ∃ (space : 36 ≤ μ.capacity)
      (fits : (TEnv.get sizeSlot μ.st.env).val.toNat ≤ μ.capacity),
      final = originalImage μ space ∧
      bytes = snapshot (originalImage μ space) (actualRange μ fits) := by
  cases d with
  | stores v1 v2 n h1 h2 e1 e2 en span off len =>
    have first : (Except.ok selectorWord : TRes U256) = .ok v1 := e1
    have second : (Except.ok codeWord : TRes U256) = .ok v2 := e2
    have localEval : (Except.ok (TEnv.get sizeSlot μ.st.env) : TRes U256) = .ok n := en
    have firstEq : selectorWord = v1 := Except.ok.inj first
    have secondEq : codeWord = v2 := Except.ok.inj second
    have localEq : TEnv.get sizeSlot μ.st.env = n := Except.ok.inj localEval
    cases firstEq
    cases secondEq
    cases localEq
    have space : 36 ≤ μ.capacity := h2
    have fits : (TEnv.get sizeSlot μ.st.env).val.toNat ≤ μ.capacity := by
      rcases span.fits with empty | range
      · rw [len] at empty
        omega
      · rw [off,len] at range
        change 0 + (TEnv.get sizeSlot μ.st.env).val.toNat ≤ μ.capacity at range
        omega
    refine ⟨space,fits,rfl,?_⟩
    cases span with
    | mk a n range =>
      dsimp only at off len
      subst a
      subst n
      rfl

/-- This characterizes only completion in the pure finite model. Negation is
not a classifier for EVM OOG, fuel exhaustion, revert or host interruption. -/
theorem completion_iff (μ final : FrameMem C Input) (bytes : List UInt8) :
    BodyCompletedAt originalOps μ final bytes ↔
      ∃ (space : 36 ≤ μ.capacity)
        (fits : (TEnv.get sizeSlot μ.st.env).val.toNat ≤ μ.capacity),
        final = originalImage μ space ∧
        bytes = snapshot (originalImage μ space) (actualRange μ fits) := by
  constructor
  · exact completed_exact
  · rintro ⟨space,fits,rfl,rfl⟩
    exact original_completed μ space fits

/-- Any two completed derivations of the SAME input agree on the whole image
and raw bytes, including overlapping stores and arbitrary retained frame data. -/
theorem completion_unique {μ a b : FrameMem C Input} {x y : List UInt8}
    (left : BodyCompletedAt originalOps μ a x)
    (right : BodyCompletedAt originalOps μ b y) : a = b ∧ x = y := by
  rcases completed_exact left with ⟨spaceL,fitsL,ha,hx⟩
  rcases completed_exact right with ⟨spaceR,fitsR,hb,hy⟩
  exact ⟨ha.trans hb.symm,hx.trans hy.symm⟩

/-- Range/capacity refusal is absence of this finite completed derivation;
it supplies no alternate operational verdict. -/
theorem capacity_refusal (μ : FrameMem C Input) (small : μ.capacity < 36) :
    ¬ ∃ final bytes, BodyCompletedAt originalOps μ final bytes := by
  rintro ⟨final,bytes,d⟩
  rcases completed_exact d with ⟨space,_,_,_⟩
  omega

theorem range_refusal (μ : FrameMem C Input)
    (large : μ.capacity < (TEnv.get sizeSlot μ.st.env).val.toNat) :
    ¬ ∃ final bytes, BodyCompletedAt originalOps μ final bytes := by
  rintro ⟨final,bytes,d⟩
  rcases completed_exact d with ⟨_,fits,_,_⟩
  omega

/-- Generic uint range supplies the capture bound for every actual completed
model derivation, not just for a separately constructed dataK expression. -/
theorem completed_bytes_bound {μ final : FrameMem C Input} {bytes : List UInt8}
    (d : BodyCompletedAt originalOps μ final bytes) : bytes.length < 2^256 := by
  rw [original_completed_length d]
  have intrinsic : PrimTy.uint.inRange (TEnv.get sizeSlot μ.st.env).val = true :=
    (TEnv.get sizeSlot μ.st.env).property
  simp only [PrimTy.inRange,decide_eq_true_eq] at intrinsic
  omega

/-- Consume initialization and ANY completed derivation at the SAME frame;
no independent output/image/return-buffer equality is requested. -/
theorem initialized_completed_exact (σ : State C Input) (key : FrameKey) (K : Nat)
    (aligned : ∃ k, K = k*32) (large : 96 ≤ K) {μ final : FrameMem C Input}
    {bytes : List UInt8} (init : FiniteEntry σ key K aligned large μ)
    (d : BodyCompletedAt originalOps μ final bytes) :
    ∃ fits : (TEnv.get sizeSlot σ.env).val.toNat ≤ K,
      final = imageK σ key K aligned large ∧
      bytes = dataK σ key K aligned large fits := by
  cases init
  rcases completed_exact d with ⟨space,fits,hfinal,hbytes⟩
  exact ⟨fits,hfinal,hbytes⟩

/-- A local36 fact reduces every completed branch of this initialized model.
It is not global equality of the generic body with the constant carrier. -/
theorem initialized36_exact (σ : State C Input) (key : FrameKey) (K : Nat)
    (aligned : ∃ k, K = k*32) (large : 96 ≤ K) {μ final : FrameMem C Input}
    {bytes : List UInt8} (init : FiniteEntry σ key K aligned large μ)
    (size : TEnv.get sizeSlot σ.env = size36)
    (d : BodyCompletedAt originalOps μ final bytes) :
    final = imageK σ key K aligned large ∧ bytes = computed36 := by
  rcases initialized_completed_exact σ key K aligned large init d with
    ⟨fits,hfinal,hbytes⟩
  rw [data36_computed σ key K aligned large size fits] at hbytes
  exact ⟨hfinal,hbytes⟩

/-- The capture uses bytes from THAT completed derivation and its derived bound.
Only its actual halt is compared; no normal Out/context equality is inferred. -/
theorem initialized36_materialized (σ : State C Input) (key : FrameKey) (K : Nat)
    (aligned : ∃ k, K = k*32) (large : 96 ≤ K) {μ final : FrameMem C Input}
    {bytes : List UInt8} (init : FiniteEntry σ key K aligned large μ)
    (size : TEnv.get sizeSlot σ.env = size36)
    (d : BodyCompletedAt originalOps μ final bytes) :
    bytesHalt bytes (completed_bytes_bound d) μ.st = .error (THalt.ofData computed36) := by
  have hbytes : bytes = computed36 :=
    (initialized36_exact σ key K aligned large init size d).2
  calc
    bytesHalt bytes (completed_bytes_bound d) μ.st = .error (THalt.ofData bytes) :=
      bytesHalt_exact _ _ _
    _ = .error (THalt.ofData computed36) := by rw [hbytes]

/-- Nonvacuous mechanical client: actual Args evaluation constructs the entry,
then every completed derivation there agrees with the proved finite result.
Original source-call/deployment/resource association is still separate. -/
theorem evaluated_literal_unique {Γ : Ctx} (σ : State C Γ) (key : FrameKey) (K : Nat)
    (aligned : ∃ k, K = k*32) (large : 96 ≤ K) :
    ∃ values : TEnv C σ.H Input,
      Args.evalT σ TryPanicCarrier.args36 = .ok values ∧
      ∃ final : FrameMem C Input,
        BodyCompletedAt originalOps (entryK (σ.withEnv values) key K aligned large)
          final computed36 ∧ final.st = σ.withEnv values ∧
          final.key = key ∧ final.capacity = K ∧
        ∀ other bytes, BodyCompletedAt originalOps
          (entryK (σ.withEnv values) key K aligned large) other bytes →
          other = final ∧ bytes = computed36 := by
  rcases evaluated_literal36 σ key K aligned large with
    ⟨values,eval,final,d,frame,keyEq,capacity⟩
  refine ⟨values,eval,final,d,frame,keyEq,capacity,?_⟩
  intro other bytes actual
  exact completion_unique actual d

end Solidity.Evm.TryPanicSourceDeterminism
