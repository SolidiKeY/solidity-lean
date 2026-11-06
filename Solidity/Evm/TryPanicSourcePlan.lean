import Solidity.Evm.TryPanicCarrier

/-!
Proof-side interpretation of the fixed store/store/revert plan. This does not
extend Prog/Stmt, source admission, a native evaluator or compiled-EVM semantics.
Operands and the terminal length stay intrinsic and generic. Only a completed
finite-memory branch is described; missing range evidence is not a revert/OOG.
-/
namespace Solidity.Evm.TryPanicSourcePlan
open TryByteImage TryPanicProducer
variable {C : Contract} {Γ : Ctx}

structure WordStore (C : Contract) (Γ : Ctx) where
  offset : U256
  value : Val C Γ .uint

structure Terminal (C : Contract) (Γ : Ctx) where
  offset : U256
  length : Val C Γ .uint

structure ThreeOp (C : Contract) (Γ : Ctx) where
  first : WordStore C Γ
  second : WordStore C Γ
  terminal : Terminal C Γ

/-- Original operand order; parameter2 remains a local, never a size36 premise. -/
def originalOps : ThreeOp C Input :=
  { first := ⟨zero,.simple (.lit selectorWord.val selectorWord.property)⟩
    second := ⟨⟨4,rfl⟩,.simple (.lit codeWord.val codeWord.property)⟩
    terminal := ⟨zero,.simple (.local sizeSlot)⟩ }

/-- The two existing writes, with their natural bounds explicitly retained. -/
def writePair (ops : ThreeOp C Γ) (μ : FrameMem C Γ)
    (h1 : ops.first.offset.val.toNat+32 ≤ μ.capacity)
    (h2 : ops.second.offset.val.toNat+32 ≤ μ.capacity) (v1 v2 : U256) : FrameMem C Γ :=
  store32 (store32 μ ⟨ops.first.offset,h1⟩ v1) ⟨ops.second.offset,h2⟩ v2

/-- Constructor conclusions compute the actual image and snapshot. No desired
bytes, halt equation, source hash, initialized-state or success field is accepted.
Evaluations occur at the actual successive store states. This Prop is proof-side;
there is no new hot indexed fold or execution/admission consumer. -/
inductive BodyCompletedAt (ops : ThreeOp C Γ) (μ : FrameMem C Γ) :
    FrameMem C Γ → List UInt8 → Prop where
  | stores (v1 v2 n : U256)
      (h1 : ops.first.offset.val.toNat+32 ≤ μ.capacity)
      (h2 : ops.second.offset.val.toNat+32 ≤ μ.capacity)
      (eval1 : ops.first.value.evalT μ.st = .ok v1)
      (eval2 : ops.second.value.evalT (store32 μ ⟨ops.first.offset,h1⟩ v1).st = .ok v2)
      (evalN : ops.terminal.length.evalT (writePair ops μ h1 h2 v1 v2).st = .ok n)
      (span : ByteSpan μ.capacity) (offset : span.offset = ops.terminal.offset)
      (length : span.length = n) :
      BodyCompletedAt ops μ (writePair ops μ h1 h2 v1 v2)
        (snapshot (writePair ops μ h1 h2 v1 v2) span)

/-- Every completed finite branch preserves the whole logical state and frame,
not just its heap projection. -/
theorem completed_frame {ops : ThreeOp C Γ} {μ final : FrameMem C Γ} {bytes : List UInt8}
    (d : BodyCompletedAt ops μ final bytes) :
    final.st = μ.st ∧ final.key = μ.key ∧ final.capacity = μ.capacity := by
  cases d
  exact ⟨rfl,rfl,rfl⟩

def firstFits (μ : FrameMem C Input) (space : 36 ≤ μ.capacity) :
    (originalOps (C := C)).first.offset.val.toNat+32 ≤ μ.capacity := by
  change 0+32 ≤ μ.capacity
  omega

def secondFits (μ : FrameMem C Input) (space : 36 ≤ μ.capacity) :
    (originalOps (C := C)).second.offset.val.toNat+32 ≤ μ.capacity := by
  change 4+32 ≤ μ.capacity
  omega

def originalImage (μ : FrameMem C Input) (space : 36 ≤ μ.capacity) : FrameMem C Input :=
  writePair originalOps μ (firstFits μ space) (secondFits μ space) selectorWord codeWord

def actualRange (μ : FrameMem C Input)
    (fits : (TEnv.get sizeSlot μ.st.env).val.toNat ≤ μ.capacity) : ByteSpan μ.capacity :=
  ⟨zero,TEnv.get sizeSlot μ.st.env,.inr (by change 0+_ ≤ _; omega)⟩

/-- Generic n: no function-wide size36 restriction or fallback outcome. -/
theorem original_completed (μ : FrameMem C Input) (space : 36 ≤ μ.capacity)
    (fits : (TEnv.get sizeSlot μ.st.env).val.toNat ≤ μ.capacity) :
    BodyCompletedAt originalOps μ (originalImage μ space)
      (snapshot (originalImage μ space) (actualRange μ fits)) := by
  exact .stores selectorWord codeWord (TEnv.get sizeSlot μ.st.env)
    (firstFits μ space) (secondFits μ space) rfl rfl rfl (actualRange μ fits) rfl rfl

/-- The terminal length is derived from the real local evaluation. It is not a
separate observed/reply length or a certificate for a desired halt. -/
theorem original_completed_length {μ final : FrameMem C Input} {bytes : List UInt8}
    (d : BodyCompletedAt originalOps μ final bytes) :
    bytes.length = (TEnv.get sizeSlot μ.st.env).val.toNat := by
  cases d with
  | stores v1 v2 n h1 h2 e1 e2 en span off len =>
    have localEval : (Except.ok (TEnv.get sizeSlot μ.st.env) : TRes U256) = .ok n := en
    have same : TEnv.get sizeSlot μ.st.env = n := Except.ok.inj localEval
    rw [snapshot_length,len,← same]

end Solidity.Evm.TryPanicSourcePlan
