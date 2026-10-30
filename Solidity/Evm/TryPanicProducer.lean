import Solidity.Evm.TryByteCapture

/-!
# M1: source-linked computed Panic producer, not source admission

The two retained bundle keys identify the exact original artifacts. Their
external provenance is checked separately; no hash injectivity, compiler
correctness, bytecode run or original carried-body equality is assumed here.
The word operands come from the actual original stores, never reference output.
-/
namespace Solidity.Evm.TryPanicProducer
open TryByteImage

abbrev Input : Ctx := [.val .uint]
def sizeSlot : Idx Input (.val .uint) := .here

def zero : U256 := ⟨0, rfl⟩
def size36 : U256 := ⟨36, rfl⟩
def selectorWord : U256 :=
  ⟨0x4e487b7100000000000000000000000000000000000000000000000000000000, rfl⟩
def codeWord : U256 := ⟨0x43, rfl⟩
def freeWord : U256 := ⟨128, rfl⟩

/-- Exact retained artifact identities, not runtime semantic premises. -/
structure BundleKey where
  pipeline : Pipeline
  source : String
  compilerHash : String
  inputHash : String
  outputHash : String
  creationHash : String
  runtimeHash : String
  deriving DecidableEq

def originalSource : String := "contract C {\n    function f(uint size) public pure {\n        assembly {\n            mstore(0, 0x4e487b7100000000000000000000000000000000000000000000000000000000)\n            mstore(4, 0x43)\n            revert(0, size)\n        }\n    }\n    function a() public returns (uint) {\n        try this.f(3) {\n            assert(false);\n        } catch Panic(uint) {\n            assert(false);\n        } catch {\n            assert(true);\n        }\n    }\n    function b() public returns (uint) {\n        try this.f(6) {\n            assert(false);\n        } catch Panic(uint) {\n            assert(false);\n        } catch {\n            assert(true);\n        }\n    }\n    function c() public returns (uint) {\n        try this.f(0x24) {\n            assert(false);\n        } catch Panic(uint c) {\n            assert(true);\n            return c;\n        } catch {\n            assert(false);\n        }\n    }\n    function d() public returns (uint) {\n        try this.f(0x100) {\n            assert(false);\n        } catch Panic(uint c) {\n            assert(true);\n            return c;\n        } catch {\n            assert(false);\n        }\n    }\n}\n// ====\n// EVMVersion: >=byzantium\n// ----\n// a() -> 0x00\n// b() -> 0x00\n// c() -> 0x43\n// d() -> 0x43\n"

def legacyBundle : BundleKey :=
  { pipeline := .legacy
    source := originalSource
    compilerHash := "6c74ffba0ea4cf9521e78b16052a98208770bb7677616de08ced239f4312d390"
    inputHash := "f6b4902eeb6b24de09bbff2a551920bf9af16fce22c769d58e88c0c41a205dd8"
    outputHash := "d8dd80611bbc54581b3d9e6a1471c75045b01701439f39e6080a1098ff35e03a"
    creationHash := "988857e8e73099fe3e0b04beb535cf254d303aa88db9a5bd25550126fe7fe2ad"
    runtimeHash := "e335ea9f2867baaaf40c876fa250ffd2bece75a4b833be111d97f9d2c1b799cc"
  }

def viaIRBundle : BundleKey :=
  { pipeline := .viaIR
    source := originalSource
    compilerHash := "6c74ffba0ea4cf9521e78b16052a98208770bb7677616de08ced239f4312d390"
    inputHash := "03fab305ff1a9b86b8b779aba695dd21bb53af7af66b78fd0f9e43ba23a21ac2"
    outputHash := "94f13db8438b5026fb5b6902565ef3759f807b769a84d9bbadb5a332f12f904f"
    creationHash := "0a86ca6323640d3728309fe5b57961ef2c15c634714fd2959d6853855ca5d470"
    runtimeHash := "faf0d96218acbf1285125e35959e2ab4babebd7f6e64446c25445aa203c90d52"
  }

/-- Exact declaration/parameter/call-site identities from both retained ASTs.
This is a provenance key, not the missing P5b carried-body construction theorem. -/
structure SourceLink where
  bundle : BundleKey
  callee : Nat
  parameter : Nat
  caller : Nat
  sourceUnit : String
  deriving DecidableEq

def link (p : Pipeline) : SourceLink :=
  { bundle := if p = .legacy then legacyBundle else viaIRBundle
    callee := 7, parameter := 2, caller := 105, sourceUnit := "original.sol" }

/-- The key is constructed from the actual logical transaction frame. -/
def frameKey (p : Pipeline) (invocation depth : Nat) (σ : State C Input) : FrameKey :=
  ⟨invocation, depth, p, 7, σ.tx.selfAddress, σ.tx.msgSender, σ.tx.msgValue⟩

/-- Scalar-only inputs still permit arbitrary retained caller heap objects. -/
theorem scalarInput : ScalarFrame Input := by
  intro R i
  cases i with
  | there i => cases i

/-- Fresh external-frame image, with no physical address assigned to old heap
objects. Capacity96 is a witness for this milestone, not a source-domain bound. -/
def fresh (σ : State C Input) (key : FrameKey) : FrameMem C Input :=
  { st := σ, key := key, scalar := scalarInput
    capacity := 96, aligned := ⟨3, rfl⟩, data := fun _ => 0
    highWaterWords := 0, resident := by decide, zeroAbove := by intros; rfl }

def at64 : WordSpan 96 := ⟨⟨64, rfl⟩, by decide⟩
def at0 : WordSpan 96 := ⟨zero, by decide⟩
def at4 : WordSpan 96 := ⟨⟨4, rfl⟩, by decide⟩

/-- Actual retained prologue operand mstore(64,128), independently of typed H. -/
def entry (σ : State C Input) (key : FrameKey) : FrameMem C Input :=
  store32 (fresh σ key) at64 freeWord

/-- The original two ordered stores, including the overlapping interval4..31. -/
def image (σ : State C Input) (key : FrameKey) : FrameMem C Input :=
  store32 (store32 (entry σ key) at0 selectorWord) at4 codeWord

/-- Actual typed size operand; an entry certificate checks it is the M1 call36. -/
def sizeSpan (σ : State C Input) (hsize : TEnv.get sizeSlot σ.env = size36) : ByteSpan 96 :=
  ⟨zero, TEnv.get sizeSlot σ.env, .inr (by rw [hsize]; decide)⟩

def produced (σ : State C Input) (key : FrameKey)
    (hsize : TEnv.get sizeSlot σ.env = size36) : List UInt8 :=
  snapshot (image σ key) (sizeSpan σ hsize)

/-- Operation-derived canonical expression; not a reference-observation vector. -/
def computed36 : List UInt8 := List.ofFn fun i : Fin 36 =>
  if 4 ≤ i.val ∧ i.val < 36 then wordByte codeWord (i.val - 4) else
  if 0 ≤ i.val ∧ i.val < 32 then wordByte selectorWord i.val else
  if 64 ≤ i.val ∧ i.val < 96 then wordByte freeWord (i.val - 64) else 0

/-- An arbitrary actual logical input satisfying size36 produces these bytes. -/
theorem produced_computed (σ : State C Input) (key : FrameKey)
    (hsize : TEnv.get sizeSlot σ.env = size36) : produced σ key hsize = computed36 := by
  apply List.ext_getElem
  · change (snapshot (image σ key) (sizeSpan σ hsize)).length = computed36.length
    rw [snapshot_length]
    change (TEnv.get sizeSlot σ.env).val.toNat = 36
    rw [hsize]
    rfl
  · intro i hi hj
    change (snapshot (image σ key) (sizeSpan σ hsize))[i] = computed36[i]
    rw [snapshot_get]
    simp only [computed36, List.getElem_ofFn, image, entry, store32, fresh,
      sizeSpan, at0, at4, at64, zero, Int.reduceToNat, Nat.reduceAdd,
      Nat.zero_add, Nat.sub_zero]


/-- Kernel computation connects stores to the ordinary Panic layout, without
using an EVM observation or assuming a desired halt equation. -/
theorem computed36_panic : computed36 = Semantics.encodePanic 67 := by decide +kernel

/-- The concrete producer has exactly36 bytes. -/
theorem computed36_length : computed36.length = 36 := List.length_ofFn

/-- All logical state components and frame identity survive the raw stores. -/
theorem image_frame (σ : State C Input) (key : FrameKey) :
    (image σ key).st = σ ∧ (image σ key).key = key := ⟨rfl, rfl⟩

private theorem store_water (μ : FrameMem C Γ) (a : WordSpan μ.capacity) (w : U256) :
    (store32 μ a w).highWaterWords =
      max μ.highWaterWords ((a.offset.val.toNat + 32 + 31) / 32) := rfl

/-- The prologue accesses exactly three words, independently of old typed H. -/
theorem entry_resident (σ : State C Input) (key : FrameKey) :
    (entry σ key).highWaterWords = 3 := by
  rw [entry, store_water]
  change max 0 ((64 + 32 + 31) / 32) = 3
  decide +kernel

/-- The stores remain within the already resident prologue region. -/
theorem image_resident (σ : State C Input) (key : FrameKey) :
    (image σ key).highWaterWords = 3 := by
  rw [image, store_water, store_water, entry_resident]
  change max (max 3 ((0 + 32 + 31) / 32)) ((4 + 32 + 31) / 32) = 3
  decide +kernel

/-- The initialized free-pointer word remains visible at byte95. -/
theorem initialized_word (σ : State C Input) (key : FrameKey) :
    (image σ key).data ⟨95, by change 95 < 96; decide⟩ = 128 := by
  simp only [image, entry, store32, fresh, at0, at4, at64, zero,
    Int.reduceToNat, Nat.reduceAdd]
  rfl

/-- Snapshot boundedness is a proof about the computed length, not a new fuel. -/
theorem produced_bound (σ : State C Input) (key : FrameKey)
    (hsize : TEnv.get sizeSlot σ.env = size36) :
    (produced σ key hsize).length < 2 ^ 256 := by
  rw [produced_computed, computed36_length]
  decide

/-- Intrinsic ghost producer step. It is not the original source's carried
callee body and is not installed into source automation or an external oracle. -/
def producer36 (key : FrameKey) (σ : State C Input)
    (hsize : TEnv.get sizeSlot σ.env = size36) : TRes (Out C σ.H (.mem bytesR :: Input)) :=
  bytesHalt (produced σ key hsize) (produced_bound σ key hsize) σ

/-- Exact raw halt of the computed producer, without normalizing away data. -/
theorem producer36_halt (key : FrameKey) (σ : State C Input)
    (hsize : TEnv.get sizeSlot σ.env = size36) :
    producer36 key σ hsize = .error (THalt.ofData computed36) := by
  rw [producer36, bytesHalt_exact, produced_computed]

/-- The approved existing decoder binds the code actually computed by stores. -/
theorem computed36_decode : Semantics.decodePanic computed36 = some codeWord := by
  decide +kernel

/-- Nonvacuity for both pipelines over ANY caller globals/heap, not just init. -/
theorem entry_exists (p : Pipeline) (invocation depth : Nat) (σ : State C []) :
    ∃ μ : FrameMem C Input, ∃ hsize : TEnv.get sizeSlot μ.st.env = size36,
      μ.st = σ.push (t := .val .uint) size36 ∧
      μ.key = frameKey p invocation depth μ.st ∧
      μ.highWaterWords = 3 ∧
      producer36 μ.key μ.st hsize = .error (THalt.ofData computed36) := by
  exact ⟨entry (σ.push size36) (frameKey p invocation depth (σ.push size36)),
    rfl, rfl, rfl, entry_resident _ _, producer36_halt _ _ rfl⟩

/-- The bounded intrinsic plan has typed word operands and an actual scoped
parameter index; it is not a Yul instruction AST or an erased execution state. -/
structure StorePlan where
  source : SourceLink
  size : Idx Input (.val .uint)
  prologueAt : WordSpan 96
  prologueWord : U256
  firstAt : WordSpan 96
  firstWord : U256
  secondAt : WordSpan 96
  secondWord : U256

def originalPlan (p : Pipeline) : StorePlan :=
  ⟨link p, sizeSlot, at64, freeWord, at0, selectorWord, at4, codeWord⟩

/-- Exact whole-plan identity, not the desired bytes or halt as an assumption.
The external source/AST correspondence check is separate from this pure witness. -/
structure StoreShapeCert (p : Pipeline) where
  plan : StorePlan
  original : plan = originalPlan p

def originalCert (p : Pipeline) : StoreShapeCert p := ⟨originalPlan p, rfl⟩

def planImage (pl : StorePlan) (σ : State C Input) (key : FrameKey) : FrameMem C Input :=
  store32 (store32 (store32 (fresh σ key) pl.prologueAt pl.prologueWord)
    pl.firstAt pl.firstWord) pl.secondAt pl.secondWord

def planSpan (pl : StorePlan) (σ : State C Input)
    (hsize : TEnv.get pl.size σ.env = size36) : ByteSpan 96 :=
  ⟨zero, TEnv.get pl.size σ.env, .inr (by rw [hsize]; decide)⟩

def planData (pl : StorePlan) (σ : State C Input) (key : FrameKey)
    (hsize : TEnv.get pl.size σ.env = size36) : List UInt8 :=
  snapshot (planImage pl σ key) (planSpan pl σ hsize)

/-- Each of the two certificates has a real fresh image for every logical input. -/
theorem certified_data (p : Pipeline) (cert : StoreShapeCert p)
    (σ : State C Input) (key : FrameKey) (hsize : TEnv.get cert.plan.size σ.env = size36) :
    planData cert.plan σ key hsize = computed36 := by
  rcases cert with ⟨pl, hpl⟩
  cases hpl
  exact produced_computed σ key hsize

/-- Source-linked computed production/capture, with exact typed result.
This does not identify this step with the original source's carried callee. -/
theorem certified_producer_halt (p : Pipeline) (cert : StoreShapeCert p)
    (σ : State C Input) (key : FrameKey) (hsize : TEnv.get cert.plan.size σ.env = size36)
    (hn : (planData cert.plan σ key hsize).length < 2 ^ 256) :
    bytesHalt (planData cert.plan σ key hsize) hn σ = .error (THalt.ofData computed36) := by
  rw [bytesHalt_exact, certified_data]

/-- Pipeline identity is preserved, rather than equating their code artifacts. -/
theorem pipeline_preserved (p : Pipeline) : (link p).bundle.pipeline = p := by
  cases p <;> rfl

/-- Both distinct retained pipelines have constructive producer certificates. -/
theorem both_certificates : Nonempty (StoreShapeCert .legacy) ∧ Nonempty (StoreShapeCert .viaIR) :=
  ⟨⟨originalCert .legacy⟩, ⟨originalCert .viaIR⟩⟩

/-- A noncircular initialization certificate: exactly the fresh image plus
prologue, not any conclusion about stores, snapshot, halt, or target execution. -/
def InitialFor (σ : State C Input) (key : FrameKey) (μ : FrameMem C Input) : Prop :=
  μ = entry σ key

theorem initial_constructed (σ : State C Input) (key : FrameKey) :
    InitialFor σ key (entry σ key) := rfl

/-- The bound is derived from the constructed plan; clients need no length oracle. -/
theorem certified_bound (p : Pipeline) (cert : StoreShapeCert p)
    (σ : State C Input) (key : FrameKey) (hsize : TEnv.get cert.plan.size σ.env = size36) :
    (planData cert.plan σ key hsize).length < 2 ^ 256 := by
  rw [certified_data, computed36_length]
  decide

/-- Ready-to-use producer/capture function over the exact pipeline certificate.
Address/sender/value are carried from this logical input, not external bytes. -/
def certifiedProducer (p : Pipeline) (cert : StoreShapeCert p)
    (invocation depth : Nat) (σ : State C Input)
    (hsize : TEnv.get cert.plan.size σ.env = size36) : TRes (Out C σ.H (.mem bytesR :: Input)) :=
  bytesHalt (planData cert.plan σ (frameKey p invocation depth σ) hsize)
    (certified_bound p cert σ (frameKey p invocation depth σ) hsize) σ

theorem certifiedProducer_exact (p : Pipeline) (cert : StoreShapeCert p)
    (invocation depth : Nat) (σ : State C Input)
    (hsize : TEnv.get cert.plan.size σ.env = size36) :
    certifiedProducer p cert invocation depth σ hsize = .error (THalt.ofData computed36) :=
  certified_producer_halt p cert σ _ hsize _

end Solidity.Evm.TryPanicProducer
