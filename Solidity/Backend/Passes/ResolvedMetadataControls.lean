import Solidity.Backend.Passes.ResolvedMetadata
import Solidity.Backend.Passes.ReachedHash
import Solidity.Backend.Passes.StatefulCaptureControls

namespace Solidity.Backend.Passes.ResolvedMetadataControls
open Backend.Environment
open Backend.Passes.Controls.Fixture

def selector : Fin (2^32) := ⟨0x12345678,by decide⟩
def declaration : SourceFunction :=
  {name := "publishedMetadata", signature := some "f(uint256)",
   callable := .abi .externalFn .selected (some selector)}
theorem resolved : metadataSelector declaration = some selector := rfl

/-- Metadata consumes the actual selected hash output memory; no stale initial
memory is substituted even though this inhabited hash happens to preserve it. -/
def metadata : ValueCertificate ReachedHash.reached (ResolvedMetadata.expression selector)
    PublishedMixedCapture.environment [selectorCode selector] ReachedHash.hash.memoryOut :=
  ResolvedMetadata.certificate ReachedHash.reached PublishedMixedCapture.environment selector
    ReachedHash.hash.memoryOut

def combined : ValuesCertificate ReachedHash.reached
    [PublishedMixedCapture.expression,.hash .keccak ReachedHash.path rfl,ResolvedMetadata.expression selector]
    PublishedMixedCapture.environment
    (PublishedValues.code .selfAddress ⟨3,by decide⟩ ++
      (keccakCode ReachedHash.offset ReachedHash.length ++ [selectorCode selector])) ReachedHash.memory :=
  consCertificate (PublishedMixedCapture.numeric ReachedHash.memory)
    (consCertificate ReachedHash.hash
      (consCertificate metadata
        (nilCertificate ReachedHash.reached PublishedMixedCapture.environment metadata.memoryOut)))

theorem source : evalValues ReachedHash.reached
    [PublishedMixedCapture.expression,.hash .keccak ReachedHash.path rfl,ResolvedMetadata.expression selector] =
    .ok [PublishedMixedCapture.answer,
      ReachedHash.reached.heap.hash .keccak Evm.Memory.CompileExamples.r0,selectorWord selector] :=
  combined.source

/-- Complete ordered result stack and ENTIRE byte memory, arbitrary saved tail. -/
theorem target (tail : List Word) :
    runSlice PublishedMixedCapture.environment
      (PublishedValues.code .selfAddress ⟨3,by decide⟩ ++
        (keccakCode ReachedHash.offset ReachedHash.length ++ [selectorCode selector]))
      ⟨tail,ReachedHash.memory⟩ = some ⟨selectorWord selector ::
        ReachedHash.reached.heap.hash .keccak Evm.Memory.CompileExamples.r0 ::
        PublishedMixedCapture.answer :: tail,ReachedHash.memory⟩ := combined.target tail

theorem declaration_after_hash :
    declarationCode declaration = some (selectorCode selector) ∧
    evalValues ReachedHash.reached [.hash .keccak ReachedHash.path rfl,ResolvedMetadata.expression selector] =
      .ok [ReachedHash.hash.value,selectorWord selector] ∧
    runSlice PublishedMixedCapture.environment
      (keccakCode ReachedHash.offset ReachedHash.length ++ [selectorCode selector])
      ⟨[PublishedMixedCapture.answer],ReachedHash.memory⟩ =
      some ⟨selectorWord selector :: ReachedHash.hash.value :: [PublishedMixedCapture.answer],
        ReachedHash.hash.memoryOut⟩ ∧
    Backend.Scalar.stackBound [selectorCode selector] 2 = true :=
  ResolvedMetadata.after_value ReachedHash.hash declaration selector resolved
    [PublishedMixedCapture.answer] (by decide +kernel)

/-- The symbolic compiler is also actually applied at the reached captured
state's selected physical representation, not just to a uniform empty fixture. -/
theorem reached_physical : ∃ (mb : Nat → Fin Evm.W) (mid : Evm.Machine) (w : Fin Evm.W),
    Evm.run StatefulCaptureControls.captureCompiled.code machine = .ok mid 0 ∧
    MappedOutput (.memory StatefulCaptureControls.captureCompiled) 1 6 base σ machine
      CaptureControls.afterCapture mid mb ∧
    Evm.ReprV .uint (selectorWord selector) (.val w) ∧
    Backend.Scalar.encodeValue .uint (selectorWord selector) = BitVec.ofNat 256 w.val ∧
    Evm.run (ResolvedMetadata.symbolic (C := C) 0 (Evm.Frag.init Γ) selector).code mid =
      .ok (mid.push (.val w)) 0 := by
  obtain ⟨mb,ob,mid,final,word,ha,_,hs,ma,_,_,_,_,_,_⟩ := StatefulCaptureControls.reached_application
  have input := ma.1
  obtain ⟨w,hw,he,ht⟩ := ResolvedMetadata.physical input selector mid.stack
  exact ⟨mb,mid,w,ha,ma,hw,he,ht⟩

theorem actual_bytes : (selectorCode selector).encode = [0x63,0x12,0x34,0x56,0x78] ∧
    (selectorAbiCode selector).encode = [0x7f,0x12,0x34,0x56,0x78] ++ List.replicate 28 0 := by
  decide +kernel

theorem wrong_alignment : Backend.Environment.pushStep (selectorCode selector) [PublishedMixedCapture.answer] ≠
    Backend.Environment.pushStep (selectorAbiCode selector) [PublishedMixedCapture.answer] := by decide +kernel

theorem wrong_selector : declarationCode declaration ≠
    some (selectorCode ⟨0x78563412,by decide⟩) := by decide +kernel

theorem missing_refused : declarationCode {callable := .abi .externalFn .selected none} = none := rfl

theorem push_capacity_refused : Backend.Scalar.stackBound [selectorCode selector] 1024 = false := by
  decide +kernel

theorem ordered_bytes : [0,6,7,8,9].map ReachedHash.memory = [0xbb,0xbb,8,9,0xbb] := ReachedHash.ordered_bytes

end Solidity.Backend.Passes.ResolvedMetadataControls
