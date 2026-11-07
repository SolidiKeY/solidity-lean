import tests.h62.item2.«audit-g25-scalar-lowering».Fixtures

/-! Positive environment/metadata/hash/namespace cases and negative compiler
controls use the unchanged intrinsic source and real gasless slice evaluator. -/
namespace Solidity.Backend.Scalar.H62Audit.EnvironmentTotality
open Solidity Solidity.Backend Solidity.Backend.Environment
open Solidity.Backend.Scalar.H62Audit.Fixtures

theorem environment_total (f : Frame) (k : EnvKey) (s : Slice) :
    ∃ t, runSlice f [select k] s = some t :=
  ⟨_, slice_select f k s⟩

theorem environment_never_rejects_all (f : Frame) (k : EnvKey) :
    ¬ ∀ s : Slice, runSlice f [select k] s = none := by
  intro reject
  have success := slice_select f k targetSlice
  rw [reject] at success
  cases success

theorem value_certificate_success {C : Contract} {Γ : Ctx} {σ : State C Γ}
    {e : Val C Γ .uint} {f : Frame} {code : List Instr} {m : Memory}
    (c : ValueCertificate σ e f code m) (tail : List Environment.Word) :
    e.evalT σ = .ok c.value ∧
      runSlice f code ⟨tail, m⟩ = some ⟨c.value :: tail, c.memoryOut⟩ :=
  ⟨c.source, c.target tail⟩

theorem value_reject_all_impossible {C : Contract} {Γ : Ctx} {σ : State C Γ}
    {e : Val C Γ .uint} {f : Frame} {code : List Instr} {m : Memory} :
    ¬ ∃ _ : ValueCertificate σ e f code m, ∀ s : Slice, runSlice f code s = none := by
  rintro ⟨c, reject⟩
  have success := c.target []
  rw [reject] at success
  cases success

theorem values_certificate_success {C : Contract} {Γ : Ctx} {σ : State C Γ}
    {es : List (Val C Γ .uint)} {f : Frame} {code : List Instr} {m : Memory}
    (c : ValuesCertificate σ es f code m) (tail : List Environment.Word) :
    evalValues σ es = .ok c.values ∧
      runSlice f code ⟨tail, m⟩ = some ⟨c.values.reverse ++ tail, c.memoryOut⟩ :=
  ⟨c.source, c.target tail⟩

/-- Selection succeeds after successful path resolution, without assuming a
memory preimage or a target execution. Memory feasibility remains per invocation. -/
theorem resolved_hash_selection_total {C : Contract} {Γ : Ctx} {R : RefTy}
    (σ : State C Γ) (b : MPath C Γ (.ref R)) (r : HRef σ.H R)
    (resolved : b.mvalT σ = .ok r) (k : HashKind) (offset output : W256) :
    ∃ code, lowerHash σ b k offset output = .ok code := by
  unfold lowerHash
  rw [resolved]
  exact ⟨_, rfl⟩

theorem resolved_metadata_total (selector : Fin (2 ^ 32)) :
    ∃ i, declarationCode { callable := .abi .externalFn .selected (some selector) } = some i :=
  ⟨selectorCode selector, rfl⟩

private def nonemptyState : State default bytesΓ :=
  { bytesState with heap := (⟨[u1, u7, u255], by decide⟩, ()) }
private def nonemptyRef : HRef nonemptyState.H bytesR := ⟨0, rfl⟩
private def nonemptySlice : Slice :=
  ⟨[u99], writeBytes emptyMemory 7 [1, 7, 255]⟩
private theorem hashInput : HashInput nonemptySlice ⟨7, by decide⟩ ⟨3, by decide⟩
    (MObj.words bytesR (nonemptyState.heap.get nonemptyRef)) :=
  ⟨by decide, by decide +kernel⟩

theorem nonempty_intrinsic_hash_success :
    Val.evalT nonemptyState (.hash .keccak bytesPath rfl : Val default bytesΓ .uint) =
      .ok (nonemptyState.heap.hash .keccak nonemptyRef) ∧
    runCrypto (keccakCode ⟨7, by decide⟩ ⟨3, by decide⟩) nonemptySlice =
      some { nonemptySlice with stack := nonemptyState.heap.hash .keccak nonemptyRef ::
        nonemptySlice.stack } :=
  intrinsic_keccak nonemptyState bytesPath nonemptyRef rfl _ _ _ hashInput

theorem every_hash_builtin_selects (k : HashKind) :
    lowerHash nonemptyState bytesPath k ⟨7, by decide⟩ ⟨64, by decide⟩ =
      .ok (builtinCode k ⟨7, by decide⟩ ⟨3, by decide⟩ ⟨64, by decide⟩) :=
  lowerHash_success nonemptyState bytesPath nonemptyRef rfl k _ _ _ _ hashInput

theorem nonempty_namespace_success :
    runCrypto (namespaceCode ⟨7, by decide⟩ ⟨3, by decide⟩ ⟨64, by decide⟩) nonemptySlice =
      some ⟨lenU (ERC7201.root [1, 7, 255]).val (ERC7201.root [1, 7, 255]).isLt ::
        nonemptySlice.stack, writeBytes nonemptySlice.memory 64 (namespacePreimage [1, 7, 255])⟩ := by
  apply namespace_source
  exact ⟨by decide, by decide, by decide +kernel⟩

/-- Frozen caller observation preserves success and panic data; exceptional
halt and empty revert deliberately share one observation. -/
theorem observable_failure_boundary :
    (Roadmap.Evm.Halt.success []).observe ≠ (Roadmap.Evm.Halt.revert []).observe ∧
    (Roadmap.Evm.Halt.revert Scalar.divisionFailure).observe ≠
      (Roadmap.Evm.Halt.revert Scalar.overflowFailure).observe ∧
    Roadmap.Evm.Halt.exceptional.observe = (Roadmap.Evm.Halt.revert []).observe := by
  decide +kernel

end Solidity.Backend.Scalar.H62Audit.EnvironmentTotality
