import Solidity.Lowering.Readonly.SourceKnownHistory
import Solidity.Lowering.Readonly.LibraryFrameEffects

/-! Actual delegated-library entry journal history. Regression purpose: the
library try branch can execute a storage-pointer body with unavailable calldata,
restore memory, and catch a revert without postulating an arbitrary checkpoint.
The equation below preserves the existing evaluator and ABI refusals. -/
namespace Solidity.Lowering.Readonly.SourceHistory
open Solidity.Source
variable {E : Env}

private theorem library_equation (G : Glob E) (F : Fr) (n : Nat) (d : Decl)
    {ps : List STy} (values : Vals E.layout ps) (rs : List STy) :
    callLibrary G F (n+1) d values rs = (do
      if F.depth ≥ 1024 then return .error []
      if !libraryBoundary ps rs then EM.halt (.stuck "unsupported library ABI boundary")
      let known := ps.all STy.isValue
      let input ← if known then do
          let encoded ← encodeVals F n false values.toR
          pure (G.selector (sigOf E.layout d.name ps) ++ encoded)
        else pure []
      let result ← libraryFrame (callInternal (calldataKnown := known) G
        { F with cd := input, depth := F.depth + 1 } n d values rs)
      match result with
      | .ok value => do
        let raw ← EM.lift (unRet rs value)
        let converted ← EM.lift raw.toVals
        pure (.ok converted)
      | .error data => pure (.error data)) := by
  simp only [callLibrary, FailureExecution.preflight]
  split
  · rfl
  · split
    · rfl
    · simp only [pure_bind]
      cases available : ps.all STy.isValue with
      | false =>
        simp only [Bool.false_eq_true, if_false]
        library_frame_factor
      | true =>
        simp only [if_true]
        congr 1
        funext encoded
        library_frame_factor

/-- The actual entry's delegated body preserves its inherited static history,
for value and pointer signatures and every success/failure outcome. -/
theorem callLibrary_succ_known (G : Glob E) (F : Fr) (n : Nat) (h : KnownAt G n)
    (d : Decl) {ps : List STy} (values : Vals E.layout ps) (rs : List STy) :
    Effect F.static (callLibrary G F (n+1) d values rs) := by
  have framed : ∀ input : Solidity.Roadmap.Bytes,
      Effect F.static (libraryFrame (callInternal (calldataKnown := ps.all STy.isValue) G
        {F with cd := input, depth := F.depth + 1} n d values rs)) := by
    intro input
    exact libraryFrame_effect F.static _
      (h.callInternal (ps.all STy.isValue) {F with cd := input, depth := F.depth + 1} d values rs)
  rw [library_equation]
  repeat' first
   | (with_reducible exact framed _)
   | (with_reducible exact Effect.pure F.static _)
   | (with_reducible exact Effect.halt F.static _)
   | (with_reducible exact Effect.lift F.static _)
   | (with_reducible exact encodeVals_effect F.static F n _ _)
   | (with_reducible exact libraryFrame_effect F.static _ (h.callInternal _ _ _ _ _))
   | refine Effect.bind _ _ _ ?_ (fun value => ?_)
   | split
   | dsimp only

end Solidity.Lowering.Readonly.SourceHistory

/-- info: 'Solidity.Lowering.Readonly.SourceHistory.callLibrary_succ_known' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms Solidity.Lowering.Readonly.SourceHistory.callLibrary_succ_known
