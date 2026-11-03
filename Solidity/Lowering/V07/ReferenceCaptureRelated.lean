import Solidity.Lowering.V07.ReferenceCapture
import Solidity.Lowering.V07.ContextMapWrite

/-! Context-related local-reference captures. The initial compiler-independent
ContextMap.Related predicate links the selected Source address/path to its
intrinsic reference; the link is derived, not supplied as a desired result.
The extended Source locals classify the returned value: no Source declaration
execution is asserted. Dropping the target capture restores the complete caller
state. No allocation/copy/delete/lifetime or admitted-program result follows. -/
namespace Solidity.Lowering.V07

/-- Actual memory capture, its initial value relation and both context
extensions. The caller state is recovered exactly after the temporary drops. -/
theorem related_memory_capture :
∀ {E : Source.Env} {srcΓ : Source.RCtx} {C : Contract} {Γ : Ctx}
 (G : Source.Glob E) (F : Source.Fr) (fuel : Nat)
 (source : Source.EMState E srcΓ) (target : State C Γ)
 (m : ContextMap srcΓ Γ)
 (Rel : (τ : Source.STy) → (u : LTy) → Source.Val E.layout τ → u.TDenote C target.H → Prop)
 (aligned : m.Related Rel source.1 target.env)
 (i : Source.Idx srcΓ (.bytes .memory)) (j : Idx Γ (.mem bytesR))
 (address : Nat) (r : HRef target.H bytesR)
 (slot : m.slot i = ⟨.mem bytesR,j⟩)
 (sourceRead : source.1.get i = .memRef rfl address)
 (targetRead : TEnv.get j target.env = some r),
 (Source.evalE G F (fuel+1) (.local i)).run source = (.ok (.val (.memRef rfl address)),source) ∧
 (memoryCapture j rfl).run target =
   .ok (⟨target.push (t := .mem bytesR) (some r),List.prefix_refl _⟩) ∧
 (MPath.var .here rfl : MPath C (.mem bytesR :: Γ) (.ref bytesR)).mvalT (target.push (t := .mem bytesR) (some r)) = .ok r ∧
 Rel (.bytes .memory) (.mem bytesR) (.memRef rfl address) (some r) ∧
 (m.cons (.bytes .memory) (.mem bytesR)).Related Rel
   (.cons (.memRef rfl address) source.1) (target.push (t := .mem bytesR) (some r)).env ∧
 (m.wk (Thin.drop (t := .mem bytesR) .refl)).Related Rel
   source.1 (target.push (t := .mem bytesR) (some r)).env ∧
 (target.push (t := .mem bytesR) (some r)).drop (.push .refl) = target := by
  intro E srcΓ C Γ G F fuel source target m Rel aligned i j address r slot sourceRead targetRead
  have linked : Rel (.bytes .memory) (.mem bytesR) (.memRef rfl address) (some r) := by
    simpa only [sourceRead,targetRead] using
      (ContextMap.value_at m Rel source.1 target.env aligned i j slot)
  have runs := capture_memory_transport G F fuel source target i j address r sourceRead targetRead
  exact ⟨runs.1,runs.2.1,runs.2.2,linked,
    ContextMap.related_cons m Rel source.1 target.env aligned _ _ _ _ linked,
    memory_capture_context m target Rel source.1 aligned r,rfl⟩

/-- Actual storage capture, its initial value relation and both context
extensions. The caller state is recovered exactly after the temporary drops. -/
theorem related_storage_capture :
∀ {E : Source.Env} {srcΓ : Source.RCtx} {C : Contract} {Γ : Ctx}
 (G : Source.Glob E) (F : Source.Fr) (fuel : Nat)
 (source : Source.EMState E srcΓ) (target : State C Γ)
 (m : ContextMap srcΓ Γ)
 (Rel : (τ : Source.STy) → (u : LTy) → Source.Val E.layout τ → u.TDenote C target.H → Prop)
 (aligned : m.Related Rel source.1 target.env)
 (i : Source.Idx srcΓ (.bytes .storage)) (j : Idx Γ (.alias bytesR))
 (path : Source.SPath) (r : SRef C (.ref bytesR))
 (slot : m.slot i = ⟨.alias bytesR,j⟩)
 (sourceRead : source.1.get i = .storRef rfl path)
 (targetRead : TEnv.get j target.env = some r),
 (Source.evalE G F (fuel+1) (.local i)).run source = (.ok (.val (.storRef rfl path)),source) ∧
 (storageCapture j).run target =
   .ok (⟨target.push (t := .alias bytesR) (some r),List.prefix_refl _⟩) ∧
 (SPath.alias .here : SPath C (.alias bytesR :: Γ) (.ref bytesR)).resolveT (target.push (t := .alias bytesR) (some r)) = .ok r ∧
 Rel (.bytes .storage) (.alias bytesR) (.storRef rfl path) (some r) ∧
 (m.cons (.bytes .storage) (.alias bytesR)).Related Rel
   (.cons (.storRef rfl path) source.1) (target.push (t := .alias bytesR) (some r)).env ∧
 (m.wk (Thin.drop (t := .alias bytesR) .refl)).Related Rel
   source.1 (target.push (t := .alias bytesR) (some r)).env ∧
 (target.push (t := .alias bytesR) (some r)).drop (.push .refl) = target := by
  intro E srcΓ C Γ G F fuel source target m Rel aligned i j path r slot sourceRead targetRead
  have linked : Rel (.bytes .storage) (.alias bytesR) (.storRef rfl path) (some r) := by
    simpa only [sourceRead,targetRead] using
      (ContextMap.value_at m Rel source.1 target.env aligned i j slot)
  have runs := capture_storage_transport G F fuel source target i j path r sourceRead targetRead
  exact ⟨runs.1,runs.2.1,runs.2.2,linked,
    ContextMap.related_cons m Rel source.1 target.env aligned _ _ _ _ linked,
    storage_capture_context m target Rel source.1 aligned r,rfl⟩

end Solidity.Lowering.V07
