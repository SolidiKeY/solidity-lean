import Solidity.Yul.Views.RetainedLocalAlias
import Solidity.Yul.Views.RetainedEntryImage

/-! Existing captured declaration images after actual local alias assignment.
The input is the current static registration view, not a final inventory law.
Local assignment changes locals only; dynamic source lengths still come from
the same actual store. Expanded snapshot canonicality/separation remain checks. -/
namespace Solidity.Yul.Views.RetainedLocalAliasImage
open Solidity.Backend.MemoryOps

/-- Expanded dynamic snapshots retain every statically computed registration. -/
theorem registration_mem_snapshot {E τ b child active a r fixed history scopes length}
    (image : @CapturedArrayImage E τ b child active a r fixed history scopes length)
    (m c) (member : c ∈ image.registrations) : c ∈ image.snapshot m := by
  first | (simp only;done) | skip
  rcases List.mem_cons.mp member with same | inside
  · exact List.mem_cons.mpr (Or.inl same)
  · obtain ⟨element,em,cm⟩ := List.mem_flatMap.mp inside
    exact List.mem_cons.mpr (Or.inr (List.mem_flatMap.mpr ⟨element,em,List.mem_append_left _ cm⟩))

/-- The actual producer poststate uses the checked captured image's coordinates.
No caller-supplied output readback, inverse or inventory agreement is required. -/
theorem source_inventory {E τ b child active Γ σ} (G : Source.Glob E) (F : Source.Fr) (n : Nat)
    (s : Source.EMState E Γ) (dst src : Source.Idx Γ σ) (prior : List (EntryReferenceScope E))
    (layout : @RetainedArrayLayout E τ b child active F.this) (fixed : Roadmap.Evm.Fixed)
    (history : RetainedIndexHistory layout) (length : Roadmap.Word)
    (image : CapturedArrayImage layout fixed history
      (captureEvaluatedValue G F (n+2) (sourceLocalAlias dst src) prior s).2 length)
    (m : SlotView)
    (view : finiteView image.registrations (s.2.ex.world.accounts F.this).storage m) :
    image.sourceInventory? (F:=F) ((RetainedLocalAlias.value G F n dst src).run s).2=
      some (image.snapshot m) := by
  first | (simp only;done) | skip
  rw [RetainedLocalAlias.value_run]
  exact image.source_view (F:=F) (s.1.set dst (s.1.get src),s.2) m view
end Solidity.Yul.Views.RetainedLocalAliasImage
