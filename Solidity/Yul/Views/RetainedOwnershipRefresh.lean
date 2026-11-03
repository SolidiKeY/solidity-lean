import Solidity.Yul.Views.RetainedOwnershipFrame

namespace Solidity.Yul.Views

/-- Reprepare against other actual locals using derived header views. No
assumed local-invariance/output law and no caller alias scan. -/
def RetainedOwnershipPlan.relocalize {E τ b child active Γ F layout fixed history written value s r}
    (p : @RetainedOwnershipPlan E τ b child active Γ F layout fixed history written value s r)
    {Δ : Source.RCtx} (callee : Source.Locals E.layout Δ) :
    RetainedOwnershipPlan F layout fixed history written value (callee,s.2) r := by
  have view := finiteEncode_view p.old _ _ p.raw ((packedSeparationCheck_iff _).mp p.oldChecked) p.encoded
  have roots : finiteView p.oldImage.registrations (s.2.ex.world.accounts F.this).storage p.raw :=
    fun c member => view c (p.oldImage.source_roots s _ p.oldComputed c member)
  have nOld := layout.sourceLength_view (F := F) s p.raw (roots _ List.mem_cons_self)
  have nNew := layout.sourceLength_view (F := F) (callee,s.2) p.raw (roots _ List.mem_cons_self)
  have sourceNew : p.oldImage.sourceInventory? (F := F) (callee,s.2)=some p.old :=
    (p.oldImage.source_view (F := F) (callee,s.2) p.raw roots).trans (congrArg some p.old_agrees.symm)
  exact ⟨p.oldLength,nNew.trans (nOld.symm.trans p.lengthComputed),p.oldImage,p.oldImageComputed,
    p.old,sourceNew,p.raw,p.encoded,p.oldChecked,p.nextImage,p.nextImageComputed,p.nextChecked,p.sourceOp,p.prepared⟩

theorem RetainedOwnershipPlan.relocalize_op {E τ b child active Γ F layout fixed history written value s r}
    (p : @RetainedOwnershipPlan E τ b child active Γ F layout fixed history written value s r)
    {Δ : Source.RCtx} (callee : Source.Locals E.layout Δ) : (p.relocalize callee).sourceOp=p.sourceOp := rfl

theorem RetainedOwnershipPlan.following_fresh {E τ b child active Γ F layout fixed history written value s r}
    (p : @RetainedOwnershipPlan E τ b child active Γ F layout fixed history written value s r) (static : F.static=false) :
    layout.sourceInventory? fixed history p.step.1.2=layout.snapshot? fixed history p.nextRaw :=
  layout.source_snapshot fixed history p.step.1.2 p.nextRaw p.nextImage p.nextImageComputed
    (fun c member => p.view static c (p.nextImage.snapshot_roots p.nextRaw c member))

theorem RetainedOwnershipPlan.retained_header_read {E τ b child active Γ F layout fixed history written value s r}
    (p : @RetainedOwnershipPlan E τ b child active Γ F layout fixed history written value s r) (static : F.static=false)
    (element : {element // element ∈ p.nextImage.elements})
    (entry : {entry // entry ∈ child.headers (layout.path.go (.index element.val.1)) (layout.childCursor fixed element.val.1)}) :
    (Source.readLen F entry.val.1).run p.step.1.2 =
      (.ok (p.nextRaw ((element.val.2.header entry).registration F.this).slot).val,p.step.1.2) := by
  let h := element.val.2.header entry
  have hm := element.val.2.header_member entry
  have bank : E.transientRoot entry.val.1=false := by
    have rootBank : E.transientRoot (layout.path.go (.index element.val.1))=false := layout.bank
    have hb := element.val.2.bank rootBank _ hm
    rw [PathPrimitiveHeader.registration_path] at hb
    exact hb
  have member : h.registration F.this ∈ p.next :=
    List.mem_cons.mpr (Or.inr (List.mem_flatMap.mpr ⟨element.val,element.property,List.mem_append_left _ hm⟩))
  exact h.readLen_view F _ p.nextRaw bank (p.view static _ member)

theorem RetainedOwnershipPlan.other_account {E τ b child active Γ F layout fixed history written value s r}
    (p : @RetainedOwnershipPlan E τ b child active Γ F layout fixed history written value s r) (other : Roadmap.Address)
    (different : other≠F.this) : p.after.source.world.accounts other=s.2.ex.world.accounts other := by
  cases static : F.static
  · obtain ⟨update,_,same⟩ := Option.map_eq_some_iff.mp p.prepared
    unfold RetainedOwnershipPlan.after
    rw [p.nonstatic static]
    change (s.2.ex.apply p.sourceOp).world.accounts other=_
    rw [←same]
    exact Source.World.set_other _ different _
  · unfold RetainedOwnershipPlan.after
    rw [p.static static]

theorem RetainedOwnershipPlan.other_key {E τ b child active Γ F layout fixed history written value s r}
    (p : @RetainedOwnershipPlan E τ b child active Γ F layout fixed history written value s r)
    (k : ResidualKey complementCarrierOwnership) (other : k.transient≠false ∨ k.address≠F.this) : p.step.2.cells k=r.cells k := by
  cases static : F.static
  · rw [p.nonstatic static]
    apply residualRun_other
    intro w member same
    obtain ⟨slot,_,equal⟩ := List.mem_map.mp member
    cases equal
    cases other with
    | inl bank => exact bank (congrArg ResidualKey.transient same)
    | inr address => exact address (congrArg ResidualKey.address same)
  · rw [p.static static]

end Solidity.Yul.Views
