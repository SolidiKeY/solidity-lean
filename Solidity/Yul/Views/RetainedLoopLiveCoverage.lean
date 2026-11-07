import Solidity.Yul.Views.RetainedLoopSequence
import Solidity.Yul.Views.RetainedLiveCoverage

/-! Live child coverage after checked writes through a loop-captured image.
The published traversal theorem is consumed at actual Source endpoints. Image
preparation, separation and operation preparation remain explicit; this does
not establish reference formation or Source-to-EVM adequacy. -/
namespace Solidity.Yul.Views.RetainedLoopLiveCoverage

theorem source_live {E Γ τ b child active} (F : Source.Fr)
    {layout : @RetainedArrayLayout E τ b child active F.this} {fixed history scopes length}
    (image : CapturedArrayImage layout fixed history scopes length) (raw : SlotView)
    (state : Source.EMState E Γ) (operation : Source.Op E.layout E.lay E.lay)
    (static : F.static=false) (checked : packedSeparationCheck (image.snapshot raw)=true)
    (prepared : finiteAccountWrite? F.this (image.snapshot raw) raw=some operation)
    (element : RetainedElementPack layout fixed) (present : element ∈ image.elements)
    (entry : {entry // entry ∈ child.headers
      (layout.path.go (.index element.1)) (layout.childCursor fixed element.1)}) :
    ∃ n, aggregateSourceLengths F ((Source.applyOp F operation).run state).2 (element.2.header entry |>.registration F.this)=some n ∧
      ∀ c∈(element.2.header entry).elements fixed F.this n,c∈image.snapshot raw := by
  exact RetainedLiveCoverage.image (F:=F) image _ _
    (RetainedLoopRefresh.source_snapshot F image raw state operation static checked prepared)
    element present entry

theorem sequence_live {E Γ τ b child active} (F : Source.Fr)
    {layout : @RetainedArrayLayout E τ b child active F.this} {fixed history scopes length}
    (image : CapturedArrayImage layout fixed history scopes length) (raw : SlotView)
    (state : Source.EMState E Γ)
    (first second : Source.Op E.layout E.lay E.lay) (error : Source.Halt)
    (static : F.static=false) (checked : packedSeparationCheck (image.snapshot raw)=true)
    (prepared : finiteAccountWrite? F.this (image.snapshot raw) raw=some second)
    (element : RetainedElementPack layout fixed) (present : element ∈ image.elements)
    (entry : {entry // entry ∈ child.headers
      (layout.path.go (.index element.1)) (layout.childCursor fixed element.1)}) :
    ∃ n, aggregateSourceLengths F ((RetainedLoopSequence.writeTwiceThenHalt F first second error).run state).2 (element.2.header entry |>.registration F.this)=some n ∧
      ∀ c∈(element.2.header entry).elements fixed F.this n,c∈image.snapshot raw := by
  exact RetainedLiveCoverage.image (F:=F) image _ _
    (RetainedLoopSequence.final_inventory F image raw state first second error static checked prepared)
    element present entry

end Solidity.Yul.Views.RetainedLoopLiveCoverage
