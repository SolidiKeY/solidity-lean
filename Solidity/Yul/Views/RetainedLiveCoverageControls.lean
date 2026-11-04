import Solidity.Yul.Views.RetainedLiveCoverage
import Solidity.Yul.Views.RetainedCallerHeadersControls

/-! A dormant saved child's actual length produces its payload registration in
the complete source inventory, not merely the static header/stamp inventory. -/
namespace Solidity.Yul.Views.Controls

def rlcElement : RetainedElementPack rhLayout agFixed := raiElements.head (by
  intro empty
  have count := congrArg List.length empty
  change 2=0 at count
  contradiction)
theorem rlc_present : rlcElement ∈ rccImage.elements := by
  change rlcElement ∈ rlcElement::_
  exact List.mem_cons_self

theorem rlc_index : rlcElement.1=1 := rfl

def rlcEntry : {entry // entry ∈ agChild.headers (rhLayout.path.go (.index rlcElement.1)) (rhLayout.childCursor agFixed rlcElement.1)} :=
  ⟨rchEntry.val,by rw [rlc_index];exact rchEntry.property⟩

def rlcHeader : PathIntHeader agEnv (agInner 1) rcU16 (102*32+2) := rlcElement.2.header rlcEntry

theorem rlc_length : aggregateSourceLengths packedStepFrame rccRun.1.2 (rlcHeader.registration account)=some 1 := rfl

theorem rlc_complete : ∀ c ∈ rlcHeader.elements agFixed account 1, c ∈ rccImage.snapshot rhRaw0 := by
  have covered := RetainedLiveCoverage.image (F:=packedStepFrame) rccImage rccRun.1.2 _ rcc_inventory rlcElement rlc_present rlcEntry
  obtain ⟨length,read,members⟩ := covered
  change aggregateSourceLengths packedStepFrame rccRun.1.2 (rlcHeader.registration account)=some length at read
  have same : length=1 := Option.some.inj (read.symm.trans rlc_length)
  subst length
  exact members

theorem rlc_payload : rlcHeader.element agFixed account 0 ∈ rccImage.snapshot rhRaw0 :=
  rlc_complete _ ((rlcHeader.elements_member agFixed account 1 _).mpr ⟨0,by decide,rfl⟩)

theorem rlc_coordinates : (rlcHeader.element agFixed account 0).slot=2000 ∧
    (rlcHeader.element agFixed account 0).field.offset=0 ∧
    (rlcHeader.element agFixed account 0).field.width=2 := ⟨rfl,rfl,rfl⟩

theorem rlc_view : scalarPathView (rlcHeader.element agFixed account 0).path
    (rlcHeader.element agFixed account 0).codec (rlcHeader.element agFixed account 0).slot
    (rccRun.1.2.2.ex.world.accounts account).storage rhRaw0 := rcc_view _ rlc_payload

theorem rlc_read : (Source.readLoc packedStepFrame (.stor ((agInner 1).go (.index 0)))).run rccRun.1.2=
    (.ok (Source.intWrap rcU16 99),rccRun.1.2) := rfl

/-- Keeping only declaration roots drops a real dynamically owned payload. -/
theorem rlc_not_roots : rlcHeader.element agFixed account 0 ∉ rccImage.registrations := by
  first | (simp only;done) | skip
  intro lost
  have slot : (rlcHeader.element agFixed account 0).slot ∈ rccImage.registrations.map (fun c => c.slot) :=
    List.mem_map.mpr ⟨_,lost,rfl⟩
  change (2000:Roadmap.Word) ∈ [0,102,103,100,101] at slot
  have absent : (2000:Roadmap.Word) ∉ [0,102,103,100,101] := by decide
  exact absent slot
end Solidity.Yul.Views.Controls
