import Solidity.Yul.World.TransientTargetPort
/-! Full local Source/residual/target rollback of an ACTUAL checked transient
store. No account/code/callee reachability or whole-bank adequacy is assumed.
The entire Source state, not just ExecState, is restored using the producer
operation's unchanged caller fields and its real paired journal. -/
namespace Solidity.Yul.World.TransientTarget
open Views Solidity.Backend
theorem store_rollback {E : Source.Env} {Γ : Source.RCtx}
    {ps ts : (a : Roadmap.Address) → List (ScalarPath E.layout (E.lay a))}
    (F : Source.Fr) (slot raw : Roadmap.Word) (s : Source.EMState E Γ)
    (r : ResidualJournal complementCarrierOwnership) (target : Transient.State) (result)
    (checked : transientSlotStore? (ps:=ps) (ts:=ts) F slot raw s r = some result)
    (normal : F.static = false) :
    store (ps:=ps) (ts:=ts) F slot raw s r target =
      some (result, .ok (Transient.write target F.this slot raw)) ∧
    (let entry : ResidualCompanion E.layout E.lay E.lay complementCarrierOwnership := ⟨s.2.ex,r⟩
     let restored := companionRollback (companionEnter entry F.this F.sender F.value F.cd F.static)
       ⟨result.1.2.2.ex,result.2⟩
     ((result.1.2.1, {result.1.2.2 with ex := restored.source}), restored.residual,
       Transient.rollback target.journal.length (Transient.write target F.this slot raw)) =
       (s,r,target)) := by
  refine ⟨store_exact F slot raw s r target result checked normal, ?_⟩
  obtain ⟨p, prepared, same⟩ := Option.map_eq_some_iff.mp checked
  subst result
  rw [packedSourceStep_nonstatic F p s r normal]
  have restored := packed_frame_rollback
    (⟨s.2.ex,r⟩ : ResidualCompanion E.layout E.lay E.lay complementCarrierOwnership)
    [p] F.this F.sender F.value F.cd F.static
  simp only [runPackedSlots] at restored
  change ((s.1, {s.2 with ex :=
      (companionRollback
        (companionEnter ⟨s.2.ex,r⟩ F.this F.sender F.value F.cd F.static)
        (applyPackedSlot ⟨s.2.ex,r⟩ p)).source}),
    (companionRollback
      (companionEnter ⟨s.2.ex,r⟩ F.this F.sender F.value F.cd F.static)
      (applyPackedSlot ⟨s.2.ex,r⟩ p)).residual,
    Transient.rollback target.journal.length (Transient.write target F.this slot raw)) =
      (s,r,target)
  rw [restored, Transient.rollback_write]

theorem store_two_outer_rollback {E : Source.Env} {Γ : Source.RCtx}
    {ps ts : (a : Roadmap.Address) → List (ScalarPath E.layout (E.lay a))}
    (F : Source.Fr) (slot raw : Roadmap.Word) (s : Source.EMState E Γ)
    (r : ResidualJournal complementCarrierOwnership) (target : Transient.State) (result)
    (checked : transientSlotStore? (ps:=ps) (ts:=ts) F slot raw s r = some result)
    (slot2 raw2 : Roadmap.Word) (result2)
    (checked2 : transientSlotStore? (ps:=ps) (ts:=ts) F slot2 raw2 result.1.2 result.2 = some result2)
    (normal : F.static = false) :
    store (ps:=ps) (ts:=ts) F slot raw s r target =
      some (result, .ok (Transient.write target F.this slot raw)) ∧
    store (ps:=ps) (ts:=ts) F slot2 raw2 result.1.2 result.2
      (Transient.write target F.this slot raw) =
      some (result2, .ok (Transient.write (Transient.write target F.this slot raw) F.this slot2 raw2)) ∧
    (let entry : ResidualCompanion E.layout E.lay E.lay complementCarrierOwnership := ⟨s.2.ex,r⟩
     let restored := companionRollback (companionEnter entry F.this F.sender F.value F.cd F.static)
       ⟨result2.1.2.2.ex,result2.2⟩
     ((result2.1.2.1, {result2.1.2.2 with ex := restored.source}), restored.residual,
       Transient.rollback target.journal.length (Transient.write (Transient.write target F.this slot raw) F.this slot2 raw2)) =
       (s,r,target)) := by
  refine ⟨store_exact F slot raw s r target result checked normal,
    store_exact F slot2 raw2 result.1.2 result.2
      (Transient.write target F.this slot raw) result2 checked2 normal, ?_⟩
  obtain ⟨p, prepared, same⟩ := Option.map_eq_some_iff.mp checked
  obtain ⟨p2, prepared2, same2⟩ := Option.map_eq_some_iff.mp checked2
  subst result2
  subst result
  simp only [packedSourceStep_nonstatic F p s r normal,
    packedSourceStep_nonstatic F p2 _ _ normal]
  have restored := packed_frame_rollback
    (⟨s.2.ex,r⟩ : ResidualCompanion E.layout E.lay E.lay complementCarrierOwnership)
    [p,p2] F.this F.sender F.value F.cd F.static
  simp only [runPackedSlots] at restored
  change ((s.1, {s.2 with ex :=
      (companionRollback
        (companionEnter ⟨s.2.ex,r⟩ F.this F.sender F.value F.cd F.static)
        (applyPackedSlot (applyPackedSlot ⟨s.2.ex,r⟩ p) p2)).source}),
    (companionRollback
      (companionEnter ⟨s.2.ex,r⟩ F.this F.sender F.value F.cd F.static)
      (applyPackedSlot (applyPackedSlot ⟨s.2.ex,r⟩ p) p2)).residual,
    Transient.rollback target.journal.length
      (Transient.writes target [(F.this,slot,raw),(F.this,slot2,raw2)])) = (s,r,target)
  rw [restored, Transient.rollback_writes]

end Solidity.Yul.World.TransientTarget
