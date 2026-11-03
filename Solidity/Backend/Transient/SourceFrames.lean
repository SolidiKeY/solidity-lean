import Solidity.Backend.Transient.Controls

/-! Actual Source primitive bodies paired with executable target transient
callbacks. These are body/rollback certificates, not G42 call-entry reachability,
ABI dispatch, environment havoc or full Source callback execution adequacy. -/
namespace Solidity.Backend.Transient

def sourceBody {E : Source.Env} {Γ : Source.RCtx} (slot : BoolSlot E)
    (parent child : Source.Fr) (first second : Bool) : Source.EM E Γ Unit := do
  Source.writeAt parent slot.path (.bool first)
  Source.writeAt child slot.path (.bool second)

theorem source_body_exact {E : Source.Env} {Γ : Source.RCtx} (slot : BoolSlot E)
    (parent child : Source.Fr) (hp : parent.static=false) (hc : child.static=false)
    (first second : Bool) (s : Source.EMState E Γ) :
    (sourceBody slot parent child first second).run s=
      (.ok (),(s.1,sourceWrite slot child.this second (sourceWrite slot parent.this first s.2))) := by
  simp only [sourceBody,Source.Hoare.run_bind,write_actual slot parent hp first s,
    write_actual slot child hc second (s.1,sourceWrite slot parent.this first s.2)]

/-- A static child is an actual Source halt after the first write, not a reset
of the entire caller. A later enclosing frame rollback is separately proved. -/
theorem source_static_child {E : Source.Env} {Γ : Source.RCtx} (slot : BoolSlot E)
    (parent child : Source.Fr) (hp : parent.static=false) (hc : child.static=true)
    (first second : Bool) (s : Source.EMState E Γ) :
    (sourceBody slot parent child first second).run s=
      (.error (.revert []),(s.1,sourceWrite slot parent.this first s.2)) := by
  simp only [sourceBody,Source.Hoare.run_bind,write_actual slot parent hp first s,
    write_static slot child hc second (s.1,sourceWrite slot parent.this first s.2)]

/-- Both source and target restore their complete original execution journals,
world/bank and machine prefixes. The Source statement above generates the exact
operations used here; no arbitrary outcome/run premise replaces it. -/
theorem paired_outer_rollback {E : Source.Env} (slot : BoolSlot E)
    (parent child : Source.Fr) (first second : Bool) (s : Source.St E) (t : State) :
    (s.ex.enter parent.this parent.sender parent.value parent.cd parent.static).rollback
      (sourceWrite slot child.this second (sourceWrite slot parent.this first s)).ex=s.ex ∧
    rollback t.journal.length
      (write (write t parent.this slot.key (boolWord first)) child.this slot.key (boolWord second))=t := by
  constructor
  · exact Source.rollback_run s.ex
      [.transient parent.this fun cells => cells.write slot.path (boolValue slot first),
       .transient child.this fun cells => cells.write slot.path (boolValue slot second)]
      parent.this parent.sender parent.value parent.cd parent.static
  · exact rollback_writes t [(parent.this,slot.key,boolWord first),(child.this,slot.key,boolWord second)]

/-- Actual independently executable target bodies under two supplied owners.
This is the interface G42 must connect to genuine CALL/DELEGATECALL contexts. -/
theorem target_callbacks (slotKey : Word) (parent child : Roadmap.Address)
    (first second : Bool) (t : State) :
    callback parent false (storeCode slotKey (boolWord first)) t=
      .ok (write t parent slotKey (boolWord first)) ∧
    callback child false (storeCode slotKey (boolWord second))
      (write t parent slotKey (boolWord first))=
      .ok (write (write t parent slotKey (boolWord first)) child slotKey (boolWord second)) :=
  ⟨callback_store parent _ _ _,callback_store child _ _ _⟩

/-- Nonempty Source caller heap, local/function-local and event/log prior are
retained by the real two-write body. Full ordered prior lists are equal. -/
theorem source_body_fields {E : Source.Env} (slot : BoolSlot E) (parent child : Source.Fr)
    (first second : Bool) (s : Source.St E) :
    let after := sourceWrite slot child.this second (sourceWrite slot parent.this first s)
    after.ex.world=s.ex.world ∧ after.heap=s.heap ∧ after.events=s.events ∧
    after.logs=s.logs ∧ after.fnLocals=s.fnLocals := ⟨rfl,rfl,rfl,rfl,rfl⟩


theorem executed_outer_rollback {E : Source.Env} {Γ : Source.RCtx} (slot : BoolSlot E)
    (parent child : Source.Fr) (hp : parent.static=false) (hc : child.static=false)
    (first second : Bool) (s : Source.EMState E Γ) (t : State) :
    (sourceBody slot parent child first second).run s=
      (.ok (),(s.1,sourceWrite slot child.this second (sourceWrite slot parent.this first s.2))) ∧
    (s.2.ex.enter parent.this parent.sender parent.value parent.cd parent.static).rollback
      (sourceWrite slot child.this second (sourceWrite slot parent.this first s.2)).ex=s.2.ex ∧
    rollback t.journal.length
      (write (write t parent.this slot.key (boolWord first)) child.this slot.key (boolWord second))=t :=
  ⟨source_body_exact slot parent child hp hc first second s,
   paired_outer_rollback slot parent child first second s.2 t⟩

/-- Full Source machine restoration for the actually executed transient-only
body. No general heap/local restoration is inferred for arbitrary callees. -/
theorem source_full_rollback {E : Source.Env} {Γ : Source.RCtx} (slot : BoolSlot E)
    (parent child : Source.Fr) (hp : parent.static=false) (hc : child.static=false)
    (first second : Bool) (s : Source.EMState E Γ) (t : State) :
    (sourceBody slot parent child first second).run s=
      (.ok (),(s.1,sourceWrite slot child.this second (sourceWrite slot parent.this first s.2))) ∧
    (s.1,{sourceWrite slot child.this second (sourceWrite slot parent.this first s.2) with
      ex := (s.2.ex.enter parent.this parent.sender parent.value parent.cd parent.static).rollback
        (sourceWrite slot child.this second (sourceWrite slot parent.this first s.2)).ex})=s ∧
    rollback t.journal.length
      (write (write t parent.this slot.key (boolWord first)) child.this slot.key (boolWord second))=t := by
  refine ⟨source_body_exact slot parent child hp hc first second s,?_,
    (paired_outer_rollback slot parent child first second s.2 t).2⟩
  have restored := (paired_outer_rollback slot parent child first second s.2 t).1
  change (s.1,{ s.2 with
    ex := (s.2.ex.enter parent.this parent.sender parent.value parent.cd parent.static).rollback
      (sourceWrite slot child.this second (sourceWrite slot parent.this first s.2)).ex })=s
  rw [restored]

end Solidity.Backend.Transient
