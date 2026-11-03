import Solidity.Lowering.V07.ReferenceEffects
import Solidity.Lowering.V07.ContextMapWrite

/-! Actual reference assignment/read ordering with a complete mapped-local
frame. Every value relation is derived from initial ContextMap.Related and the
mapped positions. No desired reached-state relation or global heap-alias law
is supplied. Value agreement alone does not establish heap alias reflection.
This is a supported expression clause, not a general Source/elaborator producer. -/
namespace Solidity.Lowering.V07

/-- Both actual pipeline runs, semantic left/right reference captures and all
reached bindings. Dropping the two captures restores exactly the updated caller. -/
theorem related_reference_assignment_pair :
∀ {E : Source.Env} {srcΓ : Source.RCtx} {C : Contract} {Γ : Ctx}
 (G : Source.Glob E) (F : Source.Fr) (fuel : Nat)
 (source : Source.EMState E srcΓ) (target : State C Γ)
 (m : ContextMap srcΓ Γ)
 (Rel : (τ : Source.STy) → (u : LTy) → Source.Val E.layout τ → u.TDenote C target.H → Prop)
 (aligned : m.Related Rel source.1 target.env)
 (i a : Source.Idx srcΓ (.bytes .memory)) (j b : Idx Γ (.mem bytesR))
 (oldAddress newAddress : Nat) (old assigned : HRef target.H bytesR)
 (writeMap : m.slot i = ⟨.mem bytesR,j⟩) (readMap : m.slot a = ⟨.mem bytesR,b⟩)
 (readI : source.1.get i = .memRef rfl oldAddress) (readA : source.1.get a = .memRef rfl newAddress)
 (targetI : TEnv.get j target.env = some old) (targetA : TEnv.get b target.env = some assigned),
 (Source.evalPair G F (fuel+3) (.assign (.local i) (.local a)) (.local i)).run source =
   (.ok (.val (.memRef rfl newAddress),.val (.memRef rfl (if G.pipeline = .legacy then oldAddress else newAddress))),
     (source.1.set i (.memRef rfl newAddress),source.2)) ∧
 (memoryAssignReadPrefix G.pipeline j b rfl).run target =
   .ok (⟨((target.setLocal j (some assigned)).push (t := .mem bytesR)
     (some (if G.pipeline = .legacy then old else assigned))).push (t := .mem bytesR) (some assigned),List.prefix_refl _⟩) ∧
 Rel (.bytes .memory) (.mem bytesR) (.memRef rfl newAddress) (some assigned) ∧
 Rel (.bytes .memory) (.mem bytesR)
   (.memRef rfl (if G.pipeline = .legacy then oldAddress else newAddress))
   (some (if G.pipeline = .legacy then old else assigned)) ∧
 ((m.wk (Thin.drop (t := .mem bytesR) .refl)).wk
   (Thin.drop (t := .mem bytesR) .refl)).Related Rel
   (source.1.set i (.memRef rfl newAddress))
   (((target.setLocal j (some assigned)).push (t := .mem bytesR)
     (some (if G.pipeline = .legacy then old else assigned))).push (t := .mem bytesR) (some assigned)).env ∧
 (((target.setLocal j (some assigned)).push (t := .mem bytesR)
   (some (if G.pipeline = .legacy then old else assigned))).push (t := .mem bytesR) (some assigned)).drop
     (.push (.push .refl)) = target.setLocal j (some assigned) ∧
 (((target.setLocal j (some assigned)).push (t := .mem bytesR)
   (some (if G.pipeline = .legacy then old else assigned))).push (t := .mem bytesR) (some assigned)).glob = target.glob := by
  intro E srcΓ C Γ G F fuel source target m Rel aligned i a j b oldAddress newAddress old assigned writeMap readMap readI readA targetI targetA
  have oldRel : Rel (.bytes .memory) (.mem bytesR) (.memRef rfl oldAddress) (some old) := by
    simpa only [readI,targetI] using (ContextMap.value_at m Rel source.1 target.env aligned i j writeMap)
  have newRel : Rel (.bytes .memory) (.mem bytesR) (.memRef rfl newAddress) (some assigned) := by
    simpa only [readA,targetA] using (ContextMap.value_at m Rel source.1 target.env aligned a b readMap)
  have rightRel : Rel (.bytes .memory) (.mem bytesR)
      (.memRef rfl (if G.pipeline = .legacy then oldAddress else newAddress))
      (some (if G.pipeline = .legacy then old else assigned)) := by
    cases G.pipeline
    · exact oldRel
    · exact newRel
  have post : m.Related Rel (source.1.set i (.memRef rfl newAddress))
      (TEnv.set j (some assigned) target.env) := ContextMap.related_write m Rel source.1 target.env aligned i j writeMap
    (.memRef rfl newAddress) (some assigned) newRel
  have one : (m.wk (Thin.drop (t := .mem bytesR) .refl)).Related Rel
      (source.1.set i (.memRef rfl newAddress))
      ((target.setLocal j (some assigned)).push (t := .mem bytesR)
        (some (if G.pipeline = .legacy then old else assigned))).env := memory_capture_context m (target.setLocal j (some assigned)) Rel
    (source.1.set i (.memRef rfl newAddress)) post (if G.pipeline = .legacy then old else assigned)
  have two : ((m.wk (Thin.drop (t := .mem bytesR) .refl)).wk
      (Thin.drop (t := .mem bytesR) .refl)).Related Rel
      (source.1.set i (.memRef rfl newAddress))
      (((target.setLocal j (some assigned)).push (t := .mem bytesR)
        (some (if G.pipeline = .legacy then old else assigned))).push (t := .mem bytesR) (some assigned)).env := memory_capture_context
    (m.wk (Thin.drop (t := .mem bytesR) .refl))
    ((target.setLocal j (some assigned)).push (t := .mem bytesR) (some (if G.pipeline = .legacy then old else assigned)))
    Rel (source.1.set i (.memRef rfl newAddress)) one assigned
  have src := source_assign_read_pair G F fuel source i a
    (.memRef rfl newAddress) (.memRef rfl oldAddress) readA readI
  refine ⟨?_,memory_assign_read_prefix_run G.pipeline target j b rfl old assigned targetI targetA,
    newRel,rightRel,two,rfl,rfl⟩
  cases order : G.pipeline <;> simpa only [order,reduceCtorEq,if_true,if_false] using src

end Solidity.Lowering.V07
