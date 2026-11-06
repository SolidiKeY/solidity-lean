import Solidity.Evm.MemoryLoopFiniteHorizon
import Solidity.Evm.MemoryLoopAllocExamples

/-! Finite capacity for a genuinely unbounded allocating source loop.
These are owner-model controls, not source/Yul/EVM compiler correspondence. -/
namespace Solidity.Evm.Memory.FiniteHorizonControls
private def C : Contract := contract!{ }
private def Γ : Ctx := [.val .uint]
private def R : RefTy := .array (.prim .uint)
private def Δ : Ctx := .mem R :: Γ
private def σ : State C Γ := (State.init C).push (t := .val .uint) (indexValue ⟨2, by decide⟩)
private def bases : Nat → Fin W := fun _ => ⟨0, W_pos⟩
private def machine : Machine :=
  { Machine.init with mem := fun a =>
      if a = 0 then w[16] else if a = 1 then w[2] else if a = 5 then w[99] else w[0] }
private def cursor : Fin W := ⟨16, by decide⟩
private theorem initial : StateRepr 1 1 6 (Frag.init Γ) σ bases machine ∧
    StructAllocatorRepr σ.heap bases 6 cursor machine := AllocSourceExamples.initial_repr

private def condition : Val C Γ .bool := .simple (.bool true)
private def allocate : Stmt C Γ Δ :=
  .declMem R (.user "fresh") (some (.newArr (.lit 0 rfl) rfl)) rfl rfl
private def body : Prog C Γ Δ := .cons allocate .nil
private def bodyCompiled : CompiledProg 1 (Frag.init Γ) body :=
  (Memory.compileProg 1 (Frag.init Γ) body).get (by decide +kernel)
private def conditionCompiled : CompiledVal 1 (Frag.init Γ) condition :=
  (Memory.compileVal 1 (Frag.init Γ) condition).get (by decide +kernel)
private def cert : LoopCert 1 (Frag.init Γ) condition body
    conditionCompiled.code bodyCompiled.code :=
  ⟨conditionCompiled.cert, bodyCompiled.frag, bodyCompiled.cert, by decide +kernel⟩

private theorem body_cost (τ : State C Γ) : allocationCostProg body τ = 1 := rfl
private theorem body_run (τ : State C Γ) :
    body.run τ = .ok ⟨τ.allocPush (defaultArray .uint ⟨0, W_pos⟩), List.prefix_append _ _⟩ := by
  have h : allocate.run τ = .ok ⟨τ.allocPush (defaultArray .uint ⟨0, W_pos⟩),
      List.prefix_append _ _⟩ :=
    newArray_decl τ .uint (.lit 0 rfl) ⟨0, W_pos⟩ rfl
  change (Prog.cons allocate .nil).run τ = _
  rw [Prog.run_cons_ok h]
  rfl

private theorem prefix_cost {o : Solidity.Out C σ.H Γ} {cost turns : Nat}
    (h : CountedLoopPrefix condition body σ o cost turns) : cost = turns := by
  induction h with
  | start => rfl
  | next hp hc hs ih => rw [ih, body_cost]

/-- Source prefixes exist constructively at every count, without requiring
physical allocator capacity or enumerating a bounded test domain. -/
private theorem prefixes (n : Nat) :
    ∃ o, CountedLoopPrefix condition body σ o n n := by
  induction n with
  | zero => exact ⟨_, .start⟩
  | succ n ih =>
    obtain ⟨o, hp⟩ := ih
    have h := CountedLoopPrefix.next hp
      (show condition.evalT o.st = .ok true from rfl) (body_run o.st)
    rw [body_cost] at h
    exact ⟨_, h⟩

/-- The strict bound is exactly the owner's initial cursor plus reached cost,
not an arbitrary decoder, root-count, or language restriction. -/
theorem finite_room (n : Nat) (fits : 16 + n < W) :
    FiniteLoopRoom 1 6 condition body σ bases machine n := by
  intro o cost turns hp ht _
  have he : cost = turns := prefix_cost hp
  refine .inr ⟨by decide, cursor, initial.2, ?_⟩
  change 16 + (cost + allocationCostProg body o.st) < W
  rw [body_cost, he]
  omega

/-- This is strictly more useful than assuming the old all-prefix room:
its source has reachable prefixes beyond any finite physical capacity. -/
theorem no_infinite_room : ¬ LoopRoom 1 6 condition body σ bases machine := by
  intro room
  obtain ⟨o, hp⟩ := prefixes W
  have ha := room o W hp.forget (show condition.evalT o.st = .ok true from rfl)
  rw [body_cost] at ha
  rcases ha with hz | ⟨_, c, _, hs⟩
  · omega
  · omega

theorem finite_transport (n : Nat) (fits : 16 + n < W) :
    CountedHorizonRelation 1 1 6 (Frag.init Γ) condition body σ bases machine n
      (TLoop.iterN (horizonBody body) (fun o => condition.evalT o.st) n ⟨σ, List.prefix_refl _⟩)
      (loopIterN (fun m => exec conditionCompiled.code 0 m)
        (fun m => exec bodyCompiled.code 0 m) n machine) :=
  cert.correct_finite_horizon n initial.1 (by decide +kernel) (finite_room n fits)

private def stopCondition : Val C Γ .bool := .simple (.bool false)
private def stopCompiled : CompiledVal 1 (Frag.init Γ) stopCondition :=
  (Memory.compileVal 1 (Frag.init Γ) stopCondition).get (by decide +kernel)
private def stopCert : LoopCert 1 (Frag.init Γ) stopCondition body
    stopCompiled.code bodyCompiled.code :=
  ⟨stopCompiled.cert, bodyCompiled.frag, bodyCompiled.cert, by decide +kernel⟩
private theorem stop_room (n : Nat) : FiniteLoopRoom 1 6 stopCondition body σ bases machine n := by
  intro _ _ _ _ _ h
  cases h
/-- An unreachable allocating body demands no allocation room, at any horizon. -/
theorem stop_transport (n : Nat) :
    CountedHorizonRelation 1 1 6 (Frag.init Γ) stopCondition body σ bases machine n
      (TLoop.iterN (horizonBody body) (fun o => stopCondition.evalT o.st) n ⟨σ, List.prefix_refl _⟩)
      (loopIterN (fun m => exec stopCompiled.code 0 m)
        (fun m => exec bodyCompiled.code 0 m) n machine) :=
  stopCert.correct_finite_horizon n initial.1 (by decide +kernel) (stop_room n)

private def fullMachine : Machine := {machine with mem := upd machine.mem 0 (.val wMax)}
/-- Preparation capacity failure is not a source/Yul execution verdict. -/
theorem full_cursor_no_finite_room : ¬ FiniteLoopRoom 1 6 condition body σ bases fullMachine 1 := by
  intro room
  exact LoopAllocExamples.full_cursor_refused
    (room _ 0 0 .start (by decide) (show condition.evalT σ = .ok true from rfl))

private def sourceObservation : Solidity.Out C [] Γ ⊕ TRes (Solidity.Out C [] Γ) → String
  | .inl o => "pending:" ++ toString o.st.H.length
  | .inr (.ok o) => "done:" ++ toString o.st.H.length
  | .inr (.error _) => "unexpected error"
private def cursorValue (m : Machine) : Option Nat :=
  match m.mem 0 with | .val n => some n.val | _ => none
private def targetObservation : Machine ⊕ Out → String × Option Nat
  | .inl m => ("pending", cursorValue m)
  | .inr (.ok m _) => ("done", cursorValue m)
  | .inr _ => ("error", none)
/-- info: ["pending:0", "pending:1", "pending:2", "pending:3"] -/
#guard_msgs in
#eval [0,1,2,3].map fun n => sourceObservation
  (TLoop.iterN (horizonBody body) (fun o => condition.evalT o.st) n ⟨σ, List.prefix_refl _⟩)
/-- info: [("pending", some 16), ("pending", some 17), ("pending", some 18), ("pending", some 19)] -/
#guard_msgs in
#eval [0,1,2,3].map fun n => targetObservation
  (loopIterN (fun m => exec conditionCompiled.code 0 m)
    (fun m => exec bodyCompiled.code 0 m) n machine)

/-- info: ["pending:0", "done:0", "done:0"] -/
#guard_msgs in
#eval [0,1,2].map fun n => sourceObservation
  (TLoop.iterN (horizonBody body) (fun o => stopCondition.evalT o.st) n ⟨σ, List.prefix_refl _⟩)
/-- info: [("pending", some 16), ("done", some 16), ("done", some 16)] -/
#guard_msgs in
#eval [0,1,2].map fun n => targetObservation
  (loopIterN (fun m => exec stopCompiled.code 0 m)
    (fun m => exec bodyCompiled.code 0 m) n machine)

end Solidity.Evm.Memory.FiniteHorizonControls
