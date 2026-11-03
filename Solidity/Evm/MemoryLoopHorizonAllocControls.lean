import Solidity.Evm.MemoryLoopHorizon
import Solidity.Evm.MemoryLoopAllocExamples

/-! Reached allocation, exact cursor growth, and allocation-before-revert
finite-horizon controls. Reuses the owner allocator witness definitionally. -/
namespace Solidity.Evm.Memory.HorizonAllocControls
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
private def condition : Val C Γ .bool :=
  .binop .gt rfl rfl (.simple (.local .here)) (.simple (.lit 0 rfl))
private def allocate : Stmt C Γ Δ :=
  .declMem R (.user "fresh") (some (.newArr (.lit 0 rfl) rfl)) rfl rfl
private def reset : Stmt C Δ Δ := .assignLocal (.there .here) (.simple (.lit 0 rfl))
private def body : Prog C Γ Δ := .cons allocate (.cons reset .nil)
private def bodyCompiled : Memory.CompiledProg 1 (Frag.init Γ) body :=
  (Memory.compileProg 1 (Frag.init Γ) body).get (by decide +kernel)
private def conditionCompiled : CompiledVal 1 (Frag.init Γ) condition :=
  (Memory.compileVal 1 (Frag.init Γ) condition).get (by decide +kernel)
private theorem body_stops (τ : State C Γ) (o : Solidity.Out C τ.H Δ)
    (ho : body.run τ = .ok o) : condition.evalT (o.st.drop body.ext) = .ok false := by
  have hd : allocate.run τ = .ok ⟨τ.allocPush (defaultArray .uint ⟨0, W_pos⟩),
      List.prefix_append _ _⟩ := newArray_decl τ .uint (.lit 0 rfl) ⟨0, W_pos⟩ rfl
  change (Prog.cons allocate (.cons reset .nil)).run τ = .ok o at ho
  rw [Prog.run_cons_ok hd] at ho
  change Except.ok ⟨(τ.allocPush (defaultArray .uint ⟨0, W_pos⟩)).setLocal
    (.there .here) (indexValue ⟨0, W_pos⟩), List.prefix_append _ _⟩ = .ok o at ho
  cases ho
  rfl

private theorem loop_room : LoopRoom 1 6 condition body σ bases machine :=
  loopRoom_one_turn condition body σ bases machine body_stops
    (.inr ⟨by decide, cursor, initial.2, by decide +kernel⟩)

private def failingBody : Prog C Γ Δ := .cons allocate (.cons .revert .nil)
private def failingBodyCompiled : Memory.CompiledProg 1 (Frag.init Γ) failingBody :=
  (Memory.compileProg 1 (Frag.init Γ) failingBody).get (by decide +kernel)
private theorem failingBody_reverts (τ : State C Γ) : failingBody.run τ = .error .revert := by
  have hd : allocate.run τ = .ok ⟨τ.allocPush (defaultArray .uint ⟨0, W_pos⟩),
      List.prefix_append _ _⟩ := newArray_decl τ .uint (.lit 0 rfl) ⟨0, W_pos⟩ rfl
  change (Prog.cons allocate (.cons .revert .nil)).run τ = .error .revert
  rw [Prog.run_cons_ok hd]
  rfl

private theorem failing_room : LoopRoom 1 6 condition failingBody σ bases machine := by
  apply loopRoom_one_turn condition failingBody σ bases machine
  · intro τ o ho
    rw [failingBody_reverts] at ho
    cases ho
  · exact .inr ⟨by decide, cursor, initial.2, by decide +kernel⟩


private def cert : LoopCert 1 (Frag.init Γ) condition body conditionCompiled.code bodyCompiled.code :=
  ⟨conditionCompiled.cert, bodyCompiled.frag, bodyCompiled.cert, by decide +kernel⟩
private def failingCert : LoopCert 1 (Frag.init Γ) condition failingBody
    conditionCompiled.code failingBodyCompiled.code :=
  ⟨conditionCompiled.cert, failingBodyCompiled.frag, failingBodyCompiled.cert, by decide +kernel⟩

theorem allocation_horizons (n : Nat) :
    HorizonRelation 1 1 6 (Frag.init Γ) condition body σ bases machine
      (TLoop.iterN (horizonBody body) (fun o => condition.evalT o.st) n ⟨σ, List.prefix_refl _⟩)
      (loopIterN (fun m => exec conditionCompiled.code 0 m)
        (fun m => exec bodyCompiled.code 0 m) n machine) :=
  cert.correct_horizon initial.1 (by decide +kernel) loop_room n

theorem allocating_revert_horizons (n : Nat) :
    HorizonRelation 1 1 6 (Frag.init Γ) condition failingBody σ bases machine
      (TLoop.iterN (horizonBody failingBody) (fun o => condition.evalT o.st) n ⟨σ, List.prefix_refl _⟩)
      (loopIterN (fun m => exec conditionCompiled.code 0 m)
        (fun m => exec failingBodyCompiled.code 0 m) n machine) :=
  failingCert.correct_horizon initial.1 (by decide +kernel) failing_room n

private def sourceObservation : Solidity.Out C [] Γ ⊕ TRes (Solidity.Out C [] Γ) → String
  | .inl o => "pending:" ++ toString o.st.H.length
  | .inr (.ok o) => "done:" ++ toString o.st.H.length
  | .inr (.error .revert) => "revert"
  | .inr (.error _) => "other error"
/-- info: ["pending:0", "pending:1", "done:1"] -/
#guard_msgs in
#eval [0,1,2].map fun n => sourceObservation
  (TLoop.iterN (horizonBody body) (fun o => condition.evalT o.st) n ⟨σ, List.prefix_refl _⟩)

/-- info: ["revert", "revert"] -/
#guard_msgs in
#eval [1,2].map fun n => sourceObservation
  (TLoop.iterN (horizonBody failingBody) (fun o => condition.evalT o.st) n ⟨σ, List.prefix_refl _⟩)

private def cursorValue (m : Machine) : Option Nat :=
  match m.mem 0 with | .val n => some n.val | _ => none
private def targetObservation : Machine ⊕ Out → String × Option Nat
  | .inl m => ("pending", cursorValue m)
  | .inr (.ok m _) => ("done", cursorValue m)
  | .inr .revert => ("revert", none)
  | .inr _ => ("other error", none)
/-- info: [("pending", some 16), ("pending", some 17), ("done", some 17)] -/
#guard_msgs in
#eval [0,1,2].map fun n => targetObservation
  (loopIterN (fun m => exec conditionCompiled.code 0 m)
    (fun m => exec bodyCompiled.code 0 m) n machine)
/-- info: [("revert", none), ("revert", none)] -/
#guard_msgs in
#eval [1,2].map fun n => targetObservation
  (loopIterN (fun m => exec conditionCompiled.code 0 m)
    (fun m => exec failingBodyCompiled.code 0 m) n machine)

end Solidity.Evm.Memory.HorizonAllocControls
