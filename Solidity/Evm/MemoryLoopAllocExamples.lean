import Solidity.Evm.MemoryLoopExamples

/-! Actual allocation in a reached loop turn, including allocation before revert. -/
namespace Solidity.Evm.Memory.LoopAllocExamples

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
private def program : Prog C Γ Γ := .cons (.loop .auto condition body) .nil
private def compiled : Loops.CompiledProg 1 (Frag.init Γ) program :=
  (Loops.compileProg 1 (Frag.init Γ) program).get (by decide +kernel)
private def publicResult : Compiler.Compilation 1 (Frag.init Γ) program :=
  (Compiler.compile 1 (Frag.init Γ) program).get (by decide +kernel)

private theorem public_shape : publicResult = .memoryLoops compiled := rfl
attribute [irreducible] publicResult

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

/-- The capacity premise is inhabited for a reached allocation, not just for zero turns. -/
theorem public_simulates : publicResult.Agrees 1 6 bases σ machine := by
  apply publicResult.correct
  rw [public_shape]
  change StateRepr 1 1 6 (Frag.init Γ) σ bases machine ∧
    1 + compiled.cert.need ≤ 6 ∧ Loops.Room compiled.cert 6 σ bases machine
  refine ⟨initial.1, by decide +kernel, ?_⟩
  exact Loops.room_singleton conditionCompiled.cert bodyCompiled.cert (by decide +kernel) loop_room

private def sourceObserve (r : TRes (Solidity.Out C [] Γ)) : Option (Int × Nat) :=
  match r with
  | .ok o => some ((TEnv.get (.here : Idx Γ (.val .uint)) o.st.env).1, o.st.H.length)
  | .error _ => none
private def targetObserve (r : Out) : Option (List Nat) :=
  match r with
  | .ok m _ => [m.mem 0, m.mem 1, m.mem 2, m.mem 5, m.mem 16].mapM fun w =>
      match w with | .val n => some n.val | _ => none
  | _ => none

/-- One fresh empty array survives scope exit; cursor advances by exactly one. -/
example : publicResult.isMemoryLoops = true := by decide +kernel
/-- info: (some (0, 1), some [17, 0, 16, 99, 0]) -/
#guard_msgs in
#eval (sourceObserve (program.run σ), targetObserve (run publicResult.code machine))

private def failingBody : Prog C Γ Δ := .cons allocate (.cons .revert .nil)
private def failingBodyCompiled : Memory.CompiledProg 1 (Frag.init Γ) failingBody :=
  (Memory.compileProg 1 (Frag.init Γ) failingBody).get (by decide +kernel)
private def failingProgram : Prog C Γ Γ := .cons (.loop .auto condition failingBody) .nil
private def failingCompiled : Loops.CompiledProg 1 (Frag.init Γ) failingProgram :=
  (Loops.compileProg 1 (Frag.init Γ) failingProgram).get (by decide +kernel)
private def failingPublic : Compiler.Compilation 1 (Frag.init Γ) failingProgram :=
  (Compiler.compile 1 (Frag.init Γ) failingProgram).get (by decide +kernel)

private theorem failing_shape : failingPublic = .memoryLoops failingCompiled := rfl
attribute [irreducible] failingPublic

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

/-- An allocation reached before revert is included in the public capacity premise. -/
theorem allocation_before_revert_simulates : failingPublic.Agrees 1 6 bases σ machine := by
  apply failingPublic.correct
  rw [failing_shape]
  change StateRepr 1 1 6 (Frag.init Γ) σ bases machine ∧
    1 + failingCompiled.cert.need ≤ 6 ∧ Loops.Room failingCompiled.cert 6 σ bases machine
  exact ⟨initial.1, by decide +kernel,
    Loops.room_singleton conditionCompiled.cert failingBodyCompiled.cert (by decide +kernel) failing_room⟩

private def sourceReverts {α : Type} : TRes α → Bool
  | .error .revert => true
  | _ => false
private def targetReverts : Out → Bool
  | .revert => true
  | _ => false
/-- info: (true, true) -/
#guard_msgs in
#eval (sourceReverts (failingProgram.run σ), targetReverts (run failingPublic.code machine))

/-- Reserving just the loop's final context would miss the array local. -/
example : compiled.cert.need = 2 := by decide +kernel
example : ¬ 1 + compiled.cert.need ≤ 2 := by decide +kernel

private def fullMachine : Machine := {machine with mem := upd machine.mem 0 (.val wMax)}

/-- Finite-word capacity cannot be faked at the last cursor word. -/
theorem full_cursor_refused : ¬ AllocationInput 1 6 1 σ bases fullMachine := by
  intro ha
  rcases ha with hz | ⟨hb, c, hr, hs⟩
  · cases hz
  · have he : wMax = c := Word.val.inj hr.arrays.free.cell
    have hv : c.val = W - 1 := (congrArg Fin.val he).symm
    have hw : 0 < W := W_pos
    omega

/-- The actual reached allocating turn requires capacity even if it will revert. -/
theorem full_reverting_loop_refused : ¬ LoopRoom 1 6 condition failingBody σ bases fullMachine := by
  intro room
  have ha := room _ 0 LoopPrefix.start (show condition.evalT σ = .ok true from rfl)
  exact full_cursor_refused ha

#print axioms public_simulates
#print axioms allocation_before_revert_simulates
end Solidity.Evm.Memory.LoopAllocExamples
