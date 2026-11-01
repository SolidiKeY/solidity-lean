import Solidity.Evm.MemoryLoopExamples
import Solidity.Evm.MemoryLoopScopeBudget
import Solidity.Evm.MemoryLoopScopeDivergenceExamples

/-! Actual allocation in a reached loop turn, including allocation before revert. -/
namespace Solidity.Evm.Memory.LoopScopeAllocExamples

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
private def wrappedProgram : Prog C Γ Γ := .cons (.ite (.simple (.bool true)) program .nil) .nil
private def wrappedCompiled := (LoopScopes.compileProg 1 wrappedProgram (Frag.init Γ)).get (by decide +kernel)
private def publicResult : Compiler.Compilation 1 (Frag.init Γ) wrappedProgram :=
  (Compiler.compile 1 (Frag.init Γ) wrappedProgram).get (by decide +kernel)

private theorem public_shape : publicResult = .memoryLoopScopes wrappedCompiled := rfl
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
    1 + wrappedCompiled.cert.need ≤ 6 ∧ LoopScopes.Room wrappedCompiled.cert 6 σ bases machine
  refine ⟨initial.1, by decide +kernel, ?_⟩
  apply LoopScopes.room_ite_true
  · rfl
  · apply LoopScopes.room_base_singleton
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
example : publicResult.isMemoryLoopScopes = true := by decide +kernel
/-- info: (some (0, 1), some [17, 0, 16, 99, 0]) -/
#guard_msgs in
#eval (sourceObserve (wrappedProgram.run σ), targetObserve (run publicResult.code machine))

private def failingBody : Prog C Γ Δ := .cons allocate (.cons .revert .nil)
private def failingBodyCompiled : Memory.CompiledProg 1 (Frag.init Γ) failingBody :=
  (Memory.compileProg 1 (Frag.init Γ) failingBody).get (by decide +kernel)
private def failingProgram : Prog C Γ Γ := .cons (.loop .auto condition failingBody) .nil
private def failingCompiled : Loops.CompiledProg 1 (Frag.init Γ) failingProgram :=
  (Loops.compileProg 1 (Frag.init Γ) failingProgram).get (by decide +kernel)
private def wrappedFailing : Prog C Γ Γ := .cons (.ite (.simple (.bool true)) failingProgram .nil) .nil
private def wrappedFailingCompiled := (LoopScopes.compileProg 1 wrappedFailing (Frag.init Γ)).get (by decide +kernel)
private def failingPublic : Compiler.Compilation 1 (Frag.init Γ) wrappedFailing :=
  (Compiler.compile 1 (Frag.init Γ) wrappedFailing).get (by decide +kernel)

private theorem failing_shape : failingPublic = .memoryLoopScopes wrappedFailingCompiled := rfl
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
    1 + wrappedFailingCompiled.cert.need ≤ 6 ∧ LoopScopes.Room wrappedFailingCompiled.cert 6 σ bases machine
  refine ⟨initial.1, by decide +kernel, ?_⟩
  apply LoopScopes.room_ite_true
  · rfl
  · apply LoopScopes.room_base_singleton
    exact Loops.room_singleton conditionCompiled.cert failingBodyCompiled.cert (by decide +kernel) failing_room

private def sourceReverts {α : Type} : TRes α → Bool
  | .error .revert => true
  | _ => false
private def targetReverts : Out → Bool
  | .revert => true
  | _ => false
/-- info: (true, true) -/
#guard_msgs in
#eval (sourceReverts (wrappedFailing.run σ), targetReverts (run failingPublic.code machine))

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

private def blockTemp : Stmt C Γ (.val .uint :: Γ) :=
  .declLocal .uint (.user "temporary") (some (.simple (.lit 7 rfl)))
private def blockBody : Prog C Γ (.val .uint :: Γ) :=
  .cons (.loop .auto condition body)
    (.cons blockTemp .nil)
private def blockProgram : Prog C Γ Γ := .cons (.block blockBody) .nil
private def blockTempCompiled := (Memory.compileStmt 1 (Frag.init Γ) blockTemp).get (by decide +kernel)
private def blockLoopCert : Loops.StmtCert 1 (Frag.init Γ) (Frag.init Γ)
    (.loop .auto condition body) [.loop conditionCompiled.code bodyCompiled.code] :=
  .loop .auto condition body conditionCompiled.code bodyCompiled.code bodyCompiled.frag
    conditionCompiled.cert bodyCompiled.cert (by decide +kernel)
private def blockInnerCert : LoopScopes.ProgCert 1 (Frag.init Γ) blockTempCompiled.frag blockBody
    ([.loop conditionCompiled.code bodyCompiled.code] ++ (blockTempCompiled.code ++ [])) :=
  .cons (.base blockLoopCert) (.cons (.base (.finite blockTempCompiled.cert)) (.nil _))
/-- Share the checked components instead of normalizing an entire computed certificate twice. -/
private def blockCompiled : LoopScopes.CompiledProg 1 (Frag.init Γ) blockProgram :=
  ⟨blockTempCompiled.frag.restrict Γ, _,
    .cons (.block blockInnerCert) (.nil _)⟩
private def blockPublic : Compiler.Compilation 1 (Frag.init Γ) blockProgram :=
  .memoryLoopScopes blockCompiled
private theorem block_shape : blockPublic = .memoryLoopScopes blockCompiled := rfl
attribute [irreducible] blockPublic
private def blockAutomatic := (Compiler.compile 1 (Frag.init Γ) blockProgram).get (by decide +kernel)
example : blockAutomatic.isMemoryLoopScopes = true := by decide +kernel

private theorem block_compiles :
    LoopScopes.compileProg 1 blockProgram (Frag.init Γ) = some blockCompiled := by
  have hc : Memory.compileVal 1 (Frag.init Γ) condition = some conditionCompiled :=
    (Option.some_get _).symm
  have hb : Memory.compileProg 1 (Frag.init Γ) body = some bodyCompiled :=
    (Option.some_get _).symm
  have ht : Memory.compileStmt 1 (Frag.init Γ) blockTemp = some blockTempCompiled :=
    (Option.some_get _).symm
  have stable : bodyCompiled.frag.restrict Γ = Frag.init Γ := by decide +kernel
  unfold blockProgram blockBody
  rw [LoopScopes.compileProg_cons, LoopScopes.compileStmt_block,
    LoopScopes.compileProg_cons, LoopScopes.compileStmt_loop, LoopScopes.compile_loop_clause,
    hc, hb]
  simp only [bind, Option.bind, pure, dif_pos stable]
  unfold blockTemp at ht ⊢
  rw [LoopScopes.compileProg_cons, LoopScopes.compileStmt_declLocal, ht]
  simp only [bind, Option.bind, pure, LoopScopes.compileProg_nil]
  rfl

private theorem automatic_block_result : blockAutomatic = blockPublic := by
  unfold blockPublic
  have hcore : inFragP (Frag.init Γ) blockProgram = none := by decide +kernel
  have hmem : Memory.compileProg 1 (Frag.init Γ) blockProgram = none :=
    Option.eq_none_of_isNone (by decide +kernel)
  have hloops : Loops.compileProg 1 (Frag.init Γ) blockProgram = none :=
    Option.eq_none_of_isNone (by decide +kernel)
  have hc : Compiler.compile 1 (Frag.init Γ) blockProgram =
      some (Compiler.Compilation.memoryLoopScopes blockCompiled) := by
    unfold Compiler.compile
    split
    next frag hfrag =>
      rw [hcore] at hfrag
      cases hfrag
    next hnone =>
      rw [hmem, hloops, block_compiles]
      rfl
  have he : blockAutomatic = Compiler.Compilation.memoryLoopScopes blockCompiled :=
    Option.some.inj ((Option.some_get _).trans hc)
  exact he

private theorem automatic_block_code : blockAutomatic.code = blockPublic.code :=
  congrArg Compiler.Compilation.code automatic_block_result

/-- Allocation survives the typed outer block's local-context drop. -/
theorem block_allocation_simulates : blockPublic.Agrees 1 6 bases σ machine := by
  apply blockPublic.correct
  rw [block_shape]
  change StateRepr 1 1 6 (Frag.init Γ) σ bases machine ∧
    1 + blockCompiled.cert.need ≤ 6 ∧ LoopScopes.Room blockCompiled.cert 6 σ bases machine
  refine ⟨initial.1, by decide +kernel, ?_⟩
  apply LoopScopes.room_block
  apply LoopScopes.room_cons_base_nonallocating
  · decide +kernel
  · exact Loops.room_singleton conditionCompiled.cert bodyCompiled.cert (by decide +kernel) loop_room

theorem automatic_block_simulates : blockAutomatic.Agrees 1 6 bases σ machine := by
  rw [automatic_block_result]
  exact block_allocation_simulates

/-- info: (some (0, 1), some [17, 0, 7, 99, 0]) -/
#guard_msgs in
#eval (sourceObserve (blockProgram.run σ), targetObserve (run blockPublic.code machine))

private def skippedProgram : Prog C Γ Γ :=
  .cons (.ite (.simple (.bool false)) program .nil) .nil
private def skippedCompiled := (LoopScopes.compileProg 1 skippedProgram (Frag.init Γ)).get (by decide +kernel)
private def skippedPublic := (Compiler.compile 1 (Frag.init Γ) skippedProgram).get (by decide +kernel)
private theorem skipped_shape : skippedPublic = .memoryLoopScopes skippedCompiled := rfl
attribute [irreducible] skippedPublic

/-- An unselected allocating loop has no capacity demand, even at the last word. -/
theorem skipped_room_full : LoopScopes.Room skippedCompiled.cert 6 σ bases fullMachine := by
  apply LoopScopes.room_ite_false
  · rfl
  · exact LoopScopes.room_nonallocating _ rfl σ bases fullMachine

theorem skipped_simulates : skippedPublic.Agrees 1 6 bases σ machine := by
  apply skippedPublic.correct
  rw [skipped_shape]
  refine ⟨initial.1, by decide +kernel, ?_⟩
  apply LoopScopes.room_ite_false
  · rfl
  · exact LoopScopes.room_nonallocating _ rfl σ bases machine

/-- info: (some (2, 0), some [16, 2, 0, 99, 0]) -/
#guard_msgs in
#eval (sourceObserve (skippedProgram.run σ), targetObserve (run skippedPublic.code machine))
example : blockCompiled.cert.need = 2 := by decide +kernel
example : ¬ 1 + blockCompiled.cert.need ≤ 2 := by decide +kernel
example : skippedCompiled.cert.allocates = true := by decide +kernel


example : blockBody.ext.depth = 1 := rfl

private theorem full_repr : StateRepr 1 1 6 (Frag.init Γ) σ bases fullMachine := by
  have hn {R : RefTy} (r : HRef [] R) : False := by cases r.get?
  have h := initial.1
  refine ⟨?_, ⟨fun r => (hn r).elim, fun r => (hn r).elim, fun r => (hn r).elim⟩,
    ?_, h.locals, ⟨fun r => (hn r).elim, fun r => (hn r).elim, fun r => (hn r).elim⟩,
    (fun _ r => (hn r).elim), RefFieldsRepr.withoutStructs _ _ _ (fun r => hn r)⟩
  · refine ⟨h.core.store, ?_, ?_, h.core.net, h.core.netSelf, h.core.bound,
      ?_, h.core.env, h.core.funds, h.core.oracle⟩
    · intro p i
      cases i with
      | here => exact ReprV.uint_of rfl
      | there i => nomatch i
    · intro R i hi
      cases i with | there i => nomatch i
    · intro R i hi
      cases i with | there i => nomatch i
  · intro R i
    cases i with | there i => nomatch i

theorem skipped_full_simulates : skippedPublic.Agrees 1 6 bases σ fullMachine := by
  apply skippedPublic.correct
  rw [skipped_shape]
  exact ⟨full_repr, by decide +kernel, skipped_room_full⟩

/-- info: (some (2, 0), true, true) -/
#guard_msgs in
#eval (sourceObserve (skippedProgram.run σ),
  match run skippedPublic.code fullMachine with | .ok m _ => m.mem 0 == Word.val wMax | _ => false,
  match run skippedPublic.code fullMachine with | .ok m _ => m.mem 1 == w[2] | _ => false)


private def spinningTail : Prog C Δ Δ :=
  .cons (.ite (.simple (.bool true)) (LoopScopeDivergenceExamples.trueSpin C Δ) .nil) .nil
private def allocatingSpin : Prog C Γ Δ := .cons allocate spinningTail
private def allocatingSpinPublic :=
  (Compiler.compile 1 (Frag.init Γ) allocatingSpin).get (by decide +kernel)
attribute [irreducible] allocatingSpinPublic
private def checkedAllocatingSpin := allocatingSpinPublic.memoryLoopScopesResult (by decide +kernel)

theorem allocating_prefix_diverges : allocatingSpin.run σ = .error .diverge := by
  let τ := σ.allocPush (defaultArray .uint ⟨0, W_pos⟩)
  have ha : allocate.run σ = .ok ⟨τ, List.prefix_append _ _⟩ :=
    newArray_decl σ .uint (.lit 0 rfl) ⟨0, W_pos⟩ rfl
  have ht : (Stmt.ite (.simple (.bool true)) (LoopScopeDivergenceExamples.trueSpin C Δ)
      (Prog.nil : Prog C Δ Δ)).run τ = .error .diverge := by
    change ((LoopScopeDivergenceExamples.trueSpin C Δ).run τ).map _ = _
    rw [LoopScopeDivergenceExamples.trueSpin_diverges (Θ := Δ) τ]
    rfl
  have hs : spinningTail.run τ = .error .diverge := by
    show TRun.seq (Stmt.ite (.simple (.bool true)) (LoopScopeDivergenceExamples.trueSpin C Δ)
      (Prog.nil : Prog C Δ Δ)).runR Prog.nil.runR τ = _
    simp only [TRun.seq, Stmt.run] at ht ⊢
    rw [ht]
  change (Prog.cons allocate spinningTail).run σ = _
  rw [Prog.run_cons_ok ha]
  change (spinningTail.run τ).map _ = _
  rw [hs]
  rfl

/-- The reached allocation has inhabited capacity even though the suffix never exits. -/
theorem allocating_prefix_simulates : allocatingSpinPublic.Agrees 1 6 bases σ machine := by
  apply allocatingSpinPublic.correct
  apply (allocatingSpinPublic.memoryLoopScopes_input (by decide +kernel) 1 6 bases σ machine).mpr
  refine ⟨initial.1, by decide +kernel, ?_⟩
  exact LoopScopes.room_of_prefixBudget checkedAllocatingSpin.cert
    (show LoopScopes.prefixBudget checkedAllocatingSpin.cert σ = some 1 from by decide +kernel)
    (.inr ⟨by decide, cursor, initial.2, by decide +kernel⟩)

theorem allocating_prefix_faults : run allocatingSpinPublic.code machine = .fault :=
  LoopScopeDivergenceExamples.agrees_fault allocatingSpinPublic rfl
    allocating_prefix_diverges allocating_prefix_simulates

theorem allocating_prefix_full_refused :
    ¬ LoopScopes.Room checkedAllocatingSpin.cert 6 σ bases fullMachine := by
  intro room
  have hd : LoopScopes.Demand checkedAllocatingSpin.cert σ 1 := by
    unfold checkedAllocatingSpin allocatingSpinPublic
    exact .head (.base (Loops.Demand.head rfl))
  exact full_cursor_refused (room 1 hd)

/-- info: some 1 -/
#guard_msgs in
#eval LoopScopes.prefixBudget checkedAllocatingSpin.cert σ

#print axioms automatic_block_simulates
#print axioms skipped_full_simulates
#print axioms allocating_prefix_faults

end Solidity.Evm.Memory.LoopScopeAllocExamples
