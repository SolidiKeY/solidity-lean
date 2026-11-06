import Solidity.Evm.MemoryLoopAllocExamples
import Solidity.Evm.MemoryLoopScopeBudget
import Solidity.Syntax.Splice

/-! Ordinary source loops over aliased primitive arrays and structs, in both
source evaluation orders, using the public compiler and inhabited inputs. -/
namespace Solidity.Evm.Memory.LoopScopeSourceExamples

private def C : Contract := contract!{ struct Record { uint n; int signed; } }
private def irC : Contract := { C with evalOrder := .viaIR }
private def bases : Nat → Fin W := fun _ => wmod 0
private def machine : Machine :=
  {Machine.init with stack := [w[77]], mem := fun a =>
    if a = 0 then w[128] else if a = 63 then w[99] else w[0]}

private theorem initial_repr (K : Contract) :
    StateRepr 1 1 64 (Frag.init []) (State.init K) bases machine ∧
    StructAllocatorRepr (State.init K).heap bases 64 (wmod 128) machine := by
  have noRef {R : RefTy} (r : HRef [] R) : False := by cases r.get?
  have hh : HeapRepr (State.init K).heap bases 64 machine :=
    ⟨fun r => (noRef r).elim, fun r => (noRef r).elim, fun r => (noRef r).elim⟩
  have hs : StructHeapRepr (State.init K).heap bases 64 machine :=
    ⟨fun r => (noRef r).elim, fun r => (noRef r).elim, fun r => (noRef r).elim⟩
  have hx : StructArraySeparated (State.init K).heap bases := fun _ r => (noRef r).elim
  have hc := Sim.init K 0 W_pos (fun _ => 0) ⟨0, W_pos⟩ rfl
  refine ⟨⟨?_, hh, ?_, by decide, hs, hx, ?_⟩, ⟨⟨hh, ?_, fun r => (noRef r).elim⟩, hs, hx,
    fun r => (noRef r).elim⟩⟩
  · refine ⟨hc.store, ?_, ?_, hc.net, hc.netSelf, hc.bound, ?_, hc.env, hc.funds, hc.oracle⟩
    · intro p i; nomatch i
    · intro R i hi; nomatch i
    · intro R i hi; nomatch i
  · intro R i; nomatch i
  · intro s f R r hf; exact (noRef r).elim
  · refine ⟨by decide, by decide, rfl, ?_⟩
    intro a ha
    change 128 ≤ a at ha
    simp only [machine]
    split <;> rename_i he
    · omega
    · split <;> rename_i he
      · omega
      · rfl

private def arrays := (sol[C]{
  uint[] memory xs = new uint[](2);
  uint[] memory same = xs;
  uint i = 0;
  if (true) { while (i < xs.length) { xs[i] = i + 3; i++; } }
  uint answer = same[1];
} : Prog C [] _)
private def arraysIR := (sol[irC]{
  uint[] memory xs = new uint[](2);
  uint[] memory same = xs;
  uint i = 0;
  if (true) { while (i < xs.length) { xs[i] = i + 3; i++; } }
  uint answer = same[1];
} : Prog irC [] _)
private def records := (sol[C]{
  Record memory r = Record(0, 5);
  Record memory same = r;
  if (true) { while (r.n < 3) { r.n++; r.signed -= 2; } }
  require(same.signed == -1);
  uint answer = same.n;
} : Prog C [] _)
private def recordsIR := (sol[irC]{
  Record memory r = Record(0, 5);
  Record memory same = r;
  if (true) { while (r.n < 3) { r.n++; r.signed -= 2; } }
  require(same.signed == -1);
  uint answer = same.n;
} : Prog irC [] _)

private def compiledArrays := (Compiler.compile 1 (Frag.init []) arrays).get (by decide +kernel)
private def compiledArraysIR := (Compiler.compile 1 (Frag.init []) arraysIR).get (by decide +kernel)
private def compiledRecords := (Compiler.compile 1 (Frag.init []) records).get (by decide +kernel)
private def compiledRecordsIR := (Compiler.compile 1 (Frag.init []) recordsIR).get (by decide +kernel)

attribute [irreducible] compiledArrays compiledArraysIR compiledRecords compiledRecordsIR

private def checkedArrays := compiledArrays.memoryLoopScopesResult (by decide +kernel)
private def checkedArraysIR := compiledArraysIR.memoryLoopScopesResult (by decide +kernel)
private def checkedRecords := compiledRecords.memoryLoopScopesResult (by decide +kernel)
private def checkedRecordsIR := compiledRecordsIR.memoryLoopScopesResult (by decide +kernel)

theorem arrays_simulate : compiledArrays.Agrees 1 64 bases (State.init C) machine := by
  apply compiledArrays.correct
  apply (compiledArrays.memoryLoopScopes_input (by decide +kernel) 1 64 bases (State.init C) machine).mpr
  refine ⟨(initial_repr C).1, by decide +kernel, ?_⟩
  exact LoopScopes.room_of_prefixBudget checkedArrays.cert
    (show LoopScopes.prefixBudget checkedArrays.cert (State.init C) = some 3 from by decide +kernel)
    (.inr ⟨by decide, wmod 128, (initial_repr C).2, by decide +kernel⟩)

theorem arraysIR_simulate : compiledArraysIR.Agrees 1 64 bases (State.init irC) machine := by
  apply compiledArraysIR.correct
  apply (compiledArraysIR.memoryLoopScopes_input (by decide +kernel) 1 64 bases (State.init irC) machine).mpr
  refine ⟨(initial_repr irC).1, by decide +kernel, ?_⟩
  exact LoopScopes.room_of_prefixBudget checkedArraysIR.cert
    (show LoopScopes.prefixBudget checkedArraysIR.cert (State.init irC) = some 3 from by decide +kernel)
    (.inr ⟨by decide, wmod 128, (initial_repr irC).2, by decide +kernel⟩)

theorem records_simulate : compiledRecords.Agrees 1 64 bases (State.init C) machine := by
  apply compiledRecords.correct
  apply (compiledRecords.memoryLoopScopes_input (by decide +kernel) 1 64 bases (State.init C) machine).mpr
  refine ⟨(initial_repr C).1, by decide +kernel, ?_⟩
  exact LoopScopes.room_of_prefixBudget checkedRecords.cert
    (show LoopScopes.prefixBudget checkedRecords.cert (State.init C) = some 2 from by decide +kernel)
    (.inr ⟨by decide, wmod 128, (initial_repr C).2, by decide +kernel⟩)

theorem recordsIR_simulate : compiledRecordsIR.Agrees 1 64 bases (State.init irC) machine := by
  apply compiledRecordsIR.correct
  apply (compiledRecordsIR.memoryLoopScopes_input (by decide +kernel) 1 64 bases (State.init irC) machine).mpr
  refine ⟨(initial_repr irC).1, by decide +kernel, ?_⟩
  exact LoopScopes.room_of_prefixBudget checkedRecordsIR.cert
    (show LoopScopes.prefixBudget checkedRecordsIR.cert (State.init irC) = some 2 from by decide +kernel)
    (.inr ⟨by decide, wmod 128, (initial_repr irC).2, by decide +kernel⟩)

private def sourceTop {K : Contract} {Δ : Ctx} (i : Idx Δ (.val .uint))
    (r : TRes (Solidity.Out K [] Δ)) : Option Int :=
  match r with
  | .ok o => some (TEnv.get i o.st.env).1
  | .error _ => none
private def targetCells (cells : List Nat) (r : Out) : Option (List Nat) :=
  match r with
  | .ok m _ => cells.mapM fun a => match m.mem a with | .val w => some w.val | _ => none
  | _ => none

/-- info: (some 4, some [131, 128, 128, 2, 4, 2, 3, 4, 99]) -/
#guard_msgs in #eval (sourceTop .here (arrays.run (State.init C)),
  targetCells [0, 1, 2, 3, 4, 128, 129, 130, 63] (run compiledArrays.code machine))
/-- info: (some 4, some [131, 128, 128, 2, 4, 2, 3, 4, 99]) -/
#guard_msgs in #eval (sourceTop .here (arraysIR.run (State.init irC)),
  targetCells [0, 1, 2, 3, 4, 128, 129, 130, 63] (run compiledArraysIR.code machine))
/-- info: (some 3, some [130, 128, 128, 128, 3, 99]) -/
#guard_msgs in #eval (sourceTop .here (records.run (State.init C)),
  targetCells [0, 1, 2, 3, 128, 63] (run compiledRecords.code machine))
/-- info: (some 3, some [130, 0, 5, 128, 3, 99]) -/
#guard_msgs in #eval (sourceTop .here (recordsIR.run (State.init irC)),
  targetCells [0, 1, 2, 3, 128, 63] (run compiledRecordsIR.code machine))

#print axioms arrays_simulate
#print axioms recordsIR_simulate
end Solidity.Evm.Memory.LoopScopeSourceExamples
