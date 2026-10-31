import Solidity.Evm.Compiler
import Solidity.Syntax.Splice
import Solidity.Backend.Failure.Observe

/-! Inhabited public-compiler regressions for ordinary direct internal calls. -/
namespace Solidity.Evm.Memory.CallExamples

private def C : Contract := contract!{
  struct Record { uint n; }
  Record stored;
  function touch(uint[] memory a, uint[] memory b, uint v) returns (uint r) {
    a[0] = v;
    require(b[0] == v);
    a = new uint[](2);
    a[0] = 88;
    require(b[0] == v);
    return b[0] + 1;
  }
  function nested(uint[] memory a) returns (uint r) { return touch(a, a, 7); }
  function touchRows(uint[][] memory a) { }
  function echo(uint[] memory a) returns (uint[] memory r) { r = a; }
  function escapeLocal(uint[] memory a) returns (uint[] memory r) {
    uint[] memory owned = new uint[](2);
    owned[0] = 33;
    r = owned;
    a = new uint[](1);
    a[0] = 44;
  }
  function fresh(uint n) returns (uint[] memory r) { r = new uint[](n); r[0] = 11; }
  function forwarded(uint n) returns (uint[] memory r) { r = fresh(n); }
  function record(Record memory a) returns (Record memory r) { a.n = 9; r = a; }
  function first(uint[] memory a) returns (uint r) { return a[0]; }
  function signedEcho(uint[] memory a, int delta) returns (int r) { a[0] = 19; return delta; }
  function boolEcho(uint[] memory a, bool flag) returns (bool r) { require(a[0] == 19); return flag; }
  function make(uint n) { uint[] memory a = new uint[](n); require(a.length == n); }
  function bump(uint[] memory a) { a[0] = 17; }
  function fail() { require(false); uint[] memory unreachable = new uint[](4); }
}
local instance : InContract := ⟨C⟩

private def bases : Nat → Fin W := fun _ => wmod 0
private def initial : State C [] := State.init C
private def machine : Machine :=
  {Machine.init with stack := [w[77]], mem := fun a =>
    if a = 0 then w[256] else if a = 127 then w[99] else w[0]}

private theorem noRef {R : RefTy} (r : HRef [] R) : False := by cases r.get?

/-- The public state and allocator inputs have the same concrete witness. -/
theorem initial_repr : StateRepr 1 1 128 (Frag.init []) initial bases machine ∧
    StructAllocatorRepr initial.heap bases 128 (wmod 256) machine := by
  have hh : HeapRepr initial.heap bases 128 machine :=
    ⟨fun r => (noRef r).elim, fun r => (noRef r).elim, fun r => (noRef r).elim⟩
  have hs : StructHeapRepr initial.heap bases 128 machine :=
    ⟨fun r => (noRef r).elim, fun r => (noRef r).elim, fun r => (noRef r).elim⟩
  have hx : StructArraySeparated initial.heap bases := fun _ r => (noRef r).elim
  have hc := Sim.init C 0 W_pos (fun _ => 0) ⟨0, W_pos⟩ rfl
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
    change 256 ≤ a at ha
    simp only [machine]
    split <;> rename_i he
    · omega
    · split <;> rename_i he
      · omega
      · rfl

private def mutation := (sol{
  uint[] memory xs = new uint[](1);
  uint untouched = 42;
  uint result = nested(xs);
  require(result == 8 && xs[0] == 7 && untouched == 42);
} : Prog C [] _)

private def references := (sol{
  uint[] memory xs = fresh(2);
  uint[] memory same = echo(xs);
  same[0] = 12;
  require(xs[0] == 12 && same.length == 2);
} : Prog C [] _)

private def copies := (sol{
  stored.n = 4;
  Record memory independent = stored;
  Record memory same = record(independent);
  require(independent.n == 9 && same.n == 9 && stored.n == 4);
} : Prog C [] _)

private def boundsFailure := (sol{
  uint[] memory xs = new uint[](0);
  uint result = first(xs);
} : Prog C [] _)

private def calleeFailure := (sol{
  uint[] memory xs = new uint[](0);
  fail();
  uint[] memory unreachable = new uint[](5);
} : Prog C [] _)

private def branches := (sol{
  uint[] memory xs = new uint[](1);
  if (xs.length == 1) { uint result = nested(xs); require(result == 8); }
  else { fail(); }
  require(xs[0] == 7);
} : Prog C [] _)

private def compiledMutation : Compiler.Compilation 1 (Frag.init []) mutation :=
  (Compiler.compile 1 (Frag.init []) mutation).get (by decide +kernel)
private def compiledReferences : Compiler.Compilation 1 (Frag.init []) references :=
  (Compiler.compile 1 (Frag.init []) references).get (by decide +kernel)
private def compiledCopies : Compiler.Compilation 1 (Frag.init []) copies :=
  (Compiler.compile 1 (Frag.init []) copies).get (by decide +kernel)
private def compiledBoundsFailure : Compiler.Compilation 1 (Frag.init []) boundsFailure :=
  (Compiler.compile 1 (Frag.init []) boundsFailure).get (by decide +kernel)
private def compiledCalleeFailure : Compiler.Compilation 1 (Frag.init []) calleeFailure :=
  (Compiler.compile 1 (Frag.init []) calleeFailure).get (by decide +kernel)
private def compiledBranches : Compiler.Compilation 1 (Frag.init []) branches :=
  (Compiler.compile 1 (Frag.init []) branches).get (by decide +kernel)
attribute [irreducible] compiledMutation compiledReferences compiledCopies
  compiledBoundsFailure compiledCalleeFailure compiledBranches

example : (mutation.run initial).toOption.isSome = true := by decide +kernel
example : (references.run initial).toOption.isSome = true := by decide +kernel
example : (copies.run initial).toOption.isSome = true := by decide +kernel
example : (branches.run initial).toOption.isSome = true := by decide +kernel
example : (boundsFailure.run initial).halt? = some .revert := by decide +kernel
example : (calleeFailure.run initial).halt? = some .revert := by decide +kernel



theorem mutation_input : compiledMutation.Input 1 128 bases initial machine := by
  apply (compiledMutation.memoryCalls_input (by decide +kernel) 1 128 bases initial machine).mpr
  exact ⟨initial_repr.1, by decide +kernel,
    .inr ⟨by decide, wmod 256, initial_repr.2, by decide +kernel⟩⟩
theorem mutation_agrees : compiledMutation.Agrees 1 128 bases initial machine :=
  compiledMutation.correct mutation_input

theorem references_input : compiledReferences.Input 1 128 bases initial machine := by
  apply (compiledReferences.memoryCalls_input (by decide +kernel) 1 128 bases initial machine).mpr
  exact ⟨initial_repr.1, by decide +kernel,
    .inr ⟨by decide, wmod 256, initial_repr.2, by decide +kernel⟩⟩
theorem references_agrees : compiledReferences.Agrees 1 128 bases initial machine :=
  compiledReferences.correct references_input

theorem copies_input : compiledCopies.Input 1 128 bases initial machine := by
  apply (compiledCopies.memoryCalls_input (by decide +kernel) 1 128 bases initial machine).mpr
  exact ⟨initial_repr.1, by decide +kernel,
    .inr ⟨by decide, wmod 256, initial_repr.2, by decide +kernel⟩⟩
theorem copies_agrees : compiledCopies.Agrees 1 128 bases initial machine :=
  compiledCopies.correct copies_input

theorem boundsFailure_input : compiledBoundsFailure.Input 1 128 bases initial machine := by
  apply (compiledBoundsFailure.memoryCalls_input (by decide +kernel) 1 128 bases initial machine).mpr
  exact ⟨initial_repr.1, by decide +kernel,
    .inr ⟨by decide, wmod 256, initial_repr.2, by decide +kernel⟩⟩
theorem boundsFailure_agrees : compiledBoundsFailure.Agrees 1 128 bases initial machine :=
  compiledBoundsFailure.correct boundsFailure_input

theorem calleeFailure_input : compiledCalleeFailure.Input 1 128 bases initial machine := by
  apply (compiledCalleeFailure.memoryCalls_input (by decide +kernel) 1 128 bases initial machine).mpr
  exact ⟨initial_repr.1, by decide +kernel,
    .inr ⟨by decide, wmod 256, initial_repr.2, by decide +kernel⟩⟩
theorem calleeFailure_agrees : compiledCalleeFailure.Agrees 1 128 bases initial machine :=
  compiledCalleeFailure.correct calleeFailure_input

theorem branches_input : compiledBranches.Input 1 128 bases initial machine := by
  apply (compiledBranches.memoryCalls_input (by decide +kernel) 1 128 bases initial machine).mpr
  exact ⟨initial_repr.1, by decide +kernel,
    .inr ⟨by decide, wmod 256, initial_repr.2, by decide +kernel⟩⟩
theorem branches_agrees : compiledBranches.Agrees 1 128 bases initial machine :=
  compiledBranches.correct branches_input

private def arrayAt {H : HTy} (hp : Heap H) (id i : Nat) : Option Int := do
  if h : H[id]? = some (.array (.prim .uint)) then
    let value ← hp.index (⟨id, h⟩ : HRef H (.array (.prim .uint))) .dyn (indexValue (wmod i))
    pure value.1
  else none

private def recordAt {H : HTy} (hp : Heap H) (id : Nat) : Option Int :=
  if h : H[id]? = some (.struct "Record{n:uint}") then
    some ((hp.field (⟨id, h⟩ : HRef H (.struct "Record{n:uint}")) (f := "n") rfl).1)
  else none

private def sourceArrays {Δ : Ctx} (out : TRes (Solidity.Out C [] Δ))
    (positions : List (Nat × Nat)) : Option (List Int) := do
  let o ← out.toOption
  let values ← positions.mapM (fun (id, i) => arrayAt o.st.heap id i)
  pure ((o.st.H.length : Int) :: values)

private def sourceRecords {Δ : Ctx} (out : TRes (Solidity.Out C [] Δ)) : Option (List Int) := do
  let o ← out.toOption
  let first ← recordAt o.st.heap 0
  let second ← recordAt o.st.heap 1
  pure [o.st.H.length, first, second]

private def targetWords (out : Out) (addresses : List Nat) : Option (List Nat) := do
  match out with
  | .ok m _ =>
    (m.stack ++ addresses.map m.mem).mapM fun w => match w with
      | .val v => some v.val
      | .slot _ => none
  | _ => none

/-- Both aliases mutate the same object; rebinding a parameter allocates independently.
The caller's primitive locals and a nonempty machine stack survive both call frames. -/
example : sourceArrays (mutation.run initial) [(0, 0), (1, 0), (1, 1)] = some [2, 7, 88, 0] := by
  decide +kernel
-- Cell 3 is the elaborator's private reference-argument capture; result is the final local.
example : mutation.ext.depth = 4 := by decide +kernel
example : targetWords (run compiledMutation.code machine) [0, 127, 2, mutation.ext.depth, 256, 257, 258, 259, 260] =
    some [77, 261, 99, 42, 8, 1, 7, 2, 88, 0] := by decide +kernel

/-- Memory returns export identity, including an object allocated by the callee.
The default return objects are retained, as required by CallRet.enterT. -/
example : sourceArrays (references.run initial) [(1, 0), (1, 1)] = some [3, 12, 0] := by
  decide +kernel
example : targetWords (run compiledReferences.code machine) [0, 127, 256, 257, 258, 259, 260] =
    some [77, 261, 99, 0, 2, 12, 0, 0] := by decide +kernel

/-- Storage-to-memory creates an independent object; memory parameters and returns alias it. -/
example : sourceRecords (copies.run initial) = some [2, 9, 0] := by decide +kernel
example : targetWords (run compiledCopies.code machine) [0, 127, 256, 257] =
    some [77, 258, 99, 9, 0] := by decide +kernel
private def storedWord : Out → Option Nat
  | .ok m _ => some (m.store (.root 0))
  | _ => none
example : storedWord (run compiledCopies.code machine) = some 4 := by decide +kernel

private def reverted : Out → Bool | .revert => true | _ => false
example : reverted (run compiledBoundsFailure.code machine) = true := by decide +kernel
example : reverted (run compiledCalleeFailure.code machine) = true := by decide +kernel
example : targetWords (run compiledBranches.code machine) [0, 127, 256, 257] =
    some [77, 261, 99, 1, 7] := by decide +kernel

example : compiledMutation.allocationCost initial = 5 := by decide +kernel
example : compiledReferences.allocationCost initial = 5 := by decide +kernel
example : compiledCopies.allocationCost initial = 2 := by decide +kernel
/-- An earlier revert reaches neither the callee's nor the caller's later allocations. -/
example : compiledCalleeFailure.allocationCost initial = 1 := by decide +kernel

private def tooFull := writeMachine machine 0 (.val (wmod (W - 4)))
theorem capacity_refused : ¬ compiledMutation.Input 1 128 bases initial tooFull := by
  intro h
  have hi := ((compiledMutation.memoryCalls_input (by decide +kernel) 1 128 bases initial tooFull).mp h).2.2
  have hcost : compiledMutation.allocationCost initial = 5 := by decide +kernel
  rcases hi with hz | ⟨_, c, ha, hs⟩
  · rw [hcost] at hz; cases hz
  · have he : c = wmod (W - 4) := Word.val.inj ha.arrays.free.cell.symm
    subst c
    rw [hcost] at hs
    have hn : ¬ (wmod (W - 4)).val + 5 < W := by decide +kernel
    exact hn hs

theorem frame_refused : ¬ compiledMutation.Input 1 1 bases initial machine := by
  intro h
  have hc := ((compiledMutation.memoryCalls_input (by decide +kernel) 1 1 bases initial machine).mp h).2.1
  have hn : 0 < compiledMutation.requiredFrame := by decide +kernel
  omega

example : (Compiler.compile 0 (Frag.init []) mutation).isSome = false := by decide +kernel

/-- These existing named fragment boundaries remain refusals. -/
private def recursive : Prog C [] [] := .cons (.callRec "recursive" 1 .nil .none (fun _ => .nil)) .nil
private def payment : Prog C [] [] :=
  .cons (.transfer (.simple (.lit 1 rfl)) (.simple (.lit 0 rfl))) .nil
private def externalCall : Prog C [] [] :=
  .cons (.tryCall ⟨.lit 1 rfl, "other", []⟩ .nil .nil .nil .none .nil .nil .nil .nil false) .nil
example : (Compiler.compile 1 (Frag.init []) recursive).isSome = false := by decide +kernel
example : (Calls.compile 1 (Frag.init []) payment).isSome = false := by decide +kernel
example : (Compiler.compile 1 (Frag.init []) externalCall).isSome = false := by decide +kernel

#print axioms Compiler.Compilation.correct
#print axioms Calls.memoryReturn
#print axioms mutation_agrees
#print axioms references_agrees
#print axioms copies_agrees



private def failedReturnArgument := (sol{
  uint[] memory empty = new uint[](0);
  uint[] memory result = fresh(empty[0]);
} : Prog C [] _)
private def noCapacityNeeded := (sol{ fail(); } : Prog C [] _)
private def falseBranch := (sol{
  uint[] memory xs = new uint[](1);
  if (xs.length == 0) { fail(); }
  else { uint result = nested(xs); require(result == 8); }
  require(xs[0] == 7);
} : Prog C [] _)
private def compiledFailedReturnArgument : Compiler.Compilation 1 (Frag.init []) failedReturnArgument :=
  (Compiler.compile 1 (Frag.init []) failedReturnArgument).get (by decide +kernel)
private def compiledNoCapacityNeeded : Compiler.Compilation 1 (Frag.init []) noCapacityNeeded :=
  (Compiler.compile 1 (Frag.init []) noCapacityNeeded).get (by decide +kernel)
private def compiledFalseBranch : Compiler.Compilation 1 (Frag.init []) falseBranch :=
  (Compiler.compile 1 (Frag.init []) falseBranch).get (by decide +kernel)
attribute [irreducible] compiledFailedReturnArgument compiledNoCapacityNeeded compiledFalseBranch

theorem failedReturnArgument_input : compiledFailedReturnArgument.Input 1 128 bases initial machine := by
  apply (compiledFailedReturnArgument.memoryCalls_input (by decide +kernel) 1 128 bases initial machine).mpr
  exact ⟨initial_repr.1, by decide +kernel,
    .inr ⟨by decide, wmod 256, initial_repr.2, by decide +kernel⟩⟩
theorem failedReturnArgument_agrees : compiledFailedReturnArgument.Agrees 1 128 bases initial machine :=
  compiledFailedReturnArgument.correct failedReturnArgument_input

theorem falseBranch_input : compiledFalseBranch.Input 1 128 bases initial machine := by
  apply (compiledFalseBranch.memoryCalls_input (by decide +kernel) 1 128 bases initial machine).mpr
  exact ⟨initial_repr.1, by decide +kernel,
    .inr ⟨by decide, wmod 256, initial_repr.2, by decide +kernel⟩⟩
theorem falseBranch_agrees : compiledFalseBranch.Agrees 1 128 bases initial machine :=
  compiledFalseBranch.correct falseBranch_input

example : (failedReturnArgument.run initial).halt? = some .revert := by decide +kernel
example : reverted (run compiledFailedReturnArgument.code machine) = true := by decide +kernel
example : compiledFailedReturnArgument.allocationCost initial = 1 := by decide +kernel
example : (falseBranch.run initial).toOption.isSome = true := by decide +kernel
example : targetWords (run compiledFalseBranch.code machine) [0, 127, 256, 257] =
    some [77, 261, 99, 1, 7] := by decide +kernel

private def invalidCursor := writeMachine machine 0 w[0]
private theorem invalidCursor_repr : StateRepr 1 1 128 (Frag.init []) initial bases invalidCursor := by
  have h := initial_repr.1
  have hc := h.core.congrMem (mem := upd machine.mem 0 w[0])
    (by intro l hl hu; change l < 1 at hu; omega)
  refine ⟨?_, h.heap.localWrite 0 (by decide) _, ?_, h.locals,
    h.structs.localWrite 0 (by decide) _, h.separated,
    RefFieldsRepr.localWrite h.refs h.structs 0 (by decide) _⟩
  · exact ⟨hc.store, hc.vals, hc.aliases, hc.net, hc.netSelf, hc.bound,
      hc.fragile, hc.env, hc.funds, hc.oracle⟩
  · intro R i; nomatch i

theorem noCapacityNeeded_input : compiledNoCapacityNeeded.Input 1 128 bases initial invalidCursor := by
  apply (compiledNoCapacityNeeded.memoryCalls_input (by decide +kernel) 1 128 bases initial invalidCursor).mpr
  exact ⟨invalidCursor_repr, by decide +kernel, .inl (by decide +kernel)⟩
theorem noCapacityNeeded_agrees : compiledNoCapacityNeeded.Agrees 1 128 bases initial invalidCursor :=
  compiledNoCapacityNeeded.correct noCapacityNeeded_input
example : (noCapacityNeeded.run initial).halt? = some .revert := by decide +kernel
example : reverted (run compiledNoCapacityNeeded.code invalidCursor) = true := by decide +kernel

private def mixedPayment : Prog C [] [] :=
  .cons (.block (.cons (.declMem (.array (.prim .uint)) (.user "xs")
    (some (.newArr (.lit 0 rfl) rfl)) rfl rfl) .nil)) payment
example : (Compiler.compile 1 (Frag.init []) mixedPayment).isSome = false := by decide +kernel



private def voidCall := (sol{
  uint marker = 42;
  uint[] memory xs = new uint[](1);
  bump(xs);
  require(xs[0] == 17 && marker == 42);
} : Prog C [] _)
private def compiledVoidCall : Compiler.Compilation 1 (Frag.init []) voidCall :=
  (Compiler.compile 1 (Frag.init []) voidCall).get (by decide +kernel)
attribute [irreducible] compiledVoidCall

theorem voidCall_input : compiledVoidCall.Input 1 128 bases initial machine := by
  apply (compiledVoidCall.memoryCalls_input (by decide +kernel) 1 128 bases initial machine).mpr
  exact ⟨initial_repr.1, by decide +kernel,
    .inr ⟨by decide, wmod 256, initial_repr.2, by decide +kernel⟩⟩
theorem voidCall_agrees : compiledVoidCall.Agrees 1 128 bases initial machine :=
  compiledVoidCall.correct voidCall_input
example : (voidCall.run initial).toOption.isSome = true := by decide +kernel
example : sourceArrays (voidCall.run initial) [(0, 0)] = some [1, 17] := by decide +kernel
example : targetWords (run compiledVoidCall.code machine) [0, 127, 1, 256, 257] =
    some [77, 258, 99, 42, 1, 17] := by decide +kernel



private def directCopy := (sol{
  stored.n = 4;
  Record memory same = record(stored);
  require(same.n == 9 && stored.n == 4);
} : Prog C [] _)
private def forwarding := (sol{
  uint[] memory xs = forwarded(1);
  xs[0] = 21;
  require(xs[0] == 21);
} : Prog C [] _)
private def compiledDirectCopy : Compiler.Compilation 1 (Frag.init []) directCopy :=
  (Compiler.compile 1 (Frag.init []) directCopy).get (by decide +kernel)
private def compiledForwarding : Compiler.Compilation 1 (Frag.init []) forwarding :=
  (Compiler.compile 1 (Frag.init []) forwarding).get (by decide +kernel)
attribute [irreducible] compiledDirectCopy compiledForwarding

theorem directCopy_input : compiledDirectCopy.Input 1 128 bases initial machine := by
  apply (compiledDirectCopy.memoryCalls_input (by decide +kernel) 1 128 bases initial machine).mpr
  exact ⟨initial_repr.1, by decide +kernel,
    .inr ⟨by decide, wmod 256, initial_repr.2, by decide +kernel⟩⟩
theorem directCopy_agrees : compiledDirectCopy.Agrees 1 128 bases initial machine :=
  compiledDirectCopy.correct directCopy_input

theorem forwarding_input : compiledForwarding.Input 1 128 bases initial machine := by
  apply (compiledForwarding.memoryCalls_input (by decide +kernel) 1 128 bases initial machine).mpr
  exact ⟨initial_repr.1, by decide +kernel,
    .inr ⟨by decide, wmod 256, initial_repr.2, by decide +kernel⟩⟩
theorem forwarding_agrees : compiledForwarding.Agrees 1 128 bases initial machine :=
  compiledForwarding.correct forwarding_input

example : (directCopy.run initial).toOption.isSome = true := by decide +kernel
example : sourceRecords (directCopy.run initial) = some [2, 9, 0] := by decide +kernel
example : targetWords (run compiledDirectCopy.code machine) [0, 127, 256, 257] =
    some [77, 258, 99, 9, 0] := by decide +kernel
example : storedWord (run compiledDirectCopy.code machine) = some 4 := by decide +kernel
example : (forwarding.run initial).toOption.isSome = true := by decide +kernel
example : sourceArrays (forwarding.run initial) [(2, 0)] = some [3, 21] := by decide +kernel
example : targetWords (run compiledForwarding.code machine) [0, 127, 256, 257, 258, 259] =
    some [77, 260, 99, 0, 0, 1, 21] := by decide +kernel



/-- Computing a capacity premise must not traverse a nonallocating source suffix. -/
private def largeCost := (sol{ make(4096); } : Prog C [] _)
private def compiledLargeCost : Compiler.Compilation 1 (Frag.init []) largeCost :=
  (Compiler.compile 1 (Frag.init []) largeCost).get (by decide +kernel)
attribute [irreducible] compiledLargeCost
example : compiledLargeCost.allocationCost initial = 4097 := by decide +kernel

theorem largeCost_input : compiledLargeCost.Input 1 128 bases initial machine := by
  apply (compiledLargeCost.memoryCalls_input (by decide +kernel) 1 128 bases initial machine).mpr
  exact ⟨initial_repr.1, by decide +kernel,
    .inr ⟨by decide, wmod 256, initial_repr.2, by decide +kernel⟩⟩
theorem largeCost_agrees : compiledLargeCost.Agrees 1 128 bases initial machine :=
  compiledLargeCost.correct largeCost_input
example : (largeCost.run initial).toOption.isSome = true := by decide +kernel
example : sourceArrays (largeCost.run initial) [(0, 0)] = some [1, 0] := by decide +kernel
example : targetWords (run compiledLargeCost.code machine) [0, 127, 256, 257, 4352] =
    some [77, 4353, 99, 4096, 0, 0] := by decide +kernel

/-- A body-local object escapes by reference. Later calls reuse private frames;
caller aliases remain shared, and rebinding the parameter preserves the caller. -/
private def callerOwnership := (sol{
  uint marker = 42;
  uint[] memory caller = new uint[](1);
  caller[0] = 5;
  uint[] memory shared = echo(caller);
  uint[] memory escaped = escapeLocal(caller);
  bump(caller);
  uint[] memory later = fresh(1);
  require(caller[0] == 17 && shared[0] == 17 && escaped[0] == 33 &&
    escaped.length == 2 && later[0] == 11 && marker == 42);
} : Prog C [] _)
private def compiledCallerOwnership : Compiler.Compilation 1 (Frag.init []) callerOwnership :=
  (Compiler.compile 1 (Frag.init []) callerOwnership).get (by decide +kernel)
attribute [irreducible] compiledCallerOwnership

theorem callerOwnership_input : compiledCallerOwnership.Input 1 128 bases initial machine := by
  apply (compiledCallerOwnership.memoryCalls_input (by decide +kernel) 1 128 bases initial machine).mpr
  exact ⟨initial_repr.1, by decide +kernel,
    .inr ⟨by decide, wmod 256, initial_repr.2, by decide +kernel⟩⟩
theorem callerOwnership_agrees : compiledCallerOwnership.Agrees 1 128 bases initial machine :=
  compiledCallerOwnership.correct callerOwnership_input

example : (callerOwnership.run initial).toOption.isSome = true := by decide +kernel
example : sourceArrays (callerOwnership.run initial) [(0, 0), (3, 0), (3, 1), (4, 0), (6, 0)] =
    some [7, 17, 33, 0, 44, 11] := by decide +kernel
example : compiledCallerOwnership.allocationCost initial = 12 := by decide +kernel
example : targetWords (run compiledCallerOwnership.code machine)
    [0, 127, 1, 256, 257, 258, 259, 260, 261, 262, 263, 264, 265, 266, 267] =
    some [77, 268, 99, 42, 1, 17, 0, 0, 2, 33, 0, 1, 44, 0, 1, 11] := by decide +kernel
#print axioms callerOwnership_agrees

/-- All non-frame premises are inhabited with room for every caller local. -/
private theorem callerOnly_repr : StateRepr 1 1 5 (Frag.init []) initial bases machine ∧
    StructAllocatorRepr initial.heap bases 5 (wmod 256) machine := by
  have hh : HeapRepr initial.heap bases 5 machine :=
    ⟨fun r => (noRef r).elim, fun r => (noRef r).elim, fun r => (noRef r).elim⟩
  have hs : StructHeapRepr initial.heap bases 5 machine :=
    ⟨fun r => (noRef r).elim, fun r => (noRef r).elim, fun r => (noRef r).elim⟩
  have hx : StructArraySeparated initial.heap bases := fun _ r => (noRef r).elim
  have hc := Sim.init C 0 W_pos (fun _ => 0) ⟨0, W_pos⟩ rfl
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
    change 256 ≤ a at ha
    simp only [machine]
    split <;> rename_i he
    · omega
    · split <;> rename_i he
      · omega
      · rfl

example : Memory.frameNeedProg mutation = 4 := by decide +kernel
example : compiledMutation.requiredFrame = 12 := by decide +kernel

theorem callerOnly_preconditions : StateRepr 1 1 5 (Frag.init []) initial bases machine ∧
    1 + Memory.frameNeedProg mutation ≤ 5 ∧
    AllocationInput 1 5 (compiledMutation.allocationCost initial) initial bases machine := by
  exact ⟨callerOnly_repr.1, by decide +kernel,
    .inr ⟨by decide, wmod 256, callerOnly_repr.2, by decide +kernel⟩⟩

theorem privateFrame_refused : ¬ compiledMutation.Input 1 5 bases initial machine := by
  intro h
  have hc := ((compiledMutation.memoryCalls_input (by decide +kernel) 1 5 bases initial machine).mp h).2.1
  have hn : 5 < 1 + compiledMutation.requiredFrame := by decide +kernel
  omega

private def discardedReturn := (sol{
  uint marker = 42;
  uint[] memory xs = new uint[](1);
  nested(xs);
  require(xs[0] == 7 && marker == 42);
} : Prog C [] _)
private def primitiveTypes := (sol{
  uint marker = 42;
  uint[] memory xs = new uint[](1);
  int value = signedEcho(xs, -3);
  bool take = boolEcho(xs, true);
  if (take) { require(value == -3); } else { revert(); }
  require(xs[0] == 19 && marker == 42);
} : Prog C [] _)
private def compiledDiscardedReturn : Compiler.Compilation 1 (Frag.init []) discardedReturn :=
  (Compiler.compile 1 (Frag.init []) discardedReturn).get (by decide +kernel)
private def compiledPrimitiveTypes : Compiler.Compilation 1 (Frag.init []) primitiveTypes :=
  (Compiler.compile 1 (Frag.init []) primitiveTypes).get (by decide +kernel)
attribute [irreducible] compiledDiscardedReturn compiledPrimitiveTypes

theorem discardedReturn_input : compiledDiscardedReturn.Input 1 128 bases initial machine := by
  apply (compiledDiscardedReturn.memoryCalls_input (by decide +kernel) 1 128 bases initial machine).mpr
  exact ⟨initial_repr.1, by decide +kernel,
    .inr ⟨by decide, wmod 256, initial_repr.2, by decide +kernel⟩⟩
theorem discardedReturn_agrees : compiledDiscardedReturn.Agrees 1 128 bases initial machine :=
  compiledDiscardedReturn.correct discardedReturn_input

theorem primitiveTypes_input : compiledPrimitiveTypes.Input 1 128 bases initial machine := by
  apply (compiledPrimitiveTypes.memoryCalls_input (by decide +kernel) 1 128 bases initial machine).mpr
  exact ⟨initial_repr.1, by decide +kernel,
    .inr ⟨by decide, wmod 256, initial_repr.2, by decide +kernel⟩⟩
theorem primitiveTypes_agrees : compiledPrimitiveTypes.Agrees 1 128 bases initial machine :=
  compiledPrimitiveTypes.correct primitiveTypes_input

example : (discardedReturn.run initial).toOption.isSome = true := by decide +kernel
example : sourceArrays (discardedReturn.run initial) [(0, 0), (1, 0)] = some [2, 7, 88] := by decide +kernel
example : targetWords (run compiledDiscardedReturn.code machine) [0, 127, 1, 256, 257, 258, 259, 260] =
    some [77, 261, 99, 42, 1, 7, 2, 88, 0] := by decide +kernel
example : (primitiveTypes.run initial).toOption.isSome = true := by decide +kernel
example : sourceArrays (primitiveTypes.run initial) [(0, 0)] = some [1, 19] := by decide +kernel
example : primitiveTypes.ext.depth = 6 := by decide +kernel
example : targetWords (run compiledPrimitiveTypes.code machine) [0, 127, 1, 4, 6, 256, 257] =
    some [77, 258, 99, 42, W - 3, 1, 1, 19] := by decide +kernel
#print axioms discardedReturn_agrees
#print axioms primitiveTypes_agrees

private theorem error_of_halt {α : Type} (result : TRes α) (e : THalt)
    (h : result.halt? = some e) : result = .error e := by
  cases result with
  | ok a => cases h
  | error e' => exact congrArg Except.error (Option.some.inj h)

/-- The published payload observer agrees with the actual supported call's source
failure. The existing inhabited compiler agreement and word revert are unchanged. -/
theorem calleeFailure_observed_empty : Backend.Failure.ResultObserves (fun _ => [])
    (calleeFailure.run initial) (.revert []) := by
  have hs : calleeFailure.run initial = .error .revert :=
    error_of_halt _ _ (by decide +kernel)
  rw [hs]
  exact .failure .empty

theorem calleeFailure_not_panic : ¬ Backend.Failure.ResultObserves (fun _ => [])
    (calleeFailure.run initial) (.revert (Semantics.encodePanic 1)) :=
  Backend.Failure.wrong_observation calleeFailure_observed_empty (by decide +kernel)

private def payloadCall : Prog C [] [.mem (.array (.prim .uint))] :=
  .cons (.declMem (.array (.prim .uint)) (.user "xs")
    (some (.newArr (.lit 1 rfl) rfl)) rfl rfl)
    (.cons (.call "payload" .nil .none (.cons (.revertData [.bytes [0xde, 0xad]]) .nil)) .nil)

theorem payloadCall_source : payloadCall.run initial = .error (.revertWith [0xde, 0xad]) :=
  error_of_halt _ _ (by decide +kernel)

theorem payloadCall_observed : Backend.Failure.ResultObserves (fun _ => [])
    (payloadCall.run initial) (.revert [0xde, 0xad]) := by
  rw [payloadCall_source]
  exact .failure (.data _)

/-- Source payload observation does not enable byte transport by the word compiler. -/
example : (Compiler.compile 1 (Frag.init []) payloadCall).isSome = false := by decide +kernel

private def aggregatePrefix := (sol{ uint[][] memory rows = new uint[][](1); } : Prog C [] _)
private def aggregateCall := (sol{
  uint[][] memory rows = new uint[][](1);
  touchRows(rows);
} : Prog C [] _)
private def compiledAggregatePrefix :=
  (Compiler.compile 1 (Frag.init []) aggregatePrefix).get (by decide +kernel)
attribute [irreducible] compiledAggregatePrefix
example : compiledAggregatePrefix.isConstruction = true := by decide +kernel
example : compiledAggregatePrefix.usesMemory = true := by decide +kernel
example : compiledAggregatePrefix.isMemoryCalls = false := by decide +kernel
example : compiledAggregatePrefix.allocationCost initial = 3 := by decide +kernel
/-- A published construction prefix is accepted; combining its new layout with a
call remains outside this task's original full-memory call relation. -/
example : (Compiler.compile 1 (Frag.init []) aggregateCall).isSome = false := by decide +kernel
#print axioms calleeFailure_observed_empty
#print axioms payloadCall_observed

end Solidity.Evm.Memory.CallExamples
