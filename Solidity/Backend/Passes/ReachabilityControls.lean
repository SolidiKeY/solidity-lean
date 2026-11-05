import Solidity.Backend.Passes.ExpressionControls

/-!
# Fresh-state reachability and exact non-stack independence controls

The populated fixture is reached by an actual intrinsic program from
State.init. This is an intrinsic fresh-state witness, not a claim about
independent Source sessions or their constructor lowering.
-/
namespace Solidity.Backend.Passes.ReachabilityControls

open Solidity.Evm
open Solidity.Evm.Memory
open Solidity.Backend.Passes.Controls
open Solidity.Backend.Passes.Controls.Fixture

private abbrev A : RefTy := .array (.prim .uint)
private abbrev One : Ctx := [.mem A]
private abbrev Two : Ctx := [.mem A, .mem A]
private abbrev Three : Ctx := [.mem A, .mem A, .mem A]

private def allocateA : Stmt C [] One :=
  .declMem A (.user "a") (some (.newArr (.lit 2 rfl) rfl)) rfl rfl
private def writeA0 : Stmt C One One :=
  .assignMem (.index .dyn (.var .here rfl) (.simple (.lit 0 rfl)))
    (.val (.simple (.lit 7 rfl)))
private def writeA1 : Stmt C One One :=
  .assignMem (.index .dyn (.var .here rfl) (.simple (.lit 1 rfl)))
    (.val (.simple (.lit 9 rfl)))
private def allocateB : Stmt C One Two :=
  .declMem A (.user "b") (some (.newArr (.lit 1 rfl) rfl)) rfl rfl
private def writeB0 : Stmt C Two Two :=
  .assignMem (.index .dyn (.var .here rfl) (.simple (.lit 0 rfl)))
    (.val (.simple (.lit 4 rfl)))
private def aliasA : Stmt C Two Three :=
  .declMem A (.user "savedA") (some (.alias (.var (.there .here) rfl))) rfl rfl
private def bottomB : Stmt C Three Three :=
  .rebindMem (.there (.there .here)) (.alias (.var (.there .here) rfl))
private def middleA : Stmt C Three Three :=
  .rebindMem (.there .here) (.alias (.var .here rfl))
private def zeroValue : Stmt C Three Γ :=
  .declLocal .uint (.user "value") none

private def a0 : State C One :=
  { storage := Storage.init C, H := [A],
    heap := (⟨[CompileExamples.uint 0 (by decide), CompileExamples.uint 0 (by decide)], by decide⟩, ()),
    env := (some ⟨0, rfl⟩, ()) }
private def a7 : State C One :=
  { a0 with heap := (⟨[CompileExamples.uint 7 (by decide), CompileExamples.uint 0 (by decide)], by decide⟩, ()) }
private def a79 : State C One :=
  { a0 with heap := (⟨[CompileExamples.uint 7 (by decide), CompileExamples.uint 9 (by decide)], by decide⟩, ()) }
private def b0 : State C Two :=
  { storage := Storage.init C, H := CompileExamples.H,
    heap := (⟨[CompileExamples.uint 7 (by decide), CompileExamples.uint 9 (by decide)], by decide⟩,
      ⟨[CompileExamples.uint 0 (by decide)], by decide⟩, ()),
    env := (some CompileExamples.r1, some CompileExamples.r0, ()) }
private def b4 : State C Two :=
  { b0 with heap := CompileExamples.hp }
private def aliases : State C Three :=
  { storage := Storage.init C, H := CompileExamples.H, heap := CompileExamples.hp,
    env := (some CompileExamples.r0, some CompileExamples.r1, some CompileExamples.r0, ()) }
private def bottom : State C Three :=
  { aliases with env := (some CompileExamples.r0, some CompileExamples.r1, some CompileExamples.r1, ()) }
private def both : State C Three :=
  { aliases with env := (some CompileExamples.r0, some CompileExamples.r0, some CompileExamples.r1, ()) }

private theorem allocateA_run :
    allocateA.run (State.init C) = .ok ⟨a0, ⟨[A], rfl⟩⟩ := by
  with_unfolding_all rfl
private theorem writeA0_run :
    writeA0.run a0 = .ok ⟨a7, List.prefix_refl _⟩ := by
  with_unfolding_all rfl
private theorem writeA1_run :
    writeA1.run a7 = .ok ⟨a79, List.prefix_refl _⟩ := by
  with_unfolding_all rfl
private theorem allocateB_run :
    allocateB.run a79 = .ok ⟨b0, ⟨[A], rfl⟩⟩ := by
  with_unfolding_all rfl
private theorem writeB0_run :
    writeB0.run b0 = .ok ⟨b4, List.prefix_refl _⟩ := by
  with_unfolding_all rfl
private theorem aliasA_run :
    aliasA.run b4 = .ok ⟨aliases, List.prefix_refl _⟩ := by
  with_unfolding_all rfl
private theorem bottomB_run :
    bottomB.run aliases = .ok ⟨bottom, List.prefix_refl _⟩ := by
  with_unfolding_all rfl
private theorem middleA_run :
    middleA.run bottom = .ok ⟨both, List.prefix_refl _⟩ := by
  with_unfolding_all rfl
private theorem zeroValue_run :
    zeroValue.run both = .ok ⟨σ, List.prefix_refl _⟩ := by
  with_unfolding_all rfl

/-- Allocate two arrays, populate both, retain two aliases to the first,
rearrange locals and introduce the scalar used by the existing fixture. -/
def populatedBuilder : Prog C [] Γ :=
  Prog.cons allocateA (.cons writeA0 (.cons writeA1 (.cons allocateB
    (.cons writeB0 (.cons aliasA (.cons bottomB (.cons middleA (.cons zeroValue .nil))))))))

/-- The exact populated typed state is reachable from a fresh intrinsic state. -/
theorem fresh_state_reaches_fixture :
    populatedBuilder.run (State.init C) = .ok ⟨σ, ⟨σ.H, rfl⟩⟩ := by
  unfold populatedBuilder
  rw [Prog.run_cons_ok allocateA_run, Prog.run_cons_ok writeA0_run,
    Prog.run_cons_ok writeA1_run, Prog.run_cons_ok allocateB_run,
    Prog.run_cons_ok writeB0_run, Prog.run_cons_ok aliasA_run,
    Prog.run_cons_ok bottomB_run, Prog.run_cons_ok middleA_run,
    Prog.run_cons_ok zeroValue_run, Prog.run_nil]
  rfl

/-- The full output machine of the concrete mixed stage. -/
def stagedOutput : Machine := writeMachine (writeMachine machine 17 w[5]) 3 w[5]

private def writeCode : List Instr :=
  [.push w[5], .mload 1, .push w[0]] ++ (arrayAddrStackCode ++ [.mstoreAt])
private def readCode : List Instr :=
  [.mload 2, .push w[0]] ++ (arrayAddrStackCode ++ [.mloadAt, .mstore 3])

private theorem write_run (tail : List Word) :
    run writeCode {machine with stack := tail} =
      .ok (writeMachine {machine with stack := tail} 17 w[5]) 0 := by
  let m : Machine := {machine with stack := tail}
  have hp : run [.push w[5], .mload 1, .push w[0]] m =
      .ok (((m.push w[5]).push w[16]).push w[0]) 0 := by rfl
  have ha : run arrayAddrStackCode (((m.push w[5]).push w[16]).push w[0]) =
      .ok ((m.push w[5]).push w[17]) 0 := by
    exact arrayAddrStack_run (m.push w[5]) ⟨16, by decide⟩ ⟨0, by decide⟩
      2 (by decide) rfl
  rw [writeCode, run_append_ok hp, run_append_ok ha]
  rfl

private theorem read_run (tail : List Word) :
    run readCode (writeMachine {machine with stack := tail} 17 w[5]) =
      .ok {stagedOutput with stack := tail} 0 := by
  let m : Machine := writeMachine {machine with stack := tail} 17 w[5]
  have hp : run [.mload 2, .push w[0]] m =
      .ok ((m.push w[16]).push w[0]) 0 := by rfl
  have ha : run arrayAddrStackCode ((m.push w[16]).push w[0]) =
      .ok (m.push w[17]) 0 := by
    exact arrayAddrStack_run m ⟨16, by decide⟩ ⟨0, by decide⟩ 2 (by decide) rfl
  rw [readCode, run_append_ok hp, run_append_ok ha]
  rfl

/-- Exact concrete non-stack independence, stronger than re-establishing Rep. -/
theorem concrete_tail_independence (tail : List Word) :
    run stagedCode {machine with stack := tail} =
      .ok {stagedOutput with stack := tail} 0 := by
  have hc : memoryCompiled.code = writeCode ++ readCode := by rfl
  rw [stagedCode, run_append_ok (assertion_run _), hc, run_append_ok (write_run tail)]
  exact read_run tail

/-- An actual saved-tail run of a fresh-state-reachable source fixture. -/
theorem reachable_nontrivial :
    populatedBuilder.run (State.init C) = .ok ⟨σ, ⟨σ.H, rfl⟩⟩ ∧
      run stagedCode {machine with stack := [w[41], w[19]]} =
        .ok {stagedOutput with stack := [w[41], w[19]]} 0 :=
  ⟨fresh_state_reaches_fixture, concrete_tail_independence _⟩

end Solidity.Backend.Passes.ReachabilityControls
