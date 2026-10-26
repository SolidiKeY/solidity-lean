import Solidity.Evm.Compiler
import Solidity.Syntax.Splice

/-!
Ordinary Solidity struct literals use the default-allocation compiler clause
followed by field writes. These inhabited source/target examples mix aliases,
array allocation, signed fields and allocating rebinding.
-/
namespace Solidity.Evm.Memory.StructDefaultExamples
open Semantics

private def C : Contract := contract!{
  struct Record { uint n; bool flag; int signed; }
}
local instance : InContract := ⟨C⟩

private def bases : Nat → Fin W := fun _ => wmod 0
private def initial : State C [] := State.init C
private def machine : Machine :=
  {Machine.init with stack := [w[77]], mem := fun a =>
    if a = 0 then w[128] else if a = 63 then w[99] else w[0]}

private theorem noRef {R : RefTy} (r : HRef [] R) : False := by cases r.get?

/-- Source and machine input premises share an actual empty heap and free tail. -/
theorem initial_repr : StateRepr 1 1 64 (Frag.init []) initial bases machine ∧
    StructAllocatorRepr initial.heap bases 64 (wmod 128) machine := by
  have hh : HeapRepr initial.heap bases 64 machine :=
    ⟨fun r => (noRef r).elim, fun r => (noRef r).elim, fun r => (noRef r).elim⟩
  have hs : StructHeapRepr initial.heap bases 64 machine :=
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
  · intro s f R r hf
    exact (noRef r).elim
  · refine ⟨by decide, by decide, rfl, ?_⟩
    intro a ha
    change 128 ≤ a at ha
    simp only [machine]
    split <;> rename_i he
    · omega
    · split <;> rename_i he
      · omega
      · rfl

private def surface := (sol{
  Record memory first = Record(7, true, -3);
  Record memory same = first;
  uint[] memory xs = new uint[](2);
  xs[0] = first.n;
  same.flag = false;
  Record memory second = Record({signed: -9, flag: true, n: 11});
  first = Record(20, false, -5);
  require(same.n == 7 && same.flag == false && same.signed == -3);
  require(second.n == 11 && second.flag && second.signed == -9);
  xs[1] = first.n + second.n;
} : Prog C [] _)

private def compiled : Compiler.Compilation 1 (Frag.init []) surface :=
  (Compiler.compile 1 (Frag.init []) surface).get (by decide +kernel)
attribute [irreducible] compiled

theorem surface_cost : allocationCostProg surface initial = 12 := by decide +kernel

theorem compiled_input : compiled.Input 1 64 bases initial machine := by
  apply (compiled.memory_input (by decide +kernel) 1 64 bases initial machine).mpr
  exact ⟨initial_repr.1, by decide +kernel,
    .inr ⟨by decide, wmod 128, initial_repr.2, by decide +kernel⟩⟩

/-- The ordinary elaborator's constructors and rebinding use the public compiler. -/
theorem compiled_agrees : compiled.Agrees 1 64 bases initial machine := compiled.correct compiled_input

private def observeTarget : Out → Option (List Nat)
  | .ok m _ => do
    let words := m.stack ++ [m.mem 0, m.mem 63] ++ (List.range 13).map (fun i => m.mem (128 + i))
    words.mapM fun w => match w with | .val v => some v.val | .slot _ => none
  | _ => none

example : observeTarget (run compiled.code machine) =
    some [77, 140, 99, 7, 0, W - 3, 2, 7, 31, 11, 1, W - 9, 20, 0, W - 5, 0] := by
  decide +kernel

private def refAt? (H : HTy) (i : Nat) (R : RefTy) : Option (HRef H R) :=
  if h : H[i]? = some R then some ⟨i, h⟩ else none
private def recordName : Name := "Record{n:uint;flag:bool;signed:int}"

private def observeSource {Δ : Ctx} : TRes (Solidity.Out C [] Δ) → Option (List Int)
  | .ok o => do
    let r0 ← refAt? o.st.H 0 (.struct recordName)
    let a ← refAt? o.st.H 1 (.array (.prim .uint))
    let r1 ← refAt? o.st.H 2 (.struct recordName)
    let r2 ← refAt? o.st.H 3 (.struct recordName)
    let x ← o.st.heap.index a .dyn (indexValue (wmod 1))
    let flag : Bool := o.st.heap.field (T := .prim .bool) r0 (f := "flag") rfl
    some [(o.st.heap.field r0 (f := "n") rfl).1,
      (o.st.heap.field r0 (f := "signed") rfl).1,
      (o.st.heap.field r1 (f := "n") rfl).1,
      (o.st.heap.field r1 (f := "signed") rfl).1,
      (o.st.heap.field r2 (f := "n") rfl).1,
      (o.st.heap.field r2 (f := "signed") rfl).1, x.1, if flag then 1 else 0]
  | .error _ => none

example : observeSource (surface.run initial) = some [7, -3, 11, -9, 20, -5, 31, 0] := by
  decide +kernel

example : (Compiler.compile 0 (Frag.init []) surface).isSome = false := by decide +kernel

private def tooFull : Machine := writeMachine machine 0 (.val (wmod (W - 10)))

/-- The checked entry rejects an input whose remaining tail cannot hold reached allocations. -/
theorem capacity_invalid : ¬ compiled.Input 1 64 bases initial tooFull := by
  intro h
  have hi := ((compiled.memory_input (by decide +kernel) 1 64 bases initial tooFull).mp h).2.2
  rcases hi with hz | ⟨_, c, ha, hs⟩
  · rw [surface_cost] at hz
    cases hz
  · have he : c = wmod (W - 10) := Word.val.inj ha.arrays.free.cell.symm
    subst c
    rw [surface_cost] at hs
    have hn : ¬ (wmod (W - 10)).val + 12 < W := by decide +kernel
    exact hn hs

private def failedArgument := (sol{
  Record memory r = Record(5 / 0, true, -3);
} : Prog C [] _)
private def failedCompilation : Compiler.Compilation 1 (Frag.init []) failedArgument :=
  (Compiler.compile 1 (Frag.init []) failedArgument).get (by decide +kernel)
attribute [irreducible] failedCompilation

private theorem cursor_state (w : Word) :
    StateRepr 1 1 64 (Frag.init []) initial bases (writeMachine machine 0 w) := by
  have h := initial_repr.1
  have hc := h.core.congrMem (mem := upd machine.mem 0 w)
    (by intro l hl hu; change l < 1 at hu; omega)
  refine ⟨?_, h.heap.localWrite 0 (by decide) _, ?_, h.locals,
    h.structs.localWrite 0 (by decide) _, h.separated,
    RefFieldsRepr.localWrite h.refs h.structs 0 (by decide) _⟩
  · exact ⟨hc.store, hc.vals, hc.aliases, hc.net, hc.netSelf, hc.bound,
      hc.fragile, hc.env, hc.funds, hc.oracle⟩
  · intro R i; nomatch i

/-- The elaborated constructor allocates its object before its failing field RHS. -/
theorem failed_input : failedCompilation.Input 1 64 bases initial tooFull := by
  apply (failedCompilation.memory_input (by decide +kernel) 1 64 bases initial tooFull).mpr
  exact ⟨cursor_state _, by decide +kernel, .inr ⟨by decide, wmod (W - 10),
    initial_repr.2.advance (wmod (W - 10)) (by decide +kernel), by decide +kernel⟩⟩

theorem failed_agrees : failedCompilation.Agrees 1 64 bases initial tooFull :=
  failedCompilation.correct failed_input

private def reverted : Out → Bool
  | .revert => true
  | _ => false

example : failedArgument.run initial = .error .revert ∧
    reverted (run failedCompilation.code tooFull) = true := by
  constructor
  · rfl
  · decide +kernel

example : allocationCostProg failedArgument initial = 3 := by decide +kernel

/-- IR evaluates all constructor arguments before allocating the object. -/
private def irContract : Contract := { C with evalOrder := .viaIR }

private def failedArgumentIR := (sol[irContract]{
  Record memory r = Record(5 / 0, true, -3);
} : Prog irContract [] _)

example : allocationCostProg failedArgumentIR (State.init irContract) = 0 := by decide +kernel

/-- The last IR field must finish before allocation too; merely forcing
arguments which precede another argument would still allocate incorrectly. -/
private def failedLastArgumentIR := (sol[irContract]{
  Record memory r = Record(5, true, -3 / 0);
} : Prog irContract [] _)

example : allocationCostProg failedLastArgumentIR (State.init irContract) = 0 := by decide +kernel

private def failedLastArgumentLegacy := (sol{
  Record memory r = Record(5, true, -3 / 0);
} : Prog C [] _)

example : allocationCostProg failedLastArgumentLegacy initial = 3 := by decide +kernel

private def unreached := (sol{
  require(false);
  Record memory r = Record(5, true, -3);
} : Prog C [] _)
private def unreachedCompilation : Compiler.Compilation 1 (Frag.init []) unreached :=
  (Compiler.compile 1 (Frag.init []) unreached).get (by decide +kernel)
attribute [irreducible] unreachedCompilation

/-- An earlier revert reaches no struct allocation, even with an unusable cursor. -/
theorem unreached_input :
    unreachedCompilation.Input 1 64 bases initial (writeMachine machine 0 w[0]) := by
  apply (unreachedCompilation.memory_input (by decide +kernel) 1 64 bases initial _).mpr
  exact ⟨cursor_state _, by decide +kernel, .inl (by decide +kernel)⟩

theorem unreached_agrees :
    unreachedCompilation.Agrees 1 64 bases initial (writeMachine machine 0 w[0]) :=
  unreachedCompilation.correct unreached_input

example : allocationCostProg unreached initial = 0 ∧
    reverted (run unreachedCompilation.code (writeMachine machine 0 w[0])) = true := by decide +kernel

private def emptyStruct : Prog C [] [.mem (.struct "Empty{x:uint;x:uint}")] :=
  .cons (.declMem (.struct "Empty{x:uint;x:uint}") (.user "empty") none
    (by decide +kernel) (by decide +kernel)) .nil
private def emptyCompilation : Compiler.Compilation 1 (Frag.init []) emptyStruct :=
  (Compiler.compile 1 (Frag.init []) emptyStruct).get (by decide +kernel)
attribute [irreducible] emptyCompilation

-- The raw typed model permits names whose rejected definition has no fields;
-- the ordinary source elaborator refuses this duplicate-member name.
-- Its empty interval still reserves a cell and requires a real allocator.
example : allocationCostProg emptyStruct initial = 1 := by decide +kernel

theorem empty_input : emptyCompilation.Input 1 64 bases initial machine := by
  apply (emptyCompilation.memory_input (by decide +kernel) 1 64 bases initial machine).mpr
  exact ⟨initial_repr.1, by decide +kernel,
    .inr ⟨by decide, wmod 128, initial_repr.2, by decide +kernel⟩⟩

theorem empty_agrees : emptyCompilation.Agrees 1 64 bases initial machine :=
  emptyCompilation.correct empty_input

example : observeTarget (run emptyCompilation.code machine) =
    some [77, 129, 99, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0] := by decide +kernel

namespace Fields

private def program := (sol{
  Record memory r = Record(10, true, -8);
  Record memory alias = r;
  Record memory other = Record(99, true, 5);
  uint[] memory xs = new uint[](1);
  r.n += 5;
  alias.n *= 2;
  r.n -= 6;
  alias.n /= 3;
  r.n %= 5;
  uint post = alias.n++;
  uint pre = ++r.n;
  uint decPost = r.n−−;
  uint decPre = −−alias.n;
  r.n++;
  ++alias.n;
  alias.n−−;
  −−r.n;
  alias.signed += -2;
  int signedPost = r.signed++;
  int signedPre = ++alias.signed;
  alias.signed−−;
  −−r.signed;
  r.signed /= -2;
  alias.signed *= -3;
  r.signed -= -1;
  alias.signed %= -5;
  require(post == 3 && pre == 5 && decPost == 5 && decPre == 3);
  require(r.n == 3 && alias.signed == -4 && signedPost == -10 && signedPre == -8);
  xs[0] = post + pre + decPost + decPre;
  delete alias.flag;
  delete r.n;
  delete alias.signed;
  require(r.n == 0 && r.flag == false && r.signed == 0);
  require(other.n == 99 && other.flag && other.signed == 5);
} : Prog C [] _)
private def compiled : Compiler.Compilation 1 (Frag.init []) program :=
  (Compiler.compile 1 (Frag.init []) program).get (by decide +kernel)
attribute [irreducible] compiled

theorem compiled_input : compiled.Input 1 64 bases initial machine := by
  apply (compiled.memory_input (by decide +kernel) 1 64 bases initial machine).mpr
  exact ⟨initial_repr.1, by decide +kernel,
    .inr ⟨by decide, wmod 128, initial_repr.2, by decide +kernel⟩⟩

theorem compiled_agrees : compiled.Agrees 1 64 bases initial machine := compiled.correct compiled_input

example : observeTarget (run compiled.code machine) =
    some [77, 136, 99, 0, 0, 0, 99, 1, 5, 1, 16, 0, 0, 0, 0, 0] := by decide +kernel

private def observeSource {Δ : Ctx} : TRes (Solidity.Out C [] Δ) → Option (List Int)
  | .ok o => do
    let r ← refAt? o.st.H 0 (.struct recordName)
    let other ← refAt? o.st.H 1 (.struct recordName)
    let a ← refAt? o.st.H 2 (.array (.prim .uint))
    let x ← o.st.heap.index a .dyn (indexValue (wmod 0))
    let flag : Bool := o.st.heap.field (T := .prim .bool) r (f := "flag") rfl
    some [(o.st.heap.field r (f := "n") rfl).1,
      (o.st.heap.field r (f := "signed") rfl).1,
      (o.st.heap.field other (f := "n") rfl).1,
      (o.st.heap.field other (f := "signed") rfl).1, x.1, if flag then 1 else 0]
  | .error _ => none

example : observeSource (program.run initial) = some [0, 0, 99, 5, 16, 0] := by decide +kernel

private def failure (k : Fin 7) : Blk C [] :=
  match k.val with
  | 0 => ⟨_, (sol{
      Record memory r = Record(115792089237316195423570985008687907853269984665640564039457584007913129639935, true, 0);
      r.n++;
    } : Prog C [] _)⟩
  | 1 => ⟨_, (sol{
      Record memory r = Record(0, true, 0);
      −−r.n;
    } : Prog C [] _)⟩
  | 2 => ⟨_, (sol{
      Record memory r = Record(0, true, 57896044618658097711785492504343953926634992332820282019728792003956564819967);
      r.signed++;
    } : Prog C [] _)⟩
  | 3 => ⟨_, (sol{
      Record memory r = Record(0, true, -57896044618658097711785492504343953926634992332820282019728792003956564819968);
      −−r.signed;
    } : Prog C [] _)⟩
  | 4 => ⟨_, (sol{
      Record memory r = Record(7, true, 0);
      r.n /= 0;
    } : Prog C [] _)⟩
  | 5 => ⟨_, (sol{
      Record memory r = Record(0, true, -5);
      r.signed %= 0;
    } : Prog C [] _)⟩
  | _ => ⟨_, (sol{
      Record memory r = Record(0, true, -57896044618658097711785492504343953926634992332820282019728792003956564819968);
      r.signed /= -1;
    } : Prog C [] _)⟩

private theorem failure_accepted : ∀ k : Fin 7,
    (Compiler.compile 1 (Frag.init []) (failure k).2).isSome = true := by decide +kernel
private def failureCompilation (k : Fin 7) : Compiler.Compilation 1 (Frag.init []) (failure k).2 :=
  (Compiler.compile 1 (Frag.init []) (failure k).2).get (failure_accepted k)
attribute [irreducible] failureCompilation

private theorem failure_memory : ∀ k : Fin 7, (failureCompilation k).isMemory = true := by decide +kernel
private theorem failure_frame : ∀ k : Fin 7, 1 + frameNeedProg (failure k).2 ≤ 64 := by decide +kernel
private theorem failure_cost : ∀ k : Fin 7, allocationCostProg (failure k).2 initial = 3 := by decide +kernel

/-- All seven checked field failures have inhabited public input premises. -/
theorem failure_inputs (k : Fin 7) : (failureCompilation k).Input 1 64 bases initial machine := by
  apply ((failureCompilation k).memory_input (failure_memory k) 1 64 bases initial machine).mpr
  refine ⟨initial_repr.1, failure_frame k, .inr ⟨by decide, wmod 128, initial_repr.2, ?_⟩⟩
  rw [failure_cost k]
  decide +kernel

theorem failure_agrees (k : Fin 7) : (failureCompilation k).Agrees 1 64 bases initial machine :=
  (failureCompilation k).correct (failure_inputs k)

private def sourceReverted {Δ : Ctx} : TRes (Solidity.Out C [] Δ) → Bool
  | .error .revert => true
  | _ => false

/-- Unsigned/signed range edges and zero division/modulo revert in source and target. -/
theorem failures_revert : ∀ k : Fin 7,
    sourceReverted ((failure k).2.run initial) = true ∧
      reverted (run (failureCompilation k).code machine) = true := by decide +kernel

end Fields

namespace WholeDelete

private def program := (sol{
  Record memory r = Record(7, true, -3);
  Record memory same = r;
  uint[] memory xs = new uint[](1);
  Record memory other = Record(9, true, -5);
  delete r;
  require(r.n == 0 && r.flag == false && r.signed == 0);
  require(same.n == 7 && same.flag && same.signed == -3);
  r.n = 21; r.flag = true; r.signed = -11;
  Record memory afterFirst = r;
  {
    Record memory nested = r;
    delete nested;
    nested.n = 32;
    require(nested.flag == false && nested.signed == 0 && r.n == 21);
  }
  delete r;
  require(r.n == 0 && r.flag == false && r.signed == 0);
  require(afterFirst.n == 21 && afterFirst.flag && afterFirst.signed == -11);
  xs[0] = same.n + afterFirst.n + other.n;
  if (xs[0] == 37) { delete same; same.n = 41; } else { delete other; }
  require(same.n == 41 && other.n == 9 && other.flag && other.signed == -5);
} : Prog C [] _)

private def compiled : Compiler.Compilation 1 (Frag.init []) program :=
  (Compiler.compile 1 (Frag.init []) program).get (by decide +kernel)
attribute [irreducible] compiled

theorem program_cost : allocationCostProg program initial = 20 := by decide +kernel

theorem compiled_input : compiled.Input 1 64 bases initial machine := by
  apply (compiled.memory_input (by decide +kernel) 1 64 bases initial machine).mpr
  exact ⟨initial_repr.1, by decide +kernel,
    .inr ⟨by decide, wmod 128, initial_repr.2, by decide +kernel⟩⟩

theorem compiled_agrees : compiled.Agrees 1 64 bases initial machine := compiled.correct compiled_input

private def observeTarget : Out → Option (List Nat)
  | .ok m _ => do
    let words := m.stack ++ [m.mem 0, m.mem 63] ++ (List.range 21).map (fun i => m.mem (128 + i))
    words.mapM fun w => match w with | .val v => some v.val | .slot _ => none
  | _ => none

theorem target_observation : observeTarget (run compiled.code machine) =
    some [77, 148, 99, 7, 1, W - 3, 1, 37, 9, 1, W - 5,
      21, 1, W - 11, 32, 0, 0, 0, 0, 0, 41, 0, 0, 0] := by decide +kernel

private def observeSource {Δ : Ctx} : TRes (Solidity.Out C [] Δ) → Option (List Int)
  | .ok o => do
    let a ← refAt? o.st.H 1 (.array (.prim .uint))
    let x ← o.st.heap.index a .dyn (indexValue (wmod 0))
    let ns ← [0, 2, 3, 4, 5, 6].mapM fun i => do
      let r ← refAt? o.st.H i (.struct recordName)
      let flag : Bool := o.st.heap.field (T := .prim .bool) r (f := "flag") rfl
      pure [(o.st.heap.field r (f := "n") rfl).1, if flag then 1 else 0,
        (o.st.heap.field r (f := "signed") rfl).1]
    some (x.1 :: ns.flatten)
  | .error _ => none

theorem source_observation : observeSource (program.run initial) =
    some [37, 7, 1, -3, 9, 1, -5, 21, 1, -11, 32, 0, 0, 0, 0, 0, 41, 0, 0] := by
  decide +kernel

example : (Compiler.compile 0 (Frag.init []) program).isSome = false := by decide +kernel

theorem capacity_invalid : ¬ compiled.Input 1 64 bases initial tooFull := by
  intro h
  have hi := ((compiled.memory_input (by decide +kernel) 1 64 bases initial tooFull).mp h).2.2
  rcases hi with hz | ⟨_, c, ha, hs⟩
  · rw [program_cost] at hz
    cases hz
  · have he : c = wmod (W - 10) := Word.val.inj ha.arrays.free.cell.symm
    subst c
    rw [program_cost] at hs
    have hn : ¬ (wmod (W - 10)).val + 20 < W := by decide +kernel
    exact hn hs

private def unreached := (sol{
  Record memory r = Record(3, true, -4);
  require(false);
  delete r;
} : Prog C [] _)
private def unreachedCompilation : Compiler.Compilation 1 (Frag.init []) unreached :=
  (Compiler.compile 1 (Frag.init []) unreached).get (by decide +kernel)
attribute [irreducible] unreachedCompilation

theorem unreached_cost : allocationCostProg unreached initial = 3 := by decide +kernel

theorem unreached_input : unreachedCompilation.Input 1 64 bases initial tooFull := by
  apply (unreachedCompilation.memory_input (by decide +kernel) 1 64 bases initial tooFull).mpr
  exact ⟨cursor_state _, by decide +kernel, .inr ⟨by decide, wmod (W - 10),
    initial_repr.2.advance (wmod (W - 10)) (by decide +kernel), by decide +kernel⟩⟩

theorem unreached_agrees : unreachedCompilation.Agrees 1 64 bases initial tooFull :=
  unreachedCompilation.correct unreached_input

example : reverted (run unreachedCompilation.code tooFull) = true := by decide +kernel
example : (match unreached.run initial with | .error .revert => true | _ => false) = true := by decide +kernel

end WholeDelete

namespace DefaultArrays

private def program := (sol{
  uint[] memory u;
  int[] memory signedValues;
  bool[] memory flags;
  require(u.length == 0 && signedValues.length == 0 && flags.length == 0);
  uint[] memory old = u;
  u = new uint[](2);
  u[0] = 17;
  delete signedValues;
  flags = new bool[](1);
  flags[0] = true;
  Record memory r = Record(9, true, -4);
  { uint[] memory nested; require(nested.length == 0); }
  if (flags[0]) { delete flags; } else { delete u; }
  require(old.length == 0 && u[0] == 17 && signedValues.length == 0 && flags.length == 0);
  require(r.n == 9 && r.flag && r.signed == -4);
} : Prog C [] _)

private def compiled : Compiler.Compilation 1 (Frag.init []) program :=
  (Compiler.compile 1 (Frag.init []) program).get (by decide +kernel)
attribute [irreducible] compiled

theorem program_cost : allocationCostProg program initial = 14 := by decide +kernel

theorem compiled_input : compiled.Input 1 64 bases initial machine := by
  apply (compiled.memory_input (by decide +kernel) 1 64 bases initial machine).mpr
  exact ⟨initial_repr.1, by decide +kernel,
    .inr ⟨by decide, wmod 128, initial_repr.2, by decide +kernel⟩⟩

theorem compiled_agrees : compiled.Agrees 1 64 bases initial machine := compiled.correct compiled_input

private def observeTarget : Out → Option (List Nat)
  | .ok m _ => do
    let words := m.stack ++ [m.mem 0, m.mem 63] ++ (List.range 15).map (fun i => m.mem (128 + i))
    words.mapM fun w => match w with | .val v => some v.val | .slot _ => none
  | _ => none

theorem target_observation : observeTarget (run compiled.code machine) =
    some [77, 142, 99, 0, 0, 0, 2, 17, 0, 0, 1, 1, 9, 1, W - 4, 0, 0, 0] := by decide +kernel

private def observeSource {Δ : Ctx} : TRes (Solidity.Out C [] Δ) → Option (List Int)
  | .ok o => do
    let u ← refAt? o.st.H 3 (.array (.prim .uint))
    let i ← refAt? o.st.H 4 (.array (.prim .int))
    let b ← refAt? o.st.H 8 (.array (.prim .bool))
    let old ← refAt? o.st.H 0 (.array (.prim .uint))
    let r ← refAt? o.st.H 6 (.struct recordName)
    let x ← o.st.heap.index u .dyn (indexValue (wmod 0))
    some [o.st.heap.len old .dyn, o.st.heap.len u .dyn, x.1,
      o.st.heap.len i .dyn, o.st.heap.len b .dyn, (o.st.heap.field r (f := "n") rfl).1]
  | .error _ => none

theorem source_observation : observeSource (program.run initial) = some [0, 2, 17, 0, 0, 9] := by
  decide +kernel

example : (Compiler.compile 0 (Frag.init []) program).isSome = false := by decide +kernel

theorem capacity_invalid : ¬ compiled.Input 1 64 bases initial tooFull := by
  intro h
  have hi := ((compiled.memory_input (by decide +kernel) 1 64 bases initial tooFull).mp h).2.2
  rcases hi with hz | ⟨_, c, ha, hs⟩
  · rw [program_cost] at hz
    cases hz
  · have he : c = wmod (W - 10) := Word.val.inj ha.arrays.free.cell.symm
    subst c
    rw [program_cost] at hs
    have hn : ¬ (wmod (W - 10)).val + 14 < W := by decide +kernel
    exact hn hs

private def unreached := (sol{
  require(false);
  uint[] memory u;
  int[] memory signedValues;
  bool[] memory flags;
} : Prog C [] _)
private def unreachedCompilation : Compiler.Compilation 1 (Frag.init []) unreached :=
  (Compiler.compile 1 (Frag.init []) unreached).get (by decide +kernel)
attribute [irreducible] unreachedCompilation

theorem unreached_cost : allocationCostProg unreached initial = 0 := by decide +kernel

theorem unreached_input :
    unreachedCompilation.Input 1 64 bases initial (writeMachine machine 0 w[0]) := by
  apply (unreachedCompilation.memory_input (by decide +kernel) 1 64 bases initial _).mpr
  exact ⟨cursor_state _, by decide +kernel, .inl unreached_cost⟩

theorem unreached_agrees :
    unreachedCompilation.Agrees 1 64 bases initial (writeMachine machine 0 w[0]) :=
  unreachedCompilation.correct unreached_input

example : reverted (run unreachedCompilation.code (writeMachine machine 0 w[0])) = true := by decide +kernel
example : unreached.run initial = .error .revert := by rfl

end DefaultArrays
end Solidity.Evm.Memory.StructDefaultExamples
