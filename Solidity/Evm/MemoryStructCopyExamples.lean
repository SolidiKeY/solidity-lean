import Solidity.Evm.Compiler

/-!
Ordinary Solidity storage-to-memory copies retain populated primitive values
and allocate independent objects. Public agreement is inhabited alongside
source/target observations of earlier aliases, scoped copies, deletion and
later mixed allocations. Refused inputs and an unreached copy pin the bounds.
-/
namespace Solidity.Evm.Memory.StructCopyExamples
open Semantics

private def C : Contract := contract!{
  struct Record { uint n; bool flag; int signed; }
  Record stored;
}
local instance : InContract := ⟨C⟩
private def recordName : Name := (C.structName? "Record").getD ""
private def bases : Nat → Fin W := fun _ => wmod 0
private def initial : State C [] := State.init C
private def machine : Machine :=
  {Machine.init with stack := [w[77]], mem := fun a =>
    if a = 0 then w[128] else if a = 63 then w[99] else w[0]}
private theorem noRef {R : RefTy} (r : HRef [] R) : False := by cases r.get?

theorem initial_repr : StateRepr 1 1 64 (Frag.init []) initial bases machine ∧
    StructAllocatorRepr initial.heap bases 64 (wmod 128) machine := by
  have hh : HeapRepr initial.heap bases 64 machine :=
    ⟨fun r => (noRef r).elim, fun r => (noRef r).elim, fun r => (noRef r).elim⟩
  have hs : StructHeapRepr initial.heap bases 64 machine :=
    ⟨fun r => (noRef r).elim, fun r => (noRef r).elim, fun r => (noRef r).elim⟩
  have hx : StructArraySeparated initial.heap bases := fun _ r => (noRef r).elim
  have hc := Sim.init C 0 W_pos (fun _ => 0) ⟨0, W_pos⟩ rfl
  refine ⟨⟨?_, hh, ?_, by decide, hs, hx, ?_⟩,
    ⟨⟨hh, ?_, fun r => (noRef r).elim⟩, hs, hx, fun r => (noRef r).elim⟩⟩
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

private def program := (sol{
  stored.n = 7;
  stored.flag = true;
  stored.signed = -3;
  Record memory first = stored;
  Record memory same = first;
  uint[] memory xs = new uint[](2);
  xs[0] = first.n;
  first.n = 11;
  first.signed = -9;
  stored.n = 20;
  stored.flag = false;
  stored.signed = -5;
  Record memory second = stored;
  first = stored;
  require(same.n == 11 && same.flag && same.signed == -9);
  require(second.n == 20 && !second.flag && second.signed == -5);
  require(first.n == 20 && !first.flag && first.signed == -5);
  first.n = 31;
  second.flag = true;
  xs[1] = first.n + same.n;
  { Record memory inside = stored; inside.n = 99; }
  require(stored.n == 20 && !stored.flag && stored.signed == -5);
  delete second;
  bool[] memory later = new bool[](1);
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
    (m.stack ++ [m.mem 0, m.mem 63] ++ (List.range 21).map (fun i => m.mem (128 + i))).mapM
      fun w => match w with | .val v => some v.val | .slot _ => none
  | _ => none

theorem target_observation : observeTarget (run compiled.code machine) =
    some [77, 148, 99, 11, 1, W - 9, 2, 7, 42, 20, 1, W - 5,
      31, 0, W - 5, 99, 0, W - 5, 0, 0, 0, 1, 0, 0] := by
  decide +kernel

private def refAt? (H : HTy) (i : Nat) (R : RefTy) : Option (HRef H R) :=
  if h : H[i]? = some R then some ⟨i, h⟩ else none
private def recordValues {H : HTy} (hp : Heap H) (i : Nat) : Option (List Int) := do
  let r ← refAt? H i (.struct recordName)
  let flag : Bool := hp.field r (f := "flag") (T := Ty.bool) (by decide +kernel)
  pure [(hp.field r (f := "n") (T := Ty.uint) (by decide +kernel)).1,
    if flag then 1 else 0,
    (hp.field r (f := "signed") (T := Ty.int) (by decide +kernel)).1]
private def observeSource {Δ : Ctx} : TRes (Solidity.Out C [] Δ) → Option (List Int)
  | .ok o => do
    let records ← [0, 2, 3, 4, 5].mapM (recordValues o.st.heap)
    let a ← refAt? o.st.H 1 (.array (.prim .uint))
    let later ← refAt? o.st.H 6 (.array (.prim .bool))
    let stored : SFields (structDef recordName) :=
      (o.st.storage.get (f := "stored") (T := .ref (.struct recordName)) (by decide +kernel)).view
    let flag : Bool := (stored.get (f := "flag") (T := Ty.bool) (by decide +kernel)).view
    pure (records.flatten ++ (o.st.heap.get a).val.map (·.1) ++
      [(o.st.heap.len later .dyn : Int), (stored.get (f := "n") (T := Ty.uint) (by decide +kernel)).view.1,
        if flag then 1 else 0,
        (stored.get (f := "signed") (T := Ty.int) (by decide +kernel)).view.1])
  | _ => none

theorem source_observation : observeSource (program.run initial) =
    some [11, 1, -9, 20, 1, -5, 31, 0, -5, 99, 0, -5, 0, 0, 0, 7, 42, 1, 20, 0, -5] := by
  decide +kernel

private def tooFull : Machine := writeMachine machine 0 (.val (wmod (W - 10)))

theorem capacity_invalid : ¬ compiled.Input 1 64 bases initial tooFull := by
  intro h
  have hi := ((compiled.memory_input (by decide +kernel) 1 64 bases initial tooFull).mp h).2.2
  rcases hi with hz | ⟨_, c, hc, hs⟩
  · rw [program_cost] at hz
    cases hz
  · have he : c = wmod (W - 10) := Word.val.inj hc.arrays.free.cell.symm
    subst c
    rw [program_cost] at hs
    have hw : 10 < W := by decide
    have hb : W - 10 < W := by omega
    rw [wmod_of_lt hb] at hs
    change W - 10 + 20 < W at hs
    omega

example : (compileProg 0 (Frag.init []) program).isNone = true := by decide +kernel

private def unreached := (sol{ require(false); Record memory skipped = stored; } : Prog C [] _)
private def unreachedCompiled : Compiler.Compilation 1 (Frag.init []) unreached :=
  (Compiler.compile 1 (Frag.init []) unreached).get (by decide +kernel)
attribute [irreducible] unreachedCompiled
private def noCapacity := writeMachine machine 0 w[0]

theorem unreached_cost : allocationCostProg unreached initial = 0 := by decide +kernel

theorem unreached_input : unreachedCompiled.Input 1 64 bases initial noCapacity := by
  apply (unreachedCompiled.memory_input (by decide +kernel) 1 64 bases initial noCapacity).mpr
  have hs : StateRepr 1 1 64 (Frag.init []) initial bases noCapacity := by
    refine ⟨?_, initial_repr.1.heap.localWrite 0 (by decide) _, ?_, by decide,
      initial_repr.1.structs.localWrite 0 (by decide) _, initial_repr.1.separated, ?_⟩
    · exact initial_repr.1.core.congrMem (by intro l hl hu; change l < 1 at hu; omega)
    · intro R i; nomatch i
    · exact RefFieldsRepr.localWrite initial_repr.1.refs initial_repr.1.structs 0 (by decide) _
  exact ⟨hs, by decide +kernel, .inl unreached_cost⟩

theorem unreached_agrees : unreachedCompiled.Agrees 1 64 bases initial noCapacity :=
  unreachedCompiled.correct unreached_input

private def reverted : Out → Bool | .revert => true | _ => false
theorem unreached_reverts : unreached.run initial = .error .revert ∧
    reverted (run unreachedCompiled.code noCapacity) = true := ⟨rfl, by decide +kernel⟩

end Solidity.Evm.Memory.StructCopyExamples
