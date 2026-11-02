import Solidity.Evm.Compiler
import Solidity.Syntax.Splice

/-!
Nonvacuous checked compiler inputs and source/compiled observations for
memory-to-storage copies, independence, replacement, cleanup and refusals.
-/
namespace Solidity.Evm.Memory.StorageCopyExamples
open Semantics
private def C : Contract := contract!{
  struct Record { uint n; bool flag; int signed; }
  struct Holder { Record item; }
  uint[] values;
  int[] signedValues;
  bool[] flags;
  Record stored;
  Holder holder;
  mapping(uint => Record) records;
  Record[] emptyRecords;
  uint[][] rows;
  mapping(uint => uint[]) arrayRecords;
}
local instance : InContract := ⟨C⟩
private def recordName : Name := (C.structName? "Record").getD ""
private def bases : Nat → Fin W := fun _ => wmod 0
private def initial : State C [] := State.init C
private def machine : Machine := {Machine.init with stack := [w[77]], mem := fun a =>
  if a = 0 then w[128] else if a = 63 then w[99] else w[0]}
private theorem noRef {R : RefTy} (r : HRef [] R) : False := by cases r.get?

theorem initial_repr : StateRepr 4 1 64 (Frag.init []) initial bases machine ∧
    StructAllocatorRepr initial.heap bases 64 (wmod 128) machine := by
  have hh : HeapRepr initial.heap bases 64 machine :=
    ⟨fun r => (noRef r).elim, fun r => (noRef r).elim, fun r => (noRef r).elim⟩
  have hs : StructHeapRepr initial.heap bases 64 machine :=
    ⟨fun r => (noRef r).elim, fun r => (noRef r).elim, fun r => (noRef r).elim⟩
  have hx : StructArraySeparated initial.heap bases := fun _ r => (noRef r).elim
  have hc := (Sim.init C 0 W_pos (fun _ => 0) ⟨0, W_pos⟩ rfl).mono (L' := 4) (by decide) (by decide)
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
  uint[] memory xs = new uint[](3);
  xs[0] = 7; xs[1] = 8; xs[2] = 9;
  values = xs;
  xs[0] = 99;
  require(values[0] == 7 && values.length == 3);
  uint[] memory ys = new uint[](1); ys[0] = 4;
  values = ys;
  require(values.length == 1 && values[0] == 4);
  values = xs;
  require(values[0] == 99 && values[2] == 9);
  uint[] memory zs = new uint[](0); values = zs;
  require(values.length == 0);
  values = ys; ys[0] = 55;
  require(values[0] == 4);
  Record memory r;
  r.n = 12; r.flag = true; r.signed = -3;
  stored = r;
  r.n = 77;
  holder.item = r;
  records[3] = r;
  r.flag = false;
  require(stored.n == 12 && stored.flag && stored.signed == -3);
  require(holder.item.n == 77 && holder.item.flag);
  require(records[3].n == 77 && records[3].flag);
} : Prog C [] _)
private def compiled : Compiler.Compilation 1 (Frag.init []) program :=
  (Compiler.compile 1 (Frag.init []) program).get (by decide +kernel)
attribute [irreducible] compiled

theorem compiled_input : compiled.Input 4 64 bases initial machine := by
  apply (compiled.memory_copy_input (by decide +kernel) 4 64 bases initial machine).mpr
  exact ⟨initial_repr.1, by decide +kernel,
    .inr ⟨by decide, wmod 128, initial_repr.2, by decide +kernel⟩, by decide +kernel⟩

theorem compiled_agrees : compiled.Agrees 4 64 bases initial machine := compiled.correct compiled_input

def sourceObservation : Option (List Int) := do
  let o ← (program.run initial).toOption
  let v : ArrView (.prim .uint) := (o.st.storage.get (f := "values") (T := .ref (.array (.prim .uint))) (by decide +kernel)).view
  let stored : SFields (structDef recordName) := (o.st.storage.get (f := "stored") (T := .ref (.struct recordName)) (by decide +kernel)).view
  pure ((v.n : Int) :: v.elems.toList.map (fun x => x.view.1) ++
    [(stored.get (f := "n") (T := .prim .uint) (by decide +kernel)).view.1,
     (stored.get (f := "signed") (T := .prim .int) (by decide +kernel)).view.1])

theorem source_observation : sourceObservation = some [1, 4, 12, -3] := by decide +kernel

private def targetObservation : Option (List Nat) := do
  let .ok m _ := run compiled.code machine | none
  pure ([m.store (rootSlot C "values"), m.store (.data (rootSlot C "values") 0),
    m.store (.data (rootSlot C "values") 1), m.store (.data (rootSlot C "values") 2),
    m.store (rootSlot C "stored"), (payloadWord (m.mem 63)).val] ++ m.stack.map (fun w => (payloadWord w).val))

/-- info: some [1, 4, 0, 0, 12, 99, 77] -/
#guard_msgs in #eval targetObservation

private def signedProgram := (sol{
  int[] memory xs = new int[](2); xs[0] = -7; xs[1] = 9; signedValues = xs;
  xs[0] = -11; require(signedValues[0] == -7);
  bool[] memory bs = new bool[](2); bs[0] = true; flags = bs;
  bs[0] = false; require(flags[0] && !flags[1]);
} : Prog C [] _)
private def signedCompiled : Compiler.Compilation 1 (Frag.init []) signedProgram :=
  (Compiler.compile 1 (Frag.init []) signedProgram).get (by decide +kernel)
attribute [irreducible] signedCompiled

theorem signed_input : signedCompiled.Input 4 64 bases initial machine := by
  apply (signedCompiled.memory_copy_input (by decide +kernel) 4 64 bases initial machine).mpr
  exact ⟨initial_repr.1, by decide +kernel,
    .inr ⟨by decide, wmod 128, initial_repr.2, by decide +kernel⟩, by decide +kernel⟩
theorem signed_agrees : signedCompiled.Agrees 4 64 bases initial machine := signedCompiled.correct signed_input

private def signedTarget : Option (List Nat) := do
  let .ok m _ := run signedCompiled.code machine | none
  pure [m.store (.data (rootSlot C "signedValues") 0), m.store (.data (rootSlot C "signedValues") 1),
    m.store (.data (rootSlot C "flags") 0), m.store (.data (rootSlot C "flags") 1)]
/-- info: some [115792089237316195423570985008687907853269984665640564039457584007913129639929, 9, 1, 0] -/
#guard_msgs in #eval signedTarget

theorem bound_invalid : ¬ compiled.Input 1 64 bases initial machine := by
  intro h
  have hb := ((compiled.memory_copy_input (by decide +kernel) 1 64 bases initial machine).mp h).2.2.2
  have hv : copyBoundProg program initial = 4 := by decide +kernel
  rw [hv] at hb
  omega

private def badDestination := (sol{ Record memory r; emptyRecords[0] = r; } : Prog C [] _)
private def badCompiled : Compiler.Compilation 1 (Frag.init []) badDestination :=
  (Compiler.compile 1 (Frag.init []) badDestination).get (by decide +kernel)
attribute [irreducible] badCompiled

theorem bad_input : badCompiled.Input 4 64 bases initial machine := by
  apply (badCompiled.memory_copy_free_input (by decide +kernel) 4 64 bases initial machine).mpr
  exact ⟨initial_repr.1, by decide +kernel,
    .inr ⟨by decide, wmod 128, initial_repr.2, by decide +kernel⟩⟩
theorem bad_agrees : badCompiled.Agrees 4 64 bases initial machine := badCompiled.correct bad_input
theorem bad_source : badDestination.run initial = .error .revert := by rfl
/-- info: true -/
#guard_msgs in #eval (run badCompiled.code machine).isRevert

theorem signed_source_success : (signedProgram.run initial).toOption.isSome = true := by decide +kernel

private def badArrayDestination := (sol{
  uint[] memory xs = new uint[](3); rows[0] = xs;
} : Prog C [] _)
private def badArrayCompiled : Compiler.Compilation 1 (Frag.init []) badArrayDestination :=
  (Compiler.compile 1 (Frag.init []) badArrayDestination).get (by decide +kernel)
attribute [irreducible] badArrayCompiled

theorem failed_copy_bound_zero : copyBoundProg badArrayDestination initial = 0 := by decide +kernel

theorem initial_repr_one : StateRepr 1 1 64 (Frag.init []) initial bases machine := by
  have h := initial_repr.1
  have hc := Sim.init C 0 W_pos (fun _ => 0) ⟨0, W_pos⟩ rfl
  refine ⟨?_, h.heap, h.pointers, h.locals, h.structs, h.separated, h.refs⟩
  refine ⟨hc.store, ?_, ?_, hc.net, hc.netSelf, hc.bound, ?_, hc.env, hc.funds, hc.oracle⟩
  · intro p i; nomatch i
  · intro R i hi; nomatch i
  · intro R i hi; nomatch i

theorem failed_array_input : badArrayCompiled.Input 1 64 bases initial machine := by
  apply (badArrayCompiled.memory_copy_input (by decide +kernel) 1 64 bases initial machine).mpr
  exact ⟨initial_repr_one, by decide +kernel,
    .inr ⟨by decide, wmod 128, initial_repr.2, by decide +kernel⟩, by decide +kernel⟩
theorem failed_array_agrees : badArrayCompiled.Agrees 1 64 bases initial machine :=
  badArrayCompiled.correct failed_array_input
theorem failed_array_source : badArrayDestination.run initial = .error .revert := by rfl
/-- info: true -/
#guard_msgs in #eval (run badArrayCompiled.code machine).isRevert

private def unreachable := (sol{
  require(false); uint[] memory xs = new uint[](3); values = xs;
} : Prog C [] _)
theorem unreachable_bound_zero : copyBoundProg unreachable initial = 0 := by decide +kernel

example : arrayCopyStore (WordStore.write WordStore.zero (.data (.root 0) 5) 123)
    (.root 0) 0 (fun _ => wmod 9) (.data (.root 0) 5) = 123 := by
  rw [arrayCopyStore, rangeStore, WordStore.write_other _ _ (by decide)]
  decide +kernel

private def referenceElements := (sol{ Record[] memory xs = new Record[](1); emptyRecords = xs; } : Prog C [] _)
example : (Compiler.compile 1 (Frag.init []) referenceElements).isNone = true := by decide +kernel

/-- A shrinking copy retains a nonzero slot beyond both live lengths. -/
example : arrayCopyStore
    (WordStore.write (WordStore.write WordStore.zero (.root 0) 3) (.data (.root 0) 5) 123)
    (.root 0) 1 (fun _ => wmod 9) (.data (.root 0) 5) = 123 := by decide +kernel

private def refArrayCtx : Ctx := [.mem (.array (.ref (.struct recordName)))]
private def refArrayCopy : Prog C refArrayCtx refArrayCtx :=
  .cons (.assignFromMem (.root "emptyRecords" (by decide +kernel))
    (.var .here (by decide +kernel))) .nil
/-- Reference-element copying itself is refused, independently of allocation. -/
example : (Compiler.compile 1 (Frag.init refArrayCtx) refArrayCopy).isNone = true := by decide +kernel

private def holderName : Name := (C.structName? "Holder").getD ""
private def refStructCtx : Ctx := [.mem (.struct holderName)]
private def refStructCopy : Prog C refStructCtx refStructCtx :=
  .cons (.assignFromMem (.root "holder" (by decide +kernel))
    (.var .here (by decide +kernel))) .nil
/-- A reference-bearing struct endpoint is refused even with an initialized pointer. -/
example : (Compiler.compile 1 (Frag.init refStructCtx) refStructCopy).isNone = true := by decide +kernel


namespace RuntimeLength

private def Γ : Ctx := [.val .uint]
private def Δ : Ctx := [.mem (.array (.prim .uint)), .val .uint]
private def state (n : Nat) : State C Γ :=
  (State.init C).push (t := .val .uint) (indexValue (wmod n))
private def machine (n : Nat) : Machine := {Machine.init with stack := [w[77]], mem := fun a =>
  if a = 0 then w[128] else if a = 1 then (Word.val (wmod n))
  else if a = 63 then w[99] else w[0]}
private def positive : Val C Δ .bool := .binop .gt rfl rfl
  (.simple (.local (.there .here))) (.simple (.lit 0 rfl))
private def writeFirst (v : Nat) (hv : (v : Int) < W) : Prog C Δ Δ :=
  .cons (.assignMem (.index .dyn (.var .here rfl) (.simple (.lit 0 rfl)))
    (.val (.simple (.lit v (by
      change decide (0 ≤ (v : Int) ∧ (v : Int) < (W : Int)) = true
      exact decide_eq_true ⟨Int.natCast_nonneg _, hv⟩))))) .nil
private def program : Prog C Γ Δ :=
  .cons (.require (.binop .le rfl rfl (.simple (.local .here)) (.simple (.lit 3 rfl))))
  (.cons (.declMem (.array (.prim .uint)) (.user "xs")
    (some (.newArr (.local .here) rfl)) rfl rfl)
  (.cons (.ite positive (writeFirst 17 (by decide)) .nil)
  (.cons (.assignFromMem (.root "values" (by decide +kernel)) (.var .here rfl))
  (.cons (.assignFromMem
    (.index (IndexTy.map (k := .uint)) (.loc (.root "arrayRecords" (by decide +kernel))) (.simple (.lit 5 rfl)))
    (.var .here rfl))
  (.cons (.ite positive (writeFirst 99 (by decide)) .nil) .nil)))))

/-- The same compiled code reads its length from an input local. -/
private def compiled : Compiler.Compilation 1 (Frag.init Γ) program :=
  (Compiler.compile 1 (Frag.init Γ) program).get (by decide +kernel)
attribute [irreducible] compiled

private theorem initial_repr (n : Nat) :
    StateRepr 4 1 64 (Frag.init Γ) (state n) bases (machine n) ∧
    StructAllocatorRepr (state n).heap bases 64 (wmod 128) (machine n) := by
  have hh : HeapRepr (state n).heap bases 64 (machine n) :=
    ⟨fun r => (noRef r).elim, fun r => (noRef r).elim, fun r => (noRef r).elim⟩
  have hs : StructHeapRepr (state n).heap bases 64 (machine n) :=
    ⟨fun r => (noRef r).elim, fun r => (noRef r).elim, fun r => (noRef r).elim⟩
  have hx : StructArraySeparated (state n).heap bases := fun _ r => (noRef r).elim
  have hc := (Sim.init C 0 W_pos (fun _ => 0) ⟨0, W_pos⟩ rfl).mono (L' := 4) (by decide) (by decide)
  refine ⟨⟨?_, hh, ?_, by decide, hs, hx, ?_⟩,
    ⟨⟨hh, ?_, fun r => (noRef r).elim⟩, hs, hx, fun r => (noRef r).elim⟩⟩
  · refine ⟨hc.store, ?_, ?_, hc.net, hc.netSelf, hc.bound, ?_, hc.env, hc.funds, hc.oracle⟩
    · intro p i
      cases i with
      | here => exact ReprV.uint_of rfl
      | there i => nomatch i
    · intro R i hi; cases i with | there i => nomatch i
    · intro R i hi; cases i with | there i => nomatch i
  · intro R i; cases i with | there i => nomatch i
  · intro s f R r hf; exact (noRef r).elim
  · refine ⟨by decide, by decide, rfl, ?_⟩
    intro a ha
    change 128 ≤ a at ha
    simp only [machine]
    split <;> rename_i he
    · omega
    · split <;> rename_i he
      · omega
      · split <;> rename_i he
        · omega
        · rfl

theorem zero_input : compiled.Input 4 64 bases (state 0) (machine 0) := by
  apply (compiled.memory_copy_input (by decide +kernel) 4 64 bases (state 0) (machine 0)).mpr
  exact ⟨(initial_repr 0).1, by decide +kernel,
    .inr ⟨by decide, wmod 128, (initial_repr 0).2, by decide +kernel⟩, by decide +kernel⟩
theorem one_input : compiled.Input 4 64 bases (state 1) (machine 1) := by
  apply (compiled.memory_copy_input (by decide +kernel) 4 64 bases (state 1) (machine 1)).mpr
  exact ⟨(initial_repr 1).1, by decide +kernel,
    .inr ⟨by decide, wmod 128, (initial_repr 1).2, by decide +kernel⟩, by decide +kernel⟩
theorem three_input : compiled.Input 4 64 bases (state 3) (machine 3) := by
  apply (compiled.memory_copy_input (by decide +kernel) 4 64 bases (state 3) (machine 3)).mpr
  exact ⟨(initial_repr 3).1, by decide +kernel,
    .inr ⟨by decide, wmod 128, (initial_repr 3).2, by decide +kernel⟩, by decide +kernel⟩
/-- The rejected length never reaches allocation or a destination write. -/
theorem guarded_input : compiled.Input 4 64 bases (state 4) (machine 4) := by
  apply (compiled.memory_copy_input (by decide +kernel) 4 64 bases (state 4) (machine 4)).mpr
  exact ⟨(initial_repr 4).1, by decide +kernel, .inl (by decide +kernel), by decide +kernel⟩

theorem zero_agrees : compiled.Agrees 4 64 bases (state 0) (machine 0) := compiled.correct zero_input
theorem one_agrees : compiled.Agrees 4 64 bases (state 1) (machine 1) := compiled.correct one_input
theorem three_agrees : compiled.Agrees 4 64 bases (state 3) (machine 3) := compiled.correct three_input
theorem guarded_agrees : compiled.Agrees 4 64 bases (state 4) (machine 4) := compiled.correct guarded_input

private def sourceObservation (n : Nat) : Option (List Nat) := do
  let o ← (program.run (state n)).toOption
  let v : ArrView (.prim .uint) :=
    (o.st.storage.get (f := "values") (T := .ref (.array (.prim .uint))) (by decide +kernel)).view
  let mp := (o.st.storage.get (f := "arrayRecords")
    (T := .ref (.mapping .uint (.ref (.array (.prim .uint))))) (by decide +kernel)).view
  let vmap : ArrView (.prim .uint) := ((lookupBy (5 : Int) mp.1.hashed).getD mp.2).view
  pure ((v.n :: v.elems.toList.map (fun x => x.view.1.toNat)) ++
    (vmap.n :: vmap.elems.toList.map (fun x => x.view.1.toNat)))
private def targetObservation (n : Nat) : Option (List Nat) := do
  let .ok m _ := run compiled.code (machine n) | none
  let root := rootSlot C "values"
  let mapped := Slot.hash (wmod 5) (rootSlot C "arrayRecords") 0
  pure ([m.store root, m.store (.data root 0), m.store mapped, m.store (.data mapped 0),
    (payloadWord (m.mem 129)).val, (payloadWord (m.mem 63)).val] ++
    m.stack.map (fun x => (payloadWord x).val))

theorem source_zero : sourceObservation 0 = some [0, 0] := by decide +kernel
theorem source_one : sourceObservation 1 = some [1, 17, 1, 17] := by decide +kernel
theorem source_three : sourceObservation 3 = some [3, 17, 0, 0, 3, 17, 0, 0] := by decide +kernel
theorem source_guard : program.run (state 4) = .error .revert := by rfl
/-- info: some [0, 0, 0, 0, 0, 99, 77] -/
#guard_msgs in #eval targetObservation 0
/-- info: some [1, 17, 1, 17, 99, 99, 77] -/
#guard_msgs in #eval targetObservation 1
/-- info: some [3, 17, 3, 17, 99, 99, 77] -/
#guard_msgs in #eval targetObservation 3
/-- info: true -/
#guard_msgs in #eval (run compiled.code (machine 4)).isRevert

end RuntimeLength

end Solidity.Evm.Memory.StorageCopyExamples
