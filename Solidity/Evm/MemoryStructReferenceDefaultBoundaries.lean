import Solidity.Evm.MemoryStructReferenceDefaultLiterals

/-! Finite member/whole-local deletion, model-only empty children, zero-word
refusal, insufficient capacity and an unreached allocation with no usable cursor. -/
namespace Solidity.Evm.Memory.StructReferenceDefaultBoundaries
open Semantics StructReferenceDefaultExamples
local instance : InContract := ⟨C⟩

private def deletion := (sol{
  Wrapper memory w;
  w.holder.leaf.n = 7;
  Holder memory saved = w.holder;
  Leaf memory savedLeaf = w.holder.leaf;
  delete w.holder;
  require(saved.leaf.n == 7 && savedLeaf.n == 7 && w.holder.leaf.n == 0);
  Wrapper memory same = w;
  delete w;
  w.holder.leaf.n = 9;
  require(same.holder.leaf.n == 0 && saved.leaf.n == 7 && savedLeaf.n == 7 && w.holder.leaf.n == 9);
} : Prog C [] _)
private def deleteCompiled : Compiler.Compilation 1 (Frag.init []) deletion :=
  (Compiler.compile 1 (Frag.init []) deletion).get (by decide +kernel)
attribute [irreducible] deleteCompiled

theorem delete_cost : allocationCostProg deletion initial = 22 := by decide +kernel
theorem delete_input : deleteCompiled.Input 1 64 bases initial machine := by
  apply (deleteCompiled.memory_input (by decide +kernel) 1 64 bases initial machine).mpr
  exact ⟨initial_repr.1, by decide +kernel,
    .inr ⟨by decide, wmod 128, initial_repr.2, by decide +kernel⟩⟩
theorem delete_agrees : deleteCompiled.Agrees 1 64 bases initial machine := deleteCompiled.correct delete_input

theorem delete_target : observeTarget (run deleteCompiled.code machine) =
    some [77,150,99,7,0,0,128,130,0,139,0,0,0,0,136,138,0,9,0,0,142,144,0,145,0,0] := by decide +kernel
theorem delete_source : observeSource (deletion.run initial) = some [11,7,0,0,0,9,0,0,0,0] := by decide +kernel

-- An invalid encoded definition has no model fields. Ordinary source admission
-- still refuses it; the raw typed model must nevertheless reserve its padding.
private def emptyName : Name := "Empty{x:uint;x:uint}"
private def modelName : Name := "Model{empty:Empty{x:uint;x:uint};items:uint[]}"
private def emptyChild : Prog C [] [.mem (.struct modelName)] :=
  .cons (.declMem (.struct modelName) (.user "model") none (by decide +kernel) (by decide +kernel)) .nil
private def emptyCompiled : Compiler.Compilation 1 (Frag.init []) emptyChild :=
  (Compiler.compile 1 (Frag.init []) emptyChild).get (by decide +kernel)
attribute [irreducible] emptyCompiled

theorem empty_cost : allocationCostProg emptyChild initial = 4 := by decide +kernel
theorem empty_input : emptyCompiled.Input 1 64 bases initial machine := by
  apply (emptyCompiled.memory_input (by decide +kernel) 1 64 bases initial machine).mpr
  exact ⟨initial_repr.1, by decide +kernel,
    .inr ⟨by decide, wmod 128, initial_repr.2, by decide +kernel⟩⟩
theorem empty_agrees : emptyCompiled.Agrees 1 64 bases initial machine := emptyCompiled.correct empty_input
private def observeEmptyTarget : Out → Option (List Nat)
  | .ok m _ => do
    (m.stack ++ [m.mem 0, m.mem 63] ++ (List.range 5).map (fun i => m.mem (128+i))).mapM
      fun w => match w with | .val v => some v.val | .slot _ => none
  | _ => none
example : observeEmptyTarget (run emptyCompiled.code machine) = some [77,132,99,0,0,128,129,0] := by decide +kernel

private def refAt? (H : HTy) (i : Nat) (R : RefTy) : Option (HRef H R) :=
  if h : H[i]? = some R then some ⟨i,h⟩ else none
private def observeEmptySource {Δ : Ctx} : TRes (Solidity.Out C [] Δ) → Option (List Nat)
  | .ok o => do
    let r ← refAt? o.st.H 2 (.struct modelName)
    let empty := o.st.heap.field (T := .ref (.struct emptyName)) r (f := "empty") rfl
    let items := o.st.heap.field (T := .ref (.array (.prim .uint))) r (f := "items") rfl
    some [empty.id, items.id, o.st.heap.len items .dyn, o.st.H.length]
  | _ => none
example : observeEmptySource (emptyChild.run initial) = some [0,1,0,3] := by decide +kernel

private def modelGrowth := initial.heap.allocDefault (.struct modelName) (by decide +kernel)
private def modelBases (i : Nat) : Fin W := if i = 0 then wmod 128 else if i = 1 then wmod 129 else wmod 130
/-- Reserving zero words cannot represent the new parent's nonzero child pointer. -/
theorem zero_pointer_invalid : ¬ RefFieldsRepr modelGrowth.heap modelBases (writeMachine machine 130 w[0]) := by
  intro h
  have hh := h modelGrowth.val (f := "empty") (R := .struct emptyName) rfl
  have ha : (modelBases modelGrowth.val.id).val + fieldOffset (structDef modelName) "empty" = 130 := by
    decide +kernel
  have hb : modelBases (modelGrowth.heap.field modelGrowth.val
      (f := "empty") (T := .ref (.struct emptyName)) rfl).id = wmod 128 := by decide +kernel
  rw [ha, hb] at hh
  simp only [writeMachine, upd_same] at hh
  have he : (0 : Nat) = 128 := congrArg Fin.val (Word.val.inj hh)
  omega

private def full : Machine := writeMachine machine 0 (.val (wmod (W - 3)))
theorem empty_capacity_invalid : ¬ emptyCompiled.Input 1 64 bases initial full := by
  intro h
  have hi := ((emptyCompiled.memory_input (by decide +kernel) 1 64 bases initial full).mp h).2.2
  rcases hi with hz | ⟨_, c, ha, hs⟩
  · rw [empty_cost] at hz; cases hz
  · have he : c = wmod (W - 3) := Word.val.inj ha.arrays.free.cell.symm
    subst c
    rw [empty_cost] at hs
    exact (by decide +kernel : ¬ (wmod (W - 3)).val + 4 < W) hs

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
private def unreached := (sol{
  require(false);
  Wrapper memory w;
  delete w.holder;
} : Prog C [] _)
private def unreachedCompiled : Compiler.Compilation 1 (Frag.init []) unreached :=
  (Compiler.compile 1 (Frag.init []) unreached).get (by decide +kernel)
attribute [irreducible] unreachedCompiled
example : allocationCostProg unreached initial = 0 := by decide +kernel
theorem unreached_input : unreachedCompiled.Input 1 64 bases initial (writeMachine machine 0 w[0]) := by
  apply (unreachedCompiled.memory_input (by decide +kernel) 1 64 bases initial _).mpr
  exact ⟨cursor_state _, by decide +kernel, .inl (by decide +kernel)⟩
theorem unreached_agrees : unreachedCompiled.Agrees 1 64 bases initial (writeMachine machine 0 w[0]) :=
  unreachedCompiled.correct unreached_input
example : unreached.run initial = .error .revert := sourceReverted_eq _ (by decide +kernel)
example : run unreachedCompiled.code (writeMachine machine 0 w[0]) = .revert := targetReverted_eq _ (by decide +kernel)

#print axioms delete_agrees
#print axioms empty_agrees
#print axioms unreached_agrees
end Solidity.Evm.Memory.StructReferenceDefaultBoundaries
