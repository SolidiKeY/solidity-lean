import Solidity.Lowering.G17.IndexCapture

/-! Discriminating captured-index controls: the old object has length two
and its replacement length three. Index two must still fail on the captured
object; consulting the rebound caller slot would incorrectly succeed. -/
namespace Solidity.Lowering.G17.IndexCapture.Controls
private abbrev C := (default : Contract)
private abbrev TgtCtx : Ctx := [.mem bytesR,.mem bytesR]
private abbrev H : HTy := [bytesR,bytesR]
private def old : HRef H bytesR := ⟨0,rfl⟩
private def assigned : HRef H bytesR := ⟨1,rfl⟩
private def zero : PrimTy.uint.Denote := ⟨0,by decide⟩
private def target : State C TgtCtx :=
  { (State.init C) with
    H := H
    heap := (⟨[zero,zero],by decide⟩,⟨[zero,zero,zero],by decide⟩,())
    env := (some assigned,some old,()) }

private def indexTwo : Val C TgtCtx .uint := .simple (.lit 2 (by decide))
private def seven : Val C TgtCtx .uint := .simple (.lit 7 (by decide))
private def after : State C TgtCtx := target.setLocal (.there .here) (some assigned)
private def lateRead : Val C TgtCtx .uint :=
  .readMem (.index .dyn (.var (.there .here) rfl) indexTwo)
private def lateWrite : Stmt C TgtCtx TgtCtx :=
  .assignMem (.index .dyn (.var (.there .here) rfl) indexTwo) (.val seven)

/-- Rejects using the rebound slot instead of the captured object for either
an indexed read or write. Both arrays are live, so danglingness cannot explain
away the difference. Bounds failure, not result-value coincidence, detects it. -/
theorem captured_base_controls :
    (readOperand (.there .here) .here rfl .dyn indexTwo).run target = .error .revert ∧
    (writeCode (.there .here) .here rfl .dyn indexTwo seven).run target = .error .revert ∧
    (match lateRead.evalT after with | .ok _ => true | .error _ => false) = true ∧
    (match lateWrite.run after with | .ok _ => true | .error _ => false) = true := by
  constructor
  · rw [read_run target (.there .here) .here rfl old assigned rfl rfl]
    simp only [target, Nat.reducePow, assigned, old, bind, Except.bind, State.setLocal, indexTwo,
            Val.evalT, Simple.evalT, PrimTy.ofLit, TRes.ofOpt, Heap.index, Heap.get, Objs.get,
            MObj.elems_dyn, Int.reduceToNat, List.length_cons, List.length_nil, Nat.zero_add,
            Nat.reduceAdd, Nat.lt_irrefl, not_false_eq_true, getElem?_neg]
  · constructor
    · rw [write_run target (.there .here) .here rfl old assigned rfl rfl]
      simp only [target, Nat.reducePow, assigned, old, bind, Except.bind, State.setLocal, seven,
                Val.evalT, Simple.evalT, PrimTy.ofLit, indexTwo, TRes.ofOpt, Heap.setIndex, Int.reduceToNat,
                Heap.get, Objs.get, MObj.elems_dyn, List.length_cons, List.length_nil, Nat.zero_add,
                Nat.reduceAdd, Nat.lt_irrefl, ↓reduceIte]
    · constructor
      ·
        simp only [after, State.setLocal, target, Nat.reducePow, assigned, old,
                TEnv.set, lateRead, indexTwo, Val.evalT, bind, Except.bind, MLoc.addrT, MPath.mvalT, TEnv.get,
                Simple.evalT, PrimTy.ofLit, pure, Except.pure, TRes.ofOpt, Heap.readAddr, Heap.index,
                Heap.get, Objs.get, MObj.elems_dyn, Int.reduceToNat, List.length_cons, List.length_nil,
                Nat.zero_add, Nat.reduceAdd, Nat.lt_add_one, getElem?_pos, List.getElem_cons_succ,
                List.getElem_cons_zero]
      ·
        simp only [Stmt.run, Stmt.runR, List.cons_append, List.nil_append, lateWrite,
                indexTwo, seven, after, target, Nat.reducePow, assigned, old, State.setLocal, TEnv.set,
                TRun.assignMem, bind, Except.bind, MSrc.mvalT, Val.evalT, Simple.evalT, PrimTy.ofLit,
                MLoc.addrT, MPath.mvalT, TEnv.get, pure, Except.pure, TRes.ofOpt, Heap.writeAddr,
                Heap.setIndex, Int.reduceToNat, Heap.get, Objs.get, MObj.elems_dyn, List.length_cons,
                List.length_nil, Nat.zero_add, Nat.reduceAdd, Nat.lt_add_one, ↓reduceIte, Heap.set, Objs.set,
                MObj.setElem_dyn, List.set_cons_succ, List.set_cons_zero, State.withHeap]

private def indexZero : Val C TgtCtx .uint := .simple (.lit 0 (by decide))

private def observeSuccessfulWrite : Option (Int × Int) :=
  match (writeCode (.there .here) .here rfl .dyn indexZero seven).run target with
  | .error _ => none
  | .ok out =>
    let k := (Simple.lit (C := C) (Γ := TgtCtx) (p := .uint) 0 (by decide)).evalT target
    match out.st.heap.index (old.wk out.ext) .dyn k,
        out.st.heap.index (assigned.wk out.ext) .dyn k with
    | some x,some y => some (x.1,y.1)
    | _,_ => none

/-- When both objects have the index, the captured object receives the write
and the replacement retains its old contents. This rejects a late-base write. -/
theorem successful_write_targets_old : observeSuccessfulWrite = some (7,0) := by
  unfold observeSuccessfulWrite
  rw [write_run target (.there .here) .here rfl old assigned rfl rfl]
  simp only [bind, Except.bind, State.setLocal, target, Nat.reducePow, zero, assigned, old, seven,
        Val.evalT, Simple.evalT, PrimTy.ofLit, indexZero, TRes.ofOpt, Heap.setIndex, Int.toNat_zero,
        Heap.get, Objs.get, MObj.elems_dyn, List.length_cons, List.length_nil, Nat.zero_add,
        Nat.reduceAdd, Nat.zero_lt_succ, ↓reduceIte, Heap.set, MObj.setElem_dyn, List.set_cons_zero,
        Objs.set, pure, Except.pure, State.push, State.withHeap, Heap.index, HRef.wk, getElem?_pos,
        List.getElem_cons_zero]

/-- A Source bounds panic carries 0x32. The native unguarded option lookup's
empty revert cannot discharge Source revert transport; a lowering guard must
preserve the payload instead of relabelling this failure. -/
theorem source_index_panic_is_not_empty : THalt.ofData (Source.panicData .index) ≠ .revert := by
  decide

#print axioms captured_base_controls
#print axioms successful_write_targets_old
#print axioms source_index_panic_is_not_empty

end Solidity.Lowering.G17.IndexCapture.Controls
