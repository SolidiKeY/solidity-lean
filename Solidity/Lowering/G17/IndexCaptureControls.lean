import Solidity.Lowering.G17.IndexBounds
import Solidity.Source.Preservation.MemoryBodyControls

/-! Discriminating captured-index controls: the old object has length two and its replacement length three. Index two must still fail on the captured object; consulting the rebound caller slot would incorrectly succeed. -/
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

/-- Rejects using the rebound slot instead of the captured object for either an indexed read or write. Both arrays are live, so danglingness cannot explain away the difference. Bounds failure, not result-value coincidence, detects it. -/
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

/-- When both objects have the index, the captured object receives the write and the replacement retains its old contents. This rejects a late-base write. -/
theorem successful_write_targets_old : observeSuccessfulWrite = some (7,0) := by
  unfold observeSuccessfulWrite
  rw [write_run target (.there .here) .here rfl old assigned rfl rfl]
  simp only [bind, Except.bind, State.setLocal, target, Nat.reducePow, zero, assigned, old, seven,
        Val.evalT, Simple.evalT, PrimTy.ofLit, indexZero, TRes.ofOpt, Heap.setIndex, Int.toNat_zero,
        Heap.get, Objs.get, MObj.elems_dyn, List.length_cons, List.length_nil, Nat.zero_add,
        Nat.reduceAdd, Nat.zero_lt_succ, ↓reduceIte, Heap.set, MObj.setElem_dyn, List.set_cons_zero,
        Objs.set, pure, Except.pure, State.push, State.withHeap, Heap.index, HRef.wk, getElem?_pos,
        List.getElem_cons_zero]

/-- A Source bounds panic carries 0x32. The native unguarded option lookup's empty revert cannot discharge Source revert transport; a lowering guard must preserve the payload instead of relabelling this failure. -/
theorem source_index_panic_is_not_empty : THalt.ofData (Source.panicData .index) ≠ .revert := by
  decide

private def capturedIds : Option (Option Nat × Option Nat) :=
  match (captureCode (.there .here) .here rfl).run target with
  | .error _ => none
  | .ok out => some ((TEnv.get .here out.st.env).map HRef.id,
      (TEnv.get (.there (.there .here)) out.st.env).map HRef.id)

/-- Rejects capturing the replacement after the rebind, or overwriting the fresh capture together with the caller slot. -/
theorem captured_prefix_identity : capturedIds = some (some 0,some 1) := by
  unfold capturedIds
  rw [capture_run target (.there .here) .here rfl old assigned rfl rfl]
  rfl

/-- Both guarded accesses check the captured object's length and emit its exact bounds-panic bytes; using the replacement would wrongly succeed. -/
theorem guarded_bounds_payload :
    (IndexBounds.readOperand (.there .here) .here rfl .dyn (.lit 2 (by decide))).run target =
      .error (THalt.ofData (Source.panicData .index)) ∧
    (IndexBounds.writeCode (.there .here) .here rfl .dyn (.lit 2 (by decide)) (.lit 7 (by decide))).run target =
      .error (THalt.ofData (Source.panicData .index)) := by
  constructor
  · rw [IndexBounds.read_run target (.there .here) .here rfl old assigned rfl rfl]
    simp only [target, Nat.reducePow, old, Simple.evalT, PrimTy.ofLit, Int.reduceToNat, Heap.len,
        Heap.get, Objs.get, MObj.elems_dyn, List.length_cons, List.length_nil, Nat.zero_add,
        Nat.reduceAdd, Nat.lt_irrefl, ↓reduceIte]
  · rw [IndexBounds.write_run target (.there .here) .here rfl old assigned rfl rfl]
    simp only [target, Nat.reducePow, old, Simple.evalT, PrimTy.ofLit, Int.reduceToNat, Heap.len,
        Heap.get, Objs.get, MObj.elems_dyn, List.length_cons, List.length_nil, Nat.zero_add,
        Nat.reduceAdd, Nat.lt_irrefl, ↓reduceIte]

/-- A valid guarded read succeeds, and a valid guarded write is the actual old-object-only store observed above. This rejects an always-panicking guard and losing or redirecting an in-bounds store. -/
theorem guarded_in_bounds :
    (IndexBounds.readOperand (.there .here) .here rfl .dyn (.lit 0 (by decide))).run target =
      .ok ((⟨after,List.prefix_refl _⟩ : Out C target.H TgtCtx),SVal.prim zero) ∧
    (IndexBounds.writeCode (.there .here) .here rfl .dyn (.lit 0 (by decide)) (.lit 7 (by decide))).run target =
      (writeCode (.there .here) .here rfl .dyn indexZero seven).run target ∧
    observeSuccessfulWrite = some (7,0) := by
  constructor
  · rw [IndexBounds.read_run target (.there .here) .here rfl old assigned rfl rfl,
      IndexCapture.read_run target (.there .here) .here rfl old assigned rfl rfl]
    simp only [target, Nat.reducePow, old, Simple.evalT, PrimTy.ofLit, Int.toNat_zero, Heap.len,
        Heap.get, Objs.get, MObj.elems_dyn, List.length_cons, List.length_nil, Nat.zero_add,
        Nat.reduceAdd, Nat.zero_lt_succ, ↓reduceIte, bind, Except.bind, Val.evalT, TRes.ofOpt,
        Heap.index, getElem?_pos, List.getElem_cons_zero, pure, Except.pure, after]
  · constructor
    · rw [IndexBounds.write_run target (.there .here) .here rfl old assigned rfl rfl]
      simp only [target, Nat.reducePow, old, Simple.evalT, PrimTy.ofLit, Int.toNat_zero, Heap.len,
          Heap.get, Objs.get, MObj.elems_dyn, List.length_cons, List.length_nil, Nat.zero_add,
          Nat.reduceAdd, Nat.zero_lt_succ, ↓reduceIte, indexZero, seven]
    · exact successful_write_targets_old

#print axioms captured_prefix_identity
#print axioms guarded_bounds_payload
#print axioms guarded_in_bounds

namespace SourceCapture
open Source
private abbrev sourceEnv := Preservation.MemoryBodyControls.E
private abbrev Aty := Preservation.MemoryBodyControls.Aty
private abbrev Ctx : RCtx := [Aty,Aty,Aty,.int .u256]
private def locals : Locals sourceEnv.layout Ctx :=
  .cons (.memRef rfl 0) (.cons (.memRef rfl 1) (.cons (.memRef rfl 0)
    (.cons (.int 42 (by decide)) .nil)))
private def world : St sourceEnv :=
  {Preservation.MemoryBodyControls.initial with heap := Preservation.MemoryBodyControls.defaulted}
private def source : EMState sourceEnv Ctx := (locals,world)
private def rebound : EMState sourceEnv Ctx := (locals.set .here (.memRef rfl 1),world)
private def index : RExpr sourceEnv Ctx (.int .u256) :=
  .length (.assign (.local .here) (.local (.there .here))) rfl
private def access : RExpr sourceEnv Ctx (.int .u256) := .indexArray (.local .here) index rfl
private def store : RExpr sourceEnv Ctx (.int .u256) :=
  .assign (.indexArray (.local .here) (by decide) index rfl) (.local (.there (.there (.there .here))))
private def updated : EMState sourceEnv Ctx :=
  (rebound.1,{world with heap := world.heap.write 0 Preservation.MemoryBodyControls.modified rfl})

/-- The index really rebinds its base to a live empty array; the read still returns the captured old object's seven. Rejects late-base lookup and stale caller locals. -/
theorem read_captured (p : Roadmap.Pipeline) :
    (evalE (Preservation.MemoryBodyControls.glob p) Preservation.MemoryBodyControls.frame 10 access).run source =
      (.ok (.val (.int 7 (by decide))),rebound) := by
  have baseRun : (evalE (Preservation.MemoryBodyControls.glob p) Preservation.MemoryBodyControls.frame 9
      (.local .here : RExpr sourceEnv Ctx Aty)).run source =
      (.ok (.val (.memRef rfl 0)),source) := rfl
  have indexRun : (evalE (Preservation.MemoryBodyControls.glob p) Preservation.MemoryBodyControls.frame 9
      index).run source = (.ok (.val (.int 0 (by decide))),rebound) := by
    cases p <;> rfl
  have actual := source_capture_order (Preservation.MemoryBodyControls.glob p)
    Preservation.MemoryBodyControls.frame 9 (.local .here : RExpr sourceEnv Ctx Aty) index rfl
    source source rebound (.memRef rfl 0) (.val (.int 0 (by decide))) baseRun indexRun
  exact actual.1.trans rfl

/-- The same effectful index must select the old location for a write; the independent old alias survives and the replacement object remains empty. Rejects redirected writes. -/
theorem write_captured (p : Roadmap.Pipeline) :
    (evalLoc (Preservation.MemoryBodyControls.glob p) Preservation.MemoryBodyControls.frame 9
      (.indexArray (.local .here : RExpr sourceEnv Ctx Aty) (by decide) index rfl)).run source =
        (.ok (.mem 0 0),rebound) ∧
    (evalE (Preservation.MemoryBodyControls.glob p) Preservation.MemoryBodyControls.frame 10 store).run source =
      (.ok (.val (.int 42 (by decide))),updated) := by
  have baseRun : (evalE (Preservation.MemoryBodyControls.glob p) Preservation.MemoryBodyControls.frame 8
      (.local .here : RExpr sourceEnv Ctx Aty)).run source =
      (.ok (.val (.memRef rfl 0)),source) := rfl
  have indexRun : (evalE (Preservation.MemoryBodyControls.glob p) Preservation.MemoryBodyControls.frame 8
      index).run source = (.ok (.val (.int 0 (by decide))),rebound) := by
    cases p <;> rfl
  have actual := source_capture_order (Preservation.MemoryBodyControls.glob p)
    Preservation.MemoryBodyControls.frame 8 (.local .here : RExpr sourceEnv Ctx Aty) index rfl
    source source rebound (.memRef rfl 0) (.val (.int 0 (by decide))) baseRun indexRun
  constructor
  · exact (actual.2 (by decide)).trans rfl
  · cases p <;> rfl

/-- Looking up the rebound empty object instead would panic with index data, making the successful old-object access discriminating. -/
theorem late_base_panics (p : Roadmap.Pipeline) :
    (evalE (Preservation.MemoryBodyControls.glob p) Preservation.MemoryBodyControls.frame 3
      (.indexArray (.local (.there .here) : RExpr sourceEnv Ctx Aty) (.const (Q.ofInt 0)) (by decide))).run rebound =
      (.error (.revert (panicData .index)),rebound) := by
  cases p <;> rfl

private def valueIndex : Source.Idx Ctx (.int .u256) := .there (.there (.there .here))
private def beforeFailure : EMState sourceEnv Ctx := (locals,updated.2)
private def writeBeforeFailure : RExpr sourceEnv Ctx (.int .u256) :=
  .assign (.indexArray (.local .here) (by decide) (.const (Q.ofInt 0)) (by decide)) (.local valueIndex)
private def failingBase : RExpr sourceEnv Ctx Aty :=
  .cond (.compare .eq (.binary .div writeBeforeFailure
      (.binary .sub (.local valueIndex) (.local valueIndex))) (.local valueIndex))
    (.local .here) (.local (.there .here))
private def failingIndex : RExpr sourceEnv Ctx (.int .u256) :=
  .indexArray (.assign (.local .here) (.local (.there .here))) (.const (Q.ofInt 0)) (by decide)

/-- A failed base retains its prior Source EM heap write and skips the index's caller rebind; rejects eager index effects or rollback of the evaluator's reached state. -/
theorem base_failure_skips_index (p : Roadmap.Pipeline) :
    (evalE (Preservation.MemoryBodyControls.glob p) Preservation.MemoryBodyControls.frame 16 failingBase).run source =
      (.error (.revert (panicData .divZero)),beforeFailure) ∧
    (evalE (Preservation.MemoryBodyControls.glob p) Preservation.MemoryBodyControls.frame 17
      (.indexArray failingBase index rfl)).run source = (.error (.revert (panicData .divZero)),beforeFailure) ∧
    (evalLoc (Preservation.MemoryBodyControls.glob p) Preservation.MemoryBodyControls.frame 17
      (.indexArray failingBase (by decide) index rfl)).run source =
      (.error (.revert (panicData .divZero)),beforeFailure) := by
  have baseRun : (evalE (Preservation.MemoryBodyControls.glob p) Preservation.MemoryBodyControls.frame 16
      failingBase).run source = (.error (.revert (panicData .divZero)),beforeFailure) := by
    cases p <;> rfl
  have indexRun : (evalE (Preservation.MemoryBodyControls.glob p) Preservation.MemoryBodyControls.frame 16
      index).run beforeFailure =
      (.ok (.val (.int 0 (by decide))),(beforeFailure.1.set .here (.memRef rfl 1),beforeFailure.2)) := by
    cases p <;> rfl
  have actual := source_capture_all (Preservation.MemoryBodyControls.glob p)
    Preservation.MemoryBodyControls.frame 16 failingBase index rfl source beforeFailure _
    (.error (.revert (panicData .divZero))) (.ok (.val (.int 0 (by decide)))) baseRun indexRun
  exact ⟨baseRun,actual.1,actual.2 (by decide)⟩

/-- An index panic after rebinding propagates with its reached Source EM state for reads and locations; rejects swallowed failures and discarded index effects. -/
theorem index_failure_keeps_effects (p : Roadmap.Pipeline) :
    (evalE (Preservation.MemoryBodyControls.glob p) Preservation.MemoryBodyControls.frame 9 failingIndex).run source =
      (.error (.revert (panicData .index)),rebound) ∧
    (evalE (Preservation.MemoryBodyControls.glob p) Preservation.MemoryBodyControls.frame 10
      (.indexArray (.local .here : RExpr sourceEnv Ctx Aty) failingIndex rfl)).run source =
      (.error (.revert (panicData .index)),rebound) ∧
    (evalLoc (Preservation.MemoryBodyControls.glob p) Preservation.MemoryBodyControls.frame 10
      (.indexArray (.local .here : RExpr sourceEnv Ctx Aty) (by decide) failingIndex rfl)).run source =
      (.error (.revert (panicData .index)),rebound) := by
  have baseRun : (evalE (Preservation.MemoryBodyControls.glob p) Preservation.MemoryBodyControls.frame 9
      (.local .here : RExpr sourceEnv Ctx Aty)).run source = (.ok (.val (.memRef rfl 0)),source) := rfl
  have indexRun : (evalE (Preservation.MemoryBodyControls.glob p) Preservation.MemoryBodyControls.frame 9
      failingIndex).run source = (.error (.revert (panicData .index)),rebound) := by
    cases p <;> rfl
  have actual := source_capture_all (Preservation.MemoryBodyControls.glob p)
    Preservation.MemoryBodyControls.frame 9 (.local .here : RExpr sourceEnv Ctx Aty) failingIndex rfl
    source source rebound (.ok (.val (.memRef rfl 0))) (.error (.revert (panicData .index))) baseRun indexRun
  exact ⟨indexRun,actual.1.trans rfl,(actual.2 (by decide)).trans rfl⟩

#print axioms base_failure_skips_index
#print axioms index_failure_keeps_effects
#print axioms read_captured
#print axioms write_captured
#print axioms late_base_panics
end SourceCapture

#print axioms captured_base_controls
#print axioms successful_write_targets_old
#print axioms source_index_panic_is_not_empty

end Solidity.Lowering.G17.IndexCapture.Controls
