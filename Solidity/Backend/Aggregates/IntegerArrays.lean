import Solidity.Backend.Aggregates.BoolArrays
import Solidity.Lowering.V07.Scalar
/-! G18.04/.05 arbitrary-width integer calldata-array value/frame consumer.
Development prerequisite: exact V07 Scalar checkpoint5d45c086, validated in a
private source-keyed stage. No admission, general frame/compiler, machine gas,
or fetched-EVM correspondence follows. Source widths remain in Source values;
the target uses V07's actual signed/unsigned intrinsic primitive. -/
namespace Solidity.Backend.Aggregates.IntegerArrays
open Solidity Lowering.V07
abbrev runtimeTy (t : Source.IntTy) : RefTy := .array (.prim (integerPrim t))
abbrev sourceTy (t : Source.IntTy) : Source.STy := .array .memory (.int t) none

def value {D : Source.Layout} (t : Source.IntTy) : Source.Val D (.int t) → (integerPrim t).Denote
  | .int n h => integerValue t n h
  | .memRef impossible _ => nomatch impossible
  | .storRef impossible _ => nomatch impossible
  | .cdRef impossible _ _ => nomatch impossible

theorem value_related {D : Source.Layout} (t : Source.IntTy) (v : Source.Val D (.int t)) :
    IntValueRel t v (value t v) := by
  cases v with
  | int n h => exact integer_related t n h
  | memRef impossible _ => nomatch impossible
  | storRef impossible _ => nomatch impossible
  | cdRef impossible _ _ => nomatch impossible

/-- Real ABI region and ordered validation derive target object capacity. -/
theorem capacity {E : Source.Env} (t : Source.IntTy) (frame : Source.Fr)
    (selector data : Roadmap.Bytes) (selector_length : selector.length = 4)
    (input : frame.cd = selector ++ data) {index offset length : Nat}
    (entry : Source.cdTail data index 32 = .ok (offset,length))
    {values : List (Source.Val E.layout (.int t))}
    (validation : (List.range length).mapM (fun j => Source.decodeWord E.layout
      (Source.cdWordAt frame (offset+32*j)) (.int t)) = .ok values) :
    (values.map (value t)).length < 2^256 := by
  rw [List.length_map, Source.cdToMem_array_length frame (.int t) offset length validation]
  exact Nat.lt_trans (BoolArrays.entry_geometry frame selector data selector_length input entry).1 (by decide)

def object {D : Source.Layout} (H : HTy) (t : Source.IntTy)
    (values : List (Source.Val D (.int t)))
    (room : (values.map (value t)).length < 2^256) : MObj H (runtimeTy t) :=
  ⟨values.map (value t),room⟩

def lower {D : Source.Layout} {C : Contract} {Γ : Ctx} (target : State C Γ)
    (t : Source.IntTy) (values : List (Source.Val D (.int t)))
    (room : (values.map (value t)).length < 2^256) : State C (.mem (runtimeTy t) :: Γ) :=
  target.allocPush (object target.H t values room)

def Related {D : Source.Layout} (t : Source.IntTy) (source : Source.Heap D) (address : Nat)
    {H : HTy} (target : Heap H) (reference : HRef H (runtimeTy t)) : Prop :=
  ∃ values : List (Source.Val D (.int t)),
    source.get address = some ⟨sourceTy t, Source.Data.array values.length
      (fun _ h => nomatch h) (fun k => .val (values.get k))⟩ ∧
    MObj.elems ArrTy.dyn (target.get reference) = values.map (value t)

/-- Actual Source copy and intrinsic allocation have the same ordered values,
using V07 integer transport, with independent fresh identities. Entry and
validation are actual operation equations, not a simulation premise. -/
theorem copy_related {E : Source.Env} {Λ : Source.RCtx} {C : Contract} {Γ : Ctx}
    (t : Source.IntTy) (frame : Source.Fr) (selector data : Roadmap.Bytes)
    (selector_length : selector.length = 4) (input : frame.cd = selector ++ data)
    {index offset length : Nat} (entry : Source.cdTail data index 32 = .ok (offset,length))
    (source : Source.EMState E Λ) (target : State C Γ)
    {values : List (Source.Val E.layout (.int t))}
    (validation : (List.range length).mapM (fun j => Source.decodeWord E.layout
      (Source.cdWordAt frame (offset+32*j)) (.int t)) = .ok values) :
    let room := capacity t frame selector data selector_length input entry validation
    Related t ((Source.cdToMem frame (sourceTy t) offset length).run source).2.2.heap
      source.2.heap.next (lower target t values room).heap
      (target.alloc (object target.H t values room)).2 := by

  dsimp only
  rw [(Source.cdToMem_array_run (σ := .int _)), validation]
  refine ⟨values, Source.Heap.alloc_get source.2.heap _, ?_⟩
  change MObj.elems ArrTy.dyn ((target.heap.alloc (object target.H t values (capacity t frame selector data selector_length input entry validation))).1.get
    (target.heap.alloc (object target.H t values (capacity t frame selector data selector_length input entry validation))).2) = values.map (value t)
  rw [Heap.get_alloc_self]
  simp only [object, MObj.wk, MObj.elems_dyn, List.map_map]
  rfl


/-- Total validation adapter over an actual successful ABI entry. Errors are
Source.Halt diagnostics; this is not machine execution or a gas model. -/
def lowerCopy {E : Source.Env} {C : Contract} {Γ : Ctx} (target : State C Γ)
    (t : Source.IntTy) (frame : Source.Fr) (selector data : Roadmap.Bytes)
    (selector_length : selector.length = 4) (input : frame.cd = selector ++ data)
    {index offset length : Nat} (entry : Source.cdTail data index 32 = .ok (offset,length)) :
    Except Source.Halt (State C (.mem (runtimeTy t) :: Γ)) :=
  match validation : (List.range length).mapM (fun j => Source.decodeWord E.layout
      (Source.cdWordAt frame (offset+32*j)) (.int t)) with
  | .error halt => .error halt
  | .ok values => .ok (lower target t values
      (capacity t frame selector data selector_length input entry validation))

/-- Reflect exact Source diagnostics in both directions, retaining the unchanged
full original state on validation failure.
ABI entry is certified; no target halt/resource/world claim is made. -/
theorem error_iff_copy_error {E : Source.Env} {Λ : Source.RCtx} {C : Contract} {Γ : Ctx}
    (source : Source.EMState E Λ) (target : State C Γ) (t : Source.IntTy)
    (frame : Source.Fr) (selector data : Roadmap.Bytes)
    (selector_length : selector.length = 4) (input : frame.cd = selector ++ data)
    {index offset length : Nat} (entry : Source.cdTail data index 32 = .ok (offset,length))
    (halt : Source.Halt) :
    lowerCopy (E := E) target t frame selector data selector_length input entry = .error halt ↔
      (Source.cdToMem frame (sourceTy t) offset length).run source = (.error halt,source) := by

  rw [(Source.cdToMem_array_run (σ := .int _))]
  unfold lowerCopy
  split
  · rename_i actual observed
    rw [observed]
    constructor
    · intro same
      cases same
      rfl
    · intro same
      have equality := Except.error.inj (congrArg Prod.fst same)
      cases equality
      rfl
  · rename_i values observed
    constructor
    · intro impossible
      cases impossible
    · intro impossible
      have wrong := congrArg Prod.fst impossible
      rw [observed] at wrong
      cases wrong


/-- Client of actual Source argument decoding followed by its existing
calldata-to-memory conversion, at the existing conversion budget zero. -/
def sourceCopy {E : Source.Env} {Λ : Source.RCtx} (t : Source.IntTy) (frame : Source.Fr)
    (data : Roadmap.Bytes) (index : Nat) : Source.EM E Λ (Source.RVal E.layout (sourceTy t)) := do
  let argument ← Source.decodeArg data index (.array .calldata (.int t) none)
  Source.convRV frame 0 (sourceTy t) (.val argument)

/-- Header failure precedes conversion; successful headers invoke the real
Source copy on the reached typed argument, without a new evaluator. -/
theorem sourceCopy_run {E : Source.Env} {Λ : Source.RCtx} (t : Source.IntTy) (frame : Source.Fr)
    (data : Roadmap.Bytes) (index : Nat) (source : Source.EMState E Λ) :
    (sourceCopy t frame data index).run source =
      match Source.cdTail data index 32 with
      | .error halt => (.error halt,source)
      | .ok (offset,length) => (Source.cdToMem frame (sourceTy t) offset length).run source := by

  unfold sourceCopy
  rw [Source.Hoare.run_bind, Source.decodeArg_cdArray_run data index (.int t) rfl source]
  rw [Source.cdHeadBytes_of_word (τ := .int t) rfl]
  unfold Source.cdArg
  cases Source.cdTail data index 32 with
  | error halt => rfl
  | ok pair => cases pair; rfl

/-- Execute actual ABI entry before word validation; both error channels are
Source diagnostics rather than machine halts. -/
def lowerEntry {E : Source.Env} {C : Contract} {Γ : Ctx} (target : State C Γ)
    (t : Source.IntTy) (frame : Source.Fr) (selector data : Roadmap.Bytes)
    (selector_length : selector.length = 4) (input : frame.cd = selector ++ data) (index : Nat) :
    Except Source.Halt (State C (.mem (runtimeTy t) :: Γ)) :=
  match entry : Source.cdTail data index 32 with
  | .error halt => .error halt
  | .ok (_offset,_length) => lowerCopy (E := E) target t frame selector data selector_length input entry

/-- Exact Source diagnostics and unchanged full state, reflected both ways
for actual argument decoding/conversion. No successful ABI entry is assumed.
Selector/frame consistency is retained; this is not machine correspondence. -/
theorem entry_error_iff_source_error {E : Source.Env} {Λ : Source.RCtx} {C : Contract} {Γ : Ctx}
    (source : Source.EMState E Λ) (target : State C Γ) (t : Source.IntTy) (frame : Source.Fr)
    (selector data : Roadmap.Bytes) (selector_length : selector.length = 4)
    (input : frame.cd = selector ++ data) (index : Nat) (halt : Source.Halt) :
    lowerEntry (E := E) target t frame selector data selector_length input index = .error halt ↔
      (sourceCopy t frame data index).run source = (.error halt,source) := by

  rw [sourceCopy_run]
  unfold lowerEntry
  split
  · rename_i actual observed
    conv => rhs; rw [observed]
    constructor
    · intro same
      cases same
      rfl
    · intro same
      have equality := Except.error.inj (congrArg Prod.fst same)
      cases equality
      rfl
  · rename_i offset length observed
    conv => rhs; rw [observed]
    exact error_iff_copy_error source target t frame selector data selector_length input observed halt


/-! Actual typed Source expression/client transport; Source budgets below
are not EVM gas or a producer of physical runtime-frame admission. -/
namespace Expression
abbrev argumentTy (t : Source.IntTy) : Source.STy := .array .calldata (.int t) none

/-- Derive the existing Source implicit conversion judgment for every width.
Explicit decidable equality avoids reducing the generated equality machinery. -/
theorem conversion_allowed (E : Source.Env) (t : Source.IntTy) :
    (argumentTy t).implicit E.isBase E.mapFree (sourceTy t) = true := by
  change (decide (t = t) && true && true && (false || true)) = true
  simp only [Bool.and_true, Bool.or_true, decide_eq_true_eq]

def expr {E : Source.Env} {caller : Source.RCtx} (t : Source.IntTy) :
    Source.RExpr E (argumentTy t :: caller) (sourceTy t) :=
  .conv (.local .here) (.inl (conversion_allowed E t))

theorem eval_expr_run {E : Source.Env} {caller : Source.RCtx} (t : Source.IntTy) (G : Source.Glob E)
    (frame : Source.Fr) (n offset length : Nat) (tail : Source.Locals E.layout caller)
    (state : Source.St E) :
    let before : Source.EMState E (argumentTy t :: caller) :=
      (.cons (.cdRef rfl offset length) tail,state)
    (Source.evalE G frame (n+2) (expr t)).run before =
      (Source.cdToMem frame (sourceTy t) offset length).run before := by

  dsimp only
  unfold expr
  change ((Source.evalE G frame (n+1) (.local .here)) >>= fun argument =>
    Source.convRV frame (n+1) (sourceTy t) argument).run _ = _
  rw [Source.Hoare.run_bind, Source.eval_local_run]
  change (Source.convRV frame (n+1) (sourceTy t)
    (.val (.cdRef (τ := argumentTy t) rfl offset length))).run _ = _
  rw [Source.convRV_cdArray]

def scopedCopy {E : Source.Env} {caller : Source.RCtx} (t : Source.IntTy) (G : Source.Glob E)
    (frame : Source.Fr) (budget : Nat) (data : Roadmap.Bytes) (index : Nat) :
    Source.EM E caller (Source.RVal E.layout (sourceTy t)) := do
  let argument ← Source.decodeArg data index (argumentTy t)
  let tail ← Source.EM.locals
  let (result,_) ← Source.EM.sub (.cons argument tail) (Source.evalE G frame budget (expr t))
  pure result

/-- Actual EM.sub drops the argument-local extension while retaining the
reached complete state, on both native success and native error at n+2. -/
theorem scopedCopy_run {E : Source.Env} {caller : Source.RCtx} (t : Source.IntTy) (G : Source.Glob E)
    (frame : Source.Fr) (n : Nat) (data : Roadmap.Bytes) (index : Nat)
    (source : Source.EMState E caller) :
    (scopedCopy t G frame (n+2) data index).run source =
      (sourceCopy t frame data index).run source := by

  rcases source with ⟨tail,state⟩
  rw [sourceCopy_run]
  unfold scopedCopy
  rw [Source.Hoare.run_bind, Source.decodeArg_cdArray_run data index (.int t) rfl,
    Source.cdHeadBytes_of_word (τ := .int t) rfl]
  unfold Source.cdArg
  cases entry : Source.cdTail data index 32 with
  | error halt => rfl
  | ok pair =>
    rcases pair with ⟨offset,length⟩
    change ((Source.EM.sub (.cons (.cdRef (τ := argumentTy t) rfl offset length) tail)
      (Source.evalE G frame (n+2) (expr t))) >>= fun result => pure result.1).run (tail,state) = _
    rw [Source.Hoare.run_bind]
    unfold Source.EM.sub
    dsimp only [ExceptT.run, ExceptT.mk]
    have evaluation := eval_expr_run t G frame n offset length tail state
    dsimp only [ExceptT.run, ExceptT.mk] at evaluation
    rw [evaluation]
    have inside := Source.cdToMem_array_run frame (.int t) offset length
      ((.cons (.cdRef (τ := argumentTy t) rfl offset length) tail,state) :
        Source.EMState E (argumentTy t :: caller))
    have outside := Source.cdToMem_array_run frame (.int t) offset length
      ((tail,state) : Source.EMState E caller)
    dsimp only [ExceptT.run, ExceptT.mk] at inside outside
    rw [inside,outside]
    cases (List.range length).mapM (fun j => Source.decodeWord E.layout
      (Source.cdWordAt frame (offset+32*j)) (.int t)) <;> rfl
end Expression

/-- Consume actual copy/read executions and V07 numeric transport. Both
object capacity and exact uint index are derived from real ABI validation;
no desired read result or representability premise is supplied. -/
theorem copy_read_related {E : Source.Env} {Λ : Source.RCtx} {C : Contract} {Γ : Ctx}
    (t : Source.IntTy) (frame : Source.Fr) (selector data : Roadmap.Bytes)
    (selector_length : selector.length = 4) (input : frame.cd = selector ++ data)
    {entryIndex offset length : Nat} (entry : Source.cdTail data entryIndex 32 = .ok (offset,length))
    (source : Source.EMState E Λ) (target : State C Γ)
    {values : List (Source.Val E.layout (.int t))}
    (validation : (List.range length).mapM (fun j => Source.decodeWord E.layout
      (Source.cdWordAt frame (offset+32*j)) (.int t)) = .ok values) (index : Fin length) :
    let room := capacity t frame selector data selector_length input entry validation
    ∃ bound : index.val < values.length,
      ((do let _ ← Source.cdToMem frame (sourceTy t) offset length
           Source.readLoc frame (.mem (τ := .int t) source.2.heap.next index.val)) : Source.EM E Λ _).run source =
        (.ok (values.get ⟨index.val,bound⟩),((Source.cdToMem frame (sourceTy t) offset length).run source).2) ∧
      (lower target t values room).heap.readAddr
        (.index (target.alloc (object target.H t values room)).2 ArrTy.dyn (uintOfNat index.val)) =
          some (value t (values.get ⟨index.val,bound⟩)) ∧
      ((lower target t values room).heap.readAddr
        (.index (target.alloc (object target.H t values room)).2 ArrTy.dyn (uintOfNat index.val))).bind
        PrimTy.num? = (values.get ⟨index.val,bound⟩).key := by

  dsimp only
  obtain ⟨bound,_,_,actual⟩ := Source.cdToMem_array_read_run frame (.int t) offset length source validation index
  have small : index.val < 2^256 := Nat.lt_trans
    (Nat.lt_trans index.isLt (BoolArrays.entry_geometry frame selector data selector_length input entry).1)
    (by decide)
  have contents : MObj.elems ArrTy.dyn
      ((lower target t values (capacity t frame selector data selector_length input entry validation)).heap.get (target.alloc (object target.H t values (capacity t frame selector data selector_length input entry validation))).2) =
        values.map (value t) := by
    unfold lower
    rw [State.allocPush_get]
    simp only [object, MObj.wk, MObj.elems_dyn, List.map_map]
    rfl
  have read : (lower target t values (capacity t frame selector data selector_length input entry validation)).heap.readAddr
      (.index (target.alloc (object target.H t values (capacity t frame selector data selector_length input entry validation))).2 ArrTy.dyn (uintOfNat index.val)) =
        some (value t (values.get ⟨index.val,bound⟩)) := by
    simp only [Heap.readAddr, Heap.index, contents, uintOfNat_val small, Int.toNat_natCast,
      List.getElem?_map, List.getElem?_eq_getElem bound, Option.map_some, List.get_eq_getElem]
  refine ⟨bound,actual,read,?_⟩
  rw [read]
  exact (value_related t (values.get ⟨index.val,bound⟩)).symm

/-- At the first invalid index, actual Source retains its newly allocated
copy and exact index-panic bytes; logical intrinsic readAddr returns none.
These distinct carriers do not assert a fetched-machine panic relation. -/
theorem copy_first_out {E : Source.Env} {Λ : Source.RCtx} {C : Contract} {Γ : Ctx}
    (t : Source.IntTy) (frame : Source.Fr) (selector data : Roadmap.Bytes)
    (selector_length : selector.length = 4) (input : frame.cd = selector ++ data)
    {entryIndex offset length : Nat} (entry : Source.cdTail data entryIndex 32 = .ok (offset,length))
    (source : Source.EMState E Λ) (target : State C Γ)
    {values : List (Source.Val E.layout (.int t))}
    (validation : (List.range length).mapM (fun j => Source.decodeWord E.layout
      (Source.cdWordAt frame (offset+32*j)) (.int t)) = .ok values) :
    let room := capacity t frame selector data selector_length input entry validation
    ((do let _ ← Source.cdToMem frame (sourceTy t) offset length
         Source.readLoc frame (.mem (τ := .int t) source.2.heap.next length)) : Source.EM E Λ _).run source =
      (.error (.revert (Source.panicData .index)),
        ((Source.cdToMem frame (sourceTy t) offset length).run source).2) ∧
    (lower target t values room).heap.readAddr
      (.index (target.alloc (object target.H t values room)).2 ArrTy.dyn (uintOfNat length)) = none ∧
    ((Source.cdToMem frame (sourceTy t) offset length).run source).2.2.heap.next = source.2.heap.next+1 := by

  dsimp only
  refine ⟨Source.cdToMem_array_read_out_run frame (.int t) offset length source validation length
    (Nat.le_refl _), ?_, ?_⟩
  · have small : length < 2^256 := Nat.lt_trans
      (BoolArrays.entry_geometry frame selector data selector_length input entry).1 (by decide)
    have contents : MObj.elems ArrTy.dyn
        ((lower target t values (capacity t frame selector data selector_length input entry validation)).heap.get (target.alloc (object target.H t values (capacity t frame selector data selector_length input entry validation))).2) =
          values.map (value t) := by
      unfold lower
      rw [State.allocPush_get]
      simp only [object, MObj.wk, MObj.elems_dyn, List.map_map]
      rfl
    simp only [Heap.readAddr, Heap.index, contents, uintOfNat_val small, Int.toNat_natCast,
      List.getElem?_map]
    rw [List.getElem?_eq_none (Nat.le_of_eq
      (Source.cdToMem_array_length frame (.int t) offset length validation))]
    rfl
  · rw [(Source.cdToMem_array_run (σ := .int _)), validation]
    rfl


/-! Typed selected-element calldata observations versus an already validated
imported snapshot. This is not general calldata-read compilation: eager
whole-array validation is strictly stronger than selecting one element. -/
namespace CalldataRead

def expr {E : Source.Env} {caller : Source.RCtx} (t : Source.IntTy) :
    Source.RExpr E (Expression.argumentTy t :: .int Source.IntTy.u256 :: caller) (.int t) :=
  .indexArray (.local .here) (.local (.there .here)) rfl

theorem eval_read_run {E : Source.Env} {caller : Source.RCtx} (t : Source.IntTy) (G : Source.Glob E)
    (frame : Source.Fr) (n offset length index : Nat) (bound : index < length)
    (typed : Source.IntTy.u256.lo ≤ (index : Int) ∧ (index : Int) ≤ Source.IntTy.u256.hi)
    (tail : Source.Locals E.layout caller) (state : Source.St E) :
    let before : Source.EMState E (Expression.argumentTy t :: .int Source.IntTy.u256 :: caller) :=
      (.cons (.cdRef rfl offset length) (.cons (.int index typed) tail),state)
    (Source.evalE G frame (n+2) (expr t)).run before =
      ((Source.decodeWord E.layout (Source.cdWordAt frame (offset+32*index)) (.int t)).map
        Source.RVal.val,before) := by

  simp only [expr, Source.eval_cdIndex_run, Source.indexLoc, Source.lengthOf, pure_bind,
    if_pos bound, Source.STy.isValueTy, Source.STy.oneWord, if_true]
  simp only [Source.readLoc]
  cases Source.decodeWord E.layout (Source.cdWordAt frame (offset+32*index)) (.int t) <;> rfl
/-- Conditional snapshot comparison. Index typing is derived from actual ABI
extent, but whole-array validation remains explicit and is NOT a consequence
of a successful selected-element Source read. -/
theorem imported_read {E : Source.Env} {caller : Source.RCtx} {C : Contract} {Γ : Ctx}
    (t : Source.IntTy) (G : Source.Glob E) (frame : Source.Fr) (n : Nat)
    (selector data : Roadmap.Bytes) (selector_length : selector.length = 4)
    (input : frame.cd = selector ++ data) {entryIndex offset length : Nat}
    (entry : Source.cdTail data entryIndex 32 = .ok (offset,length))
    (tail : Source.Locals E.layout caller) (state : Source.St E) (target : State C Γ)
    {values : List (Source.Val E.layout (.int t))}
    (validation : (List.range length).mapM (fun j => Source.decodeWord E.layout
      (Source.cdWordAt frame (offset+32*j)) (.int t)) = .ok values) (index : Fin length) :
    let room := capacity t frame selector data selector_length input entry validation
    ∃ (typed : Source.IntTy.u256.lo ≤ (index.val : Int) ∧ (index.val : Int) ≤ Source.IntTy.u256.hi)
      (bound : index.val < values.length),
      let before : Source.EMState E (Expression.argumentTy t :: .int Source.IntTy.u256 :: caller) :=
        (.cons (.cdRef rfl offset length) (.cons (.int index.val typed) tail),state)
      (Source.evalE G frame (n+2) (expr t)).run before =
        (.ok (.val (values.get ⟨index.val,bound⟩)),before) ∧
      (lower target t values room).heap.readAddr
        (.index (target.alloc (object target.H t values room)).2 ArrTy.dyn (uintOfNat index.val)) =
          some (value t (values.get ⟨index.val,bound⟩)) ∧
      ((lower target t values room).heap.readAddr
        (.index (target.alloc (object target.H t values room)).2 ArrTy.dyn (uintOfNat index.val))).bind
          PrimTy.num? = (values.get ⟨index.val,bound⟩).key := by

  dsimp only
  have small : index.val < 2^256 := Nat.lt_trans
    (Nat.lt_trans index.isLt (BoolArrays.entry_geometry frame selector data selector_length input entry).1)
    (by decide)
  have typed : Source.IntTy.u256.lo ≤ (index.val : Int) ∧ (index.val : Int) ≤ Source.IntTy.u256.hi := by
    change (0 : Int) ≤ (index.val : Int) ∧ (index.val : Int) ≤ ((2^256-1 : Nat) : Int)
    omega
  let before : Source.EMState E (Expression.argumentTy t :: .int Source.IntTy.u256 :: caller) :=
    (.cons (.cdRef rfl offset length) (.cons (.int index.val typed) tail),state)
  obtain ⟨bound,_,targetRead,numeric⟩ := copy_read_related t frame selector data selector_length input entry
    before target validation index
  obtain ⟨_,_,position,_⟩ := Source.cdToMem_array_read_run frame (.int t) offset length before validation index
  refine ⟨typed,bound,?_,targetRead,numeric⟩
  rw [eval_read_run t G frame n offset length index.val index.isLt typed tail state, position]
  rfl
/-- Explicit semantic boundary: actual selected-word success can coexist with
actual eager-import failure. These are Source/native phase observations, not a
Source-success/machine-revert theorem or an approved profile restriction. -/
theorem selected_success_import_error {E : Source.Env} {caller : Source.RCtx} {C : Contract} {Γ : Ctx}
    (t : Source.IntTy) (G : Source.Glob E) (frame : Source.Fr) (n : Nat)
    (selector data : Roadmap.Bytes) (selector_length : selector.length = 4)
    (input : frame.cd = selector ++ data) {entryIndex offset length : Nat}
    (entry : Source.cdTail data entryIndex 32 = .ok (offset,length))
    (tail : Source.Locals E.layout caller) (state : Source.St E) (target : State C Γ)
    (index : Fin length) (selected : Source.Val E.layout (.int t)) (halt : Source.Halt)
    (selected_ok : Source.decodeWord E.layout (Source.cdWordAt frame (offset+32*index.val)) (.int t) = .ok selected)
    (validation_error : (List.range length).mapM (fun j => Source.decodeWord E.layout
      (Source.cdWordAt frame (offset+32*j)) (.int t)) = .error halt) :
    ∃ typed : Source.IntTy.u256.lo ≤ (index.val : Int) ∧ (index.val : Int) ≤ Source.IntTy.u256.hi,
      let before : Source.EMState E (Expression.argumentTy t :: .int Source.IntTy.u256 :: caller) :=
        (.cons (.cdRef rfl offset length) (.cons (.int index.val typed) tail),state)
      (Source.evalE G frame (n+2) (expr t)).run before = (.ok (.val selected),before) ∧
      lowerEntry (E := E) target t frame selector data selector_length input entryIndex = .error halt := by

  have small : index.val < 2^256 := Nat.lt_trans
    (Nat.lt_trans index.isLt (BoolArrays.entry_geometry frame selector data selector_length input entry).1)
    (by decide)
  have typed : Source.IntTy.u256.lo ≤ (index.val : Int) ∧ (index.val : Int) ≤ Source.IntTy.u256.hi := by
    change (0 : Int) ≤ (index.val : Int) ∧ (index.val : Int) ≤ ((2^256-1 : Nat) : Int)
    omega
  let before : Source.EMState E (Expression.argumentTy t :: .int Source.IntTy.u256 :: caller) :=
    (.cons (.cdRef rfl offset length) (.cons (.int index.val typed) tail),state)
  refine ⟨typed,?_,?_⟩
  · rw [eval_read_run t G frame n offset length index.val index.isLt typed tail state, selected_ok]
    rfl
  · apply (entry_error_iff_source_error before target t frame selector data selector_length input entryIndex halt).2
    simp only [sourceCopy_run, entry]
    rw [(Source.cdToMem_array_run (σ := .int _)), validation_error]
end CalldataRead
end Solidity.Backend.Aggregates.IntegerArrays
