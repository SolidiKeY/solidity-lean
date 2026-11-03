import Solidity.Backend.Passes.AssignedBareRevert
import Solidity.Evm.MemoryCompileExamples

/-! An actual assignment changes the selected allocating block's demand.
The source allocation succeeds before its bounds-sensitive read fails. Exact
positive-base ownership and capacity are supplied, never desired target runs.
No failed output state or public Source/resource adequacy is asserted. -/
namespace Solidity.Backend.Passes.PositiveAllocationFailure
open Evm Evm.Memory
open Solidity.Backend.InternalFlow.RuntimeFrame
abbrev C := CompileExamples.C
abbrev Γ : Ctx := [.val .uint]
abbrev F := Frag.init Γ
abbrev A : RefTy := .array (.prim .uint)
def before : State C Γ := (State.init C).push (t := .val .uint) (CompileExamples.uint 0 (by decide))
def after : State C Γ := before.setLocal .here (CompileExamples.uint 2 (by decide))
def allocate : Stmt C Γ (.mem A :: Γ) :=
  .declMem A (.user "array") (some (.newArr (.local .here) rfl)) rfl rfl
def read : Val C (.mem A :: Γ) .uint :=
  .readMem (.index .dyn (.var .here rfl) (.simple (.local (.there .here))))
def body : Prog C Γ (.mem A :: Γ) :=
  .cons allocate (.cons (.assignLocal (.there .here) read) .nil)
def statement : Stmt C Γ Γ := .block body
def selectedStatement : Composition.Statement 1 F statement :=
  (Composition.compileStatement 1 F statement).get
    (by first | rfl | decide | omega | decide +kernel)
def selected : Composition.Program 1 F (.cons statement .nil) :=
  Composition.cons selectedStatement (Composition.nil 1 selectedStatement.checked.frag)

theorem initial_cost : selected.checked.cost before = 1 := by
  first | rfl | decide | omega | with_unfolding_all rfl

theorem reached_cost : selected.checked.cost after = 3 := by
  first | rfl | decide | omega | with_unfolding_all rfl

theorem actual_body_failure : statement.run after = .error .revert := by
  first | rfl | decide | omega | with_unfolding_all rfl

theorem workspace : 1 + selected.checked.need ≤ 8 := by
  first | rfl | decide | omega | decide +kernel
def base : Nat → Fin W := fun _ => wmod 0
def emptyMachine (cursor : Fin W) : Machine :=
  {Machine.init with stack := [w[77]], mem := fun a =>
    if a = 0 then .val cursor else if a = 8 then w[10] else if a = 9 then w[99] else w[0]}
def machine (cursor : Fin W) : Machine := writeMachine (emptyMachine cursor) 1 w[0]

/-- Actual empty-heap ownership and a positive reserved allocator cursor. -/
theorem initial (cursor : Fin W) (above : 16 ≤ cursor.val) :
    StateRepr 1 1 16 F before base (machine cursor) ∧
      StructAllocatorRepr before.heap base 16 cursor (machine cursor) := by
  have absent {R : RefTy} (r : HRef [] R) : False := by
    simpa only [List.getElem?_nil,reduceCtorEq] using r.get?
  have heap : HeapRepr (State.init C).heap base 16 (emptyMachine cursor) :=
    ⟨fun r => (absent r).elim,fun r => (absent r).elim,fun r _ _ => (absent r).elim⟩
  have empty : StateRepr 1 1 16 (Frag.init []) (State.init C) base (emptyMachine cursor) := by
    refine ⟨?_,heap,(fun i => nomatch i),by decide,
      ⟨fun r => (absent r).elim,fun r => (absent r).elim,fun r => (absent r).elim⟩,
      (fun _ r => (absent r).elim),RefFieldsRepr.withoutStructs _ _ _ (fun r => absent r)⟩
    have core := Sim.init C 0 W_pos (fun _ => 0) ⟨0,W_pos⟩ rfl
    exact ⟨core.store,(fun i => nomatch i),(fun i _ => nomatch i),core.net,
      core.netSelf,core.bound,(fun i _ => nomatch i),core.env,core.funds,core.oracle⟩
  have represented : StateRepr 1 1 16 F before base (machine cursor) :=
    empty.consVal (CompileExamples.uint 0 (by decide)) w[0] (ReprV.uint_of rfl) (by decide)
  refine ⟨represented,AllocatorRepr.withoutStructs ?_ (fun r => absent r)⟩
  refine ⟨represented.heap,⟨by decide,above,rfl,?_⟩,fun r => (absent r).elim⟩
  intro address later
  have h0 : address ≠ 0 := by omega
  have h1 : address ≠ 1 := by omega
  have h8 : address ≠ 8 := by omega
  have h9 : address ≠ 9 := by omega
  change upd (emptyMachine cursor).mem 1 w[0] address = _
  rw [upd_other _ _ h1]
  simp only [emptyMachine,h0,h8,h9,if_false]

def cursor : Fin W := wmod 64

theorem initial_capacity : AllocationInput 1 16 (selected.checked.cost after)
    before base (machine cursor) := by
  rw [reached_cost]
  exact .inr ⟨by decide,cursor,(initial cursor (by decide)).2,by decide⟩

def operand : Val C Γ .uint := .simple (.lit 2 rfl)
def valueCode : CompiledVal 1 F operand := ⟨Evm.compileVal 1 operand,.core _ rfl⟩

theorem evaluated : operand.evalT before = .ok (CompileExamples.uint 2 (by decide)) := by
  first | rfl | decide | omega | with_unfolding_all rfl

def instantiated : type_of% (AssignedBareRevert.reached
    (.here : Idx Γ (.val .uint)) operand valueCode (initial cursor (by decide)).1
    (CompileExamples.uint 2 (by decide)) evaluated statement selected 8 8 10
    (by decide) (by decide) workspace (by decide) (by decide) (by decide) (by decide)
    (.inl (by decide)) (by decide) rfl initial_capacity actual_body_failure) :=
  AssignedBareRevert.reached (.here : Idx Γ (.val .uint)) operand valueCode
    (initial cursor (by decide)).1 (CompileExamples.uint 2 (by decide)) evaluated
    statement selected 8 8 10 (by decide) (by decide) workspace
    (by decide) (by decide) (by decide) (by decide) (.inl (by decide))
    (by decide) rfl initial_capacity actual_body_failure

/-- The allocation is genuinely reached before the out-of-bounds read. -/
theorem allocation_source : allocate.run after =
    .ok ⟨after.allocPush (defaultArray .uint (wmod 2)),List.prefix_append _ _⟩ := by
  change TRun.declMem A (some (.newArr (.local .here) rfl)) rfl after = _
  exact newArray_decl after .uint (.local .here) (wmod 2) (by with_unfolding_all rfl)

theorem read_after_allocation :
    read.evalT (after.allocPush (defaultArray .uint (wmod 2))) = .error .revert := by
  first | rfl | decide | omega | with_unfolding_all rfl

end Solidity.Backend.Passes.PositiveAllocationFailure
