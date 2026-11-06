import Solidity.Yul.Views.ObjectAllocationControls

namespace Solidity.Yul.Views.Controls

def omAliases : Source.Locals mixedLayout [omArrayTy,omArrayTy] := .cons (.memRef rfl 7) (.cons (.memRef rfl 7) .nil)
def omAliasState : Source.EMState mixedEnv [omArrayTy,omArrayTy] := ⟨omAliases,omArrayState.2⟩
def omAliasExpr (second : Bool) : Source.RExpr mixedEnv [omArrayTy,omArrayTy] (.bytes .memory) :=
  .member (.indexArray (.local (if second then .there .here else .here)) (.const (Source.Q.ofInt 0)) (by decide)) 2 rfl

theorem om_alias_every_H (H) (ok : Source.MemOK mixedEnv H mixedState) : Source.MemOK mixedEnv H omAliasState := by
  have safe := om_array_every_H H ok
  exact ⟨⟨safe.1.1,⟨⟨omArrayTy,rfl,rfl⟩,⟨⟨omArrayTy,rfl,rfl⟩,trivial⟩⟩⟩,safe.2.1,safe.2.2⟩

theorem om_eval_aliases (G : Source.Glob mixedEnv) (n : Nat) :
    (Source.evalE G mixedReadFrame (n+4) (omAliasExpr false)).run omAliasState=
      (.ok (.val (Source.Val.memRef rfl 0)),omAliasState) ∧
    (Source.evalE G mixedReadFrame (n+4) (omAliasExpr true)).run omAliasState=
      (.ok (.val (Source.Val.memRef rfl 0)),omAliasState) := ⟨rfl,rfl⟩

theorem om_eval_timeout_preserved (G : Source.Glob mixedEnv) :
    (Source.evalE G mixedReadFrame 0 (omAliasExpr false)).run omAliasState=(.error .timeout,omAliasState) := rfl

def omOob : Source.RExpr mixedEnv [omArrayTy,omArrayTy] (.struct .memory mixedName) :=
  .indexArray (.local .here) (.const (Source.Q.ofInt 2)) (by decide)

theorem om_eval_oob_preserved (G : Source.Glob mixedEnv) (n : Nat) :
    (Source.evalE G mixedReadFrame (n+3) omOob).run omAliasState=(.error (.revert (Source.panicData .index)),omAliasState) := rfl

theorem om_sub_allocate_return : (Source.EM.sub (E := mixedEnv) Source.Locals.nil
    (Source.allocRef mixedStruct : Source.EM mixedEnv [] _)).run mixedState=
      (.ok (Source.Val.memRef rfl 6,Source.Locals.nil),omStructState) := rfl

theorem om_sub_late_halt : (Source.EM.sub (E := mixedEnv) Source.Locals.nil
    (do let _ ← Source.allocRef mixedStruct; Source.EM.halt (.revert [7,8]) : Source.EM mixedEnv [] Unit)).run mixedState=
      (.error (.revert [7,8]),omStructState) := rfl

/-- Actual nonmemory allocRef halts AFTER allocating. No physical preparation
None or unchanged-state/refusal interpretation is substituted for this result. -/
def omNonmemory := Source.Data.val (D := mixedLayout) (Source.Val.bool true)
def omNonmemoryState := objectAllocatedState mixedState omNonmemory

theorem om_nonmemory_error : (Source.allocRef omNonmemory).run mixedState=
    (.error (.stuck "memory reference type"),omNonmemoryState) := objectAllocRef_halt mixedState omNonmemory (by decide)

theorem om_nonmemory_not_unchanged : omNonmemoryState≠mixedState := by
  intro same
  have found := congrArg (fun s => s.2.heap.get 6) same
  change some (⟨.bool,.val (.bool true)⟩ : Sigma (Source.Data mixedLayout))=none at found
  cases found

theorem om_nonmemory_MemOK (H) (ok : Source.MemOK mixedEnv H mixedState) : Source.MemOK mixedEnv H omNonmemoryState := by
  have safe := Source.allocRef_mem' (E := mixedEnv) (H := H) omNonmemory rfl True.intro mixedState ⟨ok,.val True.intro⟩
  rw [om_nonmemory_error] at safe
  exact safe

/-- This owner-API halt example, not a proved admitted execution, has no
ordinary Placement. It does NOT refute obligations already GIVEN a Placement. -/
theorem om_nonmemory_no_ordinary_placement : ¬ Nonempty (Placement omNonmemoryState.2.heap) := by
  rintro ⟨p⟩
  have shape := p.typed 6 .bool omNonmemory (Source.Heap.alloc_get mixedHeap _)
  cases shape

/-- A raw unowned operand remains explicit unsupported physical preparation;
the owner allocation itself still succeeds. No invented Yul verdict. -/
def omBadFields : Source.DataList mixedLayout (mixedLayout.fields mixedName) :=
  .cons (.val (.bool true)) (.cons (.val mixedSeven) (.cons (.val (.memRef rfl 999))
    (.cons (.val (.memRef rfl 0)) (.cons (.val (.memRef rfl 4)) .nil))))
def omBadStruct : Source.Data mixedLayout (.struct .memory mixedName) := .struct omBadFields

theorem om_bad_child_preparation : objectAllocationView mixedHeap mixedPlacement omBadStruct rfl (.strct 5) (.strct _)
    1665 1825 (by decide) (heap_later_fresh _ _ 1665 (by decide)) (by decide) mixedPhysical=none := rfl

theorem om_bad_child_source_success : (Source.allocRef omBadStruct).run mixedState=
    (.ok (Source.Val.memRef rfl 6),objectAllocatedState mixedState omBadStruct) := objectAllocRef_run mixedState omBadStruct rfl

theorem om_bad_child_not_valid : ¬ Source.DataOK mixedEnv mixedHeap.ty omBadStruct := by
  intro valid
  cases valid with
  | struct fields =>
    cases fields with
    | cons _ tail =>
      cases tail with
      | cons _ tail =>
        cases tail with
        | cons head _ =>
          cases head with
          | val ref =>
            obtain ⟨σ,owned,shape⟩ := ref
            change none=some σ at owned
            cases owned

end Solidity.Yul.Views.Controls
