import Solidity.Yul.Views.StructConstructorRun
import Solidity.Yul.Views.ObjectAllocationRetainedControls

namespace Solidity.Yul.Views.Controls

def scTypes : List Source.STy := [.bool,.int Source.IntTy.u256,.bytes .memory,.bytes .memory,mixedArrayTy]
def scLocals : Source.Locals mixedLayout scTypes :=
  .cons (.bool true) (.cons mixedSeven (.cons (.memRef rfl 0) (.cons (.memRef rfl 0) (.cons (.memRef rfl 4) .nil))))
def scState : Source.EMState mixedEnv scTypes := ⟨scLocals,mixedState.2⟩
def scValues : Source.Vals mixedLayout scTypes :=
  .cons (.bool true) (.cons mixedSeven (.cons (.memRef rfl 0) (.cons (.memRef rfl 0) (.cons (.memRef rfl 4) .nil))))
def scArgs : Source.RConvArgs mixedEnv scTypes scTypes :=
  .cons (.local .here) rfl (.cons (.local (.there .here)) rfl
    (.cons (.local (.there (.there .here))) rfl (.cons (.local (.there (.there (.there .here)))) rfl
      (.cons (.local (.there (.there (.there (.there .here))))) rfl .nil))))

theorem sc_typed : (mixedEnv.structFields mixedName .memory).map (List.map Prod.snd)=some scTypes := rfl
theorem sc_extracted : localConstructorValues scLocals scTypes scArgs=some scValues := rfl
theorem sc_data : structConstructorData sc_typed scValues=mixedStruct := rfl

def scAfter := objectAllocatedState scState mixedStruct

theorem sc_actual_eval (G : Source.Glob mixedEnv) (n : Nat) :
    (Source.evalE G mixedReadFrame (n+7) (.structNew sc_typed scArgs)).run scState=
      (.ok (.val (Source.Val.memRef rfl 6)),scAfter) :=
  structConstructor_run G mixedReadFrame n scState sc_typed scArgs scValues sc_extracted

theorem sc_every_H (H) (ok : Source.MemOK mixedEnv H mixedState) : Source.MemOK mixedEnv H scAfter := by
  have before : Source.MemOK mixedEnv H scState :=
    ⟨⟨ok.1.1,⟨True.intro,True.intro,⟨.bytes .memory,rfl,rfl⟩,
      ⟨.bytes .memory,rfl,rfl⟩,⟨mixedArrayTy,rfl,rfl⟩,True.intro⟩⟩,ok.2⟩
  exact (structConstructor_MemOK H scState sc_typed scArgs scValues sc_extracted before).1

/-- Physical allocation is the already checked complete mixed-map encoder,
with identical source heap; local constructor evaluation does not erase locals. -/
theorem sc_physical_map : encodeMixedHeap omStructPlacement (generatedHeapEntries omStructPlacement) omStructRaw=omStructRaw :=
  om_struct_full_map

theorem sc_physical_writeback : enumeratedMemoryWriteback scAfter omStructPlacement omStructPlacement
    (retainInitial _ _) omStructRaw=.ok (some (.ok (),scAfter)) := by
  obtain ⟨raw,step,run,safe,ready,covers,distinct,same,source,reserved⟩ :=
    retainedObjectAllocation_physical mixedHeap.ty scState mixedPlacement mixedPlacement (retainInitial _ _)
      mixedStruct rfl (.strct 5) (.strct _) om_struct_inner om_struct_valid om_struct_support 1665 1825
      (by decide) (heap_later_fresh _ _ 1665 (by decide)) (by decide) mixedPhysical
      (by exact ⟨⟨mixed_actual_MemOK.1.1,⟨True.intro,True.intro,⟨.bytes .memory,rfl,rfl⟩,
        ⟨.bytes .memory,rfl,rfl⟩,⟨mixedArrayTy,rfl,rfl⟩,True.intro⟩⟩,mixed_actual_MemOK.2⟩)
      generated_mixed_types_supported av_mixed_reads mixed_reserved
  have eq := Option.some.inj (step.symm.trans om_struct_step)
  subst raw
  exact source

theorem sc_shared_children :
    (Source.readLoc (E := mixedEnv) mixedReadFrame (τ := .bytes .memory) (.mem 6 2)).run scAfter=
      (.ok (Source.Val.memRef rfl 0),scAfter) ∧
    (Source.readLoc (E := mixedEnv) mixedReadFrame (τ := .bytes .memory) (.mem 6 3)).run scAfter=
      (.ok (Source.Val.memRef rfl 0),scAfter) := ⟨rfl,rfl⟩

theorem sc_timeout (G : Source.Glob mixedEnv) :
    (Source.evalE G mixedReadFrame 0 (.structNew sc_typed scArgs)).run scState=(.error .timeout,scState) := rfl

/-- A nonlocal expression is unsupported by THIS preparation, even when
actual source evaluation succeeds. This is not admission/refusal semantics. -/
def scEmptyState : Source.EMState mixedEnv [] := ⟨.nil,mixedState.2⟩

def scNonlocal : Source.RConvArgs mixedEnv [] [.bool] := .cons (.bool true) rfl .nil

theorem sc_nonlocal_preparation : localConstructorValues Source.Locals.nil [.bool] scNonlocal=none := rfl
theorem sc_nonlocal_source (G : Source.Glob mixedEnv) :
    (Source.evalConvArgs G mixedReadFrame 2 scNonlocal).run scEmptyState=
      (.ok (Source.Vals.cons (Source.Val.bool true) .nil),scEmptyState) := rfl

/-- Identity-typed aliases are preserved across actual caller-local
substitution on both constructor success and a subsequent genuine halt. -/
theorem sc_sub_return (G : Source.Glob mixedEnv) :
    (Source.EM.sub scLocals (Source.evalE G mixedReadFrame 7 (.structNew sc_typed scArgs))).run mixedState=
      (.ok (.val (Source.Val.memRef rfl 6),scLocals),omStructState) := rfl

theorem sc_sub_late_halt (G : Source.Glob mixedEnv) :
    (Source.EM.sub scLocals (do
      let _ ← Source.evalE G mixedReadFrame 7 (.structNew sc_typed scArgs)
      Source.EM.halt (.revert [7,8]) : Source.EM mixedEnv scTypes Unit)).run mixedState=
      (.error (.revert [7,8]),omStructState) := rfl

/-- This checks the result contains BOTH same-child pointers, rather than
merely a successful allocation tag or a single surviving alias. -/
theorem sc_alias_not_dropped : scAfter.2.heap.get 6=some ⟨.struct .memory mixedName,mixedStruct⟩ := rfl

theorem sc_argument_timeout (G : Source.Glob mixedEnv) :
    (Source.evalE G mixedReadFrame 1 (.structNew sc_typed scArgs)).run scState=(.error .timeout,scState) :=
  structConstructor_args_halt G mixedReadFrame 0 scState scState .timeout sc_typed scArgs rfl

/-- The selected actual local retains the child pointer in its typed result. -/
theorem sc_selected_child : localConstructorValue scLocals (Source.RExpr.local (Source.Idx.there (Source.Idx.there .here)))=
    some (Source.Val.memRef rfl 0) := rfl

end Solidity.Yul.Views.Controls
