import Solidity.Yul.Views.AbiUintArrayControls
import Solidity.Yul.Views.AbiDecodeSequence
import Solidity.Yul.Views.RetainedEntryRun

namespace Solidity.Yul.Views.Controls

def adEmptyInput : Roadmap.Bytes := Source.wordBytes 32++Source.wordBytes 0
def adEmptyState := objectAllocatedState mixedState
  (abiUintArrayData mixedLayout (abiArrayPayload adEmptyInput 0) (abiArrayLength adEmptyInput 0))

theorem ad_empty_array :
    (Source.decodeArg adEmptyInput 0 (.array .memory (.int Source.IntTy.u256) none)).run mixedState=
      (.ok (Source.Val.memRef rfl 6),adEmptyState) := abiUintArray_run mixedState adEmptyInput 0 (by decide) (by decide) (by decide)

def adUnaligned : Roadmap.Bytes := Source.wordBytes 33++[0xa5]++Source.wordBytes 1++Source.wordBytes 77

theorem ad_unaligned_is_actual_owner_success :
    (Source.decodeArg adUnaligned 0 (.array .memory (.int Source.IntTy.u256) none)).run mixedState=
      (.ok (Source.Val.memRef rfl 6),objectAllocatedState mixedState
        (abiUintArrayData mixedLayout (abiArrayPayload adUnaligned 0) (abiArrayLength adUnaligned 0))) :=
  abiUintArray_run mixedState adUnaligned 0 (by decide) (by decide) (by decide)

theorem ad_missing_header :
    (Source.decodeArg (E := mixedEnv) [] 0 (.array .memory (.int Source.IntTy.u256) none)).run mixedState=
      (.error (.revert []),mixedState) := abiUintArray_missing_header mixedState [] 0 (by decide)

def adLarge : Roadmap.Bytes := Source.wordBytes 32++Source.wordBytes (Source.toWord (2^64))

theorem ad_large_before_payload :
    (Source.decodeArg adLarge 0 (.array .memory (.int Source.IntTy.u256) none)).run mixedState=
      (.error (.revert (Source.panicData .alloc)),mixedState) := abiUintArray_oversized mixedState adLarge 0 (by decide) (by decide)

def adShort : Roadmap.Bytes := Source.wordBytes 32++Source.wordBytes 3++Source.wordBytes 7

theorem ad_short_payload :
    (Source.decodeArg adShort 0 (.array .memory (.int Source.IntTy.u256) none)).run mixedState=
      (.error (.revert []),mixedState) := abiUintArray_short_payload mixedState adShort 0 (by decide) (by decide) (by decide)

/-- ABI bool canonicality is the owner's existing empty revert, distinct
from physical storage dirty-bool truthiness and its preserved byte2 tests. -/
def adDirtyBool : Roadmap.Bytes := Source.wordBytes 32++Source.wordBytes 1++Source.wordBytes 2

theorem ad_dirty_bool_ABI_error {Γ} (s : Source.EMState mixedEnv Γ) :
    (Source.decodeArg adDirtyBool 0 (.array .memory .bool none)).run s=(.error (.revert []),s) := by
  have off : Source.wordAt adDirtyBool 0=32 := by decide
  have length : adDirtyBool.length=96 := by simp only [adDirtyBool,List.length_append,Source.wordBytes_length]
  have len : Source.wordAt (adDirtyBool.drop 32) 0=1 := by decide
  have item : Source.wordAt (adDirtyBool.drop 64) 0=2 := by decide
  simp only [Source.decodeArg,Source.STy.isValueTy,ite_true]
  rw [off,length,len]
  simp only [if_neg (show ¬96<32+32 from by decide),if_neg (show ¬2^64≤1 from by decide),
    if_pos (show 32+32+32*1≤96 from by decide)]
  change (do
    let xs ← ([0].mapM (fun j => (Source.EM.lift (Source.decodeWord mixedLayout
      (Source.wordAt (adDirtyBool.drop 64) j) .bool) : Source.EM mixedEnv Γ (Source.Val mixedLayout .bool))))
    Source.allocRef (Source.Data.array (l := .memory) (n := none) xs.length (fun _ h => nomatch h)
      (fun i => Source.Data.val (xs.get i)))).run s= _
  rw [List.mapM_cons,item]
  rfl

def adTy : Source.STy := .array .memory (.int Source.IntTy.u256) none
def adAliases : Source.Locals mixedLayout [adTy,adTy] := .cons (.memRef rfl 6) (.cons (.memRef rfl 6) .nil)
def adAliasState : Source.EMState mixedEnv [adTy,adTy] := ⟨adAliases,adState.2⟩
def adAliasExpr (second : Bool) : Source.RExpr mixedEnv [adTy,adTy] (.int Source.IntTy.u256) :=
  .indexArray (.local (if second then .there .here else .here)) (.const (Source.Q.ofInt 1)) (by decide)

theorem ad_actual_aliases (G : Source.Glob mixedEnv) (n : Nat) :
    (Source.evalE G mixedReadFrame (n+3) (adAliasExpr false)).run adAliasState=
      (.ok (.val (uintValueOfWord mixedLayout omMaxWord)),adAliasState) ∧
    (Source.evalE G mixedReadFrame (n+3) (adAliasExpr true)).run adAliasState=
      (.ok (.val (uintValueOfWord mixedLayout omMaxWord)),adAliasState) := ⟨rfl,rfl⟩

/-- The actual decoder itself is independent of F.static: ordinary memory
allocation is not the storage-write static refusal operation. -/
theorem ad_decode_sub_return :
    (Source.EM.sub (E := mixedEnv) Source.Locals.nil
      (Source.decodeArg adInput 0 adTy : Source.EM mixedEnv [] _)).run mixedState=
      (.ok (Source.Val.memRef rfl 6,Source.Locals.nil),adState) := by
  rw [actualSub_endpoints]
  simp only [adTy]
  rw [abiUintArray_run (⟨Source.Locals.nil,mixedState.2⟩ : Source.EMState mixedEnv []) adInput 0 ad_header ad_small ad_payload]
  rfl

theorem ad_decode_sub_late_halt :
    (Source.EM.sub (E := mixedEnv) Source.Locals.nil (do
      let _ ← Source.decodeArg adInput 0 adTy
      Source.EM.halt (.revert [7,8]) : Source.EM mixedEnv [] Unit)).run mixedState=
      (.error (.revert [7,8]),adState) := by
  rw [actualSub_endpoints]
  rw [Source.Hoare.run_bind]
  simp only [adTy]
  rw [abiUintArray_run (⟨Source.Locals.nil,mixedState.2⟩ : Source.EMState mixedEnv []) adInput 0 ad_header ad_small ad_payload]
  rfl

/-- The actual dispatcher drops FOUR selector bytes before decodeArgs. -/
def adTransaction : Roadmap.Bytes := [0xde,0xad,0xbe,0xef]++adInput

theorem ad_selector_offset : calldataload adTransaction 4=32 := by
  rw [← abi_wordAt_slice_calldataload adTransaction 4 0]
  exact ad_offset

theorem ad_selector_length : calldataload adTransaction 36=3 := by
  rw [← abi_wordAt_slice_calldataload adTransaction 4 1]
  decide

theorem ad_wrong_selector_offset : calldataload adTransaction 0≠32 := by decide

end Solidity.Yul.Views.Controls
