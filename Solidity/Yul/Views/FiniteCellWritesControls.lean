import Solidity.Yul.Views.FiniteCellWrites
import Solidity.Yul.Views.MixedCellSequenceControls

/-! One interleaved Source run updates both packed persistent neighbors and a
transient field at the same numeric slot, then rewrites the first path. -/
namespace Solidity.Yul.Views.Controls
open FiniteCellWrites
open TransientSlotControls

def fcwOther := (rootRegistry account)[1]'(by decide)
def fcwOtherValue : Source.Val rootEnv.layout (rootEnv.cellTy fcwOther.path) := Source.intWrap rootU248 5

theorem fcw_other_member : fcwOther ∈ mcsPaths := by
  change fcwOther ∈ [_,fcwOther]
  exact List.mem_cons_of_mem _ List.mem_cons_self

theorem fcw_p_registered (value : Source.Val rootEnv.layout (rootEnv.cellTy mcsPath.path)) :
    Registered mcsPaths (rootTempRegistry account) ⟨mcsPath,value⟩ :=
  ⟨fun _ => mcs_member,fun bad => by change false=true at bad; cases bad⟩

theorem fcw_t_registered : Registered mcsPaths (rootTempRegistry account) ⟨tcuPath,tcuValue⟩ :=
  by
    constructor
    · intro bad; change true=false at bad; cases bad
    · intro _; exact tcu_member

theorem fcw_b_registered : Registered mcsPaths (rootTempRegistry account) ⟨fcwOther,fcwOtherValue⟩ :=
  ⟨fun _ => fcw_other_member,fun bad => by change false=true at bad; cases bad⟩

def fcwRequests : List (Request rootEnv account) :=
  [⟨mcsPath,mcsValue⟩,⟨tcuPath,tcuValue⟩,⟨fcwOther,fcwOtherValue⟩,⟨mcsPath,Source.intWrap rootU8 3⟩]

theorem fcw_registered : ∀ request ∈ fcwRequests, Registered mcsPaths (rootTempRegistry account) request := by
  intro request member
  change request ∈ [_,_,_,_] at member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with same | same | same | same <;> subst request
  · exact fcw_p_registered _
  · exact fcw_t_registered
  · exact fcw_b_registered
  · exact fcw_p_registered _

def fcwMaps := (mcsRaw,tcuRaw)
def fcwRun := (program frame fcwRequests).run child.1.2

theorem fcw_maps :
    finiteEncode mcsPaths (fcwRun.2.2.ex.world.accounts account).storage (packedMask mcsPaths mcsRaw)=some (raw fcwRequests fcwMaps).1 ∧
    finiteEncode (rootTempRegistry account) (fcwRun.2.2.ex.transient.cells account) (packedMask (rootTempRegistry account) tcuRaw)=
      some (raw fcwRequests fcwMaps).2 :=
  reencode frame child.1.2 mcsPaths _ (selectedSlotPaths_separated _ _ root_separation) rootTempChecked.separated
    fcwRequests fcw_registered fcwMaps ⟨mcs_view,tcu_before⟩ rfl

theorem fcw_words : (raw fcwRequests fcwMaps).1 0=1283 ∧ (raw fcwRequests fcwMaps).2 0=0xb6b60007 := by decide

theorem fcw_unknown : (raw fcwRequests fcwMaps).1 99=777 ∧ (raw fcwRequests fcwMaps).2 99=rawMax := by decide

theorem fcw_reads :
    (Source.readLoc frame (.stor (τ:=.int rootU8) (rootPath "a"))).run fcwRun.2=(.ok (Source.intWrap rootU8 3),fcwRun.2) ∧
    (Source.readLoc frame (.stor (τ:=.int rootU248) (rootPath "b"))).run fcwRun.2=(.ok (Source.intWrap rootU248 5),fcwRun.2) ∧
    (Source.readLoc frame (.stor (τ:=.int unsigned16) (rootPath "temp"))).run fcwRun.2=(.ok (Source.intWrap unsigned16 7),fcwRun.2) :=
  ⟨rfl,rfl,rfl⟩

theorem fcw_journal : fcwRun.2.2.ex.journal.length=child.1.2.2.ex.journal.length+4 := by
  unfold fcwRun
  rw [FiniteCellWrites.run _ _ _ rfl]
  exact Source.ExecState.journal_run _ _

/-- Request order matters when the first path is written again. -/
theorem fcw_reversed : (raw fcwRequests fcwMaps).1 0≠(raw fcwRequests.reverse fcwMaps).1 0 := by decide

theorem fcw_static : (program {frame with static:=true} fcwRequests).run child.1.2=(.error (.revert []),child.1.2) :=
  FiniteCellWrites.static _ _ _ _ rfl

theorem fcw_rollback : companionRollback (companionEnter childCore frame.this frame.sender frame.value frame.cd frame.static)
    ⟨fcwRun.2.2.ex,child.2⟩=childCore := FiniteCellWrites.rollback _ _ _ _ rfl
/-- Lack of physical registry coverage is not a Source execution refusal. -/
theorem fcw_unregistered : ¬Registered mcsPaths [] (⟨tcuPath,tcuValue⟩ : Request rootEnv account) := by
  intro missing
  have impossible := missing.2 rfl
  cases impossible

theorem fcw_unregistered_exec : ((program frame [(⟨tcuPath,tcuValue⟩ : Request rootEnv account)]).run child.1.2).1=.ok () := rfl
end Solidity.Yul.Views.Controls
