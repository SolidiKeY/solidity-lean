import Solidity.Backend.InternalFlow.RuntimeFrameV3ScalarChildEntry
import Solidity.Backend.InternalFlow.RuntimeFrameV3AllocatingScalarTarget

/-! Populated scalar child entry from an actual reached allocation endpoint.
The output machine is the one produced by capture and compiled argument entry;
no flattened full-memory equality or recursive body compiler is assumed. -/
namespace Solidity.Backend.InternalFlow.RuntimeFrame.AllocatingScalarEntry.Checks
open Evm Evm.Memory RecursiveSource ScalarRecursiveSource CountdownWitness
abbrev F := AllocatingScalarTarget.F
abbrev parent := AllocatingScalarTarget.after
abbrev input := AllocatingScalarTarget.target
def ref : HRef parent.H A := P.r0.wk (AllocatingScalarSource.extension AllocatingScalarTarget.initial)
def image : List Instr := Restore.saveCells 8 (Restore.contextCells 2 (Frame A)) ++ code (C:=P.C) 2 F

/-- The real capture result is retained and the exact same reached machine is
used for child representation, ownership and all ordered observations. -/
theorem endpoint : ∃ saved target,
 run (Restore.saveCells 8 (Restore.contextCells 2 (Frame A))) input=.ok saved 0 ∧
 run (code (C:=P.C) 2 F) saved=.ok target 0 ∧ run image input=.ok target 0 ∧
 run ([.push w[0],.mstore 4] ++ (AllocatingScalarTarget.selected.code ++ image))
  AllocatorReturn.Checks.input=.ok target 0 ∧
 StateRepr 1 2 16 F (entered parent 1 (by decide) ref) AllocatingScalarTarget.addresses target ∧
 StructAllocatorRepr (entered parent 1 (by decide) ref).heap AllocatingScalarTarget.addresses 16
  (⟨26,by decide⟩ : Fin W) target ∧
 (target.stack,[target.mem 0,target.mem 2,target.mem 3,target.mem 4,target.mem 5,target.mem 8,target.mem 9,
 target.mem 10,target.mem 11,target.mem 12,target.mem 16,target.mem 17,target.mem 18,target.mem 22])=
 ([w[77]],[w[26],w[16],w[1],w[0],w[22],w[13],w[99],w[16],w[2],w[0],w[2],w[7],w[9],w[3]]) ∧
 target.mem 3≠target.mem 11 ∧ target.mem 8≠w[12] ∧ target.mem 0≠w[30] := by
 obtain ⟨saved,captureRun,captured,represented,growth⟩ :=
   Context.capture_context (σ:=parent) (F:=F) (base:=AllocatingScalarTarget.addresses) input 8 8 10 AllocatingScalarTarget.endpoint.2.1
     (by decide) (by decide) (by decide) (by decide) (by decide) (.inl (by decide)) (by decide) rfl
 have facts := entry (C:=P.C) (R:=A) (L:=1) (b:=2) (frame:=16) (F:=F) rfl parent 1 (by decide) ref rfl rfl AllocatingScalarTarget.addresses saved represented
 let target := childMachine (R:=A) 2 saved 1 (by decide)
 have owner := growth (⟨26,by decide⟩ : Fin W) (by decide) AllocatingScalarTarget.endpoint.2.2.1 (by decide)
 have allocation : StructAllocatorRepr (entered parent 1 (by decide) ref).heap AllocatingScalarTarget.addresses 16 (⟨26,by decide⟩ : Fin W) target :=
   (owner.localWrite 3 (by decide) (by decide) w[1]).localWrite 4 (by decide) (by decide) w[0]
 have outside (x : Nat) (h3 : x≠3) (h4 : x≠4) : target.mem x=saved.mem x :=
   (upd_other _ _ h4).trans (upd_other _ _ h3)
 have locals_at (x : Nat) (small : x<8) (h3 : x≠3) (h4 : x≠4) : target.mem x=input.mem x :=
   (outside x h3 h4).trans (captured.locals x small)
 have exterior (x : Nat) (hp : x≠8) (far : x<10 ∨ 13≤x) (h3 : x≠3) (h4 : x≠4) : target.mem x=input.mem x :=
   (outside x h3 h4).trans (captured.exterior x hp far)
 have payload (i : Nat) (small : i<3) : target.mem (10+i)=input.mem (2+i) := by
   rw [outside (10+i) (by omega) (by omega)]
   simpa only [Restore.contextCells,List.getElem_map,List.getElem_range] using captured.payload i small
 have cursor : target.mem 8=w[13] := (outside 8 (by decide) (by decide)).trans captured.cursor
 have counter : target.mem 3=w[1] := by rfl
 have resultWord : target.mem 4=w[0] := by rfl
 have parentCounter : target.mem 11=w[2] := payload 1 (by decide)
 have allocator : target.mem 0=w[26] := locals_at 0 (by decide) (by decide) (by decide)
 refine ⟨saved,target,captureRun,facts.1,(run_append_ok captureRun).trans facts.1,?_,facts.2.1,allocation,?_,?_,?_,?_⟩
 · rw [run_append_ok AllocatingScalarTarget.default_entry,run_append_ok AllocatingScalarTarget.endpoint.1]
   exact (run_append_ok captureRun).trans facts.1
 · have stack : target.stack=input.stack := captured.stack
   rw [stack,allocator,locals_at 2 (by decide) (by decide) (by decide),counter,resultWord,
     locals_at 5 (by decide) (by decide) (by decide),cursor,
     exterior 9 (by decide) (.inl (by decide)) (by decide) (by decide),
     payload 0 (by decide),parentCounter,payload 2 (by decide),
     exterior 16 (by decide) (.inr (by decide)) (by decide) (by decide),
     exterior 17 (by decide) (.inr (by decide)) (by decide) (by decide),
     exterior 18 (by decide) (.inr (by decide)) (by decide) (by decide),
     exterior 22 (by decide) (.inr (by decide)) (by decide) (by decide)]
   rfl
 · rw [counter,parentCounter]
   decide
 · rw [cursor]
   decide
 · rw [allocator]
   decide

end Solidity.Backend.InternalFlow.RuntimeFrame.AllocatingScalarEntry.Checks

/-- info: 'Solidity.Backend.InternalFlow.RuntimeFrame.AllocatingScalarEntry.Checks.endpoint' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Solidity.Backend.InternalFlow.RuntimeFrame.AllocatingScalarEntry.Checks.endpoint
