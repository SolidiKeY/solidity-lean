import Solidity.Backend.Passes.ReferenceCaptureStability
import Solidity.Backend.Passes.MappedSequence

/-! The accepted legacy-memory certificate for capture then old-local rebinding.
Original Input and full selected-map/allocator output are retained. -/
namespace Solidity.Backend.Passes.ReferenceCaptureCertificate
open Evm Evm.Memory Evm.Compiler
variable {C : Contract} {Γ : Ctx} {R : RefTy}
def program (name : Var) (dst src : Idx Γ (.mem R))
    (mapFree : (Ty.ref R).mapFree = true) : Prog C Γ (.mem R :: Γ) :=
  .cons (.declMem R name (some (.alias (.var dst mapFree))) rfl mapFree)
    (.cons (.rebindMem (.there dst) (.alias (.var (.there src) mapFree))) .nil)

def compiled {b : Nat} {F : Frag Γ} (name : Var) (dst src : Idx Γ (.mem R))
    (mapFree : (Ty.ref R).mapFree = true) : Compilation b F (program (C := C) name dst src mapFree) :=
  .memory ⟨F.push (.mem R) .ok,
    declareAliasCode b dst ++
      (aliasLocalCode b (.there (u := .mem R) dst) (.there (u := .mem R) src) ++ []),
    .cons (.declareAlias F name dst mapFree)
      (.cons (.rebind _ (.there dst) (.there src) mapFree) (.nil _))⟩

theorem execution {b L frame : Nat} {F : Frag Γ}
    (name : Var) (dst src : Idx Γ (.mem R)) (mapFree : (Ty.ref R).mapFree = true)
    {state : State C Γ} {base : Nat → Fin W} {machine : Machine}
    (represented : StateRepr L b frame F state base machine)
    (capacity : b+(Γ.length+1) ≤ frame) :
    ∃ captured rebound : HRef state.H R,
      TEnv.get dst state.env = some captured ∧ TEnv.get src state.env = some rebound ∧
      (program name dst src mapFree).run state =
        .ok ⟨(state.push (t := .mem R) (some captured)).setLocal (.there dst) (some rebound),
          List.prefix_refl _⟩ ∧ ∀ tail,
      let cm := writeMachine {machine with stack := tail}
        (cell (b+Γ.length)) (.val (base captured.id))
      let em := writeMachine cm (cellOf b (.there (u := .mem R) dst)) (.val (base rebound.id))
      (compiled (C := C) (b := b) (F := F) name dst src mapFree).Input L frame base state {machine with stack := tail} ∧
      MappedOutput (compiled (C := C) (b := b) (F := F) name dst src mapFree) L frame base state {machine with stack := tail}
        ((state.push (t := .mem R) (some captured)).setLocal (.there dst) (some rebound)) em base ∧
      run (compiled (C := C) (b := b) (F := F) name dst src mapFree).code {machine with stack := tail} = .ok em 0 ∧
      run ((compiled (C := C) (b := b) (F := F) name dst src mapFree).code ++ [.mload (cell (b+Γ.length))])
        {machine with stack := tail} = .ok (em.push (.val (base captured.id))) 0 := by
  obtain ⟨captured,rebound,hc,hr,declareRun,rebindRun,tails⟩ :=
    ReferenceCaptureStability.capture_rebind_readback represented capacity dst src mapFree name
  refine ⟨captured,rebound,hc,hr,?_,?_⟩
  · rw [program,Prog.run_cons_ok declareRun,Prog.run_cons_ok rebindRun]
    rfl
  · intro tail
    obtain ⟨reached,captureRun,updateRun,readRun⟩ := tails tail
    let cm := writeMachine {machine with stack := tail}
      (cell (b+Γ.length)) (.val (base captured.id))
    let em := writeMachine cm (cellOf b (.there (u := .mem R) dst)) (.val (base rebound.id))
    refine ⟨?_,⟨reached,BaseExtends.refl base,?_⟩,?_,?_⟩
    · refine ⟨represented.stack tail,?_,Or.inl rfl⟩
      change b+max (max Γ.length (max (Γ.length+1) 0))
        (max (max (Γ.length+1) (max (Γ.length+1) 0)) (Γ.length+1)) ≤ frame
      omega
    · intro cursor hb allocator space
      have first : StructAllocatorRepr state.heap base frame cursor cm :=
        allocator.localWrite (b+Γ.length) (by omega) (by omega) (.val (base captured.id))
      exact first.localWrite _
        (Nat.lt_of_lt_of_le hb (le_lvl b (.there dst)))
        (by simpa only [cellOf,lvl_there] using
          Nat.lt_of_lt_of_le (lvl_lt b dst) represented.locals) (.val (base rebound.id))
    · change run (_ ++ (_ ++ [])) _ = _
      rw [List.append_nil,run_append_ok captureRun]
      exact updateRun
    · simpa only [compiled,Compilation.code,List.append_nil] using readRun

end Solidity.Backend.Passes.ReferenceCaptureCertificate
/-- info: 'Solidity.Backend.Passes.ReferenceCaptureCertificate.execution' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in #print axioms Solidity.Backend.Passes.ReferenceCaptureCertificate.execution
