import Solidity.Backend.Passes.MappedTail
import Solidity.Lowering.V07.ReferenceCaptureRelated

/-! Plain storage-alias capture over the existing core certificate and symbolic
Slot representation. No storage contents, layout/hash or decoder proof is added. -/
namespace Solidity.Backend.Passes.RelatedStorageCapture
open Evm Evm.Compiler Solidity.Lowering.V07

theorem execution {E : Source.Env} {srcΓ : Source.RCtx} {C : Contract} {Γ : Ctx}
    (G : Source.Glob E) (SF : Source.Fr) (fuel : Nat)
    (source : Source.EMState E srcΓ) (target : State C Γ) (m : ContextMap srcΓ Γ)
    (Rel : (τ : Source.STy) → (u : LTy) → Source.Val E.layout τ → u.TDenote C target.H → Prop)
    (aligned : m.Related Rel source.1 target.env)
    (i : Source.Idx srcΓ (.bytes .storage)) (j : Idx Γ (.alias bytesR))
    (path : Source.SPath) (r : SRef C (.ref bytesR)) (slotMap : m.slot i = ⟨.alias bytesR,j⟩)
    (sourceRead : source.1.get i = .storRef rfl path) (targetRead : TEnv.get j target.env = some r)
    {offset L frame : Nat} {F : Frag Γ} {F' : Frag (.alias bytesR :: Γ)}
    (cert : inFragP F (storageCapture (C := C) j) = some F') (plain : F.get j = .ok)
    {base : Nat → Fin W} {machine : Machine}
    (input : (Compilation.core (b := offset) F' cert).Input L frame base target machine) :
    (Source.evalE G SF (fuel+1) (.local i)).run source = (.ok (.val (.storRef rfl path)),source) ∧
    Rel (.bytes .storage) (.alias bytesR) (.storRef rfl path) (some r) ∧
    (m.cons (.bytes .storage) (.alias bytesR)).Related Rel
      (.cons (.storRef rfl path) source.1) (target.push (t := .alias bytesR) (some r)).env ∧
    (m.wk (Thin.drop (t := .alias bytesR) .refl)).Related Rel
      source.1 (target.push (t := .alias bytesR) (some r)).env ∧
    (target.push (t := .alias bytesR) (some r)).drop (.push .refl) = target ∧
    ∃ (canonical : Machine) (selected : Nat → Fin W) (slot : Slot),
      PathSlot C true r slot ∧ canonical.stack = [] ∧ ∀ tail,
      (Compilation.core (b := offset) F' cert).Input L frame base target {machine with stack := tail} ∧
      run (compileProg offset (storageCapture (C := C) j)) {machine with stack := tail} = .ok {canonical with stack := tail} 0 ∧
      MappedOutput (.core (b := offset) F' cert) L frame base target {machine with stack := tail}
        (target.push (t := .alias bytesR) (some r)) {canonical with stack := tail} selected ∧
      run (compileProg offset (storageCapture (C := C) j) ++ [.mload (cell (offset+Γ.length))]) {machine with stack := tail} =
        .ok ({canonical with stack := tail}.push (.slot slot)) 0 := by
  have facts := related_storage_capture G SF fuel source target m Rel aligned i j path r slotMap sourceRead targetRead
  obtain ⟨actualRef,slot,localRead,word,pathSlot⟩ := input.1.aliases j plain
  change TEnv.get j target.env = some actualRef at localRead
  have same : actualRef = r := Option.some.inj (localRead.symm.trans targetRead)
  subst actualRef
  have initialWord : machine.mem (cellOf offset j) = .slot slot := word
  obtain ⟨canonical,selected,_,empty,runs⟩ := compilation_success_shared_mapped
    (.core (b := offset) F' cert) input (by rfl) facts.2.1
  refine ⟨facts.1,facts.2.2.2.1,facts.2.2.2.2.1,facts.2.2.2.2.2.1,
    facts.2.2.2.2.2.2,canonical,selected,slot,pathSlot,empty,?_⟩
  intro tail
  have directRun : run (compileProg offset (storageCapture (C := C) j)) {machine with stack := tail} =
      .ok (Memory.writeMachine {machine with stack := tail} (cell (offset+Γ.length)) (.slot slot)) 0 := by
    change run [.mload (cellOf offset j),.mstore (cell (offset+Γ.length))] _ = _
    simp only [run,exec_cons_zero,Instr.step,Machine.next,Out.ok_bind,initialWord,exec_nil,Memory.writeMachine]
  have machines := (Evm.Out.ok.inj ((runs tail).1.symm.trans directRun)).1
  have freshWord := congrArg (fun m : Machine => m.mem (cell (offset+Γ.length))) machines
  change canonical.mem (cell (offset+Γ.length)) = upd machine.mem (cell (offset+Γ.length)) (.slot slot) (cell (offset+Γ.length)) at freshWord
  rw [upd_same] at freshWord
  have load : run [.mload (cell (offset+Γ.length))] {canonical with stack := tail} =
      .ok ({canonical with stack := tail}.push (.slot slot)) 0 := by
    change Evm.Out.ok ({canonical with stack := tail}.push (canonical.mem (cell (offset+Γ.length)))) 0 = _
    rw [freshWord]
  exact ⟨compilation_input_stack (.core (b := offset) F' cert) input tail,(runs tail).1,(runs tail).2,
    (run_append_ok (c₂ := [.mload (cell (offset+Γ.length))]) (runs tail).1).trans load⟩

end Solidity.Backend.Passes.RelatedStorageCapture
