import Solidity.Backend.Passes.MappedTail
import Solidity.Backend.Passes.CoreBoundary

/-! Returned storage aliases retain the original plain-fragment guard and
symbolic PathSlot. The selected branch's complete output and map are retained;
no symbolic slot is coerced to a numeric EVM storage address. -/
namespace Solidity.Backend.Passes.ReturnedStorageCapture
open Evm Evm.Compiler
variable {C : Contract} {b L frame : Nat} {Γ Δ : Ctx} {R : RefTy}
  {F : Frag Γ} {P : Prog C Γ (.alias R :: Δ)}

theorem readback (compiled : Compilation b F P)
    (accepted : Compiler.compile b F P = some compiled)
    {base : Nat → Fin W} {state : State C Γ} {machine : Machine}
    {out : Solidity.Out C state.H (.alias R :: Δ)}
    (input : compiled.Input L frame base state machine)
    (free : Evm.Prog.pays P = false) (success : P.run state = .ok out)
    (reference : SRef C (.ref R)) (bound : TEnv.get .here out.st.env = some reference)
    (plain : compiled.frag.get .here = .ok) :
    Compiler.compile b F P = some compiled ∧
    ∃ (canonical : Machine) (selected : Nat → Fin W) (slot : Slot),
      PathSlot C true reference slot ∧ canonical.stack = [] ∧ ∀ tail,
      compiled.Input L frame base state {machine with stack := tail} ∧
      run compiled.code {machine with stack := tail} = .ok {canonical with stack := tail} 0 ∧
      MappedOutput compiled (L + Evm.Prog.pushes P) frame base state {machine with stack := tail}
        out.st {canonical with stack := tail} selected ∧
      canonical.mem (cell (b+Δ.length)) = .slot slot ∧
      run (compiled.code ++ [.mload (cell (b+Δ.length))]) {machine with stack := tail} =
        .ok ({canonical with stack := tail}.push (.slot slot)) 0 := by
  obtain ⟨canonical,selected,_,empty,runs⟩ := compilation_success_shared_mapped compiled input free success
  have core := mapped_output_core compiled (runs []).2
  obtain ⟨actual,slot,localRead,word,path⟩ := core.aliases .here plain
  change TEnv.get .here out.st.env = some actual at localRead
  rw [bound] at localRead
  have same : actual = reference := Option.some.inj localRead.symm
  subst actual
  have physical : canonical.mem (cell (b+Δ.length)) = .slot slot := by
    simpa only [lvl_here] using word
  refine ⟨accepted,canonical,selected,slot,path,empty,?_⟩
  intro tail
  have load : run [.mload (cell (b+Δ.length))] {canonical with stack := tail} =
      .ok ({canonical with stack := tail}.push (.slot slot)) 0 := by
    change Evm.Out.ok ({canonical with stack := tail}.push (canonical.mem (cell (b+Δ.length)))) 0 = _
    rw [physical]
  exact ⟨compilation_input_stack compiled input tail,(runs tail).1,(runs tail).2,physical,
    (run_append_ok (c₂ := [.mload (cell (b+Δ.length))]) (runs tail).1).trans load⟩

/-- info: 'Solidity.Backend.Passes.ReturnedStorageCapture.readback' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms readback
end Solidity.Backend.Passes.ReturnedStorageCapture
