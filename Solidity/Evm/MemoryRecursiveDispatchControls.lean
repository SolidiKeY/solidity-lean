import Solidity.Evm.MemoryRecursiveNesting
import Solidity.Evm.MemoryRecursiveControls

namespace Solidity.Evm.Memory.Recursive.Dispatch.Controls
open CompileExamples ExprExamples
private abbrev D := StorageCase.D
private def program := Recursive.Controls.nested 3
private def recursiveOut : CompiledProg 0 (Frag.init Γ) program :=
  (Recursive.compileProg 0 program (Frag.init Γ)).get (by decide +kernel)
attribute [irreducible] recursiveOut

theorem old_refuses : Compiler.compile 0 (Frag.init Γ) program=none := by
  apply Option.isNone_iff_eq_none.mp
  decide +kernel

theorem recursive_found : Recursive.compileProg 0 program (Frag.init Γ)=some recursiveOut := by
  unfold recursiveOut
  exact (Option.some_get _).symm

theorem selects_fallback : compile 0 (Frag.init Γ) program=some (.inr recursiveOut) :=
  selects_recursive old_refuses recursive_found

/-- Full common agreement from an inhabited actual initial state and genuine
computed frame/demand inputs, not an assumed final execution relation. -/
theorem fallback_agrees : Agrees (.inr recursiveOut) 1 6 base StorageCase.state machine :=
  correct (.inr recursiveOut) ⟨StorageCase.fixture,by unfold recursiveOut;decide +kernel,
    room_nonallocating recursiveOut.cert (by unfold recursiveOut;decide +kernel) 6 StorageCase.state base machine⟩

private def condition : Val D Γ .bool :=
  .binop .lt rfl rfl (.simple (.local .here)) (.simple (.lit 1 rfl))
private def conditionOut := (Memory.compileVal 0 (Frag.init Γ) condition).get (by decide +kernel)
attribute [irreducible] conditionOut

/-- Actual checked-entry acceptance for arbitrarily many further levels, built
from the real compiled mixed storage/memory body and condition. -/
theorem arbitrary_extra_depth (n : Nat) :
    ∃ choice : Choice 0 (Frag.init Γ) (nest condition program n),
      compile 0 (Frag.init Γ) (nest condition program n)=some choice :=
  entry_every_depth conditionOut recursiveOut (by unfold recursiveOut;decide +kernel)
    (by unfold conditionOut;exact (Option.some_get _).symm) recursive_found n

private def oldNil : Compiler.Compilation 0 (Frag.init Γ) (.nil : Prog D Γ Γ) :=
  (Compiler.compile 0 (Frag.init Γ) .nil).get (by decide +kernel)
attribute [irreducible] oldNil

theorem keeps_old_choice : compile 0 (Frag.init Γ) (.nil : Prog D Γ Γ)=some (.inl oldNil) := by
  apply preserves_existing
  unfold oldNil
  exact (Option.some_get _).symm

theorem keeps_old_observations : Agrees (.inl oldNil) 1 6 base StorageCase.state machine ↔
    oldNil.Agrees 1 6 base StorageCase.state machine := existing_exact _ _ _ _ _ _

/-- Failure of both real checked compilers remains a preparation refusal. -/
theorem unsupported : compile 0 (Frag.init Γ) (.cons .assumeFalse (.nil : Prog D Γ Γ))=none := by
  rw [refusal_exact]
  constructor <;> apply Option.isNone_iff_eq_none.mp <;> decide +kernel

private def observed (out : Out) : Option (List Nat) := do
  match out with
  | .ok m _=>
    let count←match m.mem 3 with | .val w=>some w.val | _=>none
    let first←match m.mem 17 with | .val w=>some w.val | _=>none
    let neighbor←match m.mem 21 with | .val w=>some w.val | _=>none
    pure [count,m.store (rootSlot D "total"),first,neighbor]
  | _=>none
private def selectedCode : Option (List Instr) := (compile 0 (Frag.init Γ) program).map code
/-- info: (some [1, 16, 16, 4], true, false) -/
#guard_msgs in
#eval (selectedCode.bind (fun code=>observed (run code machine)),
  (compile 0 (Frag.init Γ) (.nil : Prog D Γ Γ)).any (fun choice=>match choice with | .inl _=>true | _=>false),
  selectedCode.bind (fun code=>observed (run code machine))==some [1,15,16,4])

end Solidity.Evm.Memory.Recursive.Dispatch.Controls
