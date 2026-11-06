import Solidity.Evm.MemoryRecursiveBranchRoom
import Solidity.Evm.MemoryRecursiveControls
import Solidity.Evm.MemoryAllocSourceExamples

namespace Solidity.Evm.Memory.Recursive.Composition.AllocationControls
open CompileExamples ExprExamples
private def D : Contract := contract!{}
private def Γ : Ctx := [.val .uint]
private def state : State D Γ := (State.init D).push (t:=.val .uint) (indexValue ⟨2,by decide⟩)
private def bases : Nat → Fin W := fun _=>⟨0,W_pos⟩
private def machine : Machine := {Machine.init with mem:=fun a=>if a=0 then w[16] else if a=1 then w[2] else if a=5 then w[99] else w[0]}
private theorem initial : StateRepr 1 1 6 (Frag.init Γ) state bases machine := AllocSourceExamples.initial_repr.1
private def loopCondition : Val D Γ .bool := .binop .gt rfl rfl (.simple (.local .here)) (.simple (.lit 0 rfl))
private def left : Prog D Γ Γ := .cons (.block (.cons (.loop .auto loopCondition
  (.cons (.assignLocal .here (.simple (.lit 0 rfl))) .nil)) .nil)) .nil
private def R : RefTy := .array (.prim .uint)
private abbrev Ξ : Ctx := .mem R::Γ
private def right : Prog D Γ Ξ := .cons (.declMem R (.user "notReached")
  (some (.newArr (.lit 0 rfl) rfl)) rfl rfl) .nil
private def yes : CompiledProg 1 (Frag.init Γ) left := (compileProg 1 left (Frag.init Γ)).get (by decide +kernel)
private def no : CompiledProg 1 (Frag.init Γ) right := (compileProg 1 right (Frag.init Γ)).get (by decide +kernel)
attribute [irreducible] yes no
private def test : Val D Γ .bool := .simple (.bool true)
private def condition := (Memory.compileVal 1 (Frag.init Γ) test).get (by decide +kernel)
private def program : Prog D Γ Γ := .cons (.ite test left right) .nil
private def built : CompiledProg 1 (Frag.init Γ) program := singleton (branch condition yes no)

theorem actual_compilation : compileProg 1 program (Frag.init Γ)=some built := by
  apply cons_found
  · apply branch_found
    · unfold condition;exact (Option.some_get _).symm
    · unfold yes;exact (Option.some_get _).symm
    · unfold no;exact (Option.some_get _).symm
  · rfl

/-- The complete compiled tree really contains allocation. It is not admitted
by falsely labeling every branch nonallocating. -/
theorem has_allocation : built.cert.allocates=true := by
  change ((yes.cert.allocates || no.cert.allocates) || false)=true
  unfold yes no
  decide +kernel

/-- The existing reserved-cursor guard is retained; an unselected allocator
is not made compilable by relaxing the invalid zero-base profile. -/
theorem zero_base_refused : (compileProg 0 right (Frag.init Γ)).isNone=true := by decide +kernel

private theorem actual_room : Room built.cert 6 state bases machine := by
  apply singleton_room
  apply branch_room_true
  · rfl
  · exact room_nonallocating yes.cert (by unfold yes;decide +kernel) 6 state bases machine

theorem selected_execution :
    LoopScopes.Result 1 1 6 built.frag state bases machine
      (fun out amount=>Cost built.cert state out amount)
      (program.run state) (run built.code machine) :=
  built.correct ⟨initial,by unfold built singleton cons branch yes no;decide +kernel,actual_room⟩

private def cursor (m : Machine) : Option Nat := match m.mem 0 with | .val w=>some w.val | _=>none
private def observed (out : Evm.Out) : Option (List Nat) := do
  match out with
  | .ok m _=>
    let first←match m.mem 1 with | .val w=>some w.val | _=>none
    let neighbor←match m.mem 5 with | .val w=>some w.val | _=>none
    let ptr←cursor m
    pure [first,neighbor,ptr]
  | _=>none

/-- info: (some [0, 99, 16], true, false, false) -/
#guard_msgs in
#eval (observed (run built.code machine),built.cert.allocates,
  observed (run built.code machine)==some [0,99,17],
  observed (run built.code machine)==some [2,99,16])

end Solidity.Evm.Memory.Recursive.Composition.AllocationControls
