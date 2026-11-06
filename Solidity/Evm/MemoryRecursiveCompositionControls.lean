import Solidity.Evm.MemoryRecursiveNestingBudget
import Solidity.Evm.MemoryRecursiveControls

namespace Solidity.Evm.Memory.Recursive.Composition.Controls
open CompileExamples ExprExamples
private abbrev D := StorageCase.D
private def left : Prog D Γ Γ := Recursive.Controls.nested 3
private abbrev Ξ : Ctx := .val .uint::Γ
private def right : Prog D Γ Ξ := .cons (.declLocal .uint (.user "temporary") (some (.simple (.lit 42 rfl)))) .nil
private def leftOut : CompiledProg 0 (Frag.init Γ) left := (compileProg 0 left (Frag.init Γ)).get (by decide +kernel)
private def rightOut : CompiledProg 0 (Frag.init Γ) right := (compileProg 0 right (Frag.init Γ)).get (by decide +kernel)
attribute [irreducible] leftOut rightOut
private def test (takeLeft : Bool) : Val D Γ .bool := .simple (.bool takeLeft)
private def testOut (takeLeft : Bool) := (Memory.compileVal 0 (Frag.init Γ) (test takeLeft)).get (by cases takeLeft <;> decide +kernel)
private def program (takeLeft : Bool) : Prog D Γ Γ := .cons (.ite (test takeLeft) left right) .nil
private def built (takeLeft : Bool) : CompiledProg 0 (Frag.init Γ) (program takeLeft) :=
  let head:=branch (testOut takeLeft) leftOut rightOut
  cons head ⟨head.frag,[],.nil _⟩

/-- The branches have DIFFERENT actual local contexts. Restriction/meet/drop
are computed by the real compiler, not assumed as an output equality. -/
theorem branch_compiled (takeLeft : Bool) : compileProg 0 (program takeLeft) (Frag.init Γ)=some (built takeLeft) := by
  apply cons_found
  · apply branch_found
    · unfold testOut;exact (Option.some_get _).symm
    · unfold leftOut;exact (Option.some_get _).symm
    · unfold rightOut;exact (Option.some_get _).symm
  · rfl

private theorem cap (takeLeft : Bool) : (built takeLeft).cert.need≤6 := by
  change max (max Γ.length (max leftOut.cert.need rightOut.cert.need)) Γ.length≤6
  unfold leftOut rightOut
  decide +kernel
private theorem no_alloc (takeLeft : Bool) : (built takeLeft).cert.allocates=false := by
  change ((leftOut.cert.allocates || rightOut.cert.allocates) || false)=false
  unfold leftOut rightOut
  decide +kernel

theorem branch_execution (takeLeft : Bool) :
    LoopScopes.Result 1 0 6 (built takeLeft).frag StorageCase.state base machine
      (fun out amount=>Cost (built takeLeft).cert StorageCase.state out amount)
      ((program takeLeft).run StorageCase.state) (run (built takeLeft).code machine) :=
  (built takeLeft).correct ⟨StorageCase.fixture,by simpa only [Nat.zero_add] using cap takeLeft,
    room_nonallocating _ (no_alloc takeLeft) 6 StorageCase.state base machine⟩

private def loopCondition : Val D Γ .bool :=
  .binop .lt rfl rfl (.simple (.local .here)) (.simple (.lit 1 rfl))
private def loopTest := (Memory.compileVal 0 (Frag.init Γ) loopCondition).get (by decide +kernel)
attribute [irreducible] loopTest

/-- Actual compiler result AND complete runtime relation, for every finite
extra depth, using derived frame/demand inputs from the concrete base body. -/
theorem every_depth_runtime (n : Nat) :
    ∃ result : CompiledProg 0 (Frag.init Γ) (Dispatch.nest loopCondition left n),
      compileProg 0 (Dispatch.nest loopCondition left n) (Frag.init Γ)=some result ∧
      LoopScopes.Result 1 0 6 result.frag StorageCase.state base machine
        (fun out amount=>Cost result.cert StorageCase.state out amount)
        ((Dispatch.nest loopCondition left n).run StorageCase.state) (run result.code machine) :=
  Dispatch.execution_every_depth loopTest leftOut (by unfold leftOut;decide +kernel)
    (by unfold loopTest;exact (Option.some_get _).symm)
    (by unfold leftOut;exact (Option.some_get _).symm)
    (by unfold leftOut;decide +kernel) StorageCase.state base machine StorageCase.fixture
    (by unfold leftOut;decide +kernel) n

private def observed (out : Evm.Out) : Option (List Nat) := do
  match out with
  | .ok m _=>
    let count←match m.mem 3 with | .val w=>some w.val | _=>none
    let first←match m.mem 17 with | .val w=>some w.val | _=>none
    let neighbor←match m.mem 21 with | .val w=>some w.val | _=>none
    pure [count,m.store (rootSlot D "total"),first,neighbor]
  | _=>none

/-- info: (some [1, 16, 16, 4], some [0, 0, 7, 4], false, false) -/
#guard_msgs in
#eval (observed (run (built true).code machine),observed (run (built false).code machine),
  observed (run (built true).code machine)==some [0,0,7,4],
  observed (run (built false).code machine)==some [1,16,16,4])

end Solidity.Evm.Memory.Recursive.Composition.Controls
