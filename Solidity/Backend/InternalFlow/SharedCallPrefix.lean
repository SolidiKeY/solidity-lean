import Solidity.Evm.MemoryCalls
/-! Constructor sharing for the existing typed compiler certificates. No new
syntax, evaluator, machine or simulation hypothesis is introduced. -/
namespace Solidity.Backend.InternalFlow.SharedCallPrefix
open Evm Evm.Memory
variable {C : Contract}

def attach {b : Nat} {Γ Δ Ξ : Ctx} {F : Frag Γ}
    {s : Stmt C Γ Δ} {P : Prog C Δ Ξ}
    (head : CompiledStmt b F s) (tail : CompiledProg b head.frag P) :
    CompiledProg b F (.cons s P) :=
  ⟨tail.frag,head.code ++ tail.code,.cons head.cert tail.cert⟩

theorem compile_attach {b : Nat} {Γ Δ Ξ : Ctx} {F : Frag Γ}
    {s : Stmt C Γ Δ} {P : Prog C Δ Ξ}
    (head : CompiledStmt b F s) (tail : CompiledProg b head.frag P)
    (hs : Memory.compileStmt b F s = some head)
    (hp : Memory.compileProg b head.frag P = some tail) :
    Memory.compileProg b F (.cons s P) = some (attach head tail) := by
  simp only [Memory.compileProg,hs,Option.bind_eq_bind,Option.bind_some,hp,Option.pure_def]
  rfl

/-- Different typed continuations share the SAME actual compiled head. This
is a code-list constructor law; no execution or preservation is postulated. -/
theorem attach_prefix {b : Nat} {Γ Δ Ξ Υ : Ctx} {F : Frag Γ}
    {s : Stmt C Γ Δ} {P : Prog C Δ Ξ} {Q : Prog C Δ Υ}
    (head : CompiledStmt b F s)
    (left : CompiledProg b head.frag P) (right : CompiledProg b head.frag Q)
    (suffix : List Evm.Instr) (tailEq : left.code = right.code ++ suffix) :
    (attach head left).code = (attach head right).code ++ suffix := by
  change head.code ++ left.code = (head.code ++ right.code) ++ suffix
  rw [tailEq,List.append_assoc]

theorem get_some {α : Type} (o : Option α) (h : o.isSome = true) (value : α)
    (eq : o = some value) : o.get h = value := by
  cases eq
  rfl
end Solidity.Backend.InternalFlow.SharedCallPrefix
