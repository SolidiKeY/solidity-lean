import Solidity.Calculus.Rules
import Solidity.Calculus.PremiseSound

namespace H28.DivisionBaseline
open Solidity

def C : Contract := { vars := [] }
def Γ : Ctx := [.val .int]
def initial (b : Bool) : PrimTy.int.Denote :=
  if b then ⟨-Semantics.intBound, by decide +kernel⟩ else ⟨1, by decide +kernel⟩
def divisor (b : Bool) : PrimTy.int.Denote :=
  if b then ⟨-1, by decide +kernel⟩ else ⟨0, by decide +kernel⟩
def σ (b : Bool) : State C Γ := (State.init C).push (t := .val .int) (initial b)
def statement (b : Bool) : Stmt C Γ Γ :=
  .opAssign .div rfl rfl (.local .here) (.simple (.lit (divisor b).1 (divisor b).2))
def update (b : Bool) : Upd C Γ Γ := .snoc .nil (.local .here (.val
  (.app2 (.binop .div rfl) (.pvV .here) (.app0 (.lit (divisor b))))))
def premise (b : Bool) : Premise C Γ Γ := .update (update b)

theorem source_link : ∀ b : Bool, Taclet C 0 .diamond (statement b) (premise b) := fun _b => .localOpAssign
theorem input_inhabited : ∀ _b : Bool, Nonempty (State C Γ) := fun b => ⟨σ b⟩
theorem rejecting_run : ∀ b : Bool, (statement b).runR (σ b) = .error .revert := by
  intro b
  cases b <;> rfl

#print axioms source_link
#print axioms input_inhabited
#print axioms rejecting_run
set_option pp.fullNames true
#check @source_link
#check @input_inhabited
#check @rejecting_run
end H28.DivisionBaseline
