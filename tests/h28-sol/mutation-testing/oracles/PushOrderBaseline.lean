import Solidity.Calculus.Rules
import Solidity.Calculus.PremiseSound

namespace H28.PushOrderBaseline
open Solidity

def arrayName : Name := String.singleton 'a'
def C : Contract := { vars := [(arrayName, .ref (.array (.prim .uint)))] }
def path : SPath C [] (.array (.prim .uint)) := .loc (.root arrayName rfl)
def empty : State C [] := .init C
def populated : State C [] := empty.withStorage (.cons (.array
  (.cons (.prim ⟨7, rfl⟩) .nil) .nil (by decide +kernel)) .nil)
def statement : Stmt C [] [] := .pushOpAssign .add rfl rfl path (.simple (.lit 1 rfl))
def extendUpdate : Upd C [] [] := .snoc .nil (.storage (.app2 .pushSlot (.app0 .storage) path.lower))
def lastIndex : Tm C [] (.val .uint) := Tms.Term.binop .sub .uint
  (Tms.Term.lenH rfl Tms.STerm.storage path.lower) (Tms.Term.nat 1 rfl) rfl
def lastPath : Tm C [] (.path (.prim .uint)) := Tms.PTerm.at (.arr .dyn) path.lower lastIndex
def added : Tm C [] (.val .uint) := Tms.Term.binopC .add rfl rfl
  (Tms.Term.find Tms.STerm.storage lastPath) (.app0 (.lit (p := .uint) ⟨1, rfl⟩))
def writeUpdate : Upd C [] [] := .snoc .nil (.storage
  (Tms.STerm.save Tms.STerm.storage lastPath (Tms.SValT.val added)))
def first : Upd C [] [] := extendUpdate
def second : Upd C [] [] := writeUpdate
def premise : Premise C [] [] := .updates first second

theorem source_link : Taclet C 0 .box statement premise := .storagePushAddAssign (hp := rfl) (sp := path) (se := .lit 1 rfl) (hlen := rfl) rfl

def afterEmpty : State C [] := empty.withStorage (.cons (.array
  (.cons (.prim ⟨1, rfl⟩) .nil) .nil (by decide +kernel)) .nil)
def afterPopulated : State C [] := empty.withStorage (.cons (.array
  (.cons (.prim ⟨7, rfl⟩) (.cons (.prim ⟨1, rfl⟩) .nil)) .nil (by decide +kernel)) .nil)
def afterWritten : State C [] := empty.withStorage (.cons (.array
  (.cons (.prim ⟨8, rfl⟩) .nil) .nil (by decide +kernel)) .nil)
def afterSwapped : State C [] := empty.withStorage (.cons (.array
  (.cons (.prim ⟨8, rfl⟩) (.cons (.prim ⟨0, rfl⟩) .nil)) .nil (by decide +kernel)) .nil)

theorem input_inhabited : Nonempty (State C []) := ⟨empty⟩
theorem empty_run : statement.runR empty = .ok ⟨afterEmpty, List.prefix_refl _⟩ := by with_unfolding_all rfl
theorem populated_run : statement.runR populated = .ok ⟨afterPopulated, List.prefix_refl _⟩ := by with_unfolding_all rfl

#print axioms source_link
#print axioms input_inhabited
#print axioms empty_run
#print axioms populated_run
set_option pp.fullNames true
#check @source_link
#check @input_inhabited
#check @empty_run
#check @populated_run
end H28.PushOrderBaseline
