import Solidity.Calculus.Rules
import Solidity.Calculus.PremiseSound

namespace H28.BoundsBaseline
open Solidity

def dynamicName : Name := String.singleton 'd'
def fixedName : Name := String.singleton 'f'
def C : Contract := { vars := [(dynamicName, .ref (.array (.prim .uint))),
  (fixedName, .ref (.fixed (.prim .uint) 1))] }
def Γ : Ctx := [.val .uint]
def empty : State C Γ := (State.init C).push (t := .val .uint) ⟨9, rfl⟩
def populated : State C Γ := empty.withStorage (.cons
  (.array (.cons (.prim ⟨7, rfl⟩) .nil) .nil (by decide +kernel))
  (.cons (.fixed (.cons (.prim ⟨7, rfl⟩) .nil)) .nil))
def σ (b : Bool) : State C Γ := if b then populated else empty

def readValue {R : RefTy} (a : ArrTy R (.prim .uint)) (root : Name)
    (hr : C.rootType root = some (.ref R)) (i : PrimTy.uint.Denote) : Val C Γ .uint :=
  .read (.index (.arr a) (.loc (.root root hr)) (.simple (.lit i.1 i.2)))
def statement {R : RefTy} (a : ArrTy R (.prim .uint)) (root : Name)
    (hr : C.rootType root = some (.ref R)) (i : PrimTy.uint.Denote) : Stmt C Γ Γ :=
  .assignLocal .here (readValue a root hr i)
def update {R : RefTy} (a : ArrTy R (.prim .uint)) (root : Name)
    (hr : C.rootType root = some (.ref R)) (i : PrimTy.uint.Denote) : Upd C Γ Γ :=
  .snoc .nil (.local .here (.val (readValue a root hr i).lower))
def premise {R : RefTy} (a : ArrTy R (.prim .uint)) (root : Name)
    (hr : C.rootType root = some (.ref R)) (i : PrimTy.uint.Denote) : Premise C Γ Γ :=
  .update (update a root hr i)

theorem source_link : ∀ {R : RefTy} (a : ArrTy R (.prim .uint)) (root : Name) (hr : C.rootType root = some (.ref R)) (i : PrimTy.uint.Denote), Taclet C 0 .diamond (statement a root hr i) (premise a root hr i) := fun {_R} a root hr i => .storageIndexReadArrayFind (ak := a) (arr := .loc (.root root hr)) (v := .here) (ie := .lit i.1 i.2) rfl

def dynamicRead : Stmt C Γ Γ := statement .dyn dynamicName rfl ⟨0, rfl⟩
def fixedBoundaryRead : Stmt C Γ Γ := statement .fixed fixedName rfl ⟨1, rfl⟩
def fixedLiveRead : Stmt C Γ Γ := statement .fixed fixedName rfl ⟨0, rfl⟩
def afterRead : State C Γ := populated.setLocal .here ⟨7, rfl⟩

theorem input_inhabited : ∀ _b : Bool, Nonempty (State C Γ) := fun b => ⟨σ b⟩
theorem dynamic_boundary_reverts : dynamicRead.runR empty = .error .revert := by rfl
theorem fixed_boundary_reverts : fixedBoundaryRead.runR populated = .error .revert := by rfl
theorem dynamic_positive_read : dynamicRead.runR populated = .ok ⟨afterRead, List.prefix_refl _⟩ := by with_unfolding_all rfl
theorem fixed_positive_read : fixedLiveRead.runR populated = .ok ⟨afterRead, List.prefix_refl _⟩ := by with_unfolding_all rfl

#print axioms source_link
#print axioms input_inhabited
#print axioms dynamic_boundary_reverts
#print axioms fixed_boundary_reverts
#print axioms dynamic_positive_read
#print axioms fixed_positive_read
set_option pp.fullNames true
#check @source_link
#check @input_inhabited
#check @dynamic_boundary_reverts
#check @fixed_boundary_reverts
#check @dynamic_positive_read
#check @fixed_positive_read
end H28.BoundsBaseline
