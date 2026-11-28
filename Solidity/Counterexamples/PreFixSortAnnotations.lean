import Solidity.SortCheck.Faithfulness


namespace Solidity
namespace Counterexamples
namespace PreFixSortAnnotations

open TacletAnnotations
open SortFaithfulness


def People : Contract := contract!{ Person alice; Person bob; }

def Flags : Contract := contract!{ bool flag; bool flag2; }

theorem person_not_int (v : SVal (.ref (.struct "Person"))) :
    SortOkS (.fixed .int) v = false := by
  cases v with
  | struct fs => rfl

theorem bool_not_int (v : SVal (.prim .bool)) :
    SortOkS (.fixed .int) v = false := by
  cases v with
  | prim b => rfl


def aliceCopy : Stmt People [] [] :=
  stmtOf (@Taclet.storageRootWriteCopySource People 0 .box [] "alice" (.struct "Person") rfl
    (.loc (.root "bob" rfl)) rfl rfl)

theorem preFix_rootCopy_not_faithful :
    ¬ RowFaithful preFixStorageRootWriteCopySource aliceCopy := by
  intro h
  obtain ⟨R, hR, _, hall⟩ := h ⟨.storage, .value, .fixed .int⟩ (by decide)
  cases hR
  have := hall (State.init People) (SRef.ofRoot "bob" rfl) _ rfl rfl
  rw [person_not_int] at this
  exact Bool.false_ne_true this

theorem current_rootCopy_faithful :
    CtorFaithful ``Taclet.storageRootWriteCopySource aliceCopy :=
  faithful_storageRootWriteCopySource

theorem preFix_rootCopyStruct_faithful {C : Contract} {k : Nat} {m : Modality} {Γ : Ctx}
    {gsp : Name} {R : RefTy} {hgsp : C.rootType gsp = some (.ref R)}
    {sp : SPath C Γ (.ref R)} {hm : (Ty.ref R).mapFree = true} {hsp : sp.isSimple = true} :
    RowFaithful preFixStorageRootWriteCopySourceStruct
      (stmtOf (@Taclet.storageRootWriteCopySource C k m Γ gsp R hgsp sp hm hsp)) :=
  rowFaithful_of (dom := .storage) (cls := .reference) rfl rfl rfl (by decide)


def flagRead : Stmt Flags [.val .bool] [.val .bool] :=
  stmtOf (@Taclet.storageRootReadSelect Flags 0 .box [.val .bool] .bool .here "flag" rfl)

theorem preFix_readSelect_not_faithful :
    ¬ RowFaithful preFixStorageRootReadSelect flagRead := by
  intro h
  obtain ⟨R, hR, _, hall⟩ := h ⟨.storage, .value, .fixed .int⟩ (by decide)
  cases hR
  have := hall ((State.init Flags).push (t := .val .bool) (false : Bool))
    (SRef.ofRoot "flag" rfl) _ rfl rfl
  rw [bool_not_int] at this
  exact Bool.false_ne_true this

theorem current_readSelect_faithful :
    CtorFaithful ``Taclet.storageRootReadSelect flagRead :=
  faithful_storageRootReadSelect

end PreFixSortAnnotations
end Counterexamples
end Solidity
