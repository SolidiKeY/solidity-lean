import Solidity.Yul.Views.RecursiveRootLegacy

namespace Solidity.Yul.Views

theorem RecursiveStorageDeclaration.pack_strct {E name fields}
    (found : E.structFields name .storage = some fields)
    (members : RecursiveStorageFields E (fields.map Prod.snd) true) :
    (RecursiveStorageDeclaration.strct name fields found members).pack = alignFixedPack (members.pack 0) := rfl

theorem RecursiveStorageFields.pack_nil (E : Source.Env) (i p a cursor) :
    (RecursiveStorageFields.nil (E := E)).pack i p a cursor = .ok ([],cursor) := rfl

theorem checkedRecursivePack_of {E τ b} (d : RecursiveStorageDeclaration E τ b) (p a cursor cs stop)
    (typed : E.pathTy p = some τ) (packed : d.pack p a cursor = .ok (cs,stop)) :
    checkedRecursivePack d p a cursor = .ok (cs,stop) := by
  unfold checkedRecursivePack
  rw [if_pos typed]
  exact packed

theorem except_computed_value {ε α} (x : Except ε α) (ready : x.toOption.isSome) : x = .ok (x.toOption.get ready) := by
  cases x with
  | error reason => cases ready
  | ok value => rfl

end Solidity.Yul.Views

namespace Solidity.Yul.Views

theorem recursive_fields_cons_ok {E τ τs hb tb} (head : RecursiveStorageDeclaration E τ hb)
    (tail : RecursiveStorageFields E τs tb) (i p a cursor left middle right stop)
    (first : checkedRecursivePack head (p.go (.field i)) a cursor = .ok (left,middle))
    (rest : tail.pack (i+1) p a middle = .ok (right,stop)) :
    (RecursiveStorageFields.cons head tail).pack i p a cursor = .ok (left++right,stop) := by
  rw [RecursiveStorageFields.pack_cons,first]
  change (tail.pack (i+1) p a middle).map (fun out => (left++out.1,out.2)) = _
  rw [rest]
  rfl

end Solidity.Yul.Views
