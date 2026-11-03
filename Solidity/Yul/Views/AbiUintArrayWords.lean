import Solidity.Yul.Views.AbiUintArrayPhysical
import Solidity.Yul.Views.AbiCalldataAgreement

namespace Solidity.Yul.Views

theorem abiUintValues_get (D : Source.Layout) (payload : Roadmap.Bytes) (n : Nat)
    (i : Fin (abiUintValues D payload n).length) :
    (abiUintValues D payload n).get i=uintValueOfWord D (abiInputWord payload i.val) := by
  change ((List.range n).map (fun j => uintValueOfWord D (abiInputWord payload j)))[i.val]'(by exact i.isLt)= _
  simp only [List.getElem_map,List.getElem_range]

theorem abiUintArray_header_word (D : Source.Layout) (address : Nat→Nat) (payload : Roadmap.Bytes) (n : Nat)
    (bound : n<2^256) : ObjectWord address (abiUintArrayData D payload n) 0 ⟨n,bound⟩ := by
  have small : (abiUintValues D payload n).length<2^256 := by rw [abiUintValues_length]; exact bound
  have read : ObjectWord address (abiUintArrayData D payload n) 0 ⟨(abiUintValues D payload n).length,small⟩ :=
    .arrayLength _ small _ _
  have same : (⟨(abiUintValues D payload n).length,small⟩ : Roadmap.Word)=⟨n,bound⟩ := Fin.ext (abiUintValues_length D payload n)
  rw [same] at read
  exact read

theorem abiUintArray_element_word (D : Source.Layout) (address : Nat→Nat) (payload : Roadmap.Bytes) (n : Nat)
    (i : Fin (abiUintValues D payload n).length) :
    ObjectWord address (abiUintArrayData D payload n) (32+i.val*32) (abiInputWord payload i.val) := by
  exact .arrayElement _ _ _ i _ _ rfl (.scalar _ _ (by rw [abiUintValues_get,uintValueOfWord_word]))

end Solidity.Yul.Views
