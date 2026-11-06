import Solidity.Yul.Views.MemoryImageOrder
import Solidity.Source.Semantics

/-! Mixed constructor order and genuine alias/overlap boundaries. Whole raw
functions and actual source program results are compared by the general laws;
finite observations discriminate overlapping or missing-target variants. -/
namespace Solidity.Yul.Views.ImageOrderControls
private def E : Source.Env := ⟨[]⟩
private def initial : Source.EMState E [] := (.nil,Source.St.init E)
private def bytes : Source.Data E.layout (.bytes .memory) := .bytes [17]
private def state := objectAllocatedState initial bytes
private def p : Placement state.2.heap := ComputedPlacement.build _ rfl (by decide)
private def words (i : Fin 2) : Roadmap.Word := if i.val=0 then 7 else 8
private def data := staticUintData E.layout 2 words
private def arrayImage : MemoryImage p data :=
  .words _ _ (staticUintData_words p 2 (by decide) words)
private def stringImage : MemoryImage p (Source.Data.string (l:=.memory) [255,0]) :=
  .string [255,0] (by decide)
private def raw : ByteView := fun i=>if i=200 then 99 else if i=319 then 170 else 0

theorem mixed_images : stringImage.encode (arrayImage.encode raw 128) 224=
    arrayImage.encode (stringImage.encode raw 224) 128 :=
  arrayImage.disjoint_commute stringImage raw 128 224 (Or.inl (by decide))

theorem old_word : arrayImage.encode (mstore raw 128 42) 192=
    mstore (arrayImage.encode raw 192) 128 42 :=
  arrayImage.mstore_commute raw 192 128 42 (Or.inr (by decide))

theorem source_order :
    ((do Source.heapPut 0 ⟨.bytes .memory,Source.Data.bytes [33]⟩; Source.allocRef data) :
      Source.EM E [] (Source.Val E.layout (.array .memory (.int Source.IntTy.u256) (some 2)))).run state=
    ((do let v ← Source.allocRef data; Source.heapPut 0 ⟨.bytes .memory,Source.Data.bytes [33]⟩; pure v) :
      Source.EM E [] (Source.Val E.layout (.array .memory (.int Source.IntTy.u256) (some 2)))).run state :=
  heapPut_objectAllocRef_commute state 0 (.bytes [33]) rfl data rfl

theorem actual_encoder_order :
    objectAllocationView state.2.heap p data rfl (.array false 2) (.array 2 _ _) 192 256
      (by decide) (ComputedAllocationWrite.computed_fresh _ p rfl) (by decide) (mstore raw 128 42)=
    (objectAllocationView state.2.heap p data rfl (.array false 2) (.array 2 _ _) 192 256
      (by decide) (ComputedAllocationWrite.computed_fresh _ p rfl) (by decide) raw).map
        (fun out=>mstore out 128 42) :=
  objectAllocationView_mstore_commute state.2.heap p data rfl _ (.array 2 _ _) 192 256
    (by decide) (ComputedAllocationWrite.computed_fresh _ p rfl) (by decide) raw 128 42 (by decide) (by decide)

private def combined := stringImage.encode (arrayImage.encode raw 128) 224
/-- info: [7, 8, 2, 255, 0, 99, 170] -/
#guard_msgs in #eval [(mload combined 128).val,(mload combined 160).val,(mload combined 224).val,
  (combined 256).toNat,(combined 257).toNat,(combined 200).toNat,(combined 319).toNat]
/-- info: (2, 7) -/
#guard_msgs in #eval ((mload (stringImage.encode (arrayImage.encode raw 128) 128) 128).val,
  (mload (arrayImage.encode (stringImage.encode raw 128) 128) 128).val)

private def missingFirst : Source.EM E [] (Source.Val E.layout (.array .memory (.int Source.IntTy.u256) (some 2))) := do
  Source.heapPut 1 ⟨.bytes .memory,Source.Data.bytes [33]⟩
  Source.allocRef data
private def missingLast : Source.EM E [] (Source.Val E.layout (.array .memory (.int Source.IntTy.u256) (some 2))) := do
  let v ← Source.allocRef data
  Source.heapPut 1 ⟨.bytes .memory,Source.Data.bytes [33]⟩
  pure v
/-- info: (1, 2) -/
#guard_msgs in #eval ((missingFirst.run state).2.2.heap.next,(missingLast.run state).2.2.heap.next)
end Solidity.Yul.Views.ImageOrderControls
