import Solidity.Yul.World.DelegateRevertOutput

/-! The selected successful request is checked against the actual arbitrary
owned-byte journal. These are computations of the producer validator, not
assumptions about a callee run or universal layout adequacy. -/
namespace Solidity.Yul.World.DelegateSuccessPreparation
open Solidity.Source
open Solidity.Yul.Views
open Solidity.Yul.World.StateCall
open Solidity.Yul.World.StateCallPhysical (flag registry)
open Solidity.Yul.World.DelegatePhysical

theorem selected_encoding (b : BoolEncodingJournal) :
    (requestEncoding (E:=env) registry registry request b).cells
      (ownedByteKey false account flag)=canonicalTrueByte := by
  have actual:=encodingWrites_result [flag] false account (fun _=>request.raw) b
    (by simp only [finiteSeparated,List.pairwise_singleton]) flag List.mem_cons_self
  change (requestEncoding (E:=env) registry registry request b).cells
    (ownedByteKey false account flag)=chosenPathCode flag (b.cells (ownedByteKey false account flag)) (fun _=>request.raw) at actual
  rw [actual]
  rfl

theorem source_op (b : BoolEncodingJournal)
    (p : RepresentedSlotPlan (E:=env) registry registry request b) :
    p.packed.sourceOp=writeOp account := by
  have checked:=p.packed.prepared
  rw [p.request_eq] at checked
  change finiteAccountWrite? account
    [representedPath flag ((requestEncoding (E:=env) registry registry request b).cells
      (ownedByteKey false account flag))] (fun _=>request.raw)=some p.packed.sourceOp at checked
  rw [selected_encoding] at checked
  have fixed : finiteAccountWrite? account [representedPath flag canonicalTrueByte]
      (fun _=>request.raw)=some (writeOp account) := by
    change some (Source.Op.account account (fun ac=>{ac with storage := preserveScalarWrite (L:=env.lay account) flagPath (representedPath flag canonicalTrueByte).codec (.bool true) ac.storage}))=_
    apply congrArg some
    apply congrArg (Source.Op.account account)
    funext ac
    rw [StateCallPhysical.preserve_true]
    rfl
  exact (Option.some.inj (checked.symm.trans fixed))

end Solidity.Yul.World.DelegateSuccessPreparation
