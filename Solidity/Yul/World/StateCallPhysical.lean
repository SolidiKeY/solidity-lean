import Solidity.Yul.World.StateCallRuntime

/-! Explicit one-field physical input for the actual typed bool write.
The selected slot/field is a declared consumer layout input, not solc layout
adequacy. Padding and owned byte journals remain in their VY2 carriers. -/
namespace Solidity.Yul.World.StateCallPhysical
open Solidity.Source
open Solidity.Roadmap (Word Bytes Outcome)
open Solidity.Yul.Views
open Solidity.Yul.World.PhysicalCompletion
open Solidity.Yul.World.StateCall

def flag : ScalarPath env.layout (env.lay CallerFrameChecks.receiver) :=
  ⟨flagPath,7,boolField,boolCodec _,.bool⟩
def registry (_ : Roadmap.Address) : List (ScalarPath env.layout (env.lay CallerFrameChecks.receiver)) := [flag]
def request : PackedSlotRequest := ⟨false,CallerFrameChecks.receiver,7,0xaabbcc01⟩
def encodingPrefix : BoolEncodingJournal := boolEncodingWrite boolEncodingInitial
  (ownedByteKey false CallerFrameChecks.receiver flag,⟨⟨2,by decide⟩,by decide⟩)
def prepared := prepareRepresentedSlot (E:=env) registry registry request encodingPrefix

theorem ready : prepared.isSome := by decide
def plan : RepresentedSlotPlan (E:=env) registry registry request encodingPrefix := prepared.get ready

theorem preserve_true {f : Field} (c : ScalarCodec env.layout (env.cellTy flagPath) f)
    (s : Source.Storage env.layout (env.lay CallerFrameChecks.receiver)) :
    preserveScalarWrite flagPath c (.bool true) s=s.write flagPath (.bool true) := by
  unfold preserveScalarWrite
  split
  · rename_i same
    obtain ⟨old,read,encoded⟩ := Option.map_eq_some_iff.mp same
    have value : old=(.bool true : Source.Val env.layout (env.cellTy flagPath)) := c.encode_injective encoded
    rw [value] at read
    have cell : s.cell flagPath=some (.bool true) := by
      cases found : s.cell flagPath with
      | none => simp only [Source.Storage.read,found] at read; cases read
      | some x => simpa only [Source.Storage.read,found] using read
    cases s with
    | mk cells =>
      simp only [Source.Storage.write,Source.Storage.set,Source.Storage.mk.injEq]
      funext q
      by_cases samePath : q=flagPath
      · subst q; simpa only [Source.Storage.cell,dif_pos] using cell
      · simp only [dif_neg samePath]
  · rfl

theorem source_op : plan.packed.sourceOp=writeOp CallerFrameChecks.receiver := by
  change (Source.Op.account CallerFrameChecks.receiver (fun ac=>{ac with storage:=preserveScalarWrite flagPath (representedPath flag canonicalTrueByte).codec (.bool true) ac.storage}))=_
  apply congrArg (Source.Op.account CallerFrameChecks.receiver)
  funext ac
  rw [preserve_true]
  rfl

theorem complement : plan.packed.residualUpdate=(complementKey false CallerFrameChecks.receiver 7,0xaabbcc00) := rfl

theorem represented_bytes : (requestEncoding (E:=env) registry registry request encodingPrefix).cells
    (ownedByteKey false CallerFrameChecks.receiver flag)=canonicalTrueByte ∧
    (requestEncoding (E:=env) registry registry request encodingPrefix).journal.length=2 ∧
    encodingPrefix.journal.length=1 := ⟨rfl,rfl,rfl⟩

theorem step_exact {Γ} (s : EMState env Γ) (r : ResidualJournal complementCarrierOwnership)
    (o : ObservedEffects env.layout env.lay env.lay) (same : o.effects.execution=s.2.ex) :
    (PhysicalSlotPort.step registry registry request encodingPrefix ReturningCall.child plan s r o same rfl).1=
      (((.ok (),changed s CallerFrameChecks.receiver),residualWrite r plan.packed.residualUpdate),
        requestEncoding (E:=env) registry registry request encodingPrefix) := by
  unfold PhysicalSlotPort.step
  rw [representedSourceStep_nonstatic _ _ _ _ rfl,source_op]
  rfl

theorem full_word {Γ} (s : EMState env Γ) (r : ResidualJournal complementCarrierOwnership)
    (o : ObservedEffects env.layout env.lay env.lay) (same : o.effects.execution=s.2.ex) :
    let result:=PhysicalSlotPort.step registry registry request encodingPrefix ReturningCall.child plan s r o same rfl
    reencodePersistentSlot (representedBanks (E:=env) registry false result.1.2)
      ⟨result.2.effects.execution,result.1.1.2⟩ CallerFrameChecks.receiver 7=some request.raw :=
  PhysicalSlotPort.persistent_word ReturningCall.child plan s r o same rfl rfl rfl (by simp only [registry,finiteSeparated,List.pairwise_singleton])

theorem source_reencode {Γ} (s : EMState env Γ) (r : ResidualJournal complementCarrierOwnership)
    (o : ObservedEffects env.layout env.lay env.lay) (same : o.effects.execution=s.2.ex) :
    reencodePersistentSlot (representedBanks (E:=env) registry false (requestEncoding (E:=env) registry registry request encodingPrefix))
      ⟨(changed s CallerFrameChecks.receiver).2.ex,residualWrite r plan.packed.residualUpdate⟩
      CallerFrameChecks.receiver 7=some request.raw := by
  have actual:=full_word s r o same
  unfold PhysicalSlotPort.step at actual
  rw [representedSourceStep_nonstatic _ _ _ _ rfl,source_op] at actual
  exact actual

theorem complement_preserved (r : ResidualJournal complementCarrierOwnership)
    (padding : r.cells (complementKey false CallerFrameChecks.receiver 7)=0xaabbcc00) :
    (residualWrite r plan.packed.residualUpdate).cells=r.cells := by
  rw [complement]
  change residualSave r.cells (complementKey false CallerFrameChecks.receiver 7) (0xaabbcc00 : Roadmap.Word)=r.cells
  funext k
  unfold residualSave
  split
  · rename_i same
    subst k
    exact padding.symm
  · rfl

end Solidity.Yul.World.StateCallPhysical
