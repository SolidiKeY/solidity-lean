import Solidity.Lowering.StorageOps.SourceArrayWriteControls
open Solidity Solidity.Storage Solidity.Storage.Representation Solidity.TypeGraph
/-! Inhabited client of the actual Source/guarded target numeric write
composition. The finite example covers the header and three children only;
there is no global hash injectivity, eager recursive or world result. -/
namespace Solidity.Lowering.StorageOps.SourceArrayWriteNumericControls
open Solidity.Backend.StorageOps Solidity.Storage.Representation.Graph Solidity.Lowering.StorageOps
open SourceArrayIndexControls SourceArrayWriteControls
abbrev hash (_ : Pre) : Nat := 16
def locations : List Solidity.Storage.Loc := [.root 0,.data (.root 0) 0,.data (.root 0) 1,.data (.root 0) 2]
theorem run : FiniteRun 64 4 10 hash [.data 0] locations := by
  constructor
  · intro p; exact (by decide : 16<64)
  · decide
  · decide
  · decide
  · intro l member
    simp only [locations,List.mem_cons,List.not_mem_nil,or_false] at member
    rcases member with rfl | rfl | rfl | rfl <;> simp only [Solidity.Storage.Loc.Bounded] <;> decide
  · intro l member
    simp only [locations,List.mem_cons,List.not_mem_nil,or_false] at member
    rcases member with rfl | rfl | rfl | rfl <;> decide

def w83 : Semantics.Word := ⟨83,by decide⟩
def output := (TargetArrayWrite.writeAt old (ix 1) w83).getD old
theorem performed : TargetArrayWrite.writeAt old (ix 1) w83=some output := by rfl

def numeric : WordStore := realize 64 hash (fun _=>ClearDemands.zero) store locations

theorem transported : Transport 64 hash locations store numeric :=
  realize_transport (fun _=>ClearDemands.zero) store locations
    (fun _a ha _b hb eq=>run.word_inj ha hb eq)

theorem fitting : ∀ l ∈ locations, TargetOperations.KeysFit l := by
  intro l member
  simp only [locations,List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl <;> exact True.intro

theorem initialized : ∀ l (member : l∈locations), target.store.cells
    (TargetOperations.toSlot l (fitting l member))=TargetOperations.encodeWord (store l) := by
  intro l member
  simp only [locations,List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl <;> rfl

theorem header : Represented old [.length .nil] base store := by
  intro q member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  subst q
  exact SourceArrayIndexControls.before (.length .nil) (by exact List.mem_cons_self)

def certificate := SourceArrayWrite.complete_numeric run old output (ix 1) w83 performed
  [] base True.intro store numeric target target.stack header
  (by intro q member; cases member) (by exact ⟨by change 1<lmax; decide,True.intro⟩)
  (by intro q member; cases member) (by intro q member; cases member)
  transported (by decide) (by decide) fitting initialized
  env [] writable path .nil state rfl rfl (.int 2 (by decide)) 2 (by decide) rfl rfl
  SourceArrayWriteControls.payload 0 rfl rfl rfl rfl

def numericAfter := writeWord numeric ((.data base 1 : Solidity.Storage.Loc).word 64 hash) w83
theorem numeric_observations :
    ([ (numeric 0).val,(numeric 16).val,(numeric 17).val,(numeric 18).val ],
     [ (numericAfter 0).val,(numericAfter 16).val,(numericAfter 17).val,(numericAfter 18).val ]) =
    ([2,53,59,61],[2,53,83,61]) := by rfl

/-- info: 'Solidity.Lowering.StorageOps.SourceArrayWriteNumericControls.run' depends on axioms: [propext] -/
#guard_msgs (whitespace := lax) in #print axioms run
/-- info: 'Solidity.Lowering.StorageOps.SourceArrayWriteNumericControls.performed' depends on axioms: [propext, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms performed
/-- info: 'Solidity.Lowering.StorageOps.SourceArrayWriteNumericControls.transported' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms transported
/-- info: 'Solidity.Lowering.StorageOps.SourceArrayWriteNumericControls.fitting' depends on axioms: [propext] -/
#guard_msgs (whitespace := lax) in #print axioms fitting
/-- info: 'Solidity.Lowering.StorageOps.SourceArrayWriteNumericControls.initialized' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms initialized
/-- info: 'Solidity.Lowering.StorageOps.SourceArrayWriteNumericControls.header' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms header
/-- info: 'Solidity.Lowering.StorageOps.SourceArrayWriteNumericControls.certificate' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms certificate
/-- info: 'Solidity.Lowering.StorageOps.SourceArrayWriteNumericControls.numeric_observations' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms numeric_observations
end Solidity.Lowering.StorageOps.SourceArrayWriteNumericControls
