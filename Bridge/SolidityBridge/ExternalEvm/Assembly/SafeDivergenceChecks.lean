import SolidityBridge.ExternalEvm.Assembly.NestedDivergenceChecks
import SolidityBridge.ExternalEvm.Assembly.SafeDivergence

namespace Solidity.Evm.External.Assembly.SafeDivergenceChecks
open EvmYul EvmYul.EVM
open NestedDivergenceChecks

def destinations : List UInt256 := ([0,1,37,38,72,108,143,178] : List Nat).map UInt256.ofNat

def labelsC : ScannedLabels codeC 38 destinations :=
  ((checkLabels codeC 38 destinations).get (by decide +kernel)).down
theorem labelsCChecked : checkLabels codeC 38 destinations = some ⟨labelsC⟩ :=
  proof_some _ (by decide +kernel) _

def labelsB : ScannedLabels codeB 37 destinations :=
  ((checkLabels codeB 37 destinations).get (by decide +kernel)).down
theorem labelsBChecked : checkLabels codeB 37 destinations = some ⟨labelsB⟩ :=
  proof_some _ (by decide +kernel) _

def labelsA : ScannedLabels codeA 0 destinations :=
  ((checkLabels codeA 0 destinations).get (by decide +kernel)).down
theorem labelsAChecked : checkLabels codeA 0 destinations = some ⟨labelsA⟩ :=
  proof_some _ (by decide +kernel) _

theorem empty1Present : (certifyScannedCode (emptyLayout ⟨1, by decide⟩) frame destinations).isSome := by
  rw [certifyScannedCode.eq_def]
  decide +kernel
def empty1 : ScannedCode frame destinations (emptyLayout ⟨1, by decide⟩) :=
  ((certifyScannedCode (emptyLayout ⟨1, by decide⟩) frame destinations).get empty1Present).down
theorem empty1Checked : certifyScannedCode (emptyLayout ⟨1, by decide⟩) frame destinations = some ⟨empty1⟩ :=
  proof_some _ empty1Present _

theorem empty108Present : (certifyScannedCode (emptyLayout ⟨108, by decide⟩) frame destinations).isSome := by
  rw [certifyScannedCode.eq_def]
  decide +kernel
def empty108 : ScannedCode frame destinations (emptyLayout ⟨108, by decide⟩) :=
  ((certifyScannedCode (emptyLayout ⟨108, by decide⟩) frame destinations).get empty108Present).down
theorem empty108Checked : certifyScannedCode (emptyLayout ⟨108, by decide⟩) frame destinations = some ⟨empty108⟩ :=
  proof_some _ empty108Present _

theorem cPresent : (certifyScannedCode imageC frame destinations).isSome := by
  rw [certifyScannedCode.eq_def, labelsCChecked]
  dsimp only [codeC, List.length_cons, List.length_nil, collectFin, bind, Option.bind]
  simp only [Fin.getElem_fin, List.getElem_cons_zero]
  simp only [certifyScannedSite.eq_def]
  decide +kernel

def safeC : ScannedCode frame destinations imageC :=
  ((certifyScannedCode imageC frame destinations).get cPresent).down
theorem cChecked : certifyScannedCode imageC frame destinations = some ⟨safeC⟩ := proof_some _ cPresent _

theorem bPresent : (certifyScannedCode imageB frame destinations).isSome := by
  rw [certifyScannedCode.eq_def, labelsBChecked]
  dsimp only [codeB, List.length_cons, List.length_nil, collectFin, bind, Option.bind]
  simp only [Fin.getElem_fin, List.getElem_cons_zero]
  simp only [certifyScannedSite.eq_def]
  rw [addressB]
  dsimp only [hereB, bind, Option.bind]
  rw [assembleC]
  dsimp only [bind, Option.bind]
  have empty : assembleChild [] (37 + imageC.size + 37) = some (emptyLayout ⟨108, by decide⟩) := rfl
  rw [empty]
  dsimp only [bind, Option.bind]
  rw [checkedB]
  dsimp only [bind, Option.bind]
  rw [cChecked]
  dsimp only [bind, Option.bind]
  rw [empty108Checked]
  rfl

def safeB : ScannedCode frame destinations imageB :=
  ((certifyScannedCode imageB frame destinations).get bPresent).down
theorem bChecked : certifyScannedCode imageB frame destinations = some ⟨safeB⟩ := proof_some _ bPresent _

theorem aPresent : (certifyScannedCode imageA frame destinations).isSome := by
  rw [certifyScannedCode.eq_def, labelsAChecked]
  dsimp only [codeA, List.length_cons, List.length_nil, collectFin, bind, Option.bind]
  simp only [Fin.getElem_fin, List.getElem_cons_zero]
  simp only [certifyScannedSite.eq_def]
  rw [addressA]
  dsimp only [hereA, bind, Option.bind]
  have empty : assembleChild [] (0 + 1) = some (emptyLayout ⟨1, by decide⟩) := rfl
  rw [empty]
  dsimp only [bind, Option.bind]
  have bodyImage : assembleChild codeB (0 + (emptyLayout ⟨1, by decide⟩).size + 37) = some imageB := assembleB
  rw [bodyImage]
  dsimp only [bind, Option.bind]
  rw [checkedA]
  dsimp only [bind, Option.bind]
  rw [empty1Checked]
  dsimp only [bind, Option.bind]
  rw [bChecked]
  rfl

def safeA : ScannedCode frame destinations imageA :=
  ((certifyScannedCode imageA frame destinations).get aPresent).down

def scanner : ScanResult frame.executionEnv.code (.ofNat 0) := ⟨destinations, by
  refine ScanPath.step _ .JUMPDEST ([1,37,38,72,108,143,178].map UInt256.ofNat) (by decide +kernel) ?_
  change ScanPath frame.executionEnv.code (.ofNat 1) ([1,37,38,72,108,143,178].map UInt256.ofNat)
  refine ScanPath.step _ .JUMPDEST ([37,38,72,108,143,178].map UInt256.ofNat) (by decide +kernel) ?_
  change ScanPath frame.executionEnv.code (.ofNat 2) ([37,38,72,108,143,178].map UInt256.ofNat)
  refine ScanPath.step _ .ISZERO ([37,38,72,108,143,178].map UInt256.ofNat) (by decide +kernel) ?_
  change ScanPath frame.executionEnv.code (.ofNat 3) ([37,38,72,108,143,178].map UInt256.ofNat)
  refine ScanPath.step _ (.Push .PUSH32) ([37,38,72,108,143,178].map UInt256.ofNat) (by decide +kernel) ?_
  change ScanPath frame.executionEnv.code (.ofNat 36) ([37,38,72,108,143,178].map UInt256.ofNat)
  refine ScanPath.step _ .JUMPI ([37,38,72,108,143,178].map UInt256.ofNat) (by decide +kernel) ?_
  change ScanPath frame.executionEnv.code (.ofNat 37) ([37,38,72,108,143,178].map UInt256.ofNat)
  refine ScanPath.step _ .JUMPDEST ([38,72,108,143,178].map UInt256.ofNat) (by decide +kernel) ?_
  change ScanPath frame.executionEnv.code (.ofNat 38) ([38,72,108,143,178].map UInt256.ofNat)
  refine ScanPath.step _ .JUMPDEST ([72,108,143,178].map UInt256.ofNat) (by decide +kernel) ?_
  change ScanPath frame.executionEnv.code (.ofNat 39) ([72,108,143,178].map UInt256.ofNat)
  refine ScanPath.step _ (.Push .PUSH32) ([72,108,143,178].map UInt256.ofNat) (by decide +kernel) ?_
  change ScanPath frame.executionEnv.code (.ofNat 72) ([72,108,143,178].map UInt256.ofNat)
  refine ScanPath.step _ .JUMPDEST ([108,143,178].map UInt256.ofNat) (by decide +kernel) ?_
  change ScanPath frame.executionEnv.code (.ofNat 73) ([108,143,178].map UInt256.ofNat)
  refine ScanPath.step _ .ISZERO ([108,143,178].map UInt256.ofNat) (by decide +kernel) ?_
  change ScanPath frame.executionEnv.code (.ofNat 74) ([108,143,178].map UInt256.ofNat)
  refine ScanPath.step _ (.Push .PUSH32) ([108,143,178].map UInt256.ofNat) (by decide +kernel) ?_
  change ScanPath frame.executionEnv.code (.ofNat 107) ([108,143,178].map UInt256.ofNat)
  refine ScanPath.step _ .JUMPI ([108,143,178].map UInt256.ofNat) (by decide +kernel) ?_
  change ScanPath frame.executionEnv.code (.ofNat 108) ([108,143,178].map UInt256.ofNat)
  refine ScanPath.step _ .JUMPDEST ([143,178].map UInt256.ofNat) (by decide +kernel) ?_
  change ScanPath frame.executionEnv.code (.ofNat 109) ([143,178].map UInt256.ofNat)
  refine ScanPath.step _ (.Push .PUSH32) ([143,178].map UInt256.ofNat) (by decide +kernel) ?_
  change ScanPath frame.executionEnv.code (.ofNat 142) ([143,178].map UInt256.ofNat)
  refine ScanPath.step _ .JUMP ([143,178].map UInt256.ofNat) (by decide +kernel) ?_
  change ScanPath frame.executionEnv.code (.ofNat 143) ([143,178].map UInt256.ofNat)
  refine ScanPath.step _ .JUMPDEST ([178].map UInt256.ofNat) (by decide +kernel) ?_
  change ScanPath frame.executionEnv.code (.ofNat 144) ([178].map UInt256.ofNat)
  refine ScanPath.step _ (.Push .PUSH32) ([178].map UInt256.ofNat) (by decide +kernel) ?_
  change ScanPath frame.executionEnv.code (.ofNat 177) ([178].map UInt256.ofNat)
  refine ScanPath.step _ .JUMP ([178].map UInt256.ofNat) (by decide +kernel) ?_
  change ScanPath frame.executionEnv.code (.ofNat 178) ([178].map UInt256.ofNat)
  refine ScanPath.step _ .JUMPDEST ([].map UInt256.ofNat) (by decide +kernel) ?_
  change ScanPath frame.executionEnv.code (.ofNat 179) ([].map UInt256.ofNat)
  refine ScanPath.step _ .STOP ([].map UInt256.ofNat) (by decide +kernel) ?_
  change ScanPath frame.executionEnv.code (.ofNat 180) ([].map UInt256.ofNat)
  exact ScanPath.stop _ (by decide +kernel)⟩

def program : LinkedProgram codeA where
  base := 0
  frame := frame
  checked := ⟨imageA, by unfold Placed; decide +kernel, safeA.decoded⟩
  scanner := scanner
  scanned := safeA
  labels := safeA.labels
  refs := by
    intro n hn
    change n ∈ [0,178,37,143] at hn
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hn
    rcases hn with rfl | rfl | rfl | rfl
    all_goals exact List.mem_map_of_mem (f := UInt256.ofNat) (by decide)

/-- An automatically generated, recursively scanned linked certificate
inhabits the general safe nested-divergence theorem. -/
theorem compiled_safe_divergence : SafeUnboundedPrefixes program.scanner.destinations frame := by
  apply witness.safe_compiled imageA frame destinations safeA frame
  exact ⟨by decide, rfl, rfl, rfl, rfl⟩

-- A finite completed outer turn can precede entry into the infinite inner loop.
def laterCode : List Instr := [.loop [] [.jumpi 1, .loop codeC []]]
def laterInput := {Machine.init with stack := [w[1], w[1], w[1], w[0]]}

def laterWitness : BlockDiverges laterCode laterInput := by
  apply BlockDiverges.afterPrefix [] [] [.jumpi 1, .loop codeC []] [] rfl
  apply LoopDiverges.afterTurns 1 (mid := {Machine.init with stack := [w[1], w[0]]}) rfl
  apply LoopDiverges.body ⟨1, by decide⟩ [w[0]] rfl rfl (by decide)
  exact BlockDiverges.afterPrefix [.jumpi 1] codeC [] [] rfl (forever Machine.init)

theorem later_source_fault : run laterCode laterInput = .fault := laterWitness.source_fault
private def laterTarget := linkChecked laterCode [] [0x00]
  {(default : EVM.State) with stack := [.ofNat 1, .ofNat 1, .ofNat 1, .ofNat 0]}
#guard laterTarget.isSome
#guard (laterTarget.bind (fun p => (fetchedSteps 19 p.frame).toOption.map
  (fun t => (t.pc.toNat, words t.stack)))) = some (72, [])

end Solidity.Evm.External.Assembly.SafeDivergenceChecks

/-- info: 'Solidity.Evm.External.Assembly.SafeDivergenceChecks.compiled_safe_divergence' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in #print axioms Solidity.Evm.External.Assembly.SafeDivergenceChecks.compiled_safe_divergence
