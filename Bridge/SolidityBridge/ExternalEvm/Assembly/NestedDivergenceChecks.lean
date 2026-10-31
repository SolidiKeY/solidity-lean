import SolidityBridge.ExternalEvm.Assembly.NestedDivergence
import SolidityBridge.ExternalEvm.Assembly.Linked
import SolidityBridge.ExternalEvm.Assembly.LayoutFacts

namespace Solidity.Evm.External.Assembly.NestedDivergenceChecks
open EvmYul EvmYul.EVM

def codeC : List Instr := [.push w[1]]
def codeB : List Instr := [.loop codeC []]
def codeA : List Instr := [.loop [] codeB]

def bytesC : List UInt8 := [0x5b] ++ push32 ⟨1, by decide⟩ ++ [0x5b]
def imageC : Image codeC 38 where
  bytes := bytesC
  size := 34
  span_eq := rfl
  emitted := by
    simp only [bytesC, codeC, emit.eq_def, emitInstr.eq_def, width]
    rfl
  length_eq := by decide +kernel
  fits := by decide
  destinations := by
    have hd : ∀ l : Label codeC, (address codeC 38 l).any
        (fun n => bytesC[n - 38]? == some 0x5b) = true := by decide +kernel
    intro l
    have hh := hd l
    cases ha : address codeC 38 l with
    | none => simp only [ha, Option.any_none, Bool.false_eq_true] at hh
    | some n =>
      refine ⟨n, rfl, ?_⟩
      simpa only [ha, Option.any_some, beq_iff_eq] using hh
  refs := []
  targets_eq := by
    simp only [codeC, targets.eq_def, instrTargets.eq_def, width]
    rfl
  validRefs := by decide +kernel

def bytesB : List UInt8 := [0x5b] ++ bytesC ++ [0x15] ++ push32 ⟨143, by decide⟩ ++ [0x57, 0x5b] ++ push32 ⟨37, by decide⟩ ++ [0x56, 0x5b]
def imageB : Image codeB 37 where
  bytes := bytesB
  size := 106
  span_eq := rfl
  emitted := by
    simp only [bytesB, bytesC, codeB, codeC, emit.eq_def, emitInstr.eq_def, span, width]
    rfl
  length_eq := by decide +kernel
  fits := by decide
  destinations := by
    have hd : ∀ l : Label codeB, (address codeB 37 l).any
        (fun n => bytesB[n - 37]? == some 0x5b) = true := by decide +kernel
    intro l
    have hh := hd l
    cases ha : address codeB 37 l with
    | none => simp only [ha, Option.any_none, Bool.false_eq_true] at hh
    | some n =>
      refine ⟨n, rfl, ?_⟩
      simpa only [ha, Option.any_some, beq_iff_eq] using hh
  refs := [37,143]
  targets_eq := by
    simp only [codeB, codeC, targets.eq_def, instrTargets.eq_def, span, width]
    rfl
  validRefs := by decide +kernel

def bytesA : List UInt8 := [0x5b, 0x5b, 0x15] ++ push32 ⟨178, by decide⟩ ++ [0x57] ++ bytesB ++ push32 ⟨0, by decide⟩ ++ [0x56, 0x5b]
def imageA : Image codeA 0 where
  bytes := bytesA
  size := 178
  span_eq := rfl
  emitted := by
    simp only [bytesA, bytesB, bytesC, codeA, codeB, codeC, emit.eq_def, emitInstr.eq_def, span, width]
    rfl
  length_eq := by decide +kernel
  fits := by decide
  destinations := by
    have hd : ∀ l : Label codeA, (address codeA 0 l).any
        (fun n => bytesA[n - 0]? == some 0x5b) = true := by decide +kernel
    intro l
    have hh := hd l
    cases ha : address codeA 0 l with
    | none => simp only [ha, Option.any_none, Bool.false_eq_true] at hh
    | some n =>
      refine ⟨n, rfl, ?_⟩
      simpa only [ha, Option.any_some, beq_iff_eq] using hh
  refs := [0,178,37,143]
  targets_eq := by
    simp only [codeA, codeB, codeC, targets.eq_def, instrTargets.eq_def, span, width]
    rfl
  validRefs := by decide +kernel

def frame : EVM.State :=
  {(default : EVM.State) with
    stack := [.ofNat 1]
    executionEnv := {(default : ExecutionEnv .EVM) with code := ⟨(bytesA ++ [0x00]).toArray⟩}}

theorem proof_some {P : Prop} (x : Option (PLift P)) (h : x.isSome) (p : P) : x = some ⟨p⟩ := by
  cases x with
  | none => cases h
  | some value => congr 1

theorem emptyPresent (base : Fin W) : (certifyCode (emptyLayout base) frame).isSome := by
  rw [certifyCode.eq_def]
  rfl

def emptyCert (base : Fin W) : DecodedCode frame (emptyLayout base) :=
  ((certifyCode (emptyLayout base) frame).get (emptyPresent base)).down

theorem emptyChecked (base : Fin W) : certifyCode (emptyLayout base) frame = some ⟨emptyCert base⟩ :=
  proof_some _ (emptyPresent base) _

theorem cPresent : (certifyCode imageC frame).isSome := by
  rw [certifyCode.eq_def]
  dsimp only [codeC, List.length_cons, List.length_nil, collectFin, bind, Option.bind]
  simp only [Fin.getElem_fin, List.getElem_cons_zero]
  simp only [certifySite.eq_def]
  decide +kernel

def certC : DecodedCode frame imageC := ((certifyCode imageC frame).get cPresent).down
theorem cChecked : certifyCode imageC frame = some ⟨certC⟩ := proof_some _ cPresent _

theorem assembleC : assembleChild codeC 38 = some imageC := by
  simpa only [assembleChild, codeC] using imageC.assemble_eq

theorem assembleB : assembleChild codeB 37 = some imageB := by
  simpa only [assembleChild, codeB] using imageB.assemble_eq

def hereB : WordAddress codeB 37 0 := ⟨by decide, ⟨37, by decide⟩, rfl⟩
def hereA : WordAddress codeA 0 0 := ⟨by decide, ⟨0, by decide⟩, rfl⟩
theorem addressB : readAddress [.loop codeC []] 37 0 = some hereB := rfl
theorem addressA : readAddress [.loop [] codeB] 0 0 = some hereA := rfl

def loopB : LoopSite (origin := 0) imageB imageC (emptyLayout ⟨108, by decide⟩) frame :=
  (checkLoop imageB imageC (emptyLayout ⟨108, by decide⟩) frame rfl).get (by decide +kernel)
def loopA : LoopSite (origin := 0) imageA (emptyLayout ⟨1, by decide⟩) imageB frame :=
  (checkLoop imageA (emptyLayout ⟨1, by decide⟩) imageB frame rfl).get (by decide +kernel)

theorem option_get {α : Type} (x : Option α) (h : x.isSome) : x = some (x.get h) := by
  cases x with
  | none => cases h
  | some value => rfl

theorem checkedB : checkLoop imageB imageC (emptyLayout ⟨108, by decide⟩) frame rfl = some loopB :=
  option_get _ _
theorem checkedA : checkLoop imageA (emptyLayout ⟨1, by decide⟩) imageB frame rfl = some loopA :=
  option_get _ _

theorem bPresent : (certifyCode imageB frame).isSome := by
  rw [certifyCode.eq_def]
  dsimp only [codeB, List.length_cons, List.length_nil, collectFin, bind, Option.bind]
  simp only [Fin.getElem_fin, List.getElem_cons_zero]
  simp only [certifySite.eq_def]
  rw [addressB]
  dsimp only [hereA, hereB, bind, Option.bind]
  rw [assembleC]
  dsimp only [hereA, hereB, bind, Option.bind]
  have empty : assembleChild [] (37 + imageC.size + 37) = some (emptyLayout ⟨108, by decide⟩) := rfl
  rw [empty]
  dsimp only [hereA, hereB, bind, Option.bind]
  rw [checkedB]
  dsimp only [hereA, hereB, bind, Option.bind]
  rw [cChecked]
  dsimp only [hereA, hereB, bind, Option.bind]
  rw [emptyChecked]
  rfl

def certB : DecodedCode frame imageB := ((certifyCode imageB frame).get bPresent).down
theorem bChecked : certifyCode imageB frame = some ⟨certB⟩ := proof_some _ bPresent _

theorem aPresent : (certifyCode imageA frame).isSome := by
  rw [certifyCode.eq_def]
  dsimp only [codeA, List.length_cons, List.length_nil, collectFin, bind, Option.bind]
  simp only [Fin.getElem_fin, List.getElem_cons_zero]
  simp only [certifySite.eq_def]
  rw [addressA]
  dsimp only [hereA, hereB, bind, Option.bind]
  have empty : assembleChild [] (0 + 1) = some (emptyLayout ⟨1, by decide⟩) := rfl
  rw [empty]
  dsimp only [hereA, hereB, bind, Option.bind]
  have bodyImage : assembleChild codeB (0 + (emptyLayout ⟨1, by decide⟩).size + 37) = some imageB := assembleB
  rw [bodyImage]
  dsimp only [hereA, hereB, bind, Option.bind]
  rw [checkedA]
  dsimp only [hereA, hereB, bind, Option.bind]
  rw [emptyChecked]
  dsimp only [hereA, hereB, bind, Option.bind]
  rw [bChecked]
  rfl

def certA : DecodedCode frame imageA := ((certifyCode imageA frame).get aPresent).down

def forever (m : Machine) : LoopDiverges codeC [] m := by
  apply LoopDiverges.forever
  intro n
  refine ⟨m, ?_⟩
  induction n with
  | zero => rfl
  | succ n ih => exact ih

def witness : BlockDiverges codeA {Machine.init with stack := [w[1]]} := by
  apply BlockDiverges.afterPrefix [] [] codeB [] rfl
  apply LoopDiverges.body ⟨1, by decide⟩ [] rfl rfl (by decide)
  exact BlockDiverges.afterPrefix [] codeC [] [] rfl (forever Machine.init)

theorem source_fault : run codeA {Machine.init with stack := [w[1]]} = .fault := witness.source_fault

theorem compiled_divergence : UnboundedPrefixes frame := by
  apply witness.compiled imageA frame certA frame
  exact ⟨by decide, rfl, rfl, rfl, rfl⟩

#guard (linkChecked codeA [] [0x00] frame).isSome
#guard (fetchedSteps 15 frame).toOption.map (fun t => (t.pc.toNat, words t.stack)) = some (37, [])

end Solidity.Evm.External.Assembly.NestedDivergenceChecks
