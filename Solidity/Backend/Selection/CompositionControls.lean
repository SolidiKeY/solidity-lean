import Solidity.Backend.Selection.Composition

/-! Concrete selector-to-byte composition, independent execution vectors and
nonvacuous decoder-premise controls. Identity adapters are not the Bridge. -/
namespace Solidity.Backend.Selection.CompositionControls

open LabelExec

def code : Code 1 2 where
  instructions := MixedControls.sampleCode
  shape := .cons (.mk 0 1 1 rfl rfl rfl)
    (.cons (.mk 0 1 2 rfl rfl rfl)
      (.cons (.mk 2 3 1 rfl rfl rfl)
        (.cons (.mk 2 2 2 rfl rfl rfl)
          (.cons (.mk 2 1 2 rfl rfl rfl) (.cons (.mk 1 0 2 rfl rfl rfl) (.nil 2))))))
  capacity := by decide

def composition : CompositionCertificate MixedControls.sampleIR (.code code.instructions) 1 2 :=
  scalarComposition MixedControls.sampleIR code MixedControls.sample_selected

theorem code_eq : composition.assembled.code = MixedControls.sampleCode :=
  scalarComposition_code MixedControls.sampleIR code MixedControls.sample_selected

theorem size_seventy : size composition.assembled.code = 70 := by rw [code_eq]; rfl

theorem source_run (caller : Evm.Machine) (stack : caller.stack = irStack [23]) :
    Evm.run MixedControls.sampleIR caller = .ok { caller with stack := irStack [5,23] } 0 := by
  rw [compileScalar_equation MixedControls.sampleIR MixedControls.sampleCode
    MixedControls.sample_selected [23] caller stack, MixedControls.sample_run]

/-- Full caller-frame equality from actual selected IR is composed into bytes. -/
theorem composed (caller : Evm.Machine) (stack : caller.stack = irStack [23]) :
    ∃ count, ExecutionTrace.Safe (encode composition.assembled.code) count
      ⟨0,[23]⟩ ⟨70,[5,23]⟩ := by
  obtain ⟨count,trace⟩ := composition.execute [23] [5,23] caller rfl stack (source_run caller stack)
  rw [size_seventy] at trace
  exact ⟨count,trace⟩

theorem inhabited : ∃ count, ExecutionTrace.Safe (encode composition.assembled.code) count
    ⟨0,[23]⟩ ⟨70,[5,23]⟩ :=
  composed { Evm.Machine.init with stack := irStack [23] } rfl

/-- Independent byte evaluation pins six actual instructions and their PC. -/
theorem actual_bytes : advance 6 (encode composition.assembled.code) ⟨0,[23]⟩ =
    some ⟨70,[5,23]⟩ := by rw [code_eq]; decide

theorem roundtrip : decode (encode composition.assembled.code) = some composition.assembled.code :=
  composition.roundtrip

theorem corrupted_tail : advance 6 (encode composition.assembled.code) ⟨0,[23]⟩ ≠
    some ⟨70,[5,24]⟩ := by rw [actual_bytes]; decide

def mutant : Program :=
  [Scalar.pushWord 6, Scalar.pushWord 17, .op (.DUP 1), .op (.SWAP 0), .op .DIV, .op .POP]

theorem mutant_run : advance 6 (encode mutant) ⟨0,[23]⟩ = some ⟨70,[6,23]⟩ := by decide

/-- A validly encoded changed literal is not the certified artifact. -/
theorem wrong_decoded_artifact : decode (encode mutant) ≠ some composition.assembled.code := by
  rw [decode_encode,code_eq]
  decide

/-- An inhabited local adapter used only to test the conditional transport. -/
def identityDecoder : DecoderPremise (encode composition.assembled.code) 1
    (LabelExec.step (encode composition.assembled.code))
    (fun count => advance count (encode composition.assembled.code)) (fun _ => True) where
  entry := by intro input height; exact True.intro
  closed := by intro start finish entry actual; exact True.intro
  agrees := by intro state entry; rfl
  zero := by intro state; rfl
  succ := by intro count state; rfl

theorem conditional_transport (caller : Evm.Machine) (stack : caller.stack = irStack [23]) :
    ∃ count, advance count (encode composition.assembled.code) ⟨0,[23]⟩ = some ⟨70,[5,23]⟩ ∧
      ∀ k, k ≤ count → ∃ reached, advance k (encode composition.assembled.code) ⟨0,[23]⟩ = some reached ∧
        reached.stack.length ≤ 1024 := by
  obtain ⟨count,actual,bounds⟩ := composition.execute_bridge identityDecoder [23] [5,23] caller
    rfl stack (source_run caller stack)
  rw [size_seventy] at actual
  exact ⟨count,actual,bounds⟩

theorem empty_reachable_rejected
    (bridgeStep : LabelExec.State → Option LabelExec.State)
    (bridgeRun : Nat → LabelExec.State → Option LabelExec.State) :
    ¬ DecoderPremise (encode composition.assembled.code) 1 bridgeStep bridgeRun (fun _ => False) := by
  intro decoder
  exact decoder.entry [23] rfl

theorem bad_step_rejected
    (bridgeRun : Nat → LabelExec.State → Option LabelExec.State)
    (reachable : LabelExec.State → Prop) :
    ¬ DecoderPremise (encode composition.assembled.code) 1 (fun _ => none) bridgeRun reachable := by
  intro decoder
  have equal : (none : Option LabelExec.State) = LabelExec.step (encode composition.assembled.code) ⟨0,[23]⟩ :=
    decoder.agrees _ (decoder.entry [23] rfl)
  rw [code_eq] at equal
  change (none : Option LabelExec.State) = some ⟨33,[5,23]⟩ at equal
  cases equal

#print axioms composition
#print axioms code_eq
#print axioms source_run
#print axioms composed
#print axioms inhabited
#print axioms actual_bytes
#print axioms roundtrip
#print axioms corrupted_tail
#print axioms mutant_run
#print axioms wrong_decoded_artifact
#print axioms identityDecoder
#print axioms conditional_transport
#print axioms empty_reachable_rejected
#print axioms bad_step_rejected

end Solidity.Backend.Selection.CompositionControls
