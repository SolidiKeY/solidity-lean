import Solidity.Backend.Selection.StructuredExecution
import Solidity.Backend.Selection.MixedSelection
import Solidity.Backend.Selection.Premises

/-! Composition against one actual assembled program and its encoded bytes.
Decoder roundtrip and executable behavior remain separate proofs. -/
namespace Solidity.Backend.Selection

/-- Assemble already-proved component certificates for the same existing block. -/
def compose {ir : List Evm.Instr} {block : Block} {n m : Nat}
    (lowering : LoweringCertificate ir block) (shape : LabelExec.BlockShape block n m)
    (room : ExpansionRoom block n m) (out : Assembled Empty)
    (assembly : assemble 0 LabelExec.emptyLink (block.expand 0).1 = some out) :
    CompositionCertificate ir block n m where
  lowering := lowering
  control := ExecutionTrace.structuredCertificate block shape room
  assembled := out
  assembly := assembly
  roundtrip := decode_encode out.code

namespace CompositionCertificate

/-- Actual IR success executes the exact composed bytes, retaining every stack
bound. This does not infer execution from the decoder roundtrip equation. -/
theorem execute {ir : List Evm.Instr} {block : Block} {n m : Nat}
    (composition : CompositionCertificate ir block n m)
    (input output : Scalar.Stack) (caller : Evm.Machine)
    (height : input.length = n) (stack : caller.stack = irStack input)
    (actual : Evm.run ir caller = .ok { caller with stack := irStack output } 0) :
    ∃ count, ExecutionTrace.Safe (encode composition.assembled.code) count
      ⟨0,input⟩ ⟨size composition.assembled.code,output⟩ := by
  have structured : StructuredExec block input output :=
    (composition.lowering.success input output caller stack).mp actual
  have assembly : assemble 0 LabelExec.emptyLink
      ([] ++ (block.expand 0).1 ++ []) = some composition.assembled := by
    simpa only [List.nil_append, List.append_nil] using composition.assembly
  obtain ⟨count,run,bounds⟩ := composition.control.realize [] [] 0 composition.assembled
    assembly input output height structured
  have emitted : composition.assembled.code =
      LabelExec.emitPrefix (block.expand 0).1 (block.expand 0).1 :=
    (assemble_eq composition.assembly).2.1
  have trace : ExecutionTrace.Safe (encode composition.assembled.code) count ⟨0,input⟩
      ⟨size (LabelExec.emitPrefix (block.expand 0).1 (block.expand 0).1),output⟩ := by
    simpa only [ExecutionTrace.Safe, List.nil_append, List.append_nil] using And.intro run bounds
  rw [← emitted] at trace
  exact ⟨count,trace⟩

end CompositionCertificate

/-- The named Bridge agreement premise transports every finite supported run.
Reachability is required at entry and closed under actual byte steps. -/
theorem decoder_advance {bytes : List UInt8} {n : Nat}
    {bridgeStep : LabelExec.State → Option LabelExec.State}
    {bridgeRun : Nat → LabelExec.State → Option LabelExec.State}
    {reachable : LabelExec.State → Prop}
    (decoder : DecoderPremise bytes n bridgeStep bridgeRun reachable)
    (count : Nat) (state : LabelExec.State) (entry : reachable state) :
    bridgeRun count state = LabelExec.advance count bytes state := by
  induction count generalizing state with
  | zero => exact decoder.zero state
  | succ count ih =>
    rw [decoder.succ, LabelExec.advance, decoder.agrees state entry]
    cases step : LabelExec.step bytes state with
    | none => rfl
    | some next =>
      simp only [Option.bind_some]
      exact ih next (decoder.closed state next entry step)

namespace CompositionCertificate

/-- Concrete-byte behavior transported through G45.05-BR, not an assertion that
this lane has proved agreement for the actual Bridge implementation. -/
theorem execute_bridge {ir : List Evm.Instr} {block : Block} {n m : Nat}
    (composition : CompositionCertificate ir block n m)
    {bridgeStep : LabelExec.State → Option LabelExec.State}
    {bridgeRun : Nat → LabelExec.State → Option LabelExec.State}
    {reachable : LabelExec.State → Prop}
    (decoder : DecoderPremise (encode composition.assembled.code) n bridgeStep bridgeRun reachable)
    (input output : Scalar.Stack) (caller : Evm.Machine)
    (height : input.length = n) (stack : caller.stack = irStack input)
    (actual : Evm.run ir caller = .ok { caller with stack := irStack output } 0) :
    ∃ count, bridgeRun count ⟨0,input⟩ = some ⟨size composition.assembled.code,output⟩ ∧
      ∀ k, k ≤ count → ∃ reached, bridgeRun k ⟨0,input⟩ = some reached ∧ reached.stack.length ≤ 1024 := by
  obtain ⟨count,run,bounds⟩ := composition.execute input output caller height stack actual
  have entry : reachable ⟨0,input⟩ := decoder.entry input height
  refine ⟨count,?_,?_⟩
  · rw [decoder_advance decoder count _ entry]
    exact run
  · intro k within
    rw [decoder_advance decoder k _ entry]
    exact bounds k within

end CompositionCertificate

/-- Literal instruction items have no symbolic label references. -/
theorem refs_instructions (code : Program) : refs (code.map (Item.instr (L := Nat) (Lib := Empty))) = [] := by
  induction code with
  | nil => rfl
  | cons instruction rest ih =>
    simpa only [refs, List.map_cons, List.filterMap_cons, Item.ref?, Option.map_none] using ih

theorem tags_instructions (code : Program) : tags (code.map (Item.instr (L := Nat) (Lib := Empty))) = [] := by
  induction code with
  | nil => rfl
  | cons instruction rest ih =>
    simpa only [tags, List.map_cons, List.filterMap_cons, Item.tag?, Option.map_none] using ih

/-- Actual assembly is constructed from the published assembler theorem. -/
theorem scalar_assembly (code : Program) :
    (assemble 0 LabelExec.emptyLink (code.map (Item.instr (L := Nat) (Lib := Empty)))).isSome := by
  apply assemble_isSome LabelExec.emptyLink
  · rw [tags_instructions]; exact List.nodup_nil
  · intro label member
    rw [refs_instructions] at member
    exact False.elim (List.not_mem_nil member)
  · intro label member
    rw [refs_instructions] at member
    exact False.elim (List.not_mem_nil member)

/-- A concrete composition constructor for the proved mixed scalar selector.
No unproved lowering certificate is supplied by the caller. -/
def scalarComposition (ir : List Evm.Instr) {n m : Nat} (code : LabelExec.Code n m)
    (selected : compileScalar ir = some code.instructions) :
    CompositionCertificate ir (.code code.instructions) n m :=
  let result := assemble 0 LabelExec.emptyLink
    (code.instructions.map (Item.instr (L := Nat) (Lib := Empty)))
  let out := result.get (scalar_assembly code.instructions)
  compose (scalarLowering ir code.instructions selected) (.code code) True.intro out (Option.some_get _).symm

theorem scalarComposition_code (ir : List Evm.Instr) {n m : Nat} (code : LabelExec.Code n m)
    (selected : compileScalar ir = some code.instructions) :
    (scalarComposition ir code selected).assembled.code = code.instructions := by
  have emitted : (scalarComposition ir code selected).assembled.code =
      LabelExec.emitPrefix (code.instructions.map Item.instr) (code.instructions.map Item.instr) :=
    (assemble_eq (scalarComposition ir code selected).assembly).2.1
  exact emitted.trans (ExecutionTrace.emit_instructions _ _)

#print axioms compose
#print axioms CompositionCertificate.execute
#print axioms decoder_advance
#print axioms CompositionCertificate.execute_bridge
#print axioms refs_instructions
#print axioms tags_instructions
#print axioms scalar_assembly
#print axioms scalarComposition
#print axioms scalarComposition_code

end Solidity.Backend.Selection
