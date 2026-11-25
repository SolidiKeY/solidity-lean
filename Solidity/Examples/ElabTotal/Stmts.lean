import Solidity.Correctness.Elab.Total
import Solidity.Correctness.Elab.Congruence
import Solidity.Syntax.Elab.CallOutput

/-!
# Checks: the block's two equations

`elabStmtsP` is total (`elabStmtsPWith` at the knot's `elabStmtP`), so a
block of two statements unfolds by `elabStmtsP_cons` twice and
`elabStmtsP_nil` once, with no `native_decide`; the per-statement producer
`elabStmtP` stays opaque (partial). The elaborator's run on a concrete
two-statement block agrees with the unfolded form, state included.
(`#print axioms`: `propext` for the two equations, `propext, Quot.sound` for
the `runFrom` form; not pinned here, the pin inventory lies outside this module.)
-/

namespace Solidity.Examples.ElabTotal.Stmts

open Solidity

variable [FreshNames]

/-- Two statements: the head, the second, the empty rest, concatenated. -/
theorem elabStmtsP_two (C : Contract) (s₁ s₂ : RawStmt) :
    elabStmtsP C [s₁, s₂] = (do
      let P ← elabStmtP C s₁
      let Q ← (do
        let P' ← elabStmtP C s₂
        let Q' ← pure []
        pure (P' ++ Q'))
      pure (P ++ Q)) := by
  rw [elabStmtsP_cons, elabStmtsP_cons, elabStmtsP_nil]

/-- The same unfolding through `runFrom`, the form downstream proofs read. -/
theorem elabStmtsP_two_runFrom (C : Contract) (s₁ s₂ : RawStmt)
    (sc : ElabScope) (st : ECtx × Nat) :
    (elabStmtsP C [s₁, s₂]).runFrom sc st =
      (do
        let P ← elabStmtP C s₁
        let Q ← elabStmtP C s₂
        pure (P ++ Q ++ [])).runFrom sc st := by
  rw [elabStmtsP_cons, elabStmtsP_cons, elabStmtsP_nil]
  simp only [bind_pure_comp, map_pure, bind_pure, List.append_nil]

private def C0 : Contract := { vars := [] }

/-- `uint x = 1; x = 2;`. -/
private def s₁ : RawStmt := .decl (.named "uint") "x" (some (.num 1))
private def s₂ : RawStmt := .assign (.name "x") (.num 2)

/-- The run's statement count and final locals, or its error. -/
private def summary (x : ElabM (SProg C0)) : Option (Nat × List String × Nat) :=
  ((x.runFrom { funs := [] } ([], 1)).map fun (P, (Γ, k)) => (P.length, Γ.map (·.1), k)).toOption

-- The block elaborates, and agrees with its statements run one after the other.
#guard summary (elabStmtsP C0 [s₁, s₂]) == some (2, ["x"], 1)
#guard summary (elabStmtsP C0 [s₁, s₂]) ==
  summary (do let P ← elabStmtP C0 s₁; let Q ← elabStmtP C0 s₂; pure (P ++ Q))
#guard summary (elabStmtsP C0 []) == some (0, [], 1)

/-- The closed statement arms are exactly the solutions of their direct equations. -/
example (C : Contract) (rc : ElabRec C) (g : RawStmt → ElabM (SProg C)) :
    (g = elabStmt1With C {rc with elabStmt1 := g}) ↔ g = elabStmt1ClosedWith C rc := by
  constructor
  · exact elabStmt1ClosedWith_unique C rc g
  · intro h; subst g; exact elabStmt1ClosedWith_eq C rc

example (C : Contract) (rc : ElabRec C) (g : RawStmt → ElabM (SProg C)) :
    (g = elabStmtPWith C {rc with elabStmtP := g}) ↔ g = elabStmtPClosedWith C rc := by
  constructor
  · exact elabStmtPClosedWith_unique C rc g
  · intro h; subst g; exact elabStmtPClosedWith_eq C rc

/-- Even a failing seed cannot change either closed arm's equation. -/
example (C : Contract) (rc : ElabRec C) (err : String) :
    elabStmt1ClosedWith C {rc with elabStmt1 := fun _ => throw err} =
      elabStmt1With C {rc with elabStmt1 := elabStmt1ClosedWith C rc} := by
  exact (elabStmt1ClosedWith_independent C rc _).trans (elabStmt1ClosedWith_eq C rc)

example (C : Contract) (rc : ElabRec C) (err : String) :
    elabStmtPClosedWith C {rc with elabStmtP := fun _ => throw err} =
      elabStmtPWith C {rc with elabStmtP := elabStmtPClosedWith C rc} := by
  exact (elabStmtPClosedWith_independent C rc _).trans (elabStmtPClosedWith_eq C rc)

/-- Nested arrays retain both dimensions and advance the width-lookup path twice. -/
example (ws : List (String × Nat)) (E : Ty) (k : String) :
    rawTyW ws (.ref (.array (.ref (.array E)))) k =
      .array (.array (rawTyW ws E ((k ++ "[]") ++ "[]"))) := by
  rw [rawTyW_array, rawTyW_array]


-- The public ABI equations use only propext and Quot.sound;
-- adding choice, sorry, or another axiom breaks these checked guards.
/-- info: 'Solidity.abiSizeGen_eq' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms abiSizeGen_eq

/-- info: 'Solidity.abiSeqSizeGen_eq' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms abiSeqSizeGen_eq

/-- info: 'Solidity.abiTupleSizeGen_eq' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms abiTupleSizeGen_eq

/-- info: 'Solidity.abiWriteGen_eq' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms abiWriteGen_eq

/-- info: 'Solidity.abiSeqWriteGen_eq' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms abiSeqWriteGen_eq

/-- info: 'Solidity.abiTupleWriteGen_eq' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms abiTupleWriteGen_eq

/-- info: 'Solidity.abiReadGen_eq' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms abiReadGen_eq

/-- info: 'Solidity.abiSeqReadGen_eq' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms abiSeqReadGen_eq

/-- info: 'Solidity.abiSeqSizeGen_result_name' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms abiSeqSizeGen_result_name

end Solidity.Examples.ElabTotal.Stmts

/-- info: 'Solidity.ElabHoist.hoistFuel_stable' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms Solidity.ElabHoist.hoistFuel_stable

/-- info: 'Solidity.ElabHoist.hoistStructural_eq' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms Solidity.ElabHoist.hoistStructural_eq

/-- info: 'Solidity.ElabHoist.hoistStructural_unique' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms Solidity.ElabHoist.hoistStructural_unique

/-- info: 'Solidity.ElabHoist.hoist_structural_eq' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms Solidity.ElabHoist.hoist_structural_eq

/-- info: 'Solidity.ElabHoist.namedClosure_eq' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms Solidity.ElabHoist.namedClosure_eq

/-- info: 'Solidity.ElabHoist.namedStructural_named' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms Solidity.ElabHoist.namedStructural_named

/-- info: 'Solidity.ElabHoist.namedStructural_eq' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms Solidity.ElabHoist.namedStructural_eq

/-- info: 'Solidity.ElabHoist.namedStructural_unique' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms Solidity.ElabHoist.namedStructural_unique

/-- info: 'Solidity.ElabHoist.hoist_named_eq' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms Solidity.ElabHoist.hoist_named_eq

/-- info: 'Solidity.ElabCallArgsGood.hoistCallArgsWith_preserves' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms Solidity.ElabCallArgsGood.hoistCallArgsWith_preserves

/-- info: 'Solidity.ElabCallArgsGood.hoistCallArgsWith_nil' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms Solidity.ElabCallArgsGood.hoistCallArgsWith_nil

/-- info: 'Solidity.ElabCallHeight.height_pos' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms Solidity.ElabCallHeight.height_pos

/-- info: 'Solidity.ElabCallHeight.mem_height_le' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms Solidity.ElabCallHeight.mem_height_le

/-- info: 'Solidity.ElabCallHeight.named_request_lt' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms Solidity.ElabCallHeight.named_request_lt

/-- info: 'Solidity.ElabCallHeight.erc_expansion_lt' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms Solidity.ElabCallHeight.erc_expansion_lt

/-- info: 'Solidity.ElabCallHeight.recover_encoding_lt' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms Solidity.ElabCallHeight.recover_encoding_lt

/-- info: 'Solidity.ElabCallHeight.decode_request_lt' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms Solidity.ElabCallHeight.decode_request_lt

/-- info: 'Solidity.ElabCallHeight.signature_selector_lt' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms Solidity.ElabCallHeight.signature_selector_lt

/-- info: 'Solidity.ElabCallHeight.function_selector_lt' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms Solidity.ElabCallHeight.function_selector_lt

/-- info: 'Solidity.ElabCallHeight.foldConst_height_le' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms Solidity.ElabCallHeight.foldConst_height_le

/-- info: 'Solidity.ElabCallHeight.argument_lt_call' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms Solidity.ElabCallHeight.argument_lt_call

/-- info: 'Solidity.ElabCallHeight.selector_height_lt' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms Solidity.ElabCallHeight.selector_height_lt

/-- info: 'Solidity.ElabCallHeight.selector_args_height_lt' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms Solidity.ElabCallHeight.selector_args_height_lt

/-- info: 'Solidity.ElabCallHeight.unmark_height_le' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms Solidity.ElabCallHeight.unmark_height_le

/-- info: 'Solidity.ElabCallHeight.bytes_placeholder_height_le' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms Solidity.ElabCallHeight.bytes_placeholder_height_le

/-- info: 'Solidity.ElabCallHeight.encoding_inputs_lt' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms Solidity.ElabCallHeight.encoding_inputs_lt

/-- info: 'Solidity.ElabCallHeight.encoding_arg_height_lt' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms Solidity.ElabCallHeight.encoding_arg_height_lt

/-- info: 'Solidity.ElabCallHeight.selector_input_lt' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms Solidity.ElabCallHeight.selector_input_lt

/-- info: 'Solidity.ElabCallHeight.selector_encoding_inputs_lt' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms Solidity.ElabCallHeight.selector_encoding_inputs_lt

/-- info: 'Solidity.ElabCallHeight.selector_receiver_lt' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms Solidity.ElabCallHeight.selector_receiver_lt

/-- info: 'Solidity.ElabCallHeight.named_callee_decreases' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms Solidity.ElabCallHeight.named_callee_decreases

/-- info: 'Solidity.ElabCallHeight.prefix_input_lt' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms Solidity.ElabCallHeight.prefix_input_lt

/-- info: 'Solidity.ElabCallHeight.prefix_cast_lt' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms Solidity.ElabCallHeight.prefix_cast_lt

/-- info: 'Solidity.ElabCallArgsGood.captureExpr_shape' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms Solidity.ElabCallArgsGood.captureExpr_shape

/-- info: 'Solidity.ElabCallArgsGood.captureBefore_shape' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms Solidity.ElabCallArgsGood.captureBefore_shape

/-- info: 'Solidity.ElabCallArgsGood.ordinary_good' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms Solidity.ElabCallArgsGood.ordinary_good

/-- info: 'Solidity.ElabCallHeight.erc_output_height' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms Solidity.ElabCallHeight.erc_output_height

/-- info: 'Solidity.ElabCallHeight.pair_output_heights' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms Solidity.ElabCallHeight.pair_output_heights

/-- info: 'Solidity.ElabCallHeight.binop_output_height' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms Solidity.ElabCallHeight.binop_output_height

/-- info: 'Solidity.ElabCallHeight.captureExpr_height_bound' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms Solidity.ElabCallHeight.captureExpr_height_bound

/-- info: 'Solidity.ElabCallHeight.captureBefore_height_bound' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms Solidity.ElabCallHeight.captureBefore_height_bound

/-- info: 'Solidity.ElabCallHeight.pair_output_heights_of_hoist' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms Solidity.ElabCallHeight.pair_output_heights_of_hoist

/-- info: 'Solidity.ElabCallHeight.binop_output_height_of_hoist' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms Solidity.ElabCallHeight.binop_output_height_of_hoist

/-- info: 'Solidity.ElabCallHeight.args_output_heights' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms Solidity.ElabCallHeight.args_output_heights

/-- info: 'Solidity.ElabCallHeight.args_output_argument_lt' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms Solidity.ElabCallHeight.args_output_argument_lt

/-- info: 'Solidity.ElabCallHeight.narrowCapture_height_bound' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms Solidity.ElabCallHeight.narrowCapture_height_bound

/-- info: 'Solidity.ElabCallHeight.forceArg_height_bound' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms Solidity.ElabCallHeight.forceArg_height_bound

/-- info: 'Solidity.ElabCallHeight.unop_output_height' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms Solidity.ElabCallHeight.unop_output_height

/-- info: 'Solidity.ElabCallHeight.field_output_height' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms Solidity.ElabCallHeight.field_output_height

/-- info: 'Solidity.ElabCallHeight.index_output_height' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms Solidity.ElabCallHeight.index_output_height

/-- info: 'Solidity.ElabCallHeight.incDec_output_height' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms Solidity.ElabCallHeight.incDec_output_height

/-- info: 'Solidity.ElabCallHeight.newArr_output_height' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms Solidity.ElabCallHeight.newArr_output_height

/-- info: 'Solidity.ElabCallHeight.ternary_output_height' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms Solidity.ElabCallHeight.ternary_output_height

/-- info: 'Solidity.ElabCallHeight.binary_output_height' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms Solidity.ElabCallHeight.binary_output_height

/-- info: 'Solidity.ElabCallHeight.modular_output_height' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms Solidity.ElabCallHeight.modular_output_height

/-- info: 'Solidity.ElabCallHeight.assignment_output_height' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms Solidity.ElabCallHeight.assignment_output_height

/-- info: 'Solidity.ElabCallHeight.compound_assignment_output' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms Solidity.ElabCallHeight.compound_assignment_output

/-- info: 'Solidity.ElabCallHeight.named_output_height' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms Solidity.ElabCallHeight.named_output_height

/-- info: 'Solidity.ElabCallHeight.addressCapture_height_bound' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms Solidity.ElabCallHeight.addressCapture_height_bound

/-- info: 'Solidity.ElabCallHeight.enumCapture_output_height' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms Solidity.ElabCallHeight.enumCapture_output_height

/-- info: 'Solidity.ElabCallHeight.castCapture_output_height' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms Solidity.ElabCallHeight.castCapture_output_height

/-- info: 'Solidity.ElabCallHeight.structural_folded_output_height' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms Solidity.ElabCallHeight.structural_folded_output_height

/-- info: 'Solidity.ElabCallHeight.structural_output_height' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms Solidity.ElabCallHeight.structural_output_height

/-- info: 'Solidity.ElabCallHeight.hoistFuel_output_height' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms Solidity.ElabCallHeight.hoistFuel_output_height

/-- info: 'Solidity.ElabCallHeight.namedClosure_output_height' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms Solidity.ElabCallHeight.namedClosure_output_height

/-- info: 'Solidity.ElabCallHeight.namedStructural_output_height' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms Solidity.ElabCallHeight.namedStructural_output_height

/-- info: 'Solidity.ElabCallHeight.hoistFuel_output_height_on' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms Solidity.ElabCallHeight.hoistFuel_output_height_on

/-- info: 'Solidity.ElabCallHeight.namedClosure_output_height_on' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms Solidity.ElabCallHeight.namedClosure_output_height_on

/-- info: 'Solidity.ElabCallHeight.namedStructural_output_height_on' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms Solidity.ElabCallHeight.namedStructural_output_height_on

/-- info: 'Solidity.ElabCallHeight.height_nodes_before_down' depends on axioms: [propext] -/
#guard_msgs in
#print axioms Solidity.ElabCallHeight.height_nodes_before_down

/-- info: 'Solidity.ElabCallHeight.named_callee_before' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms Solidity.ElabCallHeight.named_callee_before

/-- info: 'Solidity.ElabCallHeight.namedStructural_output_height_before' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms Solidity.ElabCallHeight.namedStructural_output_height_before

/-- info: 'Solidity.ElabCallHeight.named_callee_closure_output_height' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms Solidity.ElabCallHeight.named_callee_closure_output_height

/-- info: 'Solidity.ElabCallHeight.decode_front_output_height' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms Solidity.ElabCallHeight.decode_front_output_height

/-- info: 'Solidity.ElabCallHeight.hash_output_height' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms Solidity.ElabCallHeight.hash_output_height

/-- info: 'Solidity.ElabCallHeight.internal_decode_output_height' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms Solidity.ElabCallHeight.internal_decode_output_height

/-- info: 'Solidity.ElabCallHeight.encode_output_height' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms Solidity.ElabCallHeight.encode_output_height

/-- info: 'Solidity.ElabControlProof.hash_result_name' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms Solidity.ElabControlProof.hash_result_name

/-- info: 'Solidity.ElabControlProof.decode_front_eq' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms Solidity.ElabControlProof.decode_front_eq

/-- info: 'Solidity.ElabControlProof.decode_internal_result_name' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms Solidity.ElabControlProof.decode_internal_result_name

/-- info: 'Solidity.ElabControlProof.encode_nested_result_name' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms Solidity.ElabControlProof.encode_nested_result_name

/-- info: 'Solidity.ElabControlProof.encode_result_name' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms Solidity.ElabControlProof.encode_result_name

/-- info: 'Solidity.ElabCallHeight.erc_args_output_height' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms Solidity.ElabCallHeight.erc_args_output_height

/-- info: 'Solidity.ElabCallHeight.decode_output_height' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms Solidity.ElabCallHeight.decode_output_height

/-- info: 'Solidity.ElabCallHeight.bytes_index_request_lt' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms Solidity.ElabCallHeight.bytes_index_request_lt

/-- info: 'Solidity.ElabCallHeight.bytes_index_output_height' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms Solidity.ElabCallHeight.bytes_index_output_height

/-- info: 'Solidity.ElabCallHeight.sliceAdd_height_le' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms Solidity.ElabCallHeight.sliceAdd_height_le

/-- info: 'Solidity.ElabCallHeight.slice_index_request_lt' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms Solidity.ElabCallHeight.slice_index_request_lt

/-- info: 'Solidity.ElabCallHeight.slice_index_output_height' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms Solidity.ElabCallHeight.slice_index_output_height

/-- info: 'Solidity.ElabCallHeight.array_output_height' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms Solidity.ElabCallHeight.array_output_height

/-- info: 'Solidity.ElabCallHeight.sliceCopy_output_height' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms Solidity.ElabCallHeight.sliceCopy_output_height

/-- info: 'Solidity.ElabCallHeight.bytes_literal_output_height' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms Solidity.ElabCallHeight.bytes_literal_output_height

/-- info: 'Solidity.ElabCallHeight.hoistCallArgs_argument_lt' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms Solidity.ElabCallHeight.hoistCallArgs_argument_lt

/-- info: 'Solidity.ElabCallHeight.inlineSliceOpen_cases' depends on axioms: [Quot.sound] -/
#guard_msgs in
#print axioms Solidity.ElabCallHeight.inlineSliceOpen_cases

/-- info: 'Solidity.ElabCallHeight.inlineSliceOpen_desc' does not depend on any axioms -/
#guard_msgs in
#print axioms Solidity.ElabCallHeight.inlineSliceOpen_desc

/-- info: 'Solidity.ElabCallHeight.sliceSub_height_le' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms Solidity.ElabCallHeight.sliceSub_height_le

/-- info: 'Solidity.ElabCallHeight.descriptor_len_le' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms Solidity.ElabCallHeight.descriptor_len_le

/-- info: 'Solidity.ElabCallHeight.descriptor_at_request_lt' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms Solidity.ElabCallHeight.descriptor_at_request_lt

/-- info: 'Solidity.ElabCallHeight.descriptor_length_request_lt' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms Solidity.ElabCallHeight.descriptor_length_request_lt

/-- info: 'Solidity.ElabCallHeight.descriptor_decode_request_lt' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms Solidity.ElabCallHeight.descriptor_decode_request_lt

/-- info: 'Solidity.ElabCallHeight.raw_at_request_lt' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms Solidity.ElabCallHeight.raw_at_request_lt

/-- info: 'Solidity.ElabCallHeight.raw_length_request_lt' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms Solidity.ElabCallHeight.raw_length_request_lt

/-- info: 'Solidity.ElabCallHeight.raw_decode_request_lt' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms Solidity.ElabCallHeight.raw_decode_request_lt

/-- info: 'Solidity.ElabControlProof.obs_lift' depends on axioms: [propext] -/
#guard_msgs in
#print axioms Solidity.ElabControlProof.obs_lift

/-- info: 'Solidity.ElabCallHeight.slice_length_output_height_of_request' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms Solidity.ElabCallHeight.slice_length_output_height_of_request

/-- info: 'Solidity.ElabCallHeight.slice_at_output_height_of_request' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms Solidity.ElabCallHeight.slice_at_output_height_of_request

/-- info: 'Solidity.ElabCallHeight.slice_decode_output_height_of_request' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms Solidity.ElabCallHeight.slice_decode_output_height_of_request

/-- info: 'Solidity.ElabCallHeight.descriptor_length_output_height' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms Solidity.ElabCallHeight.descriptor_length_output_height

/-- info: 'Solidity.ElabCallHeight.descriptor_at_output_height' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms Solidity.ElabCallHeight.descriptor_at_output_height

/-- info: 'Solidity.ElabCallHeight.descriptor_decode_output_height' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms Solidity.ElabCallHeight.descriptor_decode_output_height

/-- info: 'Solidity.ElabCallHeight.raw_length_output_height_of_bounds' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms Solidity.ElabCallHeight.raw_length_output_height_of_bounds

/-- info: 'Solidity.ElabCallHeight.raw_at_output_height_of_bounds' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms Solidity.ElabCallHeight.raw_at_output_height_of_bounds

/-- info: 'Solidity.ElabCallHeight.raw_decode_output_height_of_bounds' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms Solidity.ElabCallHeight.raw_decode_output_height_of_bounds

/-- info: 'Solidity.ElabCallHeight.slice_length_request_lt_of_raw_bounds' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms Solidity.ElabCallHeight.slice_length_request_lt_of_raw_bounds

/-- info: 'Solidity.ElabCallHeight.slice_at_request_lt_of_raw_bounds' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms Solidity.ElabCallHeight.slice_at_request_lt_of_raw_bounds

/-- info: 'Solidity.ElabCallHeight.slice_decode_request_lt_of_raw_bounds' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms Solidity.ElabCallHeight.slice_decode_request_lt_of_raw_bounds

/-- info: 'Solidity.ElabCallHeight.slice_length_output_height_of_raw_bounds' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms Solidity.ElabCallHeight.slice_length_output_height_of_raw_bounds

/-- info: 'Solidity.ElabCallHeight.slice_at_output_height_of_raw_bounds' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms Solidity.ElabCallHeight.slice_at_output_height_of_raw_bounds

/-- info: 'Solidity.ElabCallHeight.slice_decode_output_height_of_raw_bounds' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms Solidity.ElabCallHeight.slice_decode_output_height_of_raw_bounds

/-- info: 'Solidity.ElabCallHeight.call_output_height_of_raw_bounds' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms Solidity.ElabCallHeight.call_output_height_of_raw_bounds

/-- info: 'Solidity.ElabSliceOpen.openWith_atoms' depends on axioms: [propext] -/
#guard_msgs in
#print axioms Solidity.ElabSliceOpen.openWith_atoms

/-- info: 'Solidity.ElabSliceOpen.inlineSliceOpen_raw_eq' does not depend on any axioms -/
#guard_msgs in
#print axioms Solidity.ElabSliceOpen.inlineSliceOpen_raw_eq

/-- info: 'Solidity.ElabSliceOpen.inlineSliceOpen_raw_atoms' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms Solidity.ElabSliceOpen.inlineSliceOpen_raw_atoms

/-- info: 'Solidity.ElabCallHeight.boundAtom_height_le' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms Solidity.ElabCallHeight.boundAtom_height_le

/-- info: 'Solidity.ElabCallHeight.inlineSliceOpen_raw_height' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms Solidity.ElabCallHeight.inlineSliceOpen_raw_height

/-- info: 'Solidity.ElabSliceOpen.bindBound_eq' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms Solidity.ElabSliceOpen.bindBound_eq

/-- info: 'Solidity.ElabCallHeight.selector_height_lt_with_names' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms Solidity.ElabCallHeight.selector_height_lt_with_names

/-- info: 'Solidity.ElabCallHeight.selector_args_height_lt_with_names' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms Solidity.ElabCallHeight.selector_args_height_lt_with_names

/-- info: 'Solidity.ElabCallHeight.selector_input_lt_with_names' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms Solidity.ElabCallHeight.selector_input_lt_with_names

/-- info: 'Solidity.ElabCallHeight.selector_encoding_inputs_lt_with_names' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms Solidity.ElabCallHeight.selector_encoding_inputs_lt_with_names

/-- info: 'Solidity.ElabControlProof.memory_dispatch_result_name' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms Solidity.ElabControlProof.memory_dispatch_result_name

/-- info: 'Solidity.ElabCallHeight.memory_dispatch_output_height' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms Solidity.ElabCallHeight.memory_dispatch_output_height

/-- info: 'Solidity.ElabCallHeight.producers_memory_dispatch_output_height' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms Solidity.ElabCallHeight.producers_memory_dispatch_output_height

/-- info: 'Solidity.ElabCallHeight.callbacks_encode_output_height' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms Solidity.ElabCallHeight.callbacks_encode_output_height

/-- info: 'Solidity.ElabCallHeight.callbacks_call_output_height' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms Solidity.ElabCallHeight.callbacks_call_output_height

/-- info: 'Solidity.ElabCallHeight.callbacks_closed_call_output_height' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms Solidity.ElabCallHeight.callbacks_closed_call_output_height

/-- info: 'Solidity.ElabCallHeight.callbacks_output_height' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms Solidity.ElabCallHeight.callbacks_output_height

/-- info: 'Solidity.ElabCallHeight.callbacks_closed_output_height' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms Solidity.ElabCallHeight.callbacks_closed_output_height

/-- info: 'Solidity.ElabCallHeight.callbacks_fixed_output_height' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms Solidity.ElabCallHeight.callbacks_fixed_output_height

/-- info: 'Solidity.ElabHoist.structural_height_congr' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms Solidity.ElabHoist.structural_height_congr

/-- info: 'Solidity.ElabHoist.hoistFuel_congr_on' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms Solidity.ElabHoist.hoistFuel_congr_on

/-- info: 'Solidity.ElabHoist.namedClosure_congr_on' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms Solidity.ElabHoist.namedClosure_congr_on

/-- info: 'Solidity.ElabHoist.namedStructural_congr_on' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms Solidity.ElabHoist.namedStructural_congr_on

/-- info: 'Solidity.ElabCallHeight.callbacks_fixed_closure_output_height' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms Solidity.ElabCallHeight.callbacks_fixed_closure_output_height

/-- info: 'Solidity.elabKernel_helpers' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms Solidity.elabKernel_helpers

/-- info: 'Solidity.ElabCallHeight.callbacks_call_output_height_raw' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms Solidity.ElabCallHeight.callbacks_call_output_height_raw

/-! ## Callback agreement (`Correctness/Elab/Congruence.lean`)

A callback cut off the invocations a helper makes leaves the helper's result
unchanged: the shape in which the knot's well-founded definition uses them. -/

namespace Solidity.Examples.ElabTotal.Stmts

section Agreement

open Solidity Solidity.ElabAgree

variable [FreshNames] (C : Contract)

open Classical in
/-- `stmt`, failing off the statements of `ss`. -/
private noncomputable def onlyAt (stmt : RawStmt → ElabM (SProg C)) (ss : List RawStmt) :
    RawStmt → ElabM (SProg C) :=
  fun s => if s ∈ ss then stmt s else throw "cut"

omit [FreshNames] in
/-- A block does not see a cut of its statement callback off its own statements. -/
example (stmt : RawStmt → ElabM (SProg C)) (ss : List RawStmt) :
    elabStmtsPWith C (onlyAt C stmt ss) ss = elabStmtsPWith C stmt ss := by
  apply eq_of_agree
  intro sc
  apply elabStmtsPWith_agree
  intro s hs
  simp only [onlyAt, hs, ↓reduceIte]
  exact agree_refl _ _

/-- Callbacks that agree at a scope give the binary-operator, eager-argument
and call-argument helpers the same runs there, in either direction. -/
example (H K : RawExpr → ElabM (SProg C × RawExpr)) (stmt : RawStmt → ElabM (SProg C))
    (sc : ElabScope) (op : BinOp) (a b : RawExpr) (f : String)
    (h : ∀ e, Agree sc (H e) (K e)) :
    Agree sc (hoistBinopWith C K op a b) (hoistBinopWith C H op a b) ∧
    Agree sc (eagerArgsWith C H [a, b]) (eagerArgsWith C K [a, b]) ∧
    Agree sc (hoistCallArgsWith C H stmt f [a, b]) (hoistCallArgsWith C K stmt f [a, b]) :=
  ⟨(hoistBinopWith_agree C H K sc op a b (h a) (h b)).symm,
   eagerArgsWith_agree C H K sc [a, b] false [] fun e _ => h e,
   hoistCallArgsWith_agree C H K stmt stmt sc f [a, b] (fun e _ => h e)
     fun _ _ _ => agree_refl _ _⟩

/-- An inlined body reads the block callback only in the callee's scope: two
records whose blocks agree at every scope without deployment inline alike, and
an output of one is an output of the other. -/
example (rc rc' : ElabRec C) (sc : ElabScope) (f : String) (d : FunDecl)
    (ρ : List (String × String)) (scope : List (Name × FunDecl)) (k₀ : Nat) (Γ Γf : ECtx)
    (P : SProg C)
    (h : ∀ sc' ss, sc'.top = false → Agree sc' (rc.elabStmtsP ss) (rc'.elabStmtsP ss))
    (hP : Out sc (inlinedBody C rc f d ρ false false false scope k₀ Γ Γf) P) :
    Out sc (inlinedBody C rc' f d ρ false false false scope k₀ Γ Γf) P :=
  hP.of_agree ((inlinedBody_agree C rc rc' sc f d ρ false false false scope k₀ Γ Γf
    fun body _ _ => h _ body rfl).trans (agree_refl _ _))

end Agreement

end Solidity.Examples.ElabTotal.Stmts
