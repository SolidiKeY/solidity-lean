import Solidity.Lowering.Readonly.SourceExpressionParts.Part1
import Solidity.Lowering.Readonly.SourceExpressionParts.Part2
import Solidity.Lowering.Readonly.SourceExpressionParts.Part3
import Solidity.Lowering.Readonly.SourceExpressionParts.Part4
import Solidity.Lowering.Readonly.SourceExpressionParts.Part5
import Solidity.Lowering.Readonly.SourceExpressionParts.Part6

namespace Solidity.Lowering.Readonly.SourceHistory
open Solidity.Source
theorem evalE_succ {E : Env} (G : Glob E) (F : Fr) (fuel : Nat) (_history : At G fuel) {Γ : RCtx} {τ : STy} (e : RExpr E Γ τ) :
    Effect F.static (evalE G F (fuel+1) e) := by
  cases e
  case «const» => exact evalE_const_succ G F fuel _history _
  case «bytesLit» => exact evalE_bytesLit_succ G F fuel _history _ _
  case «addressLit» => exact evalE_addressLit_succ G F fuel _history _
  case «bool» => exact evalE_bool_succ G F fuel _history _
  case «str» => exact evalE_str_succ G F fuel _history _
  case «local» => exact evalE_local_succ G F fuel _history _
  case «state» => exact evalE_state_succ G F fuel _history _ _
  case «this» => exact evalE_this_succ G F fuel _history _
  case «tuple» => exact evalE_tuple_succ G F fuel _history _
  case «conv» => exact evalE_conv_succ G F fuel _history _ _
  case «convExplicit» => exact evalE_convExplicit_succ G F fuel _history _ _
  case «unary» => exact evalE_unary_succ G F fuel _history _ _
  case «incDec» => exact evalE_incDec_succ G F fuel _history _ _ _
  case «delete» => exact evalE_delete_succ G F fuel _history _
  case «binary» => exact evalE_binary_succ G F fuel _history _ _ _
  case «compare» => exact evalE_compare_succ G F fuel _history _ _ _
  case «compareConst» => exact evalE_compareConst_succ G F fuel _history _ _ _
  case «shiftLike» => exact evalE_shiftLike_succ G F fuel _history _ _ _ _
  case «cond» => exact evalE_cond_succ G F fuel _history _ _ _
  case «assign» => exact evalE_assign_succ G F fuel _history _ _
  case «compound» => exact evalE_compound_succ G F fuel _history _ _ _ _
  case «indexArray» => exact evalE_indexArray_succ G F fuel _history _ _ _
  case «indexMapping» => exact evalE_indexMapping_succ G F fuel _history _ _
  case «indexBytes» => exact evalE_indexBytes_succ G F fuel _history _ _ _
  case «length» => exact evalE_length_succ G F fuel _history _ _
  case «payable» => exact evalE_payable_succ G F fuel _history _
  case «call» => exact evalE_call_succ G F fuel _history _ _ _
  case «magic» => exact evalE_magic_succ G F fuel _history _ _ _
  case «balance» => exact evalE_balance_succ G F fuel _history _
  case «builtin» => exact evalE_builtin_succ G F fuel _history _ _ _
  case «member» => exact evalE_member_succ G F fuel _history _ _ _
  case «structNew» => exact evalE_structNew_succ G F fuel _history _ _
  case «extCall» => exact evalE_extCall_succ G F fuel _history _ _ _ _ _
  case «transfer» => exact evalE_transfer_succ G F fuel _history _ _
  case «send» => exact evalE_send_succ G F fuel _history _ _
  case «abiEncode» => exact evalE_abiEncode_succ G F fuel _history _ _
  case «assignCopy» => exact evalE_assignCopy_succ G F fuel _history _ _ _
  case «abiDecode» => exact evalE_abiDecode_succ G F fuel _history _ _ _
  case «slice» => exact evalE_slice_succ G F fuel _history _ _ _ _ _ _ _
  case «inlineArray» => exact evalE_inlineArray_succ G F fuel _history _ _
  case «newArray» => exact evalE_newArray_succ G F fuel _history _ _ _
end Solidity.Lowering.Readonly.SourceHistory
