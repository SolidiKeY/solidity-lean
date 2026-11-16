import Solidity.Lowering.Readonly.SourceStatementParts.Part1
import Solidity.Lowering.Readonly.SourceStatementParts.Part2
import Solidity.Lowering.Readonly.SourceStatementParts.Part3
import Solidity.Lowering.Readonly.SourceStatementParts.Part4
import Solidity.Lowering.Readonly.SourceKnownAllHistories

namespace Solidity.Lowering.Readonly.SourceHistory
open Solidity.Source
theorem execS_succ {E : Env} (G : Glob E) (F : Fr) (fuel : Nat) (_history : At G fuel) (nps : Nat) (ph : Option (Ph E)) {R : List STy} {M : Bool} {k : SCtx} {Γ Γ' : RCtx} (s : RStmt E R M k Γ Γ') (locals : Locals E.layout Γ) :
    Effect F.static (execS G F (fuel+1) nps ph s locals) := by
  cases s
  case «expr» => exact execS_expr_succ G F fuel _history nps ph _ _
  case «placeholder» => exact execS_placeholder_succ G F fuel _history nps ph _ _
  case «declVar» => exact execS_declVar_succ G F fuel _history nps ph _ _
  case «declInit» => exact execS_declInit_succ G F fuel _history nps ph _ _ _
  case «block» => exact execS_block_succ G F fuel _history nps ph _ _
  case «ifThen» => exact execS_ifThen_succ G F fuel _history nps ph _ _ _
  case «ifElse» => exact execS_ifElse_succ G F fuel _history nps ph _ _ _ _
  case «whileLoop» => exact execS_whileLoop_succ G F fuel _history nps ph _ _ _
  case «doWhile» => exact execS_doWhile_succ G F fuel _history nps ph _ _ _
  case «forLoop» => exact execS_forLoop_succ G F fuel _history nps ph _ _ _ _ _
  case «skip» => exact execS_skip_succ G F fuel _history nps ph  _
  case «brk» => exact execS_brk_succ G F fuel _history nps ph  _
  case «cont» => exact execS_cont_succ G F fuel _history nps ph  _
  case «ret» => exact execS_ret_succ G F fuel _history nps ph _ _
  case «retVal» => exact execS_retVal_succ G F fuel _history nps ph _ _ _ _
  case «retTuple» => exact execS_retTuple_succ G F fuel _history nps ph _ _
  case «emit» => exact execS_emit_succ G F fuel _history nps ph _ _ _ _
  case «revertError» => exact execS_revertError_succ G F fuel _history nps ph _ _ _ _
  case «rethrow» => exact execS_rethrow_succ G F fuel _history nps ph _ _
  case «declTuple» => exact execS_declTuple_succ G F fuel _history nps ph _ _ _ _
  case «tryCall» => exact execS_tryCall_succ G F fuel _history nps ph _ _ _ _ _ _ _ _
  case «tryLibrary» => exact (all_known_at G (fuel+1)).execS true F nps ph _ _
end Solidity.Lowering.Readonly.SourceHistory
