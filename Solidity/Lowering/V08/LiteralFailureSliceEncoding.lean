import Solidity.Lowering.V08.LiteralFailureCalldataPrefix
import Solidity.Lowering.V08.SliceFailureLowering

/-! Actual slice argument evaluation composed with the existing standard ABI
encoder. The published slice evaluator remains the bounds authority; no entry
validator, runtime encoder or alternate slice semantics is introduced. -/
namespace Solidity.Lowering.V08.LiteralFailureSliceEncoding
open Solidity Source
abbrev context (Γ : RCtx) := SliceFailureLowering.context (.bytes .calldata) Γ
abbrev caller {E : Env} {Γ} (off len : Nat) (start stop : Roadmap.Word)
 (older : Locals E.layout Γ) : Locals E.layout (context Γ) :=
 SliceFailureLowering.caller (τ:=.bytes .calldata) rfl off len start stop older

def arguments {E : Env} {Γ types} (tail : RArgs E (context Γ) types) :
 RArgs E (context Γ) (.bytes .calldata::types) :=
 .cons (SliceFailureLowering.expression (.bytes .calldata) rfl false) tail

theorem arguments_run {E : Env} {Γ types} {tail : RArgs E (context Γ) types}
 {values : Source.Vals E.layout types} (G : Glob E) (F : Fr) (extra off len : Nat)
 (start stop : Roadmap.Word) (ordered : start.val≤stop.val) (bounded : stop.val≤len)
 (older : Locals E.layout Γ) (state : St E)
 (lookups : LiteralFailureMixedExpression.LocalArgs (caller off len start stop older) tail values) :
 (evalArgs G F (types.length+extra+4) (arguments tail)).run (caller off len start stop older,state)=
 (.ok (.cons (.val (.cdRef rfl (off+start.val) (stop.val-start.val))) values.toR),
  (caller off len start stop older,state)) := by
 have head := SliceFailureLowering.accepted G F (types.length+extra+1)
  (.bytes .calldata) rfl rfl off len start stop ordered bounded older state
 have tailRun := LiteralFailureMixedExpression.arguments_run G F extra
  (caller off len start stop older) state lookups
 simp only [Nat.one_mul] at head
 simp only [arguments]
 rw [evalArgs]
 dsimp only [ExceptT.run] at head tailRun
 simp only [bind,pure,ExceptT.bind,ExceptT.pure,ExceptT.bindCont,ExceptT.run,
  ExceptT.mk,StateT.bind]
 rw [head]
 simp only [bind,pure,ExceptT.bindCont,StateT.bind]
 rw [tailRun]
 rfl

theorem expression_run {E : Env} {Γ types shapes} {tail : RArgs E (context Γ) types}
 {values : Source.Vals E.layout types} {encoded : AbiEntry.Vals shapes} {parts}
 (G : Glob E) (F : Fr) (extra off len : Nat) (start stop : Roadmap.Word)
 (ordered : start.val≤stop.val) (bounded : stop.val≤len)
 (older : Locals E.layout Γ) (state : St E)
 (lookups : LiteralFailureMixedExpression.LocalArgs (caller off len start stop older) tail values)
 (located : LiteralFailureCalldataPrefix.Located F state values encoded parts) :
 (evalE G F (types.length+extra+5) (.abiEncode .encode (arguments tail))).run
 (caller off len start stop older,state)=
 (.ok (.val (.memRef rfl state.heap.next)),
  (caller off len start stop older,SourceKeccak.afterLiteral state
   (AbiEntry.encodeArgs (.cons (.bytes ((F.cd.drop (off+start.val)).take (stop.val-start.val))) encoded)))) :=
 SourceAbi.execute G F (types.length+extra+4) false (arguments tail) _ _ _ state state state _ _
 (arguments_run G F extra off len start stop ordered bounded older state lookups)
 (LiteralFailureCalldataPrefix.encoding_run F _ _ state
  (.bytes (off+start.val) (stop.val-start.val) located))

theorem arguments_revert {E : Env} {Γ types} (G : Glob E) (F : Fr)
 (extra off len : Nat) (start stop : Roadmap.Word)
 (wrong : stop.val<start.val ∨ len<stop.val) (older : Locals E.layout Γ) (state : St E)
 (tail : RArgs E (context Γ) types) :
 (evalArgs G F (types.length+extra+4) (arguments tail)).run
 (caller off len start stop older,state)=
 (.error (.revert []),(caller off len start stop older,state)) := by
 have head := SliceFailureLowering.invalid G F (types.length+extra+1)
  (.bytes .calldata) rfl rfl off len start stop wrong older state
 simp only [arguments]
 rw [evalArgs]
 dsimp only [ExceptT.run] at head
 simp only [bind,pure,ExceptT.bind,ExceptT.bindCont,ExceptT.run,
  ExceptT.mk,StateT.bind,StateT.pure,head]

theorem expression_revert {E : Env} {Γ types} (G : Glob E) (F : Fr)
 (extra off len : Nat) (start stop : Roadmap.Word)
 (wrong : stop.val<start.val ∨ len<stop.val) (older : Locals E.layout Γ) (state : St E)
 (tail : RArgs E (context Γ) types) :
 (evalE G F (types.length+extra+5) (.abiEncode .encode (arguments tail))).run
 (caller off len start stop older,state)=
 (.error (.revert []),(caller off len start stop older,state)) := by
 have actual := arguments_revert G F extra off len start stop wrong older state tail
 dsimp only [ExceptT.run] at actual
 simp only [evalE,bind,pure,ExceptT.bind,ExceptT.bindCont,ExceptT.run,
  ExceptT.mk,StateT.bind,StateT.pure,actual]

end Solidity.Lowering.V08.LiteralFailureSliceEncoding
