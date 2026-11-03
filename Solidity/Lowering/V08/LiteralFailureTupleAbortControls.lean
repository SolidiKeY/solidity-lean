import Solidity.Lowering.V08.LiteralFailureTupleAbort
import Solidity.Lowering.V08.LiteralFailureReturnSlotsControls
namespace Solidity.Lowering.V08.LiteralFailureTupleAbortControls
open Solidity Source Backend
open LiteralFailureTupleAbort
open SourceCustomErrorControls (E frame global)
open LiteralFailureDynamicReturnControls (state saved live)

def types : RCtx := [.int IntTy.u256,.int IntTy.u256,.int IntTy.u256]
def parameters : RCtx := [.int IntTy.u256,.int IntTy.u256,.bytes .memory,.bool]
def word (n : Nat) (h : n<2^256) : Source.Val E.layout (.int IntTy.u256) :=
 SourceEnvironment.sourceWord ⟨n,h⟩
def locals (marker : Roadmap.Word) : Locals E.layout parameters :=
 .cons (SourceEnvironment.sourceWord marker) (.cons (word 0 (by decide +kernel))
  (.cons (.memRef rfl 0) (.cons (.bool true) .nil)))
def old : Source.Vals E.layout types :=
 .cons (word 7 (by decide +kernel)) (.cons (word 11 (by decide +kernel))
  (.cons (word 13 (by decide +kernel)) .nil))
def changed : Locals E.layout (types.reverseAux parameters) :=
 old.onto (locals ⟨13,by decide +kernel⟩)
def arguments : RConvArgs E (types.reverseAux parameters) types :=
 .cons (.assign (.local (.there (.there (.there .here)))) (.local .here)) rfl
  (.cons (.binary .div (.local .here) (.local (.there (.there (.there (.there .here)))))) rfl
   (.cons (.assign (.local (.there (.there (.there .here)))) (.local (.there .here))) rfl .nil))
def statement : RStmt E types false .body (types.reverseAux parameters) (types.reverseAux parameters) :=
 .retTuple arguments

theorem arguments_panic (p : Roadmap.Pipeline) (static checked : Bool)
 (marker : Roadmap.Word) (bytes : Roadmap.Bytes) :
 (evalConvArgs (global p) {frame with static:=static,checked:=checked} 12 arguments).run
 (old.onto (locals marker),state bytes [])=
 (.error (.revert (panicData .divZero)),(changed,state bytes [])) := by
 cases p <;> rfl

theorem statement_panic (p : Roadmap.Pipeline) (static checked : Bool)
 (marker : Roadmap.Word) (bytes : Roadmap.Bytes) :
 (execS (global p) {frame with static:=static,checked:=checked} 13 4 none statement
 (old.onto (locals marker))).run (L0 E,state bytes [])=
 (.error (.revert (panicData .divZero)),(L0 E,state bytes [])) :=
 argument_error (global p) {frame with static:=static,checked:=checked} 12 4 arguments
 (old.onto (locals marker)) changed (state bytes []) (state bytes []) _
 (arguments_panic p static checked marker bytes)

theorem return_slots_preserved : retVals changed 0 types=.ok old.toR :=
 LiteralFailureReturnSlots.extraction old _

theorem later_argument_not_run : changed.getAt 3 (.int IntTy.u256)=.ok (word 13 (by decide +kernel)) := by rfl

theorem older_alias : changed.getAt 5 (.bytes .memory)=.ok (.memRef rfl 0) := by rfl

def successLocals (marker : Roadmap.Word) : Locals E.layout parameters :=
 .cons (SourceEnvironment.sourceWord marker) (.cons (word 1 (by decide +kernel))
  (.cons (.memRef rfl 0) (.cons (.bool true) .nil)))
def successValues : Source.Vals E.layout types :=
 .cons (word 13 (by decide +kernel)) (.cons (word 13 (by decide +kernel))
  (.cons (word 11 (by decide +kernel)) .nil))

theorem successful_arguments (p : Roadmap.Pipeline) (static checked : Bool)
 (marker : Roadmap.Word) (bytes : Roadmap.Bytes) :
 (evalConvArgs (global p) {frame with static:=static,checked:=checked} 12 arguments).run
 (old.onto (successLocals marker),state bytes [])=
 (.ok successValues,(old.onto (successLocals ⟨11,by decide +kernel⟩),state bytes [])) := by
 cases p <;> rfl

theorem successful_statement (p : Roadmap.Pipeline) (static checked : Bool)
 (marker : Roadmap.Word) (bytes : Roadmap.Bytes) :
 (execS (global p) {frame with static:=static,checked:=checked} 13 4 none statement
 (old.onto (successLocals marker))).run (L0 E,state bytes [])=
 (.ok (.ret (successValues.onto (successLocals ⟨11,by decide +kernel⟩))),(L0 E,state bytes [])) :=
 LiteralFailureReturnSlots.tuple_statement (global p) {frame with static:=static,checked:=checked}
 12 old successValues (successLocals ⟨11,by decide +kernel⟩)
 (old.onto (successLocals marker)) arguments (state bytes []) (state bytes [])
 (successful_arguments p static checked marker bytes)

theorem skipped_assignment_distinct :
 changed.getAt 3 (.int IntTy.u256)≠.ok (word 11 (by decide +kernel)) := by
 intro equality
 cases equality

theorem no_fuel (marker : Roadmap.Word) (bytes : Roadmap.Bytes) :
 (execS (global .legacy) frame 0 4 none statement (old.onto (locals marker))).run
 (L0 E,state bytes [])=(.error .timeout,(L0 E,state bytes [])) := by rfl

theorem not_bare : panicData .divZero≠([] : Roadmap.Bytes) := by decide +kernel

def packets : List Roadmap.Bytes := [panicData .divZero,panicData .arithmetic,[]]
def render (bs : Roadmap.Bytes) : String :=
 "["++String.intercalate "," (bs.map (fun b=>toString b.toNat))++"]"
#eval IO.println ("TUPLE_ABORT_PACKETS=["++String.intercalate "," (packets.map render)++"]")
#print axioms argument_error
#print axioms arguments_panic
#print axioms statement_panic
#print axioms return_slots_preserved
#print axioms later_argument_not_run
#print axioms older_alias
#print axioms successful_arguments
#print axioms successful_statement
#print axioms skipped_assignment_distinct
#print axioms no_fuel
#print axioms not_bare
end Solidity.Lowering.V08.LiteralFailureTupleAbortControls
