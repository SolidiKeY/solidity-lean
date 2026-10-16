import Solidity.Frontend.Testing
import Solidity.Calculus.Surface
import Solidity.Calculus.Closers

/-! Storage-returning calls export aliases, retaining caller locals across
callee heap growth. Direct push/pop receivers retain their native capture rule. -/

solc_import "../../../tests/solc/StorageReturns.ast.json" hash 0x61f08f1a249b8d3a
  as Solkey.Migration.StorageReturns testing

solc_scoped_problems Solkey.Migration.StorageReturns decl

namespace Solidity.Examples.Tactics.StorageReturns

open scoped Solidity.Scoped

/--
info: dl{ ⟨[ fc .push(e); ]⟩ ⇝ ⟨[ aliasType storage sp = fc; sp .push(e); ]⟩ }
---
info: dl{ ⟨[ fc .push(); ]⟩ ⇝ ⟨[ aliasType storage sp = fc; sp .push(); ]⟩ }
---
info: dl{ ⟨[ fc .pop(); ]⟩ ⇝ ⟨[ aliasType storage sp = fc; sp .pop(); ]⟩ }
-/
#guard_msgs in
run_meta do
  for name in [``Taclet.storagePushValue_unfold_leftCallReceiver,
      ``Taclet.storagePush_unfold_leftCallReceiver, ``Taclet.storagePop_unfold_leftCallReceiver] do
    let info ← Lean.getConstInfo name
    Lean.Meta.forallTelescopeReducing info.type fun _ type => Lean.logInfo m!"{type}"

open scoped Solidity.Schema in
/-- error: the replacement keeps the operation and operand on fresh `sp` -/
#guard_msgs in
#check dl{ ⟨[ fc.push(e); ]⟩ ⇝ ⟨[ aliasType storage sp = fc; sp.pop(); ]⟩ }

open scoped Solidity.Schema in
/-- error: the fresh `sp` captures the getter of the find -/
#guard_msgs in
#check dl{ ⟨[ fc.pop(); ]⟩ ⇝ ⟨[ aliasType storage sp = fc2; sp.pop(); ]⟩ }

private def bareReturn := sol[Solkey.Migration.StorageReturns]{ valuesRef(); }
private def bindReturn := sol[Solkey.Migration.StorageReturns]{ uint[] storage p = valuesRef(); }
private def rebindReturn := sol[Solkey.Migration.StorageReturns]{
  uint[] storage p = valuesRef(); p = otherRef();
}
private def argumentReturn := sol[Solkey.Migration.StorageReturns]{
  uint i = 0; uint[] storage p = rowRef(i + 1);
}

private def valueReceiver := sol[Solkey.Migration.StorageReturns]{ valuesRef().push(calls); }
private def defaultReceiver := sol[Solkey.Migration.StorageReturns]{ valuesRef().push(); }
private def popReceiver := sol[Solkey.Migration.StorageReturns]{ valuesRef().pop(); }
private def argumentReceiver := sol[Solkey.Migration.StorageReturns]{
  uint i = 0; rowRef(i + 1).push(23);
}

/-- info: eight storage-return programs preserve their typed shape through both printer paths -/
#guard_msgs in
run_meta do
  for name in [``bareReturn, ``bindReturn, ``rebindReturn, ``argumentReturn,
      ``valueReceiver, ``defaultReceiver, ``popReceiver, ``argumentReceiver] do
    let info ← Lean.getConstInfo name
    let original := info.value!
    let some ss ← Delab.withPrinter original false (Delab.ppProgS [] original)
      | throwError "storage-return printer failed: {name}"
    let printedSyntax ← `(sol[Solkey.Migration.StorageReturns]{ $[$ss;]* })
    let parsed ← Lean.Elab.Term.TermElabM.run' do
      let parsed ← Lean.Elab.Term.elabTermEnsuringType printedSyntax info.type
      Lean.Elab.Term.synthesizeSyntheticMVarsNoPostponing
      pure parsed
    unless ← Lean.Meta.isDefEq original parsed do
      throwError "storage-return roundtrip changed {name}:\n{printedSyntax}\n{original}\n{parsed}"
    let shownExpr ← Lean.Meta.mkAppM ``Prog.show #[Lean.toExpr ([] : List Var), original]
    let shown ← unsafe Lean.Meta.evalExpr String (Lean.mkConst ``String) shownExpr
    let .ok shownSyntax := Lean.Parser.runParserCategory (← Lean.getEnv) `term
        s!"sol[Solkey.Migration.StorageReturns]\{ {shown} }"
      | throwError "storage-return display does not parse: {name}\n{shown}"
    let shownParsed ← Lean.Elab.Term.TermElabM.run' do
      let parsed ← Lean.Elab.Term.elabTermEnsuringType shownSyntax info.type
      Lean.Elab.Term.synthesizeSyntheticMVarsNoPostponing
      pure parsed
    unless ← Lean.Meta.isDefEq original shownParsed do
      throwError "storage-return display roundtrip changed {name}:\n{shown}"
  Lean.logInfo "eight storage-return programs preserve their typed shape through both printer paths"

/-- info: eight open-tail prefixes preserve their typed shape and schematic continuation -/
#guard_msgs in
run_meta do
  for name in [``bareReturn, ``bindReturn, ``rebindReturn, ``argumentReturn,
      ``valueReceiver, ``defaultReceiver, ``popReceiver, ``argumentReceiver] do
    let info ← Lean.getConstInfo name
    let original := info.value!
    let type ← Lean.Meta.whnf info.type
    let args := type.getAppArgs
    let tailType := Lean.mkApp3 (Lean.mkConst ``Prog) args[0]! args[2]! args[2]!
    Lean.Meta.withLocalDeclD `ω tailType fun tail => do
      let pieces ← Delab.withPrinter original false (Delab.progExprPieces [] original)
      let some (ss, some rest) ← Delab.withPrinter original false
          (Delab.ppPartsS (pieces.push (.var tail)))
        | throwError "storage-return open-tail printer failed: {name}"
      unless rest.getId == `ω do
        throwError "storage-return printer changed its continuation: {rest}"
      let printedSyntax ← `(sol[Solkey.Migration.StorageReturns]{ $[$ss;]* })
      let parsed ← Lean.Elab.Term.TermElabM.run' do
        let parsed ← Lean.Elab.Term.elabTermEnsuringType printedSyntax info.type
        Lean.Elab.Term.synthesizeSyntheticMVarsNoPostponing
        pure parsed
      unless ← Lean.Meta.isDefEq original parsed do
        throwError "storage-return open-tail prefix changed {name}:\n{printedSyntax}"
  Lean.logInfo "eight open-tail prefixes preserve their typed shape and schematic continuation"

/-- Five helpers and twelve public cases are retained, including the deferred-effect gap. -/
example : Solkey.Migration.StorageReturns.report.length = 17 := rfl

/-- Bindings and all three direct call receivers elaborate. -/
example : (Solkey.Migration.StorageReturns.report.map fun r => (r.name, r.status.toStr)) =
    [("valuesRef", "elaborated"), ("otherRef", "elaborated"), ("rowRef", "elaborated"),
     ("allocatedRef", "elaborated"), ("rejectedRef", "elaborated"), ("bindsRoot", "elaborated"),
     ("rebinds", "elaborated"), ("returnsIndexed", "elaborated"), ("heapGrowth", "elaborated"),
     ("calleeReverts", "elaborated"), ("falseCopy", "elaborated"),
     ("receiverPush", "elaborated"), ("receiverPushValue", "elaborated"),
     ("receiverPop", "elaborated"), ("receiverReadsAfterGetter", "elaborated"),
     ("receiverReadsBeforeGetterFalse", "elaborated"),
     ("receiverEffectfulOperand", "elaborated")] := by
  decide +kernel

/-- A returned root is the same alias, and its getter runs once. -/
example : (Prog.run (State.init Solkey.Migration.StorageReturns)
    Solkey.Migration.StorageReturns.bindsRoot).isOk = true := by
  decide +kernel

/-- Rebinding selects the second returned alias without changing the first root. -/
example : (Prog.run (State.init Solkey.Migration.StorageReturns)
    Solkey.Migration.StorageReturns.rebinds).isOk = true := by
  decide +kernel

/-- A non-simple argument is captured before returning an indexed alias. -/
example : (Prog.run (State.init Solkey.Migration.StorageReturns)
    Solkey.Migration.StorageReturns.returnsIndexed).isOk = true := by
  decide +kernel

/-- Caller memory locals survive allocation in the storage-returning callee. -/
example : (Prog.run (State.init Solkey.Migration.StorageReturns)
    Solkey.Migration.StorageReturns.heapGrowth).isOk = true := by
  decide +kernel

/-- A callee's revert propagates through a storage return. -/
example : (Prog.run (State.init Solkey.Migration.StorageReturns)
    Solkey.Migration.StorageReturns.calleeReverts).halt? = some .revert := by
  decide +kernel

/-- Treating a returned storage alias as an independent copy is refuted. -/
example : (Prog.run (State.init Solkey.Migration.StorageReturns)
    Solkey.Migration.StorageReturns.falseCopy).halt? = some .panic := by
  decide +kernel

/-- Default push evaluates the getter once before appending. -/
example : (Prog.run (State.init Solkey.Migration.StorageReturns)
    Solkey.Migration.StorageReturns.receiverPush).isOk = true := by
  decide +kernel

/-- A value is appended through the returned alias. -/
example : (Prog.run (State.init Solkey.Migration.StorageReturns)
    Solkey.Migration.StorageReturns.receiverPushValue).isOk = true := by
  decide +kernel

/-- Pop evaluates the getter once before removing the selected element. -/
example : (Prog.run (State.init Solkey.Migration.StorageReturns)
    Solkey.Migration.StorageReturns.receiverPop).isOk = true := by
  decide +kernel

/-- The compiled push source observes the getter's increment. -/
example : (Prog.run (State.init Solkey.Migration.StorageReturns)
    Solkey.Migration.StorageReturns.receiverReadsAfterGetter).isOk = true := by
  decide +kernel

/-- Reading the operand before the getter would incorrectly accept this claim. -/
example : (Prog.run (State.init Solkey.Migration.StorageReturns)
    Solkey.Migration.StorageReturns.receiverReadsBeforeGetterFalse).halt? = some .panic := by
  decide +kernel

/-- The imported effectful operand reads the getter's write before incrementing. -/
theorem effectful_receiver_initial : (Prog.run (State.init Solkey.Migration.StorageReturns)
    Solkey.Migration.StorageReturns.receiverEffectfulOperand).isOk = true := by
  decide +kernel

/-- The imported box obligation for `valuesRef().push(calls++)` closes by the calculus. -/
theorem effectful_receiver_proved :
    ⊢ Solkey.Migration.StorageReturns.receiverEffectfulOperand.problem := by
  sol_prove

end Solidity.Examples.Tactics.StorageReturns
