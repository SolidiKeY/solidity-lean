import Solidity.Examples.Roadmap.V16.FiniteMemoryCompilation
import Solidity.Examples.Roadmap.V16.DispatchConsumer
import Solidity.Examples.Roadmap.V16.AbiEntryConsumer
import Solidity.Examples.Roadmap.V16.FiniteHeapConsumer
import Solidity.Examples.Roadmap.V16.CompilerConsumer
import Solidity.Examples.Roadmap.V16.ConstructionCompilation
import Solidity.Examples.Roadmap.V16.ConstructionConsumer
import Solidity.Examples.Roadmap.V16.MemoryLoopConsumer
import Solidity.Examples.Roadmap.V16.MemoryCallConsumer
import Solidity.Examples.Roadmap.V16.CallbackControls
import Lean
import Solidity.Examples.Roadmap.V16.LoopControls
import Solidity.Roadmap.V16.HashHistory
import Solidity.Examples.Roadmap.V16.SessionControls
import Solidity.Roadmap.V16.SpecificationControls
import Solidity.Roadmap.V16.CreationLibrarySpec
import Solidity.Roadmap.V16.CreationReturnConsumer
import Solidity.Roadmap.V16.H24Input
import Solidity.Roadmap.V16.NativeParentConsumer
import Solidity.Roadmap.V16.NativeRevertConsumer
import Solidity.Roadmap.V16.Relational
import Solidity.Roadmap.V16.RelationalGuardSpec
import Solidity.Roadmap.V16.SSCP2.NewAllocation
import Solidity.Roadmap.V16.SSCP2.NewAllocationControls
import Solidity.Roadmap.V16.SourceSizeControls
import Solidity.Roadmap.V16.SourceTransactionConsumer
import Solidity.Roadmap.V16.Specifications
import Solidity.Roadmap.V16.TransactionControls
import Solidity.Roadmap.V16.Transactions
import Solidity.Roadmap.V16.Transport
import Solidity.Roadmap.V16.TransportControls
import Solidity.Examples.Roadmap.V16.CalculusConsumer
import Solidity.Examples.Roadmap.V16.CallbackConsumers
import Solidity.Examples.Roadmap.V16.FramedReasonConsumer
/-! Read-only environment metadata. This is not a proof or a trust shortcut. -/
open Lean Elab Command in
run_cmd do
  let env ← getEnv
  let mut inductives : Array Json := #[]
  for (n, info) in env.constants.toList do
    if (`Solidity).isPrefixOf n then
      if let .inductInfo info := info then
        inductives := inductives.push (Json.mkObj [
          ("name", toJson n.toString), ("constructors", toJson (info.ctors.map Name.toString))])
  let mut theorems : Array Json := #[]
  for (n, info) in env.constants.toList do
    if (`Solidity.Roadmap.V16).isPrefixOf ((privateToUserName? n).getD n) ||
        (`_private.Solidity.Roadmap.V16).isPrefixOf n ||
        (`_private.Solidity.Examples.Roadmap.V16).isPrefixOf n then
      if let .thmInfo _ := info then
        let axs ← collectAxioms n
        let ty ← liftTermElabM do return (← Meta.ppExpr info.type).pretty
        let premises ← liftTermElabM do
          Meta.forallBoundedTelescope info.type (some info.type.getNumHeadForalls) fun xs _ => do
            let mut rows : Array Json := #[]
            let mut rawType := info.type
            for x in xs do
              let decl ← x.fvarId!.getDecl
              let ty ← Meta.ppExpr decl.type
              let rawDomain := rawType.consumeMData.bindingDomain!
              rawType := rawType.consumeMData.bindingBody!
              rows := rows.push (Json.mkObj [
                ("name", toJson decl.userName.toString), ("type", toJson ty.pretty),
                ("isProp", toJson (← Meta.isProp decl.type)),
                ("closedExpr", toJson (reprStr rawDomain)),
                ("constants", toJson (decl.type.getUsedConstants.toList.map Name.toString))])
            return rows
        theorems := theorems.push (Json.mkObj [
          ("name", toJson n.toString), ("ownerName", toJson ((privateToUserName? n).getD n).toString),
          ("type", toJson ty), ("premises", .arr premises),
          ("typeConstants", toJson (info.type.getUsedConstants.toList.map Name.toString)),
          ("dependencies", toJson (info.getUsedConstantsAsSet.toList.map Name.toString)),
          ("axioms", toJson (axs.toList.map Name.toString))])
  logInfo m!"V16-INVENTORY {(Json.mkObj [("modules", toJson (env.header.moduleNames.toList.map Name.toString)), ("inductives", .arr inductives), ("theorems", .arr theorems)]).compress}"
