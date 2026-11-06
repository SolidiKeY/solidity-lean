import Solidity.Frontend.Import
import Solidity.Semantics.RunFuel

/-! Kernel execution certificates for the exact modern source fixtures, in both
required pipelines. These certify the typed model, not compiler/EVM equivalence. -/
namespace Solidity.Tests.EntryPointsLeft
open Solidity Solidity.Frontend

private def initial (C : Contract) : State C [] :=
  { State.init C with
    selfBalance := ⟨5, by decide⟩
    tx := { selfAddress := ⟨7, by decide⟩, msgSender := ⟨9, by decide⟩, msgValue := ⟨13, by decide⟩ } }

private theorem fuelSuccess {C : Contract} {Γ Δ : Ctx} (P : Prog C Γ Δ)
    (σ : State C Γ) (h : (Prog.runF 8 P σ).isOk = true) :
    (Prog.run σ P).isOk = true := by
  have hd : Prog.runF 8 P σ ≠ .error .diverge := by
    intro he
    rw [he] at h
    cases h
  change (Prog.runR P σ).isOk = true
  rw [← (Prog.runF_approx 8 P σ).eq hd]
  exact h

solc_import "../solc/EntryPointsLeft.ast.json" hash 0xd3109a3bea2a97ae as Legacy.ByteFallbackRefusal testing
solc_import "../solc/EntryPointsLeft.ast.json" hash 0xd3109a3bea2a97ae as Legacy.ExternalOverloadCollisionRefusal testing
solc_import "../solc/EntryPointsLeft.ast.json" hash 0xd3109a3bea2a97ae as Legacy.ExternalOverloads testing
solc_import "../solc/EntryPointsLeft.ast.json" hash 0xd3109a3bea2a97ae as Legacy.ExternalOverride testing
solc_import "../solc/EntryPointsLeft.ast.json" hash 0xd3109a3bea2a97ae as Legacy.HelperReceiverRefusal testing
solc_import "../solc/EntryPointsLeft.ast.json" hash 0xd3109a3bea2a97ae as Legacy.InheritedFallback testing
solc_import "../solc/EntryPointsLeft.ast.json" hash 0xd3109a3bea2a97ae as Legacy.InheritedFrameFallback testing
solc_import "../solc/EntryPointsLeft.ast.json" hash 0xd3109a3bea2a97ae as Legacy.InheritedFrameReceiver testing
solc_import "../solc/EntryPointsLeft.ast.json" hash 0xd3109a3bea2a97ae as Legacy.InheritedReceiver testing
solc_import "../solc/EntryPointsLeft.ast.json" hash 0xd3109a3bea2a97ae as Legacy.InheritedRollback testing
solc_import "../solc/EntryPointsLeft.ast.json" hash 0xd3109a3bea2a97ae as Legacy.ModifiedReceiverRefusal testing
solc_import "../solc/EntryPointsLeft.ast.json" hash 0xd3109a3bea2a97ae as Legacy.NominalDispatchRefusal testing
solc_import "../solc/EntryPointsLeft.ast.json" hash 0xd3109a3bea2a97ae as Legacy.NominalGetters testing
solc_import "../solc/EntryPointsLeft.ast.json" hash 0xd3109a3bea2a97ae as Legacy.NominalKeyDispatchRefusal testing
solc_import "../solc/EntryPointsLeft.ast.json" hash 0xd3109a3bea2a97ae as Legacy.NonpayableFallbackRefusal testing
solc_import "../solc/EntryPointsLeft.ast.json" hash 0xd3109a3bea2a97ae as Legacy.OwnHelperReceiver testing
solc_import "../solc/EntryPointsLeft.ast.json" hash 0xd3109a3bea2a97ae as Legacy.ReceiveOverride testing
solc_import "../solc/EntryPointsLeft.ast.json" hash 0xd3109a3bea2a97ae as Legacy.ReceivePriority testing
solc_import "../solc/EntryPointsLeft.ast.json" hash 0xd3109a3bea2a97ae as Legacy.RefusedGetters testing
solc_import "../solc/EntryPointsLeft.ast.json" hash 0xd3109a3bea2a97ae as Legacy.RenamedExternal testing

/-- `NominalGetters.enumScalar` terminates normally from funded self address 7. -/
theorem Legacy_NominalGetters_enumScalar : (Prog.run (initial Legacy.NominalGetters) Legacy.NominalGetters.enumScalar).isOk = true := by
  apply fuelSuccess
  decide +kernel
#print axioms Legacy_NominalGetters_enumScalar

/-- `NominalGetters.enumMapping` terminates normally from funded self address 7. -/
theorem Legacy_NominalGetters_enumMapping : (Prog.run (initial Legacy.NominalGetters) Legacy.NominalGetters.enumMapping).isOk = true := by
  apply fuelSuccess
  decide +kernel
#print axioms Legacy_NominalGetters_enumMapping

/-- `NominalGetters.enumStruct` terminates normally from funded self address 7. -/
theorem Legacy_NominalGetters_enumStruct : (Prog.run (initial Legacy.NominalGetters) Legacy.NominalGetters.enumStruct).isOk = true := by
  apply fuelSuccess
  decide +kernel
#print axioms Legacy_NominalGetters_enumStruct

/-- `NominalGetters.contractScalar` terminates normally from funded self address 7. -/
theorem Legacy_NominalGetters_contractScalar : (Prog.run (initial Legacy.NominalGetters) Legacy.NominalGetters.contractScalar).isOk = true := by
  apply fuelSuccess
  decide +kernel
#print axioms Legacy_NominalGetters_contractScalar

/-- `InheritedReceiver.positive` terminates normally from funded self address 7. -/
theorem Legacy_InheritedReceiver_positive : (Prog.run (initial Legacy.InheritedReceiver) Legacy.InheritedReceiver.positive).isOk = true := by
  apply fuelSuccess
  decide +kernel
#print axioms Legacy_InheritedReceiver_positive

/-- `InheritedFallback.positive` terminates normally from funded self address 7. -/
theorem Legacy_InheritedFallback_positive : (Prog.run (initial Legacy.InheritedFallback) Legacy.InheritedFallback.positive).isOk = true := by
  apply fuelSuccess
  decide +kernel
#print axioms Legacy_InheritedFallback_positive

/-- `RenamedExternal.positive` terminates normally from funded self address 7. -/
theorem Legacy_RenamedExternal_positive : (Prog.run (initial Legacy.RenamedExternal) Legacy.RenamedExternal.positive).isOk = true := by
  apply fuelSuccess
  decide +kernel
#print axioms Legacy_RenamedExternal_positive

/-- `ReceivePriority.positive` terminates normally from funded self address 7. -/
theorem Legacy_ReceivePriority_positive : (Prog.run (initial Legacy.ReceivePriority) Legacy.ReceivePriority.positive).isOk = true := by
  apply fuelSuccess
  decide +kernel
#print axioms Legacy_ReceivePriority_positive

/-- `ReceiveOverride.positive` terminates normally from funded self address 7. -/
theorem Legacy_ReceiveOverride_positive : (Prog.run (initial Legacy.ReceiveOverride) Legacy.ReceiveOverride.positive).isOk = true := by
  apply fuelSuccess
  decide +kernel
#print axioms Legacy_ReceiveOverride_positive

/-- `ExternalOverride.positive` terminates normally from funded self address 7. -/
theorem Legacy_ExternalOverride_positive : (Prog.run (initial Legacy.ExternalOverride) Legacy.ExternalOverride.positive).isOk = true := by
  apply fuelSuccess
  decide +kernel
#print axioms Legacy_ExternalOverride_positive

/-- `ExternalOverloads.positive` terminates normally from funded self address 7. -/
theorem Legacy_ExternalOverloads_positive : (Prog.run (initial Legacy.ExternalOverloads) Legacy.ExternalOverloads.positive).isOk = true := by
  apply fuelSuccess
  decide +kernel
#print axioms Legacy_ExternalOverloads_positive

/-- `OwnHelperReceiver.positive` terminates normally from funded self address 7. -/
theorem Legacy_OwnHelperReceiver_positive : (Prog.run (initial Legacy.OwnHelperReceiver) Legacy.OwnHelperReceiver.positive).isOk = true := by
  apply fuelSuccess
  decide +kernel
#print axioms Legacy_OwnHelperReceiver_positive

/-- `InheritedFrameReceiver.positive` terminates normally from funded self address 7. -/
theorem Legacy_InheritedFrameReceiver_positive : (Prog.run (initial Legacy.InheritedFrameReceiver) Legacy.InheritedFrameReceiver.positive).isOk = true := by
  apply fuelSuccess
  decide +kernel
#print axioms Legacy_InheritedFrameReceiver_positive

/-- `InheritedFrameFallback.positive` terminates normally from funded self address 7. -/
theorem Legacy_InheritedFrameFallback_positive : (Prog.run (initial Legacy.InheritedFrameFallback) Legacy.InheritedFrameFallback.positive).isOk = true := by
  apply fuelSuccess
  decide +kernel
#print axioms Legacy_InheritedFrameFallback_positive

/-- `InheritedRollback.positive` terminates normally from funded self address 7. -/
theorem Legacy_InheritedRollback_positive : (Prog.run (initial Legacy.InheritedRollback) Legacy.InheritedRollback.positive).isOk = true := by
  apply fuelSuccess
  decide +kernel
#print axioms Legacy_InheritedRollback_positive

/-- The false source observation in `NominalGetters.falseEnum` reaches a real panic. -/
theorem Legacy_NominalGetters_falseEnum : (Prog.runF 8 Legacy.NominalGetters.falseEnum (initial Legacy.NominalGetters)).halt? = some .panic := by
  decide +kernel
#print axioms Legacy_NominalGetters_falseEnum

/-- The false source observation in `InheritedReceiver.falseObservation` reaches a real panic. -/
theorem Legacy_InheritedReceiver_falseObservation : (Prog.runF 8 Legacy.InheritedReceiver.falseObservation (initial Legacy.InheritedReceiver)).halt? = some .panic := by
  decide +kernel
#print axioms Legacy_InheritedReceiver_falseObservation

/-- The false source observation in `InheritedFallback.falseObservation` reaches a real panic. -/
theorem Legacy_InheritedFallback_falseObservation : (Prog.runF 8 Legacy.InheritedFallback.falseObservation (initial Legacy.InheritedFallback)).halt? = some .panic := by
  decide +kernel
#print axioms Legacy_InheritedFallback_falseObservation

/-- The false source observation in `RenamedExternal.falseObservation` reaches a real panic. -/
theorem Legacy_RenamedExternal_falseObservation : (Prog.runF 8 Legacy.RenamedExternal.falseObservation (initial Legacy.RenamedExternal)).halt? = some .panic := by
  decide +kernel
#print axioms Legacy_RenamedExternal_falseObservation

#guard (Legacy.InheritedReceiver.report.find? (·.sourceName == "stipendRefusal")).any fun row => row.status == .unsupported && row.admissionChecked && (row.sourceDiagnostic.map (·.name)) == some `solidity.selfPayment

#guard (Legacy.NonpayableFallbackRefusal.report.find? (·.sourceName == "entry")).any fun row => row.status == .unsupported && row.admissionChecked && (row.sourceDiagnostic.map (·.name)) == some `solidity.selfPayment

#guard (Legacy.ModifiedReceiverRefusal.report.find? (·.sourceName == "entry")).any fun row => row.status == .unsupported && row.admissionChecked && (row.sourceDiagnostic.map (·.name)) == some `solidity.selfPayment

#guard (Legacy.HelperReceiverRefusal.report.find? (·.sourceName == "entry")).any fun row => row.status == .unsupported && row.admissionChecked && (row.sourceDiagnostic.map (·.name)) == some `solidity.selfPayment

#guard (Legacy.ByteFallbackRefusal.report.find? (·.sourceName == "entry")).any fun row => row.status == .unsupported && row.admissionChecked && (row.sourceDiagnostic.map (·.name)) == some `solidity.selfPayment

#guard (Legacy.NominalDispatchRefusal.report.find? (·.sourceName == "entry")).any fun row => row.status == .unsupported && row.admissionChecked && (row.sourceDiagnostic.map (·.name)) == some `solidity.functionDispatch

#guard (Legacy.NominalKeyDispatchRefusal.report.find? (·.sourceName == "entry")).any fun row => row.status == .unsupported && row.admissionChecked && (row.sourceDiagnostic.map (·.name)) == some `solidity.functionDispatch

#guard (Legacy.ExternalOverloadCollisionRefusal.report.find? (·.sourceName == "positive")).any fun row => row.status == .unsupported && row.admissionChecked && (row.sourceDiagnostic.map (·.name)) == some `solidity.functionDispatch

#guard (Legacy.RefusedGetters.report.find? (·.sourceName == "referenceBytes")).any fun row => row.status == .unsupported

#guard (Legacy.RefusedGetters.report.find? (·.sourceName == "referenceString")).any fun row => row.status == .unsupported

#guard (Legacy.RefusedGetters.report.find? (·.sourceName == "functionResult")).any fun row => row.status == .unsupported && row.admissionChecked && (row.sourceDiagnostic.map (·.name)) == some `solidity.functionDispatch

#guard (Legacy.NominalGetters.funs.find? fun (_, f) => f.sourceDecl.any (·.name == "shade")).any fun (_, f) =>
  f.rets.any fun (n, t) => abiTyName f.widths n t == some "uint8"

#guard (Legacy.NominalGetters.funs.find? fun (_, f) => f.sourceDecl.any (·.name == "owner")).any fun (_, f) =>
  f.rets.any fun (n, t) => abiTyName f.widths n t == some "address"
solc_import "../solc/EntryPointsLeft.viaIR.ast.json" hash 0xd282805b1d3ea697 as ViaIR.ByteFallbackRefusal testing
solc_import "../solc/EntryPointsLeft.viaIR.ast.json" hash 0xd282805b1d3ea697 as ViaIR.ExternalOverloadCollisionRefusal testing
solc_import "../solc/EntryPointsLeft.viaIR.ast.json" hash 0xd282805b1d3ea697 as ViaIR.ExternalOverloads testing
solc_import "../solc/EntryPointsLeft.viaIR.ast.json" hash 0xd282805b1d3ea697 as ViaIR.ExternalOverride testing
solc_import "../solc/EntryPointsLeft.viaIR.ast.json" hash 0xd282805b1d3ea697 as ViaIR.HelperReceiverRefusal testing
solc_import "../solc/EntryPointsLeft.viaIR.ast.json" hash 0xd282805b1d3ea697 as ViaIR.InheritedFallback testing
solc_import "../solc/EntryPointsLeft.viaIR.ast.json" hash 0xd282805b1d3ea697 as ViaIR.InheritedFrameFallback testing
solc_import "../solc/EntryPointsLeft.viaIR.ast.json" hash 0xd282805b1d3ea697 as ViaIR.InheritedFrameReceiver testing
solc_import "../solc/EntryPointsLeft.viaIR.ast.json" hash 0xd282805b1d3ea697 as ViaIR.InheritedReceiver testing
solc_import "../solc/EntryPointsLeft.viaIR.ast.json" hash 0xd282805b1d3ea697 as ViaIR.InheritedRollback testing
solc_import "../solc/EntryPointsLeft.viaIR.ast.json" hash 0xd282805b1d3ea697 as ViaIR.ModifiedReceiverRefusal testing
solc_import "../solc/EntryPointsLeft.viaIR.ast.json" hash 0xd282805b1d3ea697 as ViaIR.NominalDispatchRefusal testing
solc_import "../solc/EntryPointsLeft.viaIR.ast.json" hash 0xd282805b1d3ea697 as ViaIR.NominalGetters testing
solc_import "../solc/EntryPointsLeft.viaIR.ast.json" hash 0xd282805b1d3ea697 as ViaIR.NominalKeyDispatchRefusal testing
solc_import "../solc/EntryPointsLeft.viaIR.ast.json" hash 0xd282805b1d3ea697 as ViaIR.NonpayableFallbackRefusal testing
solc_import "../solc/EntryPointsLeft.viaIR.ast.json" hash 0xd282805b1d3ea697 as ViaIR.OwnHelperReceiver testing
solc_import "../solc/EntryPointsLeft.viaIR.ast.json" hash 0xd282805b1d3ea697 as ViaIR.ReceiveOverride testing
solc_import "../solc/EntryPointsLeft.viaIR.ast.json" hash 0xd282805b1d3ea697 as ViaIR.ReceivePriority testing
solc_import "../solc/EntryPointsLeft.viaIR.ast.json" hash 0xd282805b1d3ea697 as ViaIR.RefusedGetters testing
solc_import "../solc/EntryPointsLeft.viaIR.ast.json" hash 0xd282805b1d3ea697 as ViaIR.RenamedExternal testing

/-- `NominalGetters.enumScalar` terminates normally from funded self address 7. -/
theorem ViaIR_NominalGetters_enumScalar : (Prog.run (initial ViaIR.NominalGetters) ViaIR.NominalGetters.enumScalar).isOk = true := by
  apply fuelSuccess
  decide +kernel
#print axioms ViaIR_NominalGetters_enumScalar

/-- `NominalGetters.enumMapping` terminates normally from funded self address 7. -/
theorem ViaIR_NominalGetters_enumMapping : (Prog.run (initial ViaIR.NominalGetters) ViaIR.NominalGetters.enumMapping).isOk = true := by
  apply fuelSuccess
  decide +kernel
#print axioms ViaIR_NominalGetters_enumMapping

/-- `NominalGetters.enumStruct` terminates normally from funded self address 7. -/
theorem ViaIR_NominalGetters_enumStruct : (Prog.run (initial ViaIR.NominalGetters) ViaIR.NominalGetters.enumStruct).isOk = true := by
  apply fuelSuccess
  decide +kernel
#print axioms ViaIR_NominalGetters_enumStruct

/-- `NominalGetters.contractScalar` terminates normally from funded self address 7. -/
theorem ViaIR_NominalGetters_contractScalar : (Prog.run (initial ViaIR.NominalGetters) ViaIR.NominalGetters.contractScalar).isOk = true := by
  apply fuelSuccess
  decide +kernel
#print axioms ViaIR_NominalGetters_contractScalar

/-- `InheritedReceiver.positive` terminates normally from funded self address 7. -/
theorem ViaIR_InheritedReceiver_positive : (Prog.run (initial ViaIR.InheritedReceiver) ViaIR.InheritedReceiver.positive).isOk = true := by
  apply fuelSuccess
  decide +kernel
#print axioms ViaIR_InheritedReceiver_positive

/-- `InheritedFallback.positive` terminates normally from funded self address 7. -/
theorem ViaIR_InheritedFallback_positive : (Prog.run (initial ViaIR.InheritedFallback) ViaIR.InheritedFallback.positive).isOk = true := by
  apply fuelSuccess
  decide +kernel
#print axioms ViaIR_InheritedFallback_positive

/-- `RenamedExternal.positive` terminates normally from funded self address 7. -/
theorem ViaIR_RenamedExternal_positive : (Prog.run (initial ViaIR.RenamedExternal) ViaIR.RenamedExternal.positive).isOk = true := by
  apply fuelSuccess
  decide +kernel
#print axioms ViaIR_RenamedExternal_positive

/-- `ReceivePriority.positive` terminates normally from funded self address 7. -/
theorem ViaIR_ReceivePriority_positive : (Prog.run (initial ViaIR.ReceivePriority) ViaIR.ReceivePriority.positive).isOk = true := by
  apply fuelSuccess
  decide +kernel
#print axioms ViaIR_ReceivePriority_positive

/-- `ReceiveOverride.positive` terminates normally from funded self address 7. -/
theorem ViaIR_ReceiveOverride_positive : (Prog.run (initial ViaIR.ReceiveOverride) ViaIR.ReceiveOverride.positive).isOk = true := by
  apply fuelSuccess
  decide +kernel
#print axioms ViaIR_ReceiveOverride_positive

/-- `ExternalOverride.positive` terminates normally from funded self address 7. -/
theorem ViaIR_ExternalOverride_positive : (Prog.run (initial ViaIR.ExternalOverride) ViaIR.ExternalOverride.positive).isOk = true := by
  apply fuelSuccess
  decide +kernel
#print axioms ViaIR_ExternalOverride_positive

/-- `ExternalOverloads.positive` terminates normally from funded self address 7. -/
theorem ViaIR_ExternalOverloads_positive : (Prog.run (initial ViaIR.ExternalOverloads) ViaIR.ExternalOverloads.positive).isOk = true := by
  apply fuelSuccess
  decide +kernel
#print axioms ViaIR_ExternalOverloads_positive

/-- `OwnHelperReceiver.positive` terminates normally from funded self address 7. -/
theorem ViaIR_OwnHelperReceiver_positive : (Prog.run (initial ViaIR.OwnHelperReceiver) ViaIR.OwnHelperReceiver.positive).isOk = true := by
  apply fuelSuccess
  decide +kernel
#print axioms ViaIR_OwnHelperReceiver_positive

/-- `InheritedFrameReceiver.positive` terminates normally from funded self address 7. -/
theorem ViaIR_InheritedFrameReceiver_positive : (Prog.run (initial ViaIR.InheritedFrameReceiver) ViaIR.InheritedFrameReceiver.positive).isOk = true := by
  apply fuelSuccess
  decide +kernel
#print axioms ViaIR_InheritedFrameReceiver_positive

/-- `InheritedFrameFallback.positive` terminates normally from funded self address 7. -/
theorem ViaIR_InheritedFrameFallback_positive : (Prog.run (initial ViaIR.InheritedFrameFallback) ViaIR.InheritedFrameFallback.positive).isOk = true := by
  apply fuelSuccess
  decide +kernel
#print axioms ViaIR_InheritedFrameFallback_positive

/-- `InheritedRollback.positive` terminates normally from funded self address 7. -/
theorem ViaIR_InheritedRollback_positive : (Prog.run (initial ViaIR.InheritedRollback) ViaIR.InheritedRollback.positive).isOk = true := by
  apply fuelSuccess
  decide +kernel
#print axioms ViaIR_InheritedRollback_positive

/-- The false source observation in `NominalGetters.falseEnum` reaches a real panic. -/
theorem ViaIR_NominalGetters_falseEnum : (Prog.runF 8 ViaIR.NominalGetters.falseEnum (initial ViaIR.NominalGetters)).halt? = some .panic := by
  decide +kernel
#print axioms ViaIR_NominalGetters_falseEnum

/-- The false source observation in `InheritedReceiver.falseObservation` reaches a real panic. -/
theorem ViaIR_InheritedReceiver_falseObservation : (Prog.runF 8 ViaIR.InheritedReceiver.falseObservation (initial ViaIR.InheritedReceiver)).halt? = some .panic := by
  decide +kernel
#print axioms ViaIR_InheritedReceiver_falseObservation

/-- The false source observation in `InheritedFallback.falseObservation` reaches a real panic. -/
theorem ViaIR_InheritedFallback_falseObservation : (Prog.runF 8 ViaIR.InheritedFallback.falseObservation (initial ViaIR.InheritedFallback)).halt? = some .panic := by
  decide +kernel
#print axioms ViaIR_InheritedFallback_falseObservation

/-- The false source observation in `RenamedExternal.falseObservation` reaches a real panic. -/
theorem ViaIR_RenamedExternal_falseObservation : (Prog.runF 8 ViaIR.RenamedExternal.falseObservation (initial ViaIR.RenamedExternal)).halt? = some .panic := by
  decide +kernel
#print axioms ViaIR_RenamedExternal_falseObservation

#guard (ViaIR.InheritedReceiver.report.find? (·.sourceName == "stipendRefusal")).any fun row => row.status == .unsupported && row.admissionChecked && (row.sourceDiagnostic.map (·.name)) == some `solidity.selfPayment

#guard (ViaIR.NonpayableFallbackRefusal.report.find? (·.sourceName == "entry")).any fun row => row.status == .unsupported && row.admissionChecked && (row.sourceDiagnostic.map (·.name)) == some `solidity.selfPayment

#guard (ViaIR.ModifiedReceiverRefusal.report.find? (·.sourceName == "entry")).any fun row => row.status == .unsupported && row.admissionChecked && (row.sourceDiagnostic.map (·.name)) == some `solidity.selfPayment

#guard (ViaIR.HelperReceiverRefusal.report.find? (·.sourceName == "entry")).any fun row => row.status == .unsupported && row.admissionChecked && (row.sourceDiagnostic.map (·.name)) == some `solidity.selfPayment

#guard (ViaIR.ByteFallbackRefusal.report.find? (·.sourceName == "entry")).any fun row => row.status == .unsupported && row.admissionChecked && (row.sourceDiagnostic.map (·.name)) == some `solidity.selfPayment

#guard (ViaIR.NominalDispatchRefusal.report.find? (·.sourceName == "entry")).any fun row => row.status == .unsupported && row.admissionChecked && (row.sourceDiagnostic.map (·.name)) == some `solidity.functionDispatch

#guard (ViaIR.NominalKeyDispatchRefusal.report.find? (·.sourceName == "entry")).any fun row => row.status == .unsupported && row.admissionChecked && (row.sourceDiagnostic.map (·.name)) == some `solidity.functionDispatch

#guard (ViaIR.ExternalOverloadCollisionRefusal.report.find? (·.sourceName == "positive")).any fun row => row.status == .unsupported && row.admissionChecked && (row.sourceDiagnostic.map (·.name)) == some `solidity.functionDispatch

#guard (ViaIR.RefusedGetters.report.find? (·.sourceName == "referenceBytes")).any fun row => row.status == .unsupported

#guard (ViaIR.RefusedGetters.report.find? (·.sourceName == "referenceString")).any fun row => row.status == .unsupported

#guard (ViaIR.RefusedGetters.report.find? (·.sourceName == "functionResult")).any fun row => row.status == .unsupported && row.admissionChecked && (row.sourceDiagnostic.map (·.name)) == some `solidity.functionDispatch

#guard (ViaIR.NominalGetters.funs.find? fun (_, f) => f.sourceDecl.any (·.name == "shade")).any fun (_, f) =>
  f.rets.any fun (n, t) => abiTyName f.widths n t == some "uint8"

#guard (ViaIR.NominalGetters.funs.find? fun (_, f) => f.sourceDecl.any (·.name == "owner")).any fun (_, f) =>
  f.rets.any fun (n, t) => abiTyName f.widths n t == some "address"

private def Legacy_invalidEnum : Prog Legacy.NominalGetters [] [] := sol[Legacy.NominalGetters]{
  shade = 3;
  try this.solcGetter8() returns (Shade value) { assert(false); }
  catch Panic(uint code) { assert(code == 0x21); } catch { assert(false); }
}
/-- An invalid typed storage enum triggers exactly Panic(0x21), not success or exhaustion. -/
theorem Legacy_enumPanic : (Prog.run (initial Legacy.NominalGetters) Legacy_invalidEnum).isOk = true := by
  apply fuelSuccess
  decide +kernel
#print axioms Legacy_enumPanic

private def ViaIR_invalidEnum : Prog ViaIR.NominalGetters [] [] := sol[ViaIR.NominalGetters]{
  shade = 3;
  try this.solcGetter8() returns (Shade value) { assert(false); }
  catch Panic(uint code) { assert(code == 0x21); } catch { assert(false); }
}
/-- An invalid typed storage enum triggers exactly Panic(0x21), not success or exhaustion. -/
theorem ViaIR_enumPanic : (Prog.run (initial ViaIR.NominalGetters) ViaIR_invalidEnum).isOk = true := by
  apply fuelSuccess
  decide +kernel
#print axioms ViaIR_enumPanic

solc_import "../solc/EntryPointsLeft.ast.json" hash 0xd3109a3bea2a97ae as Legacy.ContractKeyGetter testing

/-- A contract-valued mapping key remains a static address-ABI getter input. -/
theorem Legacy_ContractKeyGetter_positive : (Prog.run (initial Legacy.ContractKeyGetter) Legacy.ContractKeyGetter.positive).isOk = true := by
  apply fuelSuccess
  decide +kernel
#print axioms Legacy_ContractKeyGetter_positive

solc_import "../solc/EntryPointsLeft.viaIR.ast.json" hash 0xd282805b1d3ea697 as ViaIR.ContractKeyGetter testing

/-- A contract-valued mapping key remains a static address-ABI getter input. -/
theorem ViaIR_ContractKeyGetter_positive : (Prog.run (initial ViaIR.ContractKeyGetter) ViaIR.ContractKeyGetter.positive).isOk = true := by
  apply fuelSuccess
  decide +kernel
#print axioms ViaIR_ContractKeyGetter_positive

end Solidity.Tests.EntryPointsLeft
