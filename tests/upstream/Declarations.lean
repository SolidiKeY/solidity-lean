import Solidity.Tools.Upstream

/-! Declaration-lowering controls: local deletion uses the existing assignment
semantics, for every primitive type and typed state. No rule is added. -/
solc_import "../solc/DeclarationsLowering.ast.json" hash 0xf1c9786256bb1433
  as Imported.DeclarationsLowering testing
solc_import "../solc/DeclarationsLowering.ast.json" hash 0xf1c9786256bb1433
  as Imported.EffectfulImmutable testing

solc_import "../solc/DeclarationsLowering.ast.json" hash 0xf1c9786256bb1433
  as Imported.InvalidTransitive testing
solc_import "../solc/DeclarationsLowering.ast.json" hash 0xf1c9786256bb1433
  as Imported.DynamicDiscard testing

solc_import "../solc/DeclarationsLowering.ast.json" hash 0xf1c9786256bb1433
  as Imported.ModifierAdmission testing

solc_import "../solc/DeclarationsLowering.ast.json" hash 0xf1c9786256bb1433
  as Imported.ExcludedImmutable testing

solc_import "../solc/DeclarationsLowering.ast.json" hash 0xf1c9786256bb1433
  as Imported.InitSequence testing
solc_import "../solc/DeclarationsLoweringIR.ast.json" hash 0x93167cd6ec08cde8
  as Imported.IR.DeclarationsLowering testing
solc_import "../solc/DeclarationsLoweringIR.ast.json" hash 0x93167cd6ec08cde8
  as Imported.IR.EffectfulImmutable testing
solc_import "../solc/DeclarationsLoweringIR.ast.json" hash 0x93167cd6ec08cde8
  as Imported.IR.InitSequence testing
solc_import "../solc/DeclarationsLoweringIR.ast.json" hash 0x93167cd6ec08cde8
  as Imported.IR.ExcludedImmutable testing

solc_import "../solc/DeclarationsLowering.ast.json" hash 0xf1c9786256bb1433
  as Imported.ForwardImmutable testing
solc_import "../solc/DeclarationsLowering.ast.json" hash 0xf1c9786256bb1433
  as Imported.IndirectForwardImmutable testing
solc_import "../solc/DeclarationsLowering.ast.json" hash 0xf1c9786256bb1433
  as Imported.UnsupportedImmutable testing
solc_import "../solc/DeclarationsLoweringIR.ast.json" hash 0x93167cd6ec08cde8
  as Imported.IR.ForwardImmutable testing
solc_import "../solc/DeclarationsLoweringIR.ast.json" hash 0x93167cd6ec08cde8
  as Imported.IR.IndirectForwardImmutable testing
solc_import "../solc/DeclarationsLoweringIR.ast.json" hash 0x93167cd6ec08cde8
  as Imported.IR.UnsupportedImmutable testing

solc_import "../solc/DeclarationsLowering.ast.json" hash 0xf1c9786256bb1433
  as Imported.ForwardDerived testing
solc_import "../solc/DeclarationsLowering.ast.json" hash 0xf1c9786256bb1433
  as Imported.EntryDerived testing
solc_import "../solc/DeclarationsLoweringIR.ast.json" hash 0x93167cd6ec08cde8
  as Imported.IR.ForwardDerived testing
solc_import "../solc/DeclarationsLoweringIR.ast.json" hash 0x93167cd6ec08cde8
  as Imported.IR.EntryDerived testing

solc_import "../solc/DeclarationsLowering.ast.json" hash 0xf1c9786256bb1433
  as Imported.EffectfulForwardDerived testing
solc_import "../solc/DeclarationsLoweringIR.ast.json" hash 0x93167cd6ec08cde8
  as Imported.IR.EffectfulForwardDerived testing

solc_import "../solc/DeclarationsLowering.ast.json" hash 0xf1c9786256bb1433
  as Imported.ArgumentDerived testing
solc_import "../solc/DeclarationsLowering.ast.json" hash 0xf1c9786256bb1433
  as Imported.ImplicitPhaseDerived testing
solc_import "../solc/DeclarationsLoweringIR.ast.json" hash 0x93167cd6ec08cde8
  as Imported.IR.ArgumentDerived testing
solc_import "../solc/DeclarationsLoweringIR.ast.json" hash 0x93167cd6ec08cde8
  as Imported.IR.ImplicitPhaseDerived testing

solc_import "../solc/DeclarationsLowering.ast.json" hash 0xf1c9786256bb1433
  as Imported.StringArrayERC testing
solc_import "../solc/DeclarationsLoweringIR.ast.json" hash 0x93167cd6ec08cde8
  as Imported.IR.StringArrayERC testing

solc_import "../solc/DeclarationsLowering.ast.json" hash 0xf1c9786256bb1433
  as Imported.ImplicitUnsupportedInitialization testing
solc_import "../solc/DeclarationsLoweringIR.ast.json" hash 0x93167cd6ec08cde8
  as Imported.IR.ImplicitUnsupportedInitialization testing

namespace Solidity.Upstream.Declarations
open Solidity

private def zero {C : Contract} {Γ : Ctx} : (p : PrimTy) → Val C Γ p
  | .bool => .simple (.bool false)
  | .uint => .simple (.lit 0 rfl)
  | .int => .simple (.lit 0 rfl)

/-- The emitted local assignment writes exactly the Solidity default, retaining
all other state through the existing typed setLocal operation. -/
theorem deleteLocal_agrees {C : Contract} {Γ : Ctx} (p : PrimTy)
    (i : Idx Γ (.val p)) (σ : State C Γ) :
    TRun.assignLocal i (zero p) σ =
      .ok ⟨σ.setLocal i (PrimTy.dflt p), List.prefix_refl _⟩ := by
  cases p <;> rfl

/-- info: 'Solidity.Upstream.Declarations.deleteLocal_agrees' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms deleteLocal_agrees

private def C : Contract := contract!{
  uint stored; uint calls; uint[] values; bytes payload;
  function make() returns (uint) { return 5; }
  function valuesRef() returns (uint[] storage r) { calls++; r = values; }
}
private def observe {Γ : Ctx} (o : TRes (Out C [] Γ)) : Option Int :=
  (do let a ← o; pure (← Val.evalT a.st (.read (.root "stored" rfl))).1).toOption

/-- Deleting an unsigned local leaves its neighbors intact. -/
theorem unsigned : observe ((sol[C]{ uint x = 5; uint y = 6; delete x;
    stored = x + y; }).run (State.init C)) = some 6 := by decide +kernel

/-- The former value must not survive deletion. -/
theorem unsigned_negative : observe ((sol[C]{ uint x = 5; delete x;
    stored = x; }).run (State.init C)) ≠ some 5 := by decide +kernel

/-- Boolean and signed locals receive false and zero. -/
theorem other_types : observe ((sol[C]{ bool b = true; int x = -7;
    delete b; delete x; if (!b && x == 0) { stored = 1; }
  }).run (State.init C)) = some 1 := by decide +kernel

/-- A deleting index is evaluated once and clears only its selected element. -/
theorem indexed_delete : observe ((sol[C]{ values.push(5); values.push(6);
    uint i = 0; delete values[i++]; stored = i + values[0] + values[1];
  }).run (State.init C)) = some 7 := by decide +kernel

/-- An effectful storage receiver retains its single evaluation. -/
theorem receiver_delete : observe ((sol[C]{ values.push(5); delete valuesRef()[0];
    stored = calls + values[0];
  }).run (State.init C)) = some 1 := by decide +kernel

-- A value expression is not a deletable place.
#guard (elabProgS C [.delete (.num 5)]).toOption.isNone
#guard (elabProgS C [.delete (.binop .add (.num 1) (.num 2))]).toOption.isNone

private def member (receiver : String) : Lean.Json :=
  (Lean.Json.parse ("{\"nodeType\":\"MemberAccess\",\"expression\":" ++ receiver ++ "}")).toOption.getD .null

#guard (elabProgS C [.delete (.call "make" [])]).toOption.isNone
#guard (elabProgS C [.decl (.named "uint") "x" (some (.num 5)),
  .delete (.incDec .postInc (.name "x"))]).toOption.isNone

#guard (elabProgS C [.declStorage (.array (.named "uint")) "p" (some (.name "values")),
  .delete (.name "p")]).toOption.isNone

-- Only a lineage contract identity may skip a receiver evaluation.
#guard Frontend.isBaseMember [1] (member "{\"nodeType\":\"Identifier\",\"name\":\"Base\",\"referencedDeclaration\":1}")
#guard !Frontend.isBaseMember [1] (member "{\"nodeType\":\"Identifier\",\"name\":\"object\",\"referencedDeclaration\":2}")
#guard !Frontend.isBaseMember [1] (member "{\"nodeType\":\"FunctionCall\",\"referencedDeclaration\":1}")
#guard !Frontend.isBaseMember [1] (member "{\"nodeType\":\"IndexAccess\",\"referencedDeclaration\":1}")

private def sourceCheck (expected : String) (wrong : Bool := false) (ir : Bool := false) : IO Unit := do
  let text := "{\"vectors\":[" ++
    "{\"signature\":\"qualified()\",\"args\":[],\"failure\":false,\"expected\":[\"" ++
    (if wrong then "99" else "13") ++ "\"]}," ++
    "{\"signature\":\"qualified()\",\"args\":[],\"failure\":false,\"expected\":[\"14\"]}," ++
    "{\"signature\":\"signedLiteral()\",\"args\":[],\"failure\":false,\"expected\":[\"" ++
    toString ((2^256 : Int) - 7) ++ "\"]}," ++
    "{\"signature\":\"constantKinds()\",\"args\":[],\"failure\":false,\"expected\":[\"1\"]}," ++
    "{\"signature\":\"shadow()\",\"args\":[],\"failure\":false,\"expected\":[\"3\"]}]}"
  let .ok data := Lean.Json.parse text | throw (IO.userError "bad control JSON")
  let result := Tools.Upstream.replay
    (if ir then Imported.IR.DeclarationsLowering else Imported.DeclarationsLowering)
    (if ir then Imported.IR.DeclarationsLowering.report else Imported.DeclarationsLowering.report) data
  unless (result.getObjValAs? String "status").toOption == some expected do
    throw (IO.userError result.pretty)

#eval sourceCheck "working"
#eval sourceCheck "broken" true
#eval sourceCheck "working" false true
#eval sourceCheck "broken" true true
private def immutableCheck (wrong : Bool := false) (ir : Bool := false) : IO Unit := do
  let text := "{\"vectors\":[" ++
    "{\"signature\":\"value()\",\"args\":[],\"failure\":false,\"expected\":[\"2\"]}," ++
    "{\"signature\":\"count()\",\"args\":[],\"failure\":false,\"expected\":[\"" ++
    (if wrong then "0" else "1") ++ "\"]}," ++
    "{\"signature\":\"value()\",\"args\":[],\"failure\":false,\"expected\":[\"2\"]}," ++
    "{\"signature\":\"count()\",\"args\":[],\"failure\":false,\"expected\":[\"1\"]}]}"
  let .ok data := Lean.Json.parse text | throw (IO.userError "bad immutable control JSON")
  let result := Tools.Upstream.replay
    (if ir then Imported.IR.EffectfulImmutable else Imported.EffectfulImmutable)
    (if ir then Imported.IR.EffectfulImmutable.report else Imported.EffectfulImmutable.report) data
  unless (result.getObjValAs? String "status").toOption == some (if wrong then "broken" else "working") do
    throw (IO.userError result.pretty)

#eval immutableCheck
#eval immutableCheck true
#eval immutableCheck false true
#eval immutableCheck true true
#guard (Imported.ExcludedImmutable.report.find? (·.sourceSignature == "constructor()")).any
  (fun row => row.status == .excluded)
#guard (Imported.IR.ExcludedImmutable.report.find? (·.sourceSignature == "constructor()")).any
  (fun row => row.status == .excluded)

private def sequenceCheck (wrong : Bool := false) (ir : Bool := false) : IO Unit := do
  let text := "{\"vectors\":[{\"signature\":\"get()\",\"args\":[],\"failure\":false,\"expected\":[\"" ++
    (if wrong then "253" else "255") ++ "\"]}]}"
  let .ok data := Lean.Json.parse text | throw (IO.userError "bad sequence control JSON")
  let result := Tools.Upstream.replay
    (if ir then Imported.IR.InitSequence else Imported.InitSequence)
    (if ir then Imported.IR.InitSequence.report else Imported.InitSequence.report) data
  unless (result.getObjValAs? String "status").toOption == some (if wrong then "broken" else "working") do
    throw (IO.userError result.pretty)

#eval sequenceCheck
#eval sequenceCheck true
#eval sequenceCheck false true
#eval sequenceCheck true true

#guard (Imported.InvalidTransitive.report.find? (·.sourceSignature == "value()")).any
  (fun row => row.status != .elaborated)
#guard (Imported.DynamicDiscard.report.find? (·.sourceSignature == "value()")).any
  (fun row => row.status != .elaborated)

#guard (Imported.ModifierAdmission.report.find? (·.sourceSignature == "value()")).any
  (fun row => row.status != .elaborated)


private def forwardCheck (wrong : Bool := false) (ir : Bool := false) : IO Unit := do
  let text := "{\"vectors\":[{\"signature\":\"observed()\",\"args\":[],\"failure\":false,\"expected\":[\"" ++
    (if wrong then "2" else "0") ++ "\",\"2\"]}]}"
  let .ok data := Lean.Json.parse text | throw (IO.userError "bad forward control JSON")
  let result := Tools.Upstream.replay
    (if ir then Imported.IR.ForwardImmutable else Imported.ForwardImmutable)
    (if ir then Imported.IR.ForwardImmutable.report else Imported.ForwardImmutable.report) data
  unless (result.getObjValAs? String "status").toOption == some (if wrong then "broken" else "working") do
    throw (IO.userError result.pretty)
#eval forwardCheck
#eval forwardCheck true
#eval forwardCheck false true
#eval forwardCheck true true
#guard (Imported.IndirectForwardImmutable.report.find? (·.sourceSignature == "constructor()")).any
  (fun row => row.status != .elaborated)
#guard (Imported.IR.IndirectForwardImmutable.report.find? (·.sourceSignature == "constructor()")).any
  (fun row => row.status != .elaborated)


private def entriesCheck (wrong : Bool := false) (ir : Bool := false) : IO Unit := do
  let text := "{\"vectors\":[{\"signature\":\"chosen()\",\"args\":[],\"failure\":false,\"expected\":[\"" ++
    (if wrong then "1" else "2") ++ "\"]},{\"signature\":\"inherited()\",\"args\":[],\"failure\":false,\"expected\":[\"3\"]}]}"
  let .ok data := Lean.Json.parse text | throw (IO.userError "bad entry control JSON")
  let result := Tools.Upstream.replay
    (if ir then Imported.IR.EntryDerived else Imported.EntryDerived)
    (if ir then Imported.IR.EntryDerived.report else Imported.EntryDerived.report) data
  unless (result.getObjValAs? String "status").toOption == some (if wrong then "broken" else "working") do
    throw (IO.userError result.pretty)
#eval entriesCheck
#eval entriesCheck true
#eval entriesCheck false true
#eval entriesCheck true true
#guard (Imported.ForwardDerived.report.find? (·.sourceSignature == "constructor()")).any
  (fun row => row.status == .elaborated)
#guard !(Imported.EntryDerived.report.any (·.sourceSignature == "hidden()"))
#guard (Imported.EntryDerived.report.filter (·.sourceSignature == "chosen()")).length == 1
#guard (Imported.IR.ForwardDerived.report.find? (·.sourceSignature == "constructor()")).any
  (fun row => row.status == .elaborated)
#guard !(Imported.IR.EntryDerived.report.any (·.sourceSignature == "hidden()"))
#guard (Imported.IR.EntryDerived.report.filter (·.sourceSignature == "chosen()")).length == 1

#guard (Imported.EffectfulForwardDerived.report.find? (·.sourceSignature == "constructor()")).any
  (fun row => row.status == .elaborated)
#guard (Imported.IR.EffectfulForwardDerived.report.find? (·.sourceSignature == "constructor()")).any
  (fun row => row.status == .elaborated)


-- The compiler's legacy initialization order differs from viaIR for these
-- inherited-construction probes. Pin each mode, and reject a false observation.
private def phaseCheck (which : Nat) (wrong : Bool := false) (ir : Bool := false) : IO Unit := do
  let model := if ir then
    match which with
    | 0 => Imported.IR.ForwardDerived
    | 1 => Imported.IR.EffectfulForwardDerived
    | 2 => Imported.IR.ArgumentDerived
    | _ => Imported.IR.ImplicitPhaseDerived
    else match which with
    | 0 => Imported.ForwardDerived
    | 1 => Imported.EffectfulForwardDerived
    | 2 => Imported.ArgumentDerived
    | _ => Imported.ImplicitPhaseDerived
  let report := if ir then
    match which with
    | 0 => Imported.IR.ForwardDerived.report
    | 1 => Imported.IR.EffectfulForwardDerived.report
    | 2 => Imported.IR.ArgumentDerived.report
    | _ => Imported.IR.ImplicitPhaseDerived.report
    else match which with
    | 0 => Imported.ForwardDerived.report
    | 1 => Imported.EffectfulForwardDerived.report
    | 2 => Imported.ArgumentDerived.report
    | _ => Imported.ImplicitPhaseDerived.report
  let expected := if wrong then "99" else if which == 3 then "5" else if ir then "0" else "2"
  let text := "{\"vectors\":[{\"signature\":\"observed()\",\"args\":[],\"failure\":false,\"expected\":[\"" ++
    expected ++ "\"]}]}"
  let .ok data := Lean.Json.parse text | throw (IO.userError "bad phase control JSON")
  let result := Tools.Upstream.replay model report data
  unless (result.getObjValAs? String "status").toOption == some (if wrong then "broken" else "working") do
    throw (IO.userError result.pretty)
#eval for which in [:4] do
  phaseCheck which
  phaseCheck which true
  phaseCheck which false true
  phaseCheck which true true


-- A bytes buffer must still require an explicit string conversion.
#guard (elabProgS C [.decl (.named "uint") "result"
  (some (.call "erc7201" [.name "payload"]))]).toOption.isNone
private def stringArrayCheck (wrong : Bool := false) (ir : Bool := false) : IO Unit := do
  let text := "{\"vectors\":[{\"signature\":\"test()\",\"args\":[],\"failure\":false,\"expected\":[\"" ++
    (if wrong then "0" else "1") ++ "\"]}]}"
  let .ok data := Lean.Json.parse text | throw (IO.userError "bad string control JSON")
  let result := Tools.Upstream.replay
    (if ir then Imported.IR.StringArrayERC else Imported.StringArrayERC)
    (if ir then Imported.IR.StringArrayERC.report else Imported.StringArrayERC.report) data
  unless (result.getObjValAs? String "status").toOption == some (if wrong then "broken" else "working") do
    throw (IO.userError result.pretty)
#eval stringArrayCheck
#eval stringArrayCheck true
#eval stringArrayCheck false true
#eval stringArrayCheck true true

#guard (Imported.ImplicitUnsupportedInitialization.report.find? (·.sourceSignature == "constructor()")).any
  (fun row => row.status == .excluded)
#guard (Imported.IR.ImplicitUnsupportedInitialization.report.find? (·.sourceSignature == "constructor()")).any
  (fun row => row.status == .excluded)

#guard (Imported.ImplicitUnsupportedInitialization.report.find? (·.sourceSignature == "observed()")).any
  (fun row => row.status == .elaborated)
#guard (Imported.IR.ImplicitUnsupportedInitialization.report.find? (·.sourceSignature == "observed()")).any
  (fun row => row.status == .elaborated)

private def implicitRefusalCheck (ir : Bool := false) : IO Unit := do
  let .ok data := Lean.Json.parse
    "{\"vectors\":[{\"signature\":\"observed()\",\"args\":[],\"failure\":false,\"expected\":[\"7\"]}]}"
    | throw (IO.userError "bad implicit refusal control JSON")
  let result := Tools.Upstream.replay
    (if ir then Imported.IR.ImplicitUnsupportedInitialization else Imported.ImplicitUnsupportedInitialization)
    (if ir then Imported.IR.ImplicitUnsupportedInitialization.report else Imported.ImplicitUnsupportedInitialization.report) data
  unless (result.getObjValAs? String "status").toOption == some "broken" do
    throw (IO.userError result.pretty)
#eval implicitRefusalCheck
#eval implicitRefusalCheck true


-- Callback classification is metadata, not execution of an unavailable host.
#eval do
  let text ← IO.FS.readFile "tests/solc/DeclarationsLoweringIR.ast.json"
  let j ← IO.ofExcept (Lean.Json.parse text)
  let ast ← IO.ofExcept (j.getObjVal? "ast")
  let callback : Frontend.SolcContract ← IO.ofExcept (Frontend.readContract ast "InitializerCallback" [] true (viaIR := true))
  unless callback.ctor.any (fun (f : Frontend.SolcFun) => f.writingCall) do
    throw (IO.userError "implicit initializer lost callback reading")
  let purePhase : Frontend.SolcContract ← IO.ofExcept (Frontend.readContract ast "ImplicitPhaseDerived" [] true (viaIR := true))
  unless purePhase.ctor.any (fun (f : Frontend.SolcFun) => !f.writingCall) do
    throw (IO.userError "pure implicit phase incorrectly marked as callback-capable")

end Solidity.Upstream.Declarations

-- Contract-valued roots are retained as address roots by the combined importer.
-- Their unread immutable initializer must still execute its increment.
private def immutableEffectCheck (wrong : Bool := false) (ir : Bool := false) : IO Unit := do
  let text := "{\"vectors\":[{\"signature\":\"observed()\",\"args\":[],\"failure\":false,\"expected\":[\"" ++
    (if wrong then "0" else "1") ++ "\"]}]}"
  let .ok data := Lean.Json.parse text | throw (IO.userError "bad immutable control JSON")
  let result := Solidity.Tools.Upstream.replay
    (if ir then Imported.IR.UnsupportedImmutable else Imported.UnsupportedImmutable)
    (if ir then Imported.IR.UnsupportedImmutable.report else Imported.UnsupportedImmutable.report) data
  unless (result.getObjValAs? String "status").toOption == some (if wrong then "broken" else "working") do
    throw (IO.userError result.pretty)
#eval immutableEffectCheck
#eval immutableEffectCheck true
#eval immutableEffectCheck false true
#eval immutableEffectCheck true true
