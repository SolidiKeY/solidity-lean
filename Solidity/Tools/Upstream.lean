import Solidity.Frontend.Import
import Solidity.Tools.Run
import Solidity.Semantics.RunFuel
import Solidity.Semantics.RevertMemory
import Solidity.Tools.EntryReturn
import Solidity.Tools.CreationTryReplay
import Solidity.Tools.LibraryTryReplay

/-!
# Replay upstream typed ABI semantic vectors

The JavaScript adapter retains Solidity's native fixture bytes and supplies
checked scalar arguments or typed ABI input bytes. This command imports each contract through `solc_import`, then
executes the vectors in order on the typed interpreter, retaining storage and
rolling back failed calls. It reports observations, not proofs. Unsupported
vectors, import gaps and exhausted loop fuel cannot count as passing tests.
-/

namespace Solidity.Tools.Upstream

open Lean Elab Command Meta Frontend

private def str (s : String) : Json := toJson s
private def result (status reason : String) (extra : List (String × Json) := []) : Json :=
  Json.mkObj ([("status", str status), ("reason", str reason)] ++ extra)

/-- Resource failures remain inconclusive even when an importer embeds the
exception text in a per-function row rather than throwing it. -/
def resourceLimited (reason : String) : Bool :=
  ["heartbeats", "maximum recursion", "out of memory"].any fun text =>
    (reason.toLower.splitOn text).length > 1

/-- Preserve all importer diagnostics; an earlier warning cannot hide a
later resource failure. This result never certifies a runtime observation. -/
def diagnosticFailure (messages : List String) : Json :=
  result (if messages.any resourceLimited then "blocked" else "broken")
    ("\n".intercalate messages)

private def argument (j : Json) : Except String RawExpr := do
  let value ← j.getStr?
  if value == "true" then return .bool true
  if value == "false" then return .bool false
  let some n := value.toInt? | throw s!"invalid scalar argument {value}"
  return if n < 0 then .unop .neg (.num n.natAbs) else .num n.toNat

private def word : Semantics.CallValue → Except String String
  | .uint n => pure (toString n.1)
  | .int n => pure (toString (n.1 % (2^256 : Int)))
  | .bool b => pure (if b then "1" else "0")

/-- Resolve source ABI entries by exact canonical signature and compiler identity.
No source-local helper, retained override or special entry is a fallback target.
The row-only path supports native (non-source) replay controls. -/
def resolveEntry (C : Contract) (rows : List ImportRow) (signature : String) : Except String String := do
  let source := C.funs.any fun (_, f) => f.sourceDecl.isSome
  let candidates := if source then C.funs.filterMap fun (name, f) => do
      let identity ← f.sourceDecl
      guard (identity.declaration.isSome && identity.externalEntry &&
        identity.signature == some signature)
      pure name
    else
      let canonical (s : String) := match s.splitOn "(" with
        | [name, args] => name ++ "(" ++
          ((args.replace "uint256" "uint").replace "int256" "int").replace "address payable" "address"
        | _ => s
      rows.filterMap fun r =>
        if canonical r.sourceSignature == canonical signature &&
            (Semantics.lookupBy r.name C.funs).isSome then some r.name else none
  match candidates with
  | [name] => pure name
  | [] => throw s!"no imported ABI entry for {signature}"
  | _ => throw s!"ambiguous imported ABI entry for {signature}"

/-- ABI bounds retained by the source reader, including enum membership.
The JavaScript adapter separately checks canonical word widths. -/
private def inRanges (row : ImportRow) (vector : Json) : Bool := Id.run do
  if row.paramRanges.isEmpty then return true
  let .ok args := vector.getObjValAs? (List String) "args" | return false
  if args.length != row.params.length then return false
  let values := row.params.zip args
  return row.paramRanges.all fun (name, lo, hi) =>
    (values.find? fun ((param, _), _) => param == name).any fun (_, value) =>
      value.toInt?.any fun n => lo ≤ n && n ≤ hi

/-- External entry reading: retain actual failure data, but keep the supplied
transaction environment. In particular this is not a self-call. Existing
indexed guards generate concrete bytes before execution; no outcome is used
to choose a panic code. Call arguments here are ABI-decoded locals or checked
scalar literals; arbitrary effectful top-level argument expressions are outside
this adapter. Ordinary calculus entry points remain unchanged. -/
def entryProgParts (C : Contract) (pre body post : List RawStmt)
    (encoded : Option (String × EntryReturn.Plan) := none) : Except String (Blk C []) := do
  let all := pre ++ body ++ post
  let k := RawStmt.maxIdxs all + 1
  let ss ← freshenBlocks (C.vars.map (·.1)) [] all
  unless ss.length == all.length do throw "entry statement boundaries changed during freshening"
  let action : ElabM (SProg C) := do
    let funs ← match encoded with
      | none => pure C.funs
      | some (f, plan) => EntryReturn.scope C f plan
    withReader (fun sc => { sc with funs }) do
      let P ← elabStmtsP C (ss.take pre.length)
      let Q ← withReader (fun sc => { sc with retainFailureData := true }) do
        let source := (ss.drop pre.length).take body.length
        match encoded, source with
        | some _, [.declMemory T x (some e)] =>
          -- The synthetic name lives only in this elaboration scope. Hoisting
          -- resolves it there and supplies the actual typed memory result;
          -- the ordinary declaration then checks that result's exact shape.
          let (P, value) ← hoist C e
          pure (P ++ (← elabStmtsP C [.declMemory T x (some value)]))
        | _, _ => elabStmtsP C source
      let R ← elabStmtsP C (ss.drop (pre.length + body.length))
      pure (P ++ Q ++ R)
  let P ← action.runFrom' { funs := C.funs } ([], k)
  SProg.chain [] [] P

/-- Observe only source execution; ABI preparation and serialization retain
ordinary decoder/encoder semantics, including their failure policy. -/
def entryProg (C : Contract) (ss : List RawStmt) : Except String (Blk C []) :=
  entryProgParts C [] ss []

/-- A failed generated guard emits exactly its own bytes, independent of the
fixture's expectation and without evaluating a source body. -/
theorem entryGuard_failed {C : Contract} {Γ : Ctx} (code fuel : Nat)
    (g : Val C Γ .bool) (σ : State C Γ) (h : g.evalT σ = .ok false) :
    (panicStmt code g).runF fuel σ =
      .error (THalt.ofData (Semantics.encodePanic code)) := by
  simp [panicStmt, Stmt.runF, TRun.ite, h, boolT, TRun.seq,
    TRun.revertData, RevPart.evalT]
  rfl

/-- A successful guard preserves the entire typed state, including the
transaction environment, heap, storage and ledger. -/
theorem entryGuard_success {C : Contract} {Γ : Ctx} (code fuel : Nat)
    (g : Val C Γ .bool) (σ : State C Γ) (h : g.evalT σ = .ok true) :
    (panicStmt code g).runF fuel σ = .ok ⟨σ, List.prefix_refl _⟩ := by
  simp only [panicStmt, Stmt.runF, TRun.ite, h, boolT, TRun.nil]
  rfl

/-- Evaluating a guard can itself fail; that earlier failure is forwarded,
not replaced by the guard's panic code. -/
theorem entryGuard_prior {C : Contract} {Γ : Ctx} (code fuel : Nat)
    (g : Val C Γ .bool) (σ : State C Γ) (e : THalt) (h : g.evalT σ = .error e) :
    (panicStmt code g).runF fuel σ = .error e := by
  simp [panicStmt, Stmt.runF, TRun.ite, h]
  rfl

namespace ABI
open Semantics
private def dataName := "__upstream_data"
private def outputName := "__upstream_output"
private def argName (i : Nat) := s!"__upstream_argument{i}"
private def retName (i : Nat) := s!"__upstream_return{i}"

def shape : Nat → Ty → List (String × Nat) → String → Except String String
  | 0, _, _, _ => throw "ABI schema depth budget exhausted"
  | fuel + 1, T, ws, key => do
    match T with
    | .prim p =>
      if (lookupBy (key ++ "#enum") ws).isSome then throw "nominal enum ABI range needs a declaration adapter"
      if let some fn := fnRow? ws key then
        let some (_, _, external) := fnParts? fn | throw "invalid function ABI metadata"
        if external then return "function" else throw "internal function has no ABI value"
      match AbiKind.ofValue p ws key with
      | .uint n => return if (lookupBy (key ++ "#address") ws).isSome then "address" else s!"uint{n}"
      | .int n => return s!"int{n}"
      | .bool => return "bool"
      | .bytesN n => return s!"bytes{n}"
      | _ => throw "invalid primitive ABI kind"
    | .ref (.array T) =>
      if lookupBy (key ++ "[]#bytes") ws == some 1 then
        return if (lookupBy (key ++ "#string") ws).isSome then "string" else "bytes"
      return (← shape fuel T ws (key ++ "[]")) ++ "[]"
    | .ref (.fixed T n) => return (← shape fuel T ws (key ++ "[]")) ++ s!"[{n}]"
    | .ref (.struct s) =>
      let parts ← (structDef s).mapM fun (f,T) => shape fuel T (structWidths s) f
      return "(" ++ String.intercalate "," parts ++ ")"
    | .ref (.mapping ..) => throw "mapping has no ABI encoding"

private def typeExpr : RawTy → Except String RawExpr
  | .named s => pure (.name s)
  | .array T => do
    let e ← typeExpr T
    pure (match e with
      | .name s => .name (s ++ "[]")
      | _ => .call "#abiArrayType" [e])
  | .fixed T n => return .index (← typeExpr T) (.num n)
  | .mapping .. => throw "mapping is not an ABI type"

def needsCanonical (d : FunDecl) : Bool :=
  d.params.any fun (x,T) => !(T matches .prim _) || (fnRow? d.widths x).isSome

def validate (d : FunDecl) (inputs outputs : List String) : Except String Unit := do
  let actualInputs ← d.params.mapM fun (x,T) => shape 128 T d.widths x
  let actualOutputs ← d.rets.mapM fun (x,T) => shape 128 T d.widths x
  unless actualInputs == inputs && actualOutputs == outputs do
    throw s!"ABI schema disagrees with admitted declarations: {actualInputs} -> {actualOutputs}"

/-- Build both the canonical input probe and the once-only source execution from
existing typed ABI operations. Source calls retain their ordinary admission. -/
def program (C : Contract) (d : FunDecl) (f : String) (ctor probe : Bool)
    (bytes : List Nat) : Except String (Blk C []) := do
  if bytes.any (· >= 256) then throw "invalid calldata byte"
  let reserved := [dataName, outputName] ++ (List.range d.params.length).map argName ++
    (List.range d.rets.length).map retName
  if C.vars.any (fun (x, _) => reserved.contains x) then throw "reserved ABI observer name collision"
  if C.funs.any (fun (x, _) => [bytesLitName, abiDecodeName, "abi.encode"].contains x) then
    throw "reserved ABI builtin name collision"
  let ts ← d.params.mapM fun (x,T) => typeExpr (abiRawTy T d.widths x)
  let (_, decode) := abiDecodeHeads C dataName ts
  let declarations ← d.params.zipIdx.mapM fun ((x,T),i) => do
    let raw := abiRawTy T d.widths x
    match T with
    | .prim _ => pure (RawStmt.decl raw (argName i) (some (decode i)))
    | .ref _ =>
      if lookupBy x d.paramLocs == some .storage then throw "storage parameter is not an ABI value"
      pure (RawStmt.declMemory raw (argName i) (some (decode i)))
  let args := (List.range d.params.length).map fun i => RawExpr.name (argName i)
  let call := RawExpr.call f args
  -- Serialize the actual source return frame inside a single-memory-result
  -- call. The observer takes these bytes directly: no outer ABI envelope.
  if !probe && !ctor && d.rets.length > 1 && d.rets.any (fun (_, T) => T matches .ref _) then
    return ← entryProgParts C
      ([.declMemory (.named "bytes") dataName (some (.bytesLit bytes))] ++ declarations)
      [.declMemory (.named "bytes") outputName
        (some (.call EntryReturn.wrapperName args))] [] (some (f, .memory))
  if !probe && !ctor && d.rets.length > 1 &&
      d.rets.any (fun (n, _) => (fnRow? d.widths n).isSome) then
    return ← entryProgParts C
      ([.declMemory (.named "bytes") dataName (some (.bytesLit bytes))] ++ declarations)
      [.declMemory (.named "bytes") outputName
        (some (.call EntryReturn.wrapperName args))] [] (some (f, .functionTuple))
  let captures ← if probe then pure [] else if ctor then pure (if C.ctor.isNone && C.inits.isEmpty && args.isEmpty then [] else [RawStmt.call (.name "constructor") args])
    else if d.rets.length == 1 then do
      let [(x,T)] := d.rets | throw "single return shape mismatch"
      let raw := abiRawTy T d.widths x
      pure [match T with
        | .prim _ => RawStmt.decl raw (retName 0) (some call)
        | .ref _ => if d.retStorage then RawStmt.declStorage raw (retName 0) (some call)
          else RawStmt.declMemory raw (retName 0) (some call)]
    else if d.rets.isEmpty then pure [RawStmt.call (.name f) args]
    else do
      let targets ← d.rets.zipIdx.mapM fun ((x,T),i) => match T with
        | .prim _ => pure (some (abiRawTy T d.widths x, retName i))
        | .ref _ => throw "multiple reference returns need a typed return adapter"
      pure [RawStmt.tupleDecl targets call]
  let returns := if probe then args else
    (List.range d.rets.length).map fun i => RawExpr.name (retName i)
  entryProgParts C ([.declMemory (.named "bytes") dataName (some (.bytesLit bytes))] ++ declarations)
    captures [.declMemory (.named "bytes") outputName (some (.call "abi.encode" returns))]

private def findBytes (x : Var) : (Γ : Ctx) → List Var → Option (Idx Γ (.mem bytesR))
  | [], _ => none
  | t :: Γ, n :: ns =>
    if n == x then match t with
      | .mem (.array (.prim .uint)) => some .here
      | _ => none
    else (findBytes x Γ ns).map Idx.there
  | _ :: _, [] => none

def readBytes {C : Contract} {Γ : Ctx} (σ : State C Γ)
    (i : Idx Γ (.mem bytesR)) : Except String (List Nat) := do
  let .ok bs := (RevPart.mem .raw i).evalT σ | throw "unset ABI output bytes"
  pure (bs.map UInt8.toNat)

theorem readBytes_exact {C : Contract} {Γ : Ctx} (σ : State C Γ)
    (i : Idx Γ (.mem bytesR)) (r : HRef σ.H bytesR)
    (h : TEnv.get i σ.env = some r) :
    readBytes σ i = .ok (((σ.heap.get r).1.map (fun v => UInt8.ofNat v.val.toNat)).map UInt8.toNat) := by
  simp only [readBytes, RevPart.evalT_mem σ .raw i r h]
  rfl

def output {C : Contract} {Γ : Ctx} (σ : State C Γ) (names : List Var) : Except String (List Nat) := do
  let some i := findBytes (.user outputName) Γ names | throw "missing typed ABI output local"
  readBytes σ i

def canonical (C : Contract) (d : FunDecl) (f : String) (bytes : List Nat)
    (σ : State C []) (force : Bool := false) : Except String Unit := do
  if !force && !needsCanonical d then return ()
  let ⟨_,Q⟩ ← program C d f false true bytes
  let .ok o := Q.runF 1000 σ | throw "calldata requires lazy/noncanonical ABI decoder replay"
  let encoded ← output o.st (Q.outNames [])
  -- External ABI entry permits trailing data. In this adapter raw calldata
  -- observations (msg.data/assembly/host operations) are refused separately;
  -- only the declared argument objects are available to the source body.
  unless encoded == bytes.take encoded.length do
    throw "noncanonical calldata requires lazy ABI decoder replay"

end ABI

/-- Typed host-context validation, separate from runtime JSON/decimal parsing.
No value outside the nonzero 160-bit deployment domain can reach the cast. -/
def selfTryContextValid (kind : String) (address : Nat) : Bool :=
  kind == "direct-self-try" && decide (address ≠ 0 ∧ address < 2^160)

/-- Replay complete supported vector sequences. Fuel exhaustion is inconclusive. -/
def replay (C : Contract) (rows : List ImportRow) (data : Json) : Json := Id.run do
  let bad := rows.filter fun r => r.status != .elaborated && r.status != .skipped
  if !bad.isEmpty then
    return result (if bad.any (resourceLimited ∘ ImportRow.reason) then "blocked" else "broken") "frontend import gaps" [("gaps", toJson (bad.map fun r =>
      Json.mkObj [("function", str r.sourceSignature), ("status", str r.status.toStr),
        ("reason", str r.reason)]))]
  if let .ok reason := data.getObjValAs? String "blocked" then
    return result "blocked" reason
  let .ok vectors := data.getObjValAs? (Array Json) "vectors"
    | return result "blocked" "missing execution vectors"
  if vectors.isEmpty then return result "blocked" "no execution vectors"
  if (data.getObjValAs? Bool "requiresSelfContext").toOption == some true &&
      !(data.getObjVal? "hostContext").isOk then
    return result "blocked" "missing self-try deployment context"
  let selfContext : Option Nat := if (data.getObjVal? "hostContext").isOk then do
    let host ← (data.getObjVal? "hostContext").toOption
    let kind ← (host.getObjValAs? String "kind").toOption
    let address ← (host.getObjValAs? String "selfAddress").toOption
    let n ← address.toNat?
    if selfTryContextValid kind n then some n else none
  else some 0
  let some selfAddress := selfContext | return result "blocked" "invalid self-try deployment context"
  let tx : TTx :=
    { msgSender := PrimTy.ofIntD .uint 103164821458651970696730694074090566015747358738
      selfAddress := PrimTy.ofIntD .uint (Int.ofNat selfAddress) }
  let mut state := State.deploy C tx
  let mut deployed := false
  let mut deploymentFailed := false
  let mut observed : Array Json := #[]
  let contextEvidence : List (String × Json) := if (data.getObjVal? "hostContext").isOk then
    [("selfAddress", toJson (toString selfAddress))] else []
  for vector in vectors do
    let stopped (status reason : String) (extra : List (String × Json) := []) :=
      result status reason (contextEvidence ++ (("observed", toJson observed) :: extra))
    if deploymentFailed then return stopped "blocked" "calls after failed deployment need the upstream empty-code host"
    let .ok signature := vector.getObjValAs? String "signature"
      | return stopped "blocked" "missing signature"
    let raw := (vector.getObjVal? "calldata").isOk
    let argsResult := if raw then .ok [] else
      (vector.getObjValAs? (Array Json) "args").bind fun xs => xs.toList.mapM argument
    let .ok args := argsResult
      | return stopped "blocked" "unsupported scalar argument"
    let ctor := signature == "constructor"
    if !deployed && !ctor then
      let .ok ⟨_, Q⟩ := entryProg C (if C.ctor.isNone && C.inits.isEmpty then [] else [.call (.name "constructor") []])
        | return stopped "broken" "default deployment does not elaborate"
      match Prog.runF 1000 Q state with
      | .error .diverge | .error .exhausted =>
        return stopped "blocked" "deployment exhausted loop fuel/resources"
      | .error _ => return stopped "broken" "unexpected default deployment failure"
      | .ok o => state := o.st.glob
      deployed := true
    let resolved := resolveEntry C rows signature
    let function := resolved.toOption
    let declaration := if ctor then C.ctor else function.bind (Semantics.lookupBy · C.funs)
    if !ctor then state := state.transactionEntry
    if !raw then
      if let some declaration := declaration then
        for ((parameter, _), arg) in declaration.params.zip args do
          if (Semantics.lookupBy (parameter ++ "#address") declaration.widths).isSome then
            let some value := arg.litVal?
              | return stopped "blocked" "non-scalar address ABI argument"
            unless 0 ≤ value && value < 2^160 do
              return stopped "blocked" "noncanonical address ABI argument"
    let rawProgram : Except String (Blk C []) := do
      -- Source enum cardinality may be narrower than its erased ABI uint.
      -- Primitive ranges have byte widths; other nominal ranges need a decoder adapter.
      let row : Option ImportRow := if ctor then rows.find? (·.sourceName == "constructor") else
        function.bind fun name => rows.find? (·.name == name)
      if row.any (fun (r : ImportRow) => (r.paramRanges ++ r.elemRanges.map (fun (entry : String × Int × Int × Option Nat) => (entry.1, entry.2.1, entry.2.2.1))).any fun (_, lo, hi) =>
          !(List.range 32).any fun k =>
            let bits := 8 * (k + 1)
            (lo == 0 && hi == (2^bits : Int) - 1) ||
              (lo == -(2^(bits - 1) : Int) && hi == (2^(bits - 1) : Int) - 1)) then
        throw "nominal enum ABI range needs a declaration adapter"
      let bytes ← vector.getObjValAs? (List Nat) "calldata"
      let inputs ← vector.getObjValAs? (List String) "inputTypes"
      let outputs ← vector.getObjValAs? (List String) "outputTypes"
      let d ← if ctor then pure (C.ctor.getD { params := [], body := [] }) else do
        let some f := function | throw "missing unique source ABI declaration"
        let some d := Semantics.lookupBy f C.funs | throw "missing source ABI function"
        pure d
      ABI.validate d inputs outputs
      let canonicalOnly ← match vector.getObjVal? "canonicalOnly" with
        | .error _ => pure false
        | .ok j => fromJson? j
      ABI.canonical C d (function.getD "constructor") bytes state canonicalOnly
      ABI.program C d (function.getD "constructor") ctor false bytes
    if raw then
      if let .error reason := rawProgram then return stopped "blocked" reason
    let program := if raw then rawProgram else if ctor then entryProg C (if C.ctor.isNone && C.inits.isEmpty && args.isEmpty then [] else [.call (.name "constructor") args]) else do
      let name ← resolved
      entryProg C [← runStmt C name args]
    if let .error reason := program then
      return stopped "broken" s!"call does not elaborate: {signature}: {reason}"
    let .ok ⟨_, Q⟩ := program
      | return stopped "blocked" "missing call program"
    let before := state
    let rangeRow : Option ImportRow := if ctor then rows.find? (·.sourceName == "constructor") else
        function.bind fun name => rows.find? (·.name == name)
    let badRange := !raw && rangeRow.any (fun row => !inRanges row vector)
    let outcome := if badRange then .error .revert else if ctor && !((C.ctor.map (·.payable)).getD false) && state.tx.msgValue.1 != 0
      then .error .revert else Prog.runF 1000 Q state
    let actual : Except String (Bool × List String × List Nat × List Nat) := do
      match outcome with
      | .error .diverge => throw "execution exhausted loop fuel"
      | .error .exhausted =>
        throw "execution reached a model resource bound (including recursive unrolling); not an EVM failure"
      | .error .revert => pure (true, [], [], [])
      | .error (.revertWith bytes) =>
        pure (true, [], bytes.map UInt8.toNat, [])
      | .error .panic =>
        throw "generic model panic does not retain the ABI panic code"
      | .ok o =>
        if raw then return (false, [], [], ← ABI.output o.st (Q.outNames []))
        let vals := localVals (Q.outNames []) o.st.env
        let count := if ctor then 0 else
          ((function.bind fun f => Semantics.lookupBy f C.funs).map (·.rets.length)).getD 0
        let values ← (List.range count).mapM fun i => do
          let name := if count == 1 then retLocal else s!"{retLocal}{i}"
          let some value := Semantics.lookupBy (Var.ofName name) vals
            | throw s!"missing returned scalar {name}"
          word value
        pure (false, values, [], [])
    let .ok (failed, values, bytes, returned) := actual
      | return stopped "blocked" (match actual with
          | .error reason => reason
          | .ok _ => "unsupported execution outcome")
          [("inconclusiveVector", vector), ("blockedVector", vector)]
    observed := observed.push (Json.mkObj ([("signature", str signature),
      ("failed", toJson failed), ("values", toJson values), ("revertBytes", toJson bytes), ("returnBytes", toJson returned)] ++
      if raw then [("calldataBytes", (vector.getObjVal? "calldata").toOption.getD Json.null)] else []))
    let stopped (status reason : String) (extra : List (String × Json) := []) :=
      result status reason (contextEvidence ++ (("observed", toJson observed) :: extra))
    let .ok expectedFailure := vector.getObjValAs? Bool "failure"
      | return stopped "blocked" "missing expected outcome"
    let .ok expectedValues := if raw then .ok [] else vector.getObjValAs? (List String) "expected"
      | return stopped "blocked" "missing expected return values"
    let expectedData : Except String (List Nat) := match vector.getObjVal? "revertBytes" with
      | .error _ => .ok []
      | .ok encoded => fromJson? encoded
    let .ok expectedBytes := expectedData
      | return stopped "blocked" "invalid expected revert bytes"
    if expectedBytes.any (· >= 256) then return stopped "blocked" "invalid expected revert byte"
    let rawExpected : Except String (List Nat) := if raw then
      vector.getObjValAs? (List Nat) "expectedBytes" else .ok []
    let .ok expectedRaw := rawExpected | return stopped "blocked" "invalid expected ABI bytes"
    if expectedRaw.any (· >= 256) then return stopped "blocked" "invalid expected ABI byte"
    let mismatch := if raw then (if failed then bytes else returned) != expectedRaw
      else values != expectedValues || bytes != expectedBytes
    if failed != expectedFailure || mismatch then
      return stopped "broken" s!"runtime expectation mismatch: {signature}"
        [("expected", vector)]
    match outcome with
    | .ok o => state := o.st.glob
    | .error _ => state := before
    if ctor then
      deployed := true
      deploymentFailed := failed
  return result "working" "all supported runtime vectors match" (contextEvidence ++ [("observed", toJson observed)])

syntax (name := upstreamBatch) "#upstream_batch " str " to " str : command

@[command_elab upstreamBatch]
def elabUpstreamBatch : CommandElab := fun stx => do
  let input := stx[1].isStrLit?.getD ""
  let output := stx[3].isStrLit?.getD ""
  let cases ← ofExcept ((Json.parse (← IO.FS.readFile input)).bind Json.getArr?)
  let mut results : Array Json := #[]
  for entry in cases do
    let baseline ← get
    let path ← ofExcept (entry.getObjValAs? String "path")
    let outcome ← (do
      try
      if ((entry.getObjVal? "hostContext").toOption.bind (fun h => (h.getObjValAs? String "kind").toOption)) == some "creation-try-source" then
        return ← CreationTryReplay.elaborate entry
      if ((entry.getObjVal? "hostContext").toOption.bind (fun h => (h.getObjValAs? String "kind").toOption)) == some "linked-library-try-source" then
        return ← LibraryTryReplay.elaborate entry
      let fixture ← ofExcept (entry.getObjValAs? String "fixture")
      let contract ← ofExcept (entry.getObjValAs? String "contract")
      let name := Lean.Name.str `Upstream contract
      let bytes ← IO.FS.readBinFile fixture
      let command := s!"solc_import {toJson fixture |>.compress} hash {hex16 (fnv1a64 bytes)} as Upstream.«{contract}» testing entrypoints"
      let env ← getEnv
      let parsed ← ofExcept (Parser.runParserCategory env `command command)
      elabCommand parsed
      let diagnostics ← ((← get).messages.toList.filter fun message =>
        message.severity == .error || message.severity == .warning).mapM fun message =>
          message.data.toString
      unless diagnostics.isEmpty do return diagnosticFailure diagnostics
      liftTermElabM do
        let term ← `($(mkCIdent ``replay) $(mkCIdent name)
          $(mkCIdent (name ++ `report))
          ((Json.parse $(quote entry.compress)).toOption.getD Json.null))
        let expression ← Term.elabTermEnsuringType term (mkConst ``Json)
        Term.synthesizeSyntheticMVarsNoPostponing
        let expression ← instantiateMVars expression
        unsafe evalExpr Json (mkConst ``Json) expression
      catch ex =>
        let reason ← ex.toMessageData.toString
        let limited := resourceLimited reason
        let status := if limited
          then "blocked" else "broken"
        pure (result status reason) : CommandElabM Json)
    set baseline
    let fields := outcome.getObj?.toOption.map (·.toList) |>.getD []
    let pipeline := (entry.getObjValAs? String "pipeline").toOption.getD "legacy"
    results := results.push (Json.mkObj (("path", str path) :: ("pipeline", str pipeline) :: fields))
    IO.FS.writeFile output (toJson results |>.pretty)

end Solidity.Tools.Upstream
