import Solidity.Frontend.LibraryTryImport

/-! Concrete linked-library source replay, separate from universal source
validity. The world executes source bodies; expectations only compare outputs. -/
namespace Solidity.Tools.LibraryTryReplay
open Lean Elab Command Term Meta Frontend ContractWorld
private def result (status reason : String) (extra : List (String × Json) := []) :=
  Json.mkObj ([("status",toJson status),("reason",toJson reason)] ++ extra)
private def address (s : String) : Except String Address := do
  let some n := s.toNat? | throw "unsigned address required"
  let some w := PrimTy.ofInt? .uint n | throw "address word required"
  let some a := Address.ofWord? w | throw "160-bit address required"
  return a

/-- Only this canonical Boolean input is admitted, before any source effect. -/
def input (bytes : List Nat) : Except String Bool := do
  unless bytes.length == 32 && bytes.all (· < 256) do throw "canonical bool word required"
  let value := bytes.foldl (fun n b => 256*n+b) 0
  if value == 0 then return false
  else if value == 1 then return true
  else throw "invalid bool word"

/-- Library deployment and each caller method execute once in original order. -/
def replay {K : Type} [DecidableEq K] (contracts : K → Contract) (roles : K → Role) {caller library : K}
    (deployLibrary : World contracts → Address → ContractWorld.Context → TRes (World contracts × Handle library))
    (deployCaller : World contracts → Address → ContractWorld.Context → TRes (World contracts × Handle caller))
    (run : World contracts → Handle caller → ContractWorld.Context → Address → String → Bool → TRes (World contracts × List Nat))
    (readStorage : World contracts → Handle caller → TRes Int)
    (entry : Json) : Json := Id.run do
  let prepare : Except String (Address × Address × Address × Array Json) := do
    let h ← entry.getObjVal? "hostContext"
    unless (← h.getObjValAs? String "kind") == "linked-library-try-source" &&
      (← h.getObjValAs? String "selfAddress") == "816484669177263916909924781827997526878516243634" &&
      (← h.getObjValAs? String "libraryAddress") == "457415396813334496268612927368880745799219276745" &&
      (← h.getObjValAs? String "sender") == "103164821458651970696730694074090566093359944210" &&
      (← h.getObjValAs? String "senderFunds") == "1000000000000000000000000000000" &&
      (← h.getObjValAs? String "ownerFunds") == "0" && (← h.getObjValAs? String "value") == "0" &&
      (← h.getObjValAs? String "timestamp") == "0" do throw "exact linked runtime context required"
    let caller ← address (← h.getObjValAs? String "selfAddress")
    let linked ← address (← h.getObjValAs? String "libraryAddress")
    let sender ← address (← h.getObjValAs? String "sender")
    let vectors ← entry.getObjValAs? (Array Json) "vectors"
    unless !vectors.isEmpty do throw "nonempty original vectors required"
    return (caller,linked,sender,vectors)
  let .ok (owner,linked,sender,vectors) := prepare | return result "blocked" "invalid linked context/vectors"
  let initial := World.empty contracts (fun a => if a = sender then
    (⟨1000000000000000000000000000000, by decide +kernel⟩ : ContractWorld.Word) else PrimTy.dflt .uint) roles
  let ctx : ContractWorld.Context := { sender }
  let .ok (w,lib) := deployLibrary initial linked ctx | return result "blocked" "actual library deployment failed"
  let .ok (w,self) := deployCaller w owner ctx | return result "blocked" "actual caller deployment failed"
  let mut world := w
  let mut observed : Array Json := #[]
  for vector in vectors do
    let parsed : Except String (String × Bool × List Nat × Bool) := do
      return (← vector.getObjValAs? String "signature", ← input (← vector.getObjValAs? (List Nat) "calldata"),
        ← vector.getObjValAs? (List Nat) "expectedBytes", ← vector.getObjValAs? Bool "failure")
    let .ok (signature,b,expected,failure) := parsed | return result "blocked" "unsupported linked input" [("observed",toJson observed)]
    let .ok (next,bytes) := run world self ctx lib.address signature b
      | return result "blocked" "linked method has no completed admitted execution" [("observed",toJson observed)]
    let .ok field := readStorage next self | return result "blocked" "actual caller storage observation failed" [("observed",toJson observed)]
    observed := observed.push (Json.mkObj [("signature",toJson signature),("failed",toJson false),
      ("values",toJson ([] : List String)),("returnBytes",toJson bytes),("revertBytes",toJson ([] : List Nat)),("callerStorageField",toJson field)])
    if failure || expected != bytes then return result "broken" "actual linked source output mismatch" [("observed",toJson observed)]
    world := next
  return result "working" "all complete linked source vectors match in order" [("observed",toJson observed)]

/-- Compile the whole checked source before evaluating the typed world run. -/
def elaborate (entry : Json) : CommandElabM Json := do
  let fixture ← ofExcept (entry.getObjValAs? String "fixture")
  let owner ← ofExcept (entry.getObjValAs? String "contract")
  let bytes ← IO.FS.readBinFile fixture
  let name : Lean.Name := `UpstreamLibraryTry
  let command := s!"solc_library_try {toJson fixture |>.compress} hash {hex16 (fnv1a64 bytes)} from_contract {toJson owner |>.compress} as UpstreamLibraryTry"
  let parsed ← ofExcept (Parser.runParserCategory (← getEnv) `command command)
  elabCommand parsed
  let errors := (← get).messages.toList.filter (fun m => m.severity == .error || m.severity == .warning)
  unless errors.isEmpty do return result "broken" ("\n".intercalate (← errors.mapM (·.data.toString)))
  liftTermElabM do
    let term ← `($(mkCIdent ``replay) $(mkCIdent (name ++ `contracts)) $(mkCIdent (name ++ `roles))
      $(mkCIdent (name ++ `deployLibrary)) $(mkCIdent (name ++ `deployCaller)) $(mkCIdent (name ++ `run)) $(mkCIdent (name ++ `readStorage))
      ((Json.parse $(quote entry.compress)).toOption.getD Json.null))
    let expression ← Term.elabTermEnsuringType term (mkConst ``Json)
    Term.synthesizeSyntheticMVarsNoPostponing
    let expression ← instantiateMVars expression
    unsafe evalExpr Json (mkConst ``Json) expression
end Solidity.Tools.LibraryTryReplay
