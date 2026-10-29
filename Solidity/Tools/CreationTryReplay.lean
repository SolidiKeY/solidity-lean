import Solidity.Frontend.CreationTryImport

/-! Native observation of the bounded, declaration-resolved creation source
fragment. The explicit world/context is runtime evidence, not an admissibility
profile, oracle installation or a general CREATE-address correspondence claim. -/
namespace Solidity.Tools.CreationTryReplay
open Lean Elab Command Term Meta Frontend ContractWorld

private def result (status reason : String) (extra : List (String × Json) := []) : Json :=
  Json.mkObj ([("status", toJson status), ("reason", toJson reason)] ++ extra)

/-- Explicit runtime context only: one-byte positive nonce, existing Keccak,
standard CREATE RLP. World.create still consumes an explicitly supplied address. -/
def target (self : Address) (nonce : Nat) : Except String Address := do
  unless 0 < nonce && nonce < 128 do throw "creation address context: one-byte nonce required"
  let bytes := (Semantics.wordBytes self.1.1.toNat).drop 12 |>.map UInt8.toNat
  let n : Nat := Keccak.keccak256Nat ([0xd6, 0x94] ++ bytes ++ [nonce]) % 2^160
  let some word := PrimTy.ofInt? .uint (n : Int) | throw "creation address context: invalid word"
  let some address := Address.ofWord? word | throw "creation address context: invalid address"
  return address

private def address (text : String) : Except String Address := do
  let some n := text.toNat? | throw "creation context: unsigned address required"
  let some w := PrimTy.ofInt? .uint n | throw "creation context: invalid address word"
  let some a := Address.ofWord? w | throw "creation context: address exceeds 160 bits"
  return a

/-- Execute the actual typed programs in original vector order, threading the
returned world. Constructor errors, heaps or bytes never come from the EVM. -/
def replay {K : Type} [DecidableEq K] (contracts : K → Contract) {owner : K}
    (deploy : World contracts → Address → ContractWorld.Context → TRes (World contracts × Handle owner))
    (run : World contracts → Handle owner → ContractWorld.Context → Address → String → TRes (World contracts × List Nat))
    (entry : Json) : Json := Id.run do
  let prepared : Except String (Address × Address × Array Json) := do
    let host ← entry.getObjVal? "hostContext"
    unless (← host.getObjValAs? String "kind") == "creation-try-source" do throw "creation-only host context required"
    unless (← host.getObjValAs? String "value") == "0" &&
        (← host.getObjValAs? String "ownerFunds") == "0" &&
        (← host.getObjValAs? String "timestamp") == "0" &&
        (← host.getObjValAs? String "senderFunds") == "1000000000000000000000000000000" &&
        (← host.getObjValAs? Nat "firstCreationNonce") == 1 do throw "unsupported creation context"
    let selfText ← host.getObjValAs? String "selfAddress"
    let senderText ← host.getObjValAs? String "sender"
    unless selfText == "457415396813334496268612927368880745799219276745" &&
        senderText == "103164821458651970696730694074090566093359944210" do
      throw "creation context: exact recorded deployment and sender required"
    let self ← address selfText
    let sender ← address senderText
    let vectors ← entry.getObjValAs? (Array Json) "vectors"
    unless !vectors.isEmpty do throw "creation context: nonempty vectors required"
    return (self, sender, vectors)
  let .ok (factory, sender, vectors) := prepared | return result "blocked" "invalid creation context or vectors"
  let zero : Word := ⟨0, by decide +kernel⟩
  let funded : Word := ⟨1000000000000000000000000000000, by decide +kernel⟩
  let initial := World.empty contracts (fun a => if a = sender then funded else zero)
  let ctx : ContractWorld.Context := { sender }
  let .ok (deployed, self) := deploy initial factory ctx
    | return result "blocked" "actual implicit caller deployment failed"
  let mut world := deployed
  let mut observed : Array Json := #[]
  for i in [:vectors.size] do
    let vector := vectors[i]!
    let parsed : Except String (String × List Nat × Bool) := do
      let signature ← vector.getObjValAs? String "signature"
      let calldata ← vector.getObjValAs? (List Nat) "calldata"
      unless calldata.isEmpty do throw "creation source ABI: no argument bytes supported"
      return (signature, ← vector.getObjValAs? (List Nat) "expectedBytes", ← vector.getObjValAs? Bool "failure")
    let .ok (signature, expected, failure) := parsed
      | return result "blocked" "unsupported creation vector shape" [("observed", toJson observed)]
    let .ok fresh := target self.address (i+1)
      | return result "blocked" "unsupported creation address context" [("observed", toJson observed)]
    let actual := run world self ctx fresh signature
    match actual with
    | .error _ => return result "blocked" "creation source did not complete normally; no failure observation fabricated" [("observed", toJson observed)]
    | .ok (next, bytes) =>
      observed := observed.push (Json.mkObj [
        ("signature", toJson signature), ("failed", toJson false), ("values", toJson ([] : List String)),
        ("returnBytes", toJson bytes), ("revertBytes", toJson ([] : List Nat)),
        ("creationTarget", toJson (toString fresh.1.1)), ("creationNonce", toJson (i+1)),
        ("constructorInstalled", toJson (next.accounts fresh).isSome)])
      if failure || expected != bytes then return result "broken" "actual creation source output mismatch" [("observed", toJson observed)]
      world := next
  return result "working" "all complete creation source vectors match in order"
    [("observed", toJson observed), ("selfAddress", toJson (toString self.address.1.1))]

/-- Compile the complete original source independently of the ordinary
single-contract importer report, then evaluate its actual world/caller run. -/
def elaborate (entry : Json) : CommandElabM Json := do
  let fixture ← ofExcept (entry.getObjValAs? String "fixture")
  let contractName ← ofExcept (entry.getObjValAs? String "contract")
  let bytes ← IO.FS.readBinFile fixture
  let name : Lean.Name := `UpstreamCreation
  let command := s!"solc_creation_try {toJson fixture |>.compress} hash {hex16 (fnv1a64 bytes)} from_contract {toJson contractName |>.compress} as UpstreamCreation"
  let parsed ← ofExcept (Parser.runParserCategory (← getEnv) `command command)
  elabCommand parsed
  let errors := (← get).messages.toList.filter (fun m => m.severity == .error || m.severity == .warning)
  unless errors.isEmpty do
    return result "broken" ("\n".intercalate (← errors.mapM (·.data.toString)))
  liftTermElabM do
    let term ← `($(mkCIdent ``replay) $(mkCIdent (name ++ `contracts))
      $(mkCIdent (name ++ `deploy)) $(mkCIdent (name ++ `run))
      ((Json.parse $(quote entry.compress)).toOption.getD Json.null))
    let expression ← Term.elabTermEnsuringType term (mkConst ``Json)
    Term.synthesizeSyntheticMVarsNoPostponing
    let expression ← instantiateMVars expression
    unsafe evalExpr Json (mkConst ``Json) expression

end Solidity.Tools.CreationTryReplay
