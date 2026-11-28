import Solidity.Yul.StatefulRun
import Solidity.SolcValidation.IrParse
import Solidity.Frontend.Yul.ClosedParse
import Solidity.Yul.BlockExtract
import Lean.Data.Json

/-! Checked import of a named runtime object from solc object-dialect IrSyntax.
Both parsers retain their certificates. The memoryguard literal is represented by an explicit identity function; other
compiler-only object operations and
unsupported machine builtins are refused, including in unexecuted bodies.
Token preservation is not an external solc/EVM semantic agreement theorem. -/
namespace Solidity.Yul.StatefulImport
open Solidity.SolcValidation

def select : List String → Object IrSyntax.Code → Option IrSyntax.Code
  | [], .object _ code _ => some code
  | name :: path, .object _ _ children => do
    let child ← children.find? fun child => match child with
      | .object n _ _ | .data n _ => n == name
    select path child
  | _, .data _ _ => none

def hexByte (n : Nat) : String :=
  String.mk ["0123456789abcdef".toList[n / 16 % 16]!, "0123456789abcdef".toList[n % 16]!]

def renderToken : IrSyntax.Tok → String
  | .ident s => s
  | .num n => toString n
  | .str s => "\"" ++ s ++ "\""
  | .hex bs => "hex\"" ++ String.join (bs.map fun b => hexByte b.val) ++ "\""
  | .lbrace => "{"
  | .rbrace => "}"
  | .lparen => "("
  | .rparen => ")"
  | .comma => ","
  | .assign => ":="
  | .arrow => "->"

def render (code : IrSyntax.Code) : String := String.intercalate " " (code.toks.map renderToken)
def source (code : IrSyntax.Code) : Solidity.Frontend.Checked.Bytes :=
  ("assembly { function memoryguard(x) -> r { r := x } " ++ render code ++ " }").toUTF8.data.toList

def supported {a r} : Builtin a r → Bool
  | .pure _ | .pop | .stop | .invalid | .callvalue | .sload | .sstore | .mload | .mstore | .mstore8
  | .calldatasize | .calldataload | .calldatacopy | .returndatasize | .returndatacopy
  | .mcopy | .return | .revert => true
  | _ => false

def checkTokens (tokens : List IrSyntax.Tok) : Except String Unit := do
  for token in tokens do
    if let .ident name := token then
      if let some ⟨_, _, op⟩ := lookupBuiltin name then
        unless supported op do throw ("unsupported runtime builtin: " ++ name)

structure Imported (text : String) (path : List String) where
  ir : IrSyntax.Parsed text
  code : IrSyntax.Code
  selected : select path ir.parts.root = some code
  roundtrip : IrSyntax.lex (render code) = some code.toks
  supportedTokens : checkTokens code.toks = .ok ()
  checked : ClosedSyntax.Parsed [] (source code)

def parse (text : String) (path : List String) : Except String (Imported text path) := do
  let ir ← IrSyntax.parse text
  match hs : select path ir.parts.root with
  | none => throw "runtime object path is missing or names data"
  | some code =>
    if hr : IrSyntax.lex (render code) = some code.toks then
      match ht : checkTokens code.toks with
      | .error reason => throw reason
      | .ok () =>
        match ClosedSyntax.parse [] (source code) with
        | .error reason => throw ("unsupported runtime syntax, typing or placement: " ++ reprStr reason)
        | .ok checked => pure ⟨ir, code, hs, hr, ht, checked⟩
    else throw "runtime token rendering did not roundtrip"

def Imported.run {text path} (p : Imported text path) (limit fuel : Nat)
    (initial : StatefulRun.Machine) : Except StatefulRun.Signal StatefulRun.Machine :=
  StatefulRun.run limit fuel p.checked.checked.typing.code initial

/-- Original IR provenance is inherited from the certifying object parser. -/
theorem Imported.provenance {text path} (p : Imported text path) :
    IrSyntax.lex text = some (IrSyntax.objectToks p.ir.parts.root) ∧ IrSyntax.objectWf p.ir.parts.root = true :=
  p.ir.sound
def selfTest : IO UInt32 := do
  let cases : List (String × String) := [
    ("if callvalue() { revert(0,0) } sstore(0,1)", "1::false"),
    ("sstore(0,7) mstore(0,9) return(31,1)", "7:09:false"),
    ("sstore(0,7) mstore(0,9) revert(31,1)", "0:09:true"),
    ("function f() { return(0,0) } f() sstore(0,9)", "0::false"),
    ("function f(v) -> r { sstore(0,add(sload(0),v)) r := sload(0) } mstore(0,sub(f(1),f(2))) return(31,1)", "3:01:false"),
    ("mstore(0,16909060) mcopy(29,28,3) return(28,4)", "0:01010203:false"),
    ("calldatacopy(0,1,3) return(0,3)", "0:340000:false"),
    ("for { let i := 0 } lt(i,3) { i := add(i,1) } { sstore(0,add(sload(0),1)) }", "3::false"),
    ("mstore(0,memoryguard(128)) return(31,1)", "0:80:false"),
    ("if 0 { pop(caller()) }", "parse-error"),
    ("function f() { pop(gas()) }", "parse-error"),
    ("returndatacopy(0,0,1)", "run-error"),
    ("return(0,1025)", "run-error"),
    ("switch calldatasize() case 2 { sstore(0,11) } default { sstore(0,99) }", "11::false"),
    ("function f() -> r { r := 7 leave sstore(0,99) } sstore(0,f())", "7::false"),
    ("for { let i := 0 } lt(i,5) { i := add(i,1) } { if eq(i,1) { continue } if eq(i,3) { break } sstore(0,add(sload(0),1)) }", "2::false")]
  for (body, expected) in cases do
    let actual := match parse ("object \"t\" { code { " ++ body ++ " } }") [] with
      | .error _ => "parse-error"
      | .ok p => match p.run 1024 1000 (StatefulRun.Machine.empty ⟨#[0x12,0x34]⟩) with
        | .error _ => "run-error"
        | .ok s => toString (s.storage (word 0)).val ++ ":" ++
          String.join (s.returnData.data.toList.map fun b => hexByte b.toNat) ++ ":" ++ toString s.reverted
    unless actual == expected do
      IO.eprintln s!"FAIL {body}: expected {expected}, got {actual}"
      return 1
  let text := "object \"root\" { code { pop(caller()) } object \"runtime\" { code { sstore(0,5) } } }"
  let .ok p := parse text ["runtime"] | IO.eprintln "FAIL runtime selection"; return 1
  match p.run 1024 0 StatefulRun.Machine.empty with
  | .error .exhausted => pure ()
  | _ => IO.eprintln "FAIL fuel exhaustion"; return 1
  match p.run 1024 1000 StatefulRun.Machine.empty with
  | .ok s => unless (s.storage (word 0)).val == 5 do IO.eprintln "FAIL selected code"; return 1
  | _ => IO.eprintln "FAIL selected execution"; return 1
  let .ok p := parse "object \"value\" { code { sstore(0,callvalue()) } }" [] | IO.eprintln "FAIL callvalue import"; return 1
  match p.run 1024 1000 { StatefulRun.Machine.empty with callValue := word 42 } with
  | .ok s => unless (s.storage (word 0)).val == 42 do IO.eprintln "FAIL callvalue read"; return 1
  | _ => IO.eprintln "FAIL callvalue execution"; return 1
  IO.println s!"PASS stateful-yul {cases.length + 3} cases"
  return 0

/-- Script entry: args are IR file, slash-separated child-object path (`-` for
root), fuel, max output bytes, calldata hex, and comma-separated slot=value
initial storage/query entries (`-` for empty), optional decimal call value (default 0).
Decimal words are range checked.
Use a two-line wrapper importing this module and defining `main := driver`;
keeping main namespaced avoids collisions when the library root imports it. -/
def driver (args : List String) : IO UInt32 := do
  if args == ["--self-test"] then return ← selfTest
  let fail := fun (message : String) => do
    IO.println ((Lean.Json.mkObj [("status", .str "error"), ("error", .str message)]).compress)
    pure (1 : UInt32)
  let args := if args.length == 6 then args ++ ["0"] else args
  let [file, path, fuelText, limitText, calldataHex, storageText, valueText] := args
    | return ← fail "expected: IR_FILE OBJECT_PATH FUEL MAX_OUTPUT_BYTES CALLDATA_HEX STORAGE [CALL_VALUE]"
  let some value := valueText.toNat? | return ← fail "call value must be a natural number"
  if value ≥ 2^256 then return ← fail "call value out of range"
  let some fuel := fuelText.toNat? | return ← fail "fuel must be a natural number"
  let some limit := limitText.toNat? | return ← fail "max output bytes must be a natural number"
  let some [.hex bytes] := IrSyntax.lex ("hex\"" ++ calldataHex ++ "\"")
    | return ← fail "calldata must be an even-length hex string without 0x"
  let mut slots : List (Word × Word) := []
  for entry in (if storageText == "-" then [] else storageText.splitOn ",") do
    let [key, value] := entry.splitOn "=" | return ← fail "storage entries must be slot=value"
    let (some key, some value) := (key.toNat?, value.toNat?)
      | return ← fail "storage words must be decimal natural numbers"
    if key ≥ 2^256 || value ≥ 2^256 then return ← fail "storage word out of range"
    if slots.any (fun p => p.1.val == key) then return ← fail "duplicate storage slot"
    slots := slots ++ [(word key, word value)]
  let text ← IO.FS.readFile file
  let parsed := parse text (if path == "-" then [] else path.splitOn "/")
  if let .error message := parsed then return ← fail message
  let .ok imported := parsed | return ← fail "import failed"
  let initial : StatefulRun.Machine :=
    { StatefulRun.Machine.empty ⟨(bytes.map fun b => UInt8.ofNat b.val).toArray⟩ with
      callValue := word value, storage := fun key => ((slots.find? fun p => p.1 == key).map Prod.snd).getD (word 0) }
  match imported.run limit fuel initial with
  | .error failure => return ← fail (match failure with
    | .exhausted => "fuel exhausted"
    | .unsupported name => "unsupported runtime builtin: " ++ name
    | .outputLimit => "host output limit exceeded"
    | .returndataBounds => "returndata copy out of bounds"
    | .invalid => "invalid opcode"
    | .halted _ => "unexpected unhandled halt")
  | .ok result =>
    IO.println ((Lean.Json.mkObj [
      ("status", .str "ok"), ("reverted", .bool result.reverted),
      ("returnData", .str (String.join (result.returnData.data.toList.map fun b => hexByte b.toNat))),
      ("storage", .arr (slots.map (fun p => Lean.Json.arr #[.str (toString p.1.val),
        .str (toString (result.storage p.1).val)])).toArray)]).compress)
    pure 0

end Solidity.Yul.StatefulImport
