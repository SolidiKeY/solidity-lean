import Lean
import H62AbiWorld.SuccessContracts

/-! Exact Backend.encode fixtures exported for optional external reference runs.
No #eval result is a Lean gas/fork proof. Prefixes deliberately initialize a
nonzero stack tail and two sentinel bytes before executing the actual emitter. -/
namespace H62.AbiWorld.RuntimeVectors
open Solidity Solidity.Backend Solidity.Backend.Failure Solidity.Backend.AbiWorld Lean

def bytesJson (bs : List UInt8) : Json := toJson (bs.map UInt8.toNat)

def packet (name : String) (input : Input) (suffix : Program := []) : Json :=
  let payload := input.bytes
  let prologue := [pushNat 77] ++ writes 7 [85] ++ writes (8+payload.length) [119]
  let body := emit 8 input ++ suffix
  Json.mkObj [("name",toJson name),("program_kind",toJson "packet"),
    ("compiled",toJson true),("kind",toJson (match input with | .returned _ => "success" | _ => "revert")),
    ("offset",toJson (8:Nat)),("payload",bytesJson payload),("code",bytesJson (encode (prologue++body))),
    ("body_code",bytesJson (encode body)),("prefix_bytes",toJson (encode prologue).length),
    ("tail",toJson (["77"] : List String))]

def addition (name : String) (a b : Nat) : Json :=
  let prologue := [pushNat a,pushNat b]
  let base := (encode prologue).length
  match CheckedAddArtifact.compile 8 base 0 with
  | none => Json.mkObj [("name",toJson name),("compiled",toJson false)]
  | some out => Json.mkObj [("name",toJson name),("compiled",toJson true),
      ("program_kind",toJson "checked_add"),("a",toJson (toString a)),("b",toJson (toString b)),
      ("code",bytesJson (encode prologue++encode out.code)),("base",toJson base)]

def vectors : Json := Json.arr #[
  packet "return_two" (.returned [0,255]),
  packet "return_word300" (.returned (AbiEntry.wordBytes 300)),
  packet "return_suffix" (.returned [0,255]) [.op .ADD],
  packet "empty_revert" .empty,
  packet "panic300" (.panic ⟨300,by decide⟩),
  packet "error_two" (.reason [0,255]),
  addition "add_small" 2 3,
  addition "add_zero" 0 0,
  addition "add_max_no_overflow" (2^256-1) 0,
  addition "add_overflow" (2^256-1) 1]

end H62.AbiWorld.RuntimeVectors
#eval IO.println ("H62_VECTORS=" ++ H62.AbiWorld.RuntimeVectors.vectors.compress)
