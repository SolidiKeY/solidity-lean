import Lean
import Solidity.Backend.PrimitivePackets.UnsignedCast.Controls

namespace UnsignedCastMatrix
open Lean Solidity Solidity.Evm Solidity.Evm.Memory
open Solidity.Backend.PrimitivePackets.UnsignedCast
open Solidity.Backend.PrimitivePackets.UnsignedCast.Controls

def sourceObservation (bits : Nat) (legal : Legal bits) (pipeline : Roadmap.Pipeline)
    (checked : Bool) (n : Int) (range : Source.IntTy.u256.lo ≤ n ∧ n ≤ Source.IntTy.u256.hi) : Option Int :=
  match ((Source.evalE (globals pipeline) (frame checked) 2
      (expression bits legal .here)).run (source n range)).1 with
  | .ok result => match result.get with
    | .ok result => result.key
    | .error _ => none
  | .error _ => none

def wordObservation : Word → Option Nat
  | .val word => some word.val
  | .slot _ => none

def row (bits : Nat) (pipeline : Roadmap.Pipeline) (checked : Bool) (tag : String) (n : Int) : Json := Id.run do
  let mut passed := false
  let mut sourceValue : Option Int := none
  let mut stack : List (Option Nat) := []
  let mut cells : List (Option Nat) := []
  let mut code := "missing"
  let expected := n % ((2 ^ bits : Nat) : Int)
  if legal : Legal bits then
    if range : Source.IntTy.u256.lo ≤ n ∧ n ≤ Source.IntTy.u256.hi then
      sourceValue := sourceObservation bits legal pipeline checked n range
      if let some compiled := Memory.compileVal 1 frag (value (C := C) bits legal .here) then
        code := reprStr compiled.code
        match Evm.run compiled.code (machine n range) with
        | .ok output skip =>
          stack := output.stack.map wordObservation
          cells := [0,8,9].map (fun cell => wordObservation (output.mem cell))
          passed := sourceValue == some expected && skip == 0 &&
            stack == [some expected.toNat,some 77,some 88] && cells == [some 64,some 10,some 99]
        | _ => pure ()
  return Json.mkObj [("bits",toJson bits),("pipeline",toJson (if pipeline = .legacy then "legacy" else "viaIR")),
    ("checked",toJson checked),("case",toJson tag),("input",toJson (toString n)),
    ("expected",toJson (toString expected)),("source",toJson (sourceValue.map toString)),
    ("stack",toJson (stack.map (fun n => n.map toString))),("cells",toJson (cells.map (fun n => n.map toString))),
    ("code",toJson code),("passed",toJson passed)]

def matrix : List Json := (List.range 31).flatMap fun width =>
  let bits := 8 * (width+1)
  [Roadmap.Pipeline.legacy,.viaIR].flatMap fun pipeline =>
    [true,false].flatMap fun checked =>
      [("zero",(0 : Int)),("power",((2 ^ bits : Nat) : Int)),
        ("max",((2 ^ 256 : Nat) : Int)-1)].map fun (tag,n) => row bits pipeline checked tag n

#eval IO.println ("UNSIGNED_CAST_MATRIX " ++ (toJson matrix).compress)
end UnsignedCastMatrix
