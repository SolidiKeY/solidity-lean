import Solidity.Backend.Opcode

/-!
Generated additive diagnostic; run generate_opcode_fixture.py --check.
The observed function copies the exact pinned Scalar.ternary body and type.
The candidate uses all 83 constructors of the actual Backend.Op datatype.
This fixture does not modify the original function or its frozen axiom pin.
-/
namespace MigrateBackendOpcodeFixture
open Solidity.Backend
abbrev Word := BitVec 256

def observed : Op → Option (Word → Word → Word → Word)
  | .ADDMOD => some (fun a b k => if k == 0 then 0
      else BitVec.ofNat 256 ((a.toNat + b.toNat) % k.toNat))
  | .MULMOD => some (fun a b k => if k == 0 then 0
      else BitVec.ofNat 256 ((a.toNat * b.toNat) % k.toNat))
  | _ => none

def candidate (op : Op) : Option (Word → Word → Word → Word) :=
  Op.casesOn op
    none -- STOP
    none -- ADD
    none -- MUL
    none -- SUB
    none -- DIV
    none -- SDIV
    none -- MOD
    none -- SMOD
    (some (fun a b k => if k == 0 then 0
      else BitVec.ofNat 256 ((a.toNat + b.toNat) % k.toNat))) -- ADDMOD
    (some (fun a b k => if k == 0 then 0
      else BitVec.ofNat 256 ((a.toNat * b.toNat) % k.toNat))) -- MULMOD
    none -- EXP
    none -- SIGNEXTEND
    none -- LT
    none -- GT
    none -- SLT
    none -- SGT
    none -- EQ
    none -- ISZERO
    none -- AND
    none -- OR
    none -- XOR
    none -- NOT
    none -- BYTE
    none -- SHL
    none -- SHR
    none -- SAR
    none -- CLZ
    none -- KECCAK256
    none -- ADDRESS
    none -- BALANCE
    none -- ORIGIN
    none -- CALLER
    none -- CALLVALUE
    none -- CALLDATALOAD
    none -- CALLDATASIZE
    none -- CALLDATACOPY
    none -- CODESIZE
    none -- CODECOPY
    none -- GASPRICE
    none -- EXTCODESIZE
    none -- EXTCODECOPY
    none -- RETURNDATASIZE
    none -- RETURNDATACOPY
    none -- EXTCODEHASH
    none -- BLOCKHASH
    none -- COINBASE
    none -- TIMESTAMP
    none -- NUMBER
    none -- PREVRANDAO
    none -- GASLIMIT
    none -- CHAINID
    none -- SELFBALANCE
    none -- BASEFEE
    none -- BLOBHASH
    none -- BLOBBASEFEE
    none -- POP
    none -- MLOAD
    none -- MSTORE
    none -- MSTORE8
    none -- SLOAD
    none -- SSTORE
    none -- JUMP
    none -- JUMPI
    none -- PC
    none -- MSIZE
    none -- GAS
    none -- JUMPDEST
    none -- TLOAD
    none -- TSTORE
    none -- MCOPY
    none -- CREATE
    none -- CALL
    none -- CALLCODE
    none -- RETURN
    none -- DELEGATECALL
    none -- CREATE2
    none -- STATICCALL
    none -- REVERT
    none -- INVALID
    none -- SELFDESTRUCT
    (fun _ => none) -- DUP
    (fun _ => none) -- SWAP
    (fun _ => none) -- LOG

theorem candidate_eq_observed (op : Op) : candidate op = observed op := by
  cases op <;> rfl

/-- info: 'MigrateBackendOpcodeFixture.candidate' does not depend on any axioms -/
#guard_msgs in #print axioms candidate
#print axioms observed
#print axioms candidate_eq_observed

example (n : Fin 16) : candidate (.DUP n) = none := rfl
example (n : Fin 16) : candidate (.SWAP n) = none := rfl
example (n : Fin 5) : candidate (.LOG n) = none := rfl
example : (candidate .ADDMOD).map (fun f => f 7 9 0) = some 0 := rfl
example : (candidate .MULMOD).map (fun f => f 7 9 0) = some 0 := rfl
example : (candidate .ADDMOD).map (fun f => f 3 4 5) = some 2 := rfl
example : (candidate .MULMOD).map (fun f => f 3 4 5) = some 2 := rfl
example : (candidate .ADDMOD).map (fun f => f 3 4 5) ≠ some 3 := by
  decide +kernel

end MigrateBackendOpcodeFixture
