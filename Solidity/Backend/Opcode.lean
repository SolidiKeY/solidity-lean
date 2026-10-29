/-!
# Osaka instructions and their byte encoding (G45.05)

The target instruction set of the backend (`docs/feature-work/backend-assembler.md`):
every opcode the Osaka fork defines, as an intrinsic datatype.

* `Op` is an opcode without immediate data: the 80 fixed opcodes (with
  `CLZ`, EIP-7939; `TLOAD`/`TSTORE`, EIP-1153; `MCOPY`, EIP-5656), and the
  indexed families `DUP n`, `SWAP n` (`n : Fin 16`) and `LOG n` (`n : Fin 5`).
* `Instr` is an `Op` or `PUSHn` with `n : Fin 33` and an immediate of
  exactly `n` bytes (`Vector UInt8 n`), so `PUSH0` is `push 0 #v[]` and no
  instruction carries a truncated or oversized immediate.

`Instr.encode` writes an instruction as its bytes (the immediate big-endian,
as written), `encode` a program; `decode` reads bytes back and refuses an
undefined opcode or a `PUSH` whose immediate runs past the end. Proved:

* `decode_encode` — `decode (encode p) = some p`;
* `encode_injective` — distinct programs have distinct bytes;
* `encode_decode` — whatever `decode` accepts re-encodes to the same bytes,
  so `decode` is exactly the inverse of `encode` on its image.

Reading a byte is checked once over all 256 values (`tableAgrees_all`:
`Op.code_ofCode`, `pushCode_of_pushWidth`); writing an opcode is checked by
cases (`Op.ofCode_code`, `Op.pushWidth_code`, `pushWidth_pushCode`).
Jump-destination analysis is in `Backend/Jumpdest.lean`. Gas is not
modelled and the EIP-170/3860 size limits are idealized
(`docs/solidity-scope.md`, G01 Q2 and G06 Q2).
-/

namespace Solidity.Backend

/-- An Osaka opcode that carries no immediate data. -/
inductive Op where
  | STOP
  | ADD
  | MUL
  | SUB
  | DIV
  | SDIV
  | MOD
  | SMOD
  | ADDMOD
  | MULMOD
  | EXP
  | SIGNEXTEND
  | LT
  | GT
  | SLT
  | SGT
  | EQ
  | ISZERO
  | AND
  | OR
  | XOR
  | NOT
  | BYTE
  | SHL
  | SHR
  | SAR
  | CLZ
  | KECCAK256
  | ADDRESS
  | BALANCE
  | ORIGIN
  | CALLER
  | CALLVALUE
  | CALLDATALOAD
  | CALLDATASIZE
  | CALLDATACOPY
  | CODESIZE
  | CODECOPY
  | GASPRICE
  | EXTCODESIZE
  | EXTCODECOPY
  | RETURNDATASIZE
  | RETURNDATACOPY
  | EXTCODEHASH
  | BLOCKHASH
  | COINBASE
  | TIMESTAMP
  | NUMBER
  | PREVRANDAO
  | GASLIMIT
  | CHAINID
  | SELFBALANCE
  | BASEFEE
  | BLOBHASH
  | BLOBBASEFEE
  | POP
  | MLOAD
  | MSTORE
  | MSTORE8
  | SLOAD
  | SSTORE
  | JUMP
  | JUMPI
  | PC
  | MSIZE
  | GAS
  | JUMPDEST
  | TLOAD
  | TSTORE
  | MCOPY
  | CREATE
  | CALL
  | CALLCODE
  | RETURN
  | DELEGATECALL
  | CREATE2
  | STATICCALL
  | REVERT
  | INVALID
  | SELFDESTRUCT
  /-- `DUP(n+1)`, opcode `0x80 + n`. -/
  | DUP (n : Fin 16)
  /-- `SWAP(n+1)`, opcode `0x90 + n`. -/
  | SWAP (n : Fin 16)
  /-- `LOGn`, opcode `0xa0 + n`. -/
  | LOG (n : Fin 5)
  deriving DecidableEq, Repr

namespace Op

/-- The opcode byte. -/
def code : Op → UInt8
  | .STOP => 0x00
  | .ADD => 0x01
  | .MUL => 0x02
  | .SUB => 0x03
  | .DIV => 0x04
  | .SDIV => 0x05
  | .MOD => 0x06
  | .SMOD => 0x07
  | .ADDMOD => 0x08
  | .MULMOD => 0x09
  | .EXP => 0x0a
  | .SIGNEXTEND => 0x0b
  | .LT => 0x10
  | .GT => 0x11
  | .SLT => 0x12
  | .SGT => 0x13
  | .EQ => 0x14
  | .ISZERO => 0x15
  | .AND => 0x16
  | .OR => 0x17
  | .XOR => 0x18
  | .NOT => 0x19
  | .BYTE => 0x1a
  | .SHL => 0x1b
  | .SHR => 0x1c
  | .SAR => 0x1d
  | .CLZ => 0x1e
  | .KECCAK256 => 0x20
  | .ADDRESS => 0x30
  | .BALANCE => 0x31
  | .ORIGIN => 0x32
  | .CALLER => 0x33
  | .CALLVALUE => 0x34
  | .CALLDATALOAD => 0x35
  | .CALLDATASIZE => 0x36
  | .CALLDATACOPY => 0x37
  | .CODESIZE => 0x38
  | .CODECOPY => 0x39
  | .GASPRICE => 0x3a
  | .EXTCODESIZE => 0x3b
  | .EXTCODECOPY => 0x3c
  | .RETURNDATASIZE => 0x3d
  | .RETURNDATACOPY => 0x3e
  | .EXTCODEHASH => 0x3f
  | .BLOCKHASH => 0x40
  | .COINBASE => 0x41
  | .TIMESTAMP => 0x42
  | .NUMBER => 0x43
  | .PREVRANDAO => 0x44
  | .GASLIMIT => 0x45
  | .CHAINID => 0x46
  | .SELFBALANCE => 0x47
  | .BASEFEE => 0x48
  | .BLOBHASH => 0x49
  | .BLOBBASEFEE => 0x4a
  | .POP => 0x50
  | .MLOAD => 0x51
  | .MSTORE => 0x52
  | .MSTORE8 => 0x53
  | .SLOAD => 0x54
  | .SSTORE => 0x55
  | .JUMP => 0x56
  | .JUMPI => 0x57
  | .PC => 0x58
  | .MSIZE => 0x59
  | .GAS => 0x5a
  | .JUMPDEST => 0x5b
  | .TLOAD => 0x5c
  | .TSTORE => 0x5d
  | .MCOPY => 0x5e
  | .CREATE => 0xf0
  | .CALL => 0xf1
  | .CALLCODE => 0xf2
  | .RETURN => 0xf3
  | .DELEGATECALL => 0xf4
  | .CREATE2 => 0xf5
  | .STATICCALL => 0xfa
  | .REVERT => 0xfd
  | .INVALID => 0xfe
  | .SELFDESTRUCT => 0xff
  | .DUP n => UInt8.ofNat (0x80 + n.val)
  | .SWAP n => UInt8.ofNat (0x90 + n.val)
  | .LOG n => UInt8.ofNat (0xa0 + n.val)

/-- The opcode a byte names, if it names one without immediate data:
`none` for `PUSH0`–`PUSH32` and for undefined bytes. -/
def ofCode (b : UInt8) : Option Op :=
  let n := b.toNat
  if h : 0x80 ≤ n ∧ n < 0x90 then some (.DUP ⟨n - 0x80, by omega⟩)
  else if h : 0x90 ≤ n ∧ n < 0xa0 then some (.SWAP ⟨n - 0x90, by omega⟩)
  else if h : 0xa0 ≤ n ∧ n < 0xa5 then some (.LOG ⟨n - 0xa0, by omega⟩)
  else match n with
    | 0x00 => some .STOP
    | 0x01 => some .ADD
    | 0x02 => some .MUL
    | 0x03 => some .SUB
    | 0x04 => some .DIV
    | 0x05 => some .SDIV
    | 0x06 => some .MOD
    | 0x07 => some .SMOD
    | 0x08 => some .ADDMOD
    | 0x09 => some .MULMOD
    | 0x0a => some .EXP
    | 0x0b => some .SIGNEXTEND
    | 0x10 => some .LT
    | 0x11 => some .GT
    | 0x12 => some .SLT
    | 0x13 => some .SGT
    | 0x14 => some .EQ
    | 0x15 => some .ISZERO
    | 0x16 => some .AND
    | 0x17 => some .OR
    | 0x18 => some .XOR
    | 0x19 => some .NOT
    | 0x1a => some .BYTE
    | 0x1b => some .SHL
    | 0x1c => some .SHR
    | 0x1d => some .SAR
    | 0x1e => some .CLZ
    | 0x20 => some .KECCAK256
    | 0x30 => some .ADDRESS
    | 0x31 => some .BALANCE
    | 0x32 => some .ORIGIN
    | 0x33 => some .CALLER
    | 0x34 => some .CALLVALUE
    | 0x35 => some .CALLDATALOAD
    | 0x36 => some .CALLDATASIZE
    | 0x37 => some .CALLDATACOPY
    | 0x38 => some .CODESIZE
    | 0x39 => some .CODECOPY
    | 0x3a => some .GASPRICE
    | 0x3b => some .EXTCODESIZE
    | 0x3c => some .EXTCODECOPY
    | 0x3d => some .RETURNDATASIZE
    | 0x3e => some .RETURNDATACOPY
    | 0x3f => some .EXTCODEHASH
    | 0x40 => some .BLOCKHASH
    | 0x41 => some .COINBASE
    | 0x42 => some .TIMESTAMP
    | 0x43 => some .NUMBER
    | 0x44 => some .PREVRANDAO
    | 0x45 => some .GASLIMIT
    | 0x46 => some .CHAINID
    | 0x47 => some .SELFBALANCE
    | 0x48 => some .BASEFEE
    | 0x49 => some .BLOBHASH
    | 0x4a => some .BLOBBASEFEE
    | 0x50 => some .POP
    | 0x51 => some .MLOAD
    | 0x52 => some .MSTORE
    | 0x53 => some .MSTORE8
    | 0x54 => some .SLOAD
    | 0x55 => some .SSTORE
    | 0x56 => some .JUMP
    | 0x57 => some .JUMPI
    | 0x58 => some .PC
    | 0x59 => some .MSIZE
    | 0x5a => some .GAS
    | 0x5b => some .JUMPDEST
    | 0x5c => some .TLOAD
    | 0x5d => some .TSTORE
    | 0x5e => some .MCOPY
    | 0xf0 => some .CREATE
    | 0xf1 => some .CALL
    | 0xf2 => some .CALLCODE
    | 0xf3 => some .RETURN
    | 0xf4 => some .DELEGATECALL
    | 0xf5 => some .CREATE2
    | 0xfa => some .STATICCALL
    | 0xfd => some .REVERT
    | 0xfe => some .INVALID
    | 0xff => some .SELFDESTRUCT
    | _ => none

end Op

/-- The immediate width a byte announces: `some n` for `PUSHn`
(`0x5f + n`, `n ≤ 32`), `none` for every other byte. -/
def pushWidth (b : UInt8) : Option (Fin 33) :=
  if h : 0x5f ≤ b.toNat ∧ b.toNat ≤ 0x7f then some ⟨b.toNat - 0x5f, by omega⟩ else none

/-- The opcode byte of `PUSHn`. -/
def pushCode (n : Fin 33) : UInt8 := UInt8.ofNat (0x5f + n.val)

/-! ## The opcode table, checked over all 256 bytes -/

theorem pushWidth_pushCode : ∀ n : Fin 33, pushWidth (pushCode n) = some n := by decide

/-- Every byte's decoding re-encodes to that byte (both readings). -/
def tableAgrees (b : UInt8) : Bool :=
  (match pushWidth b with | some n => pushCode n == b && (Op.ofCode b).isNone | none => true) &&
  (match Op.ofCode b with | some o => o.code == b | none => true)

theorem tableAgrees_all : (List.range 256).all (fun k => tableAgrees (UInt8.ofNat k)) = true := by
  decide +kernel

theorem tableAgrees_of (b : UInt8) : tableAgrees b = true := by
  have hb : UInt8.ofNat b.toNat = b := UInt8.ofNat_toNat
  have h := List.all_eq_true.mp tableAgrees_all b.toNat (List.mem_range.mpr b.toNat_lt)
  rw [hb] at h
  exact h

theorem pushCode_of_pushWidth {b : UInt8} {n : Fin 33} (h : pushWidth b = some n) :
    pushCode n = b := by
  have t := tableAgrees_of b
  simp only [tableAgrees, h, Bool.and_eq_true, beq_iff_eq] at t
  exact t.1.1

/-- No byte is both a `PUSH` and an opcode without immediate. -/
theorem ofCode_of_pushWidth {b : UInt8} {n : Fin 33} (h : pushWidth b = some n) :
    Op.ofCode b = none := by
  have t := tableAgrees_of b
  simp only [tableAgrees, h, Bool.and_eq_true, beq_iff_eq, Option.isNone_iff_eq_none] at t
  exact t.1.2

namespace Op

theorem ofCode_code : ∀ o : Op, ofCode o.code = some o := by
  intro o
  cases o <;> first | rfl | (rename_i n; revert n; decide)

theorem pushWidth_code : ∀ o : Op, pushWidth o.code = none := by
  intro o
  cases o <;> first | rfl | (rename_i n; revert n; decide)

theorem code_ofCode {b : UInt8} {o : Op} (h : ofCode b = some o) : o.code = b := by
  have t := tableAgrees_of b
  simp only [tableAgrees, h, Bool.and_eq_true, beq_iff_eq] at t
  exact t.2

theorem code_injective {o o' : Op} (h : o.code = o'.code) : o = o' := by
  have h' : ofCode o.code = ofCode o'.code := by rw [h]
  rw [ofCode_code, ofCode_code] at h'
  exact Option.some.inj h'

end Op

/-! ## Instructions and programs -/

/-- An Osaka instruction: an opcode, or `PUSHn` with exactly `n` immediate
bytes, most significant first. -/
inductive Instr where
  | op (o : Op)
  | push (n : Fin 33) (imm : Vector UInt8 n)
  deriving DecidableEq, Repr

/-- A program: instructions in code order. -/
abbrev Program := List Instr

namespace Instr

/-- The instruction's bytes. -/
def encode : Instr → List UInt8
  | .op o => [o.code]
  | .push n imm => pushCode n :: imm.toList

/-- The number of bytes the instruction occupies. -/
def size : Instr → Nat
  | .op _ => 1
  | .push n _ => n.val + 1

/-- The instruction's opcode byte, its first byte. -/
def opcode : Instr → UInt8
  | .op o => o.code
  | .push n _ => pushCode n

/-- A `PUSH`'s size does not depend on its immediate. -/
theorem size_push (n : Fin 33) (imm : Vector UInt8 n) : (push n imm).size = n.val + 1 := rfl

theorem length_encode (i : Instr) : i.encode.length = i.size := by
  cases i <;> simp only [encode, size, List.length_cons, List.length_nil, Vector.length_toList]

end Instr

/-- A program's bytes. -/
def encode (p : Program) : List UInt8 := p.flatMap Instr.encode

/-- A program's size in bytes. -/
def size (p : Program) : Nat := (p.map Instr.size).sum

@[simp] theorem encode_nil : encode [] = [] := rfl

@[simp] theorem encode_cons (i : Instr) (p : Program) :
    encode (i :: p) = i.encode ++ encode p := by
  simp only [encode, List.flatMap_cons]

theorem encode_append (p q : Program) : encode (p ++ q) = encode p ++ encode q := by
  simp only [encode, List.flatMap_append]

theorem length_encode (p : Program) : (encode p).length = size p := by
  induction p with
  | nil => rfl
  | cons i p ih =>
    simp only [encode_cons, List.length_append, Instr.length_encode, ih, size, List.map_cons,
      List.sum_cons]

/-- Read bytes as a program. `none` on an undefined opcode or on a `PUSHn`
with fewer than `n` bytes after it. -/
def decode : List UInt8 → Option Program
  | [] => some []
  | b :: bs =>
    match pushWidth b with
    | some n =>
      if h : n.val ≤ bs.length then
        (decode (bs.drop n)).map (.push n ⟨(bs.take n).toArray, by simp only [List.size_toArray, List.length_take]; omega⟩ :: ·)
      else none
    | none =>
      match Op.ofCode b with
      | some o => (decode bs).map (.op o :: ·)
      | none => none
termination_by bs => bs.length
decreasing_by all_goals simp only [List.length_drop, List.length_cons]; omega

/-- `decode` inverts `encode`. -/
theorem decode_encode (p : Program) : decode (encode p) = some p := by
  induction p with
  | nil => simp only [encode_nil, decode]
  | cons i p ih =>
    cases i with
    | op o =>
      simp only [encode_cons, Instr.encode, List.cons_append, List.nil_append, decode,
        Op.pushWidth_code, Op.ofCode_code, ih, Option.map_some]
    | push n imm =>
      have hlen : n.val ≤ (imm.toList ++ encode p).length := by
        simp only [List.length_append, Vector.length_toList]; omega
      have htake : (imm.toList ++ encode p).take n = imm.toList :=
        List.take_left' Vector.length_toList
      have hdrop : (imm.toList ++ encode p).drop n = encode p :=
        List.drop_left' Vector.length_toList
      simp only [encode_cons, Instr.encode, List.cons_append, decode, pushWidth_pushCode, hlen,
        dite_true, hdrop, ih, Option.map_some, Option.some.injEq, List.cons.injEq, and_true]
      congr

/-- Distinct programs have distinct bytes. -/
theorem encode_injective {p q : Program} (h : encode p = encode q) : p = q := by
  have h' : decode (encode p) = decode (encode q) := by rw [h]
  rw [decode_encode, decode_encode] at h'
  exact Option.some.inj h'

/-- Whatever `decode` accepts re-encodes to the bytes it read. -/
theorem encode_decode {c : List UInt8} {p : Program} (h : decode c = some p) : encode p = c := by
  fun_induction decode c generalizing p with
  | case1 => cases h; rfl
  | case2 b bs n hw hn ih =>
    cases hd : decode (bs.drop n) with
    | none => simp only [hd, Option.map_none, reduceCtorEq] at h
    | some q =>
      simp only [hd, Option.map_some, Option.some.injEq] at h
      subst h
      simp only [encode_cons, Instr.encode, pushCode_of_pushWidth hw, ih hd, List.cons_append,
        Vector.toList_mk, List.take_append_drop]
  | case3 => cases h
  | case4 b bs hw o ho ih =>
    cases hd : decode bs with
    | none => simp only [hd, Option.map_none, reduceCtorEq] at h
    | some q =>
      simp only [hd, Option.map_some, Option.some.injEq] at h
      subst h
      simp only [encode_cons, Instr.encode, Op.code_ofCode ho, ih hd, List.cons_append,
        List.nil_append]
  | case5 => cases h

end Solidity.Backend
