import Solidity.Evm.Machine

/-!
Typed labels and byte layout for the existing core instruction language.
Every instruction boundary (including the continuation) has a JUMPDEST.
PUSH32 keeps relocation sizes independent of the destination. This module
only resolves code layout; it does not assert execution correspondence.
-/
namespace Solidity.Evm.External.Assembly

/-- A boundary in this particular core code, including its continuation. -/
abbrev Label (code : List Instr) := Fin (code.length + 1)

mutual
  /-- Bytes before the next core instruction's boundary, including this
  instruction's leading JUMPDEST. Unsupported instructions have no layout. -/
  def width : Instr → Option Nat
    | .push (.val _) => some 34
    | .pop => some 2
    | .jump _ | .jumpi _ => some 35
    | .loop c b => do return (← span c) + (← span b) + 72
    | _ => none
  /-- Excludes the final continuation JUMPDEST. -/
  def span : List Instr → Option Nat
    | [] => some 0
    | i :: rest => do return (← width i) + (← span rest)
end

/-- Every prefix must itself have supported widths. -/
def address (code : List Instr) (base : Nat) (label : Label code) : Option Nat :=
  (span (code.take label.val)).map (base + ·)

/-- A relocation carries both the relative instruction count and exact
absolute word address. Neither out-of-code labels nor wrapped PCs inhabit it. -/
structure Relocation (code : List Instr) (base origin offset : Nat) where
  target : Label code
  relative : target.val = origin + 1 + offset
  pc : Fin W
  exactAddress : address code base target = some pc.val

/-- Refuse a forward offset outside this code, an unsupported prefix, or
an address that would wrap when encoded as an EVM word. -/
def resolve (code : List Instr) (base origin offset : Nat) :
    Option (Relocation code base origin offset) := do
  if h : origin + 1 + offset < code.length + 1 then
    let target : Label code := ⟨origin + 1 + offset, h⟩
    match ha : address code base target with
    | none => none
    | some n =>
      if hn : n < W then
        some ⟨target, rfl, ⟨n, hn⟩, ha⟩
      else none
  else none

theorem resolve_relative {code : List Instr} {base origin offset : Nat}
    (r : Relocation code base origin offset) :
    r.target.val = origin + 1 + offset := r.relative

theorem resolve_absolute {code : List Instr} {base origin offset : Nat}
    (r : Relocation code base origin offset) :
    address code base r.target = some r.pc.val := r.exactAddress

theorem resolve_in_bounds {code : List Instr} {base origin offset : Nat}
    (r : Relocation code base origin offset) : origin + 1 + offset ≤ code.length := by
  have h : r.target.val < code.length + 1 := r.target.isLt
  rw [r.relative] at h
  omega

theorem resolve_out_of_bounds (code : List Instr) (base origin offset : Nat)
    (h : code.length < origin + 1 + offset) : resolve code base origin offset = none := by
  simp only [resolve]
  split
  · omega
  · rfl

/-- Big-endian fixed-width immediate; word truncation cannot occur because
its input already inhabits Fin W. -/
def push32 (w : Fin W) : List UInt8 :=
  0x7f :: (List.range 32).map (fun j => UInt8.ofNat (w.val / 256 ^ (31 - j) % 256))

theorem push32_length (w : Fin W) : (push32 w).length = 33 := by
  simp only [push32, List.length_cons, List.length_map, List.length_range]

/-! Assemble an existing list directly, without an intermediate source IR.
Nested loop components have their own label scopes, as does core exec. -/
mutual
  def emit (code : List Instr) (base : Nat) : Option (List UInt8) :=
    match code with
    | [] => some [0x5b]
    | i :: rest => do
      let w ← width i
      let body ← emitInstr i rest base
      let tail ← emit rest (base + w)
      return 0x5b :: (body ++ tail)
  termination_by sizeOf code
  decreasing_by all_goals simp_wf <;> omega
  def emitInstr (i : Instr) (rest : List Instr) (base : Nat) : Option (List UInt8) :=
    match i with
    | .push (.val w) => some (push32 w)
    | .pop => some [0x50]
    | .jump n => do
      let r ← resolve (i :: rest) base 0 n
      return push32 r.pc ++ [0x56]
    | .jumpi n => do
      let r ← resolve (i :: rest) base 0 n
      return push32 r.pc ++ [0x57]
    | .loop c b => do
      let cw ← span c
      let bw ← span b
      let cond ← emit c (base + 1)
      let body ← emit b (base + cw + 37)
      if hentry : base < W then
        if hexit : base + cw + bw + 72 < W then
          return cond ++ [0x15] ++ push32 ⟨base + cw + bw + 72, hexit⟩ ++
            [0x57] ++ body ++ push32 ⟨base, hentry⟩ ++ [0x56]
        else none
      else none
    | _ => none
  termination_by sizeOf i + sizeOf rest
  decreasing_by all_goals simp_wf <;> omega
end

/-! The absolute destinations used by the emitted macros, including nested
loop entry/exit edges. This is target metadata, not another source language. -/
mutual
  def targets (code : List Instr) (base : Nat) : Option (List Nat) :=
    match code with
    | [] => some []
    | i :: rest => do
      let w ← width i
      let here ← instrTargets i rest base
      let later ← targets rest (base + w)
      return here ++ later
  termination_by sizeOf code
  decreasing_by all_goals simp_wf <;> omega
  def instrTargets (i : Instr) (rest : List Instr) (base : Nat) : Option (List Nat) :=
    match i with
    | .push (.val _) | .pop => some []
    | .jump n | .jumpi n => do
      let r ← resolve (i :: rest) base 0 n
      return [r.pc.val]
    | .loop c b => do
      let cw ← span c
      let bw ← span b
      let ct ← targets c (base + 1)
      let bt ← targets b (base + cw + 37)
      return base :: (base + cw + bw + 72) :: (ct ++ bt)
    | _ => none
  termination_by sizeOf i + sizeOf rest
  decreasing_by all_goals simp_wf <;> omega
end

/-- Checked output: all core boundaries contain JUMPDEST bytes and the
whole image fits in the word address space. This is a layout certificate,
not a driver/gas or execution-simulation certificate. -/
structure Image (code : List Instr) (base : Nat) where
  bytes : List UInt8
  size : Nat
  span_eq : span code = some size
  emitted : emit code base = some bytes
  length_eq : bytes.length = size + 1
  fits : base + size < W
  destinations : ∀ l : Label code, ∃ n, address code base l = some n ∧
    bytes[n - base]? = some 0x5b
  refs : List Nat
  targets_eq : targets code base = some refs
  validRefs : ∀ n ∈ refs, base ≤ n ∧ n < W ∧ bytes[n - base]? = some 0x5b

/-- Finite validation installs the layout invariants in the output type.
The assembler refuses when an invariant is not established. -/
def assemble (code : List Instr) (base : Nat := 0) : Option (Image code base) := do
  match hs : span code, he : emit code base, ht : targets code base with
  | some size, some bytes, some refs =>
    if hl : bytes.length = size + 1 then
      if hf : base + size < W then
        if hd : ∀ l : Label code, (address code base l).any
            (fun n => bytes[n - base]? == some 0x5b) = true then
          if hr : ∀ n ∈ refs, base ≤ n ∧ n < W ∧ bytes[n - base]? = some 0x5b then
            some ⟨bytes, size, hs, he, hl, hf, fun l => by
              have hh := hd l
              cases ha : address code base l with
              | none => simp only [ha, Option.any_none, Bool.false_eq_true] at hh
              | some n =>
                refine ⟨n, rfl, ?_⟩
                simpa only [ha, Option.any_some, beq_iff_eq] using hh,
              refs, ht, hr⟩
          else none
        else none
      else none
    else none
  | _, _, _ => none

/-- Every returned label points to a JUMPDEST byte, including the exit. -/
theorem assembled_destination {code : List Instr} {base : Nat}
    (image : Image code base) (l : Label code) :
    ∃ n, address code base l = some n ∧ image.bytes[n - base]? = some 0x5b :=
  image.destinations l

end Solidity.Evm.External.Assembly
