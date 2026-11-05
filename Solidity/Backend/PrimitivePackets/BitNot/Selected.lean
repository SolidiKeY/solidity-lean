import Solidity.Backend.PrimitivePackets.BitNot.Source
import Solidity.Evm.MemoryCompile

/-! Actual public selection of unsigned complement. Narrow widths retain the
existing modulo-2^bits mask after full-word NOT; uint256 needs no narrowing.
No requested CompiledVal, emitted program or desired run is a caller premise. -/
namespace Solidity.Backend.PrimitivePackets.BitNot
open Evm Evm.Memory Solidity.Lowering.V07

def value {C : Contract} {Γ : Ctx} (bits : Nat) (i : Idx Γ (.val .uint)) : Val C Γ .uint :=
  UnsignedComplement.complementValue bits (.simple (.local i))

def rawSelected {C : Contract} {Γ : Ctx} (offset : Nat) (F : Frag Γ) (i : Idx Γ (.val .uint)) :
    CompiledVal offset F (.unop .bnot rfl rfl (.simple (.local i)) : Val C Γ .uint) :=
  ⟨unaryCode .bnot (Evm.compileVal (C:=C) offset (.simple (.local i))),
    .unary .bnot rfl rfl _ _ (.core _ rfl)⟩

def selectionExists {C : Contract} {Γ : Ctx} (offset : Nat) (F : Frag Γ) (e : Val C Γ .uint) : Bool :=
  (Memory.compileVal offset F e).isSome

def emittedCode {C : Contract} {Γ : Ctx} (offset : Nat) (F : Frag Γ) (e : Val C Γ .uint) : Option (List Instr) :=
  (Memory.compileVal offset F e).map (fun compiled => compiled.code)

theorem compilable {C : Contract} {Γ : Ctx} (bits offset : Nat) (F : Frag Γ) (i : Idx Γ (.val .uint)) :
    (Memory.compileVal offset F (value (C:=C) bits i)).isSome := by
  change selectionExists offset F (value bits i) = true
  by_cases narrow : bits < 256
  · have expression : value (C:=C) bits i = .binop .mod rfl rfl (.unop .bnot rfl rfl (.simple (.local i)))
        (.simple (.lit ((2^bits : Nat) : Int) (UnsignedNarrowing.modulus_range bits narrow))) := by
      simp only [value,UnsignedComplement.complementValue,UnsignedCasts.castValue,dif_pos narrow]
    rw [expression]
    rfl
  · have expression : value (C:=C) bits i = .unop .bnot rfl rfl (.simple (.local i)) := by
      simp only [value,UnsignedComplement.complementValue,UnsignedCasts.castValue,dif_neg narrow]
    rw [expression]
    rfl

def selected {C : Contract} {Γ : Ctx} (bits offset : Nat) (F : Frag Γ) (i : Idx Γ (.val .uint)) :
    CompiledVal offset F (value (C:=C) bits i) :=
  (Memory.compileVal offset F (value bits i)).get (compilable bits offset F i)

theorem public_selection {C : Contract} {Γ : Ctx} (bits offset : Nat) (F : Frag Γ) (i : Idx Γ (.val .uint)) :
    Memory.compileVal offset F (value (C:=C) bits i) = some (selected bits offset F i) :=
  (Option.some_get (compilable bits offset F i)).symm

theorem compiled_code {C : Contract} {Γ : Ctx} (bits offset : Nat) (F : Frag Γ) (i : Idx Γ (.val .uint)) :
    (Memory.compileVal offset F (value (C:=C) bits i)).map (fun compiled => compiled.code) =
    some (if narrow : bits < 256 then
      binaryCode .uint .mod
        (unaryCode .bnot (Evm.compileVal (C:=C) offset (.simple (.local i))))
        (Evm.compileVal (C:=C) (Γ:=Γ) offset (.simple (.lit ((2^bits : Nat) : Int)
          (UnsignedNarrowing.modulus_range bits narrow))))
    else unaryCode .bnot (Evm.compileVal (C:=C) offset (.simple (.local i)))) := by
  change emittedCode offset F (value bits i) = _
  by_cases narrow : bits < 256
  · have expression : value (C:=C) bits i = .binop .mod rfl rfl (.unop .bnot rfl rfl (.simple (.local i)))
        (.simple (.lit ((2^bits : Nat) : Int) (UnsignedNarrowing.modulus_range bits narrow))) := by
      simp only [value,UnsignedComplement.complementValue,UnsignedCasts.castValue,dif_pos narrow]
    rw [expression,dif_pos narrow]
    rfl
  · have expression : value (C:=C) bits i = .unop .bnot rfl rfl (.simple (.local i)) := by
      simp only [value,UnsignedComplement.complementValue,UnsignedCasts.castValue,dif_neg narrow]
    rw [expression,dif_neg narrow]
    rfl

theorem narrow_code {C : Contract} {Γ : Ctx} (bits offset : Nat) (F : Frag Γ) (i : Idx Γ (.val .uint))
    (narrow : bits < 256) :
    (selected (C:=C) bits offset F i).code =
      binaryCode .uint .mod
        (unaryCode .bnot (Evm.compileVal (C:=C) offset (.simple (.local i))))
        (Evm.compileVal (C:=C) (Γ:=Γ) offset (.simple (.lit ((2^bits : Nat) : Int)
          (UnsignedNarrowing.modulus_range bits narrow)))) := by
  have code := compiled_code (C:=C) bits offset F i
  rw [public_selection] at code
  simpa only [Option.map_some,Option.some.injEq,dif_pos narrow] using code

theorem full_code {C : Contract} {Γ : Ctx} (offset : Nat) (F : Frag Γ) (i : Idx Γ (.val .uint)) :
    (selected (C:=C) 256 offset F i).code =
      Evm.compileVal (C:=C) offset (.simple (.local i)) ++ [.not] := by
  rfl
end Solidity.Backend.PrimitivePackets.BitNot

/-- info: 'Solidity.Backend.PrimitivePackets.BitNot.compilable' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Solidity.Backend.PrimitivePackets.BitNot.compilable
/-- info: 'Solidity.Backend.PrimitivePackets.BitNot.public_selection' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Solidity.Backend.PrimitivePackets.BitNot.public_selection
/-- info: 'Solidity.Backend.PrimitivePackets.BitNot.compiled_code' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Solidity.Backend.PrimitivePackets.BitNot.compiled_code
/-- info: 'Solidity.Backend.PrimitivePackets.BitNot.narrow_code' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Solidity.Backend.PrimitivePackets.BitNot.narrow_code
/-- info: 'Solidity.Backend.PrimitivePackets.BitNot.full_code' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Solidity.Backend.PrimitivePackets.BitNot.full_code
/-- info: 'Solidity.Backend.PrimitivePackets.BitNot.rawSelected' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms Solidity.Backend.PrimitivePackets.BitNot.rawSelected
/-- info: 'Solidity.Backend.PrimitivePackets.BitNot.selected' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Solidity.Backend.PrimitivePackets.BitNot.selected
