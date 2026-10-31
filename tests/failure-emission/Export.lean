import Solidity.Backend.Failure.Emit

/-! Executable export of actual Backend.encode output for bounded external
vectors. This is not a proof or a new ABI encoder. -/
namespace Solidity.Backend.Failure.Export

def nums (bs : List UInt8) : String :=
  "[" ++ String.intercalate "," (bs.map (fun b => toString b.toNat)) ++ "]"

def framePrefix (a : Nat) (i : Input) : Program :=
  (if a = 0 then [] else [pushByte 0x55, pushNat (a - 1), .op .MSTORE8]) ++
  [pushByte 0x77, pushNat (a + i.bytes.length), .op .MSTORE8]

def vector (name : String) (a : Nat) (i : Input) (tailWords : Nat := 0)
    (suffix : Program := []) : IO Unit := do
  let p := framePrefix a i ++ List.replicate tailWords (.push ⟨0, by decide⟩ #v[]) ++ emit a i ++ suffix
  IO.println ("{\"name\":\"" ++ name ++ "\",\"offset\":" ++ toString a ++
    ",\"tailWords\":" ++ toString tailWords ++ ",\"code\":" ++ nums (encode p) ++
    ",\"payload\":" ++ nums i.bytes ++ "}")

#eval vector "empty_revert" 0 .empty
#eval vector "empty_return" 5 (.returned [])
#eval vector "panic01" 5 (.panic ⟨1, by decide⟩)
#eval vector "panic12" 31 (.panic ⟨0x12, by decide⟩)
#eval vector "error_boom" 7 (.reason [0x62, 0x6f, 0x6f, 0x6d])
#eval vector "error33" 31 (.reason (List.replicate 33 0x78))
#eval vector "custom_denied" 5 (.custom
  (Semantics.selectorBytes (Semantics.customSelector "Denied(uint256)") ++ Semantics.wordBytes 7))
#eval vector "raw_boundary65" 31 (.custom ((List.range 65).map UInt8.ofNat))
#eval vector "return_boundary65" 31 (.returned ((List.range 65).map UInt8.ofNat))
#eval vector "suffix_ignored" 31 (.returned [1, 2, 3]) 0 (emit 31 (.custom [9, 9]))
#eval vector "stack1022" 0 .empty 1022
#eval vector "stack1023" 0 .empty 1023
end Solidity.Backend.Failure.Export
