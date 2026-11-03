import SolidityBridge.ExternalEvm.Assembly.Scanner

/-! H7 supplies the bounded vendor equation missing at the published Scanner
producer. That producer's historical opaque-interface header is superseded by
this separately pinned patch; its ScanPath/width/uniqueness proofs are reused.
No equality with a formerly opaque constant or arbitrary-code totalization is
claimed. Outside the bound the original partial executable is retained. -/
namespace Solidity.Evm.External.Assembly
open EvmYul EvmYul.EVM

theorem scanner_word_rebuild (pc : UInt256) : UInt256.ofNat pc.toNat = pc := by
  apply congrArg UInt256.mk
  apply Fin.ext
  exact Nat.mod_eq_of_lt pc.val.isLt

theorem scanner_next_nat (code : ByteArray) (pc : UInt256) (op : Operation .EVM)
    (bound : code.size + 33 < W) (inside : pc.toNat < code.size) :
    (N pc op).toNat = pc.toNat + 1 + argOnNBytesOfInstr op := by
  have width : argOnNBytesOfInstr op ≤ 32 := argument_width_bound op
  have fits : pc.toNat + 1 + argOnNBytesOfInstr op < W := by omega
  have he : N pc op = .ofNat (pc.toNat + 1 + argOnNBytesOfInstr op) := by
    change (pc + .ofNat 1) + .ofNat (argOnNBytesOfInstr op) = _
    calc
      _ = ((UInt256.ofNat pc.toNat) + .ofNat 1) + .ofNat (argOnNBytesOfInstr op) := by
        rw [scanner_word_rebuild]
      _ = _ := by rw [word_add,word_add]
  exact (congrArg UInt256.toNat he).trans (word_nat _ fits)

/-- The actual bounded vendor traversal has exactly the published parse/N
path destinations, including arbitrary accumulator order and duplicates. -/
theorem ScanPath.vendor_scan {code : ByteArray} {pc : UInt256}
    {destinations : List UInt256} (path : ScanPath code pc destinations)
    (bound : code.size + 33 < W) (acc : Array UInt256) :
    D_J_scan code pc.toNat acc = acc ++ destinations.toArray := by
  induction path generalizing acc with
  | stop pc parsed =>
    rw [D_J_scan]
    by_cases inside : pc.toNat < code.size
    · rw [dif_pos inside,parsed]
      exact Array.append_empty.symm
    · rw [dif_neg inside]
      exact Array.append_empty.symm
  | step pc op tail parsed next ih =>
    have inside : pc.toNat < code.size := by
      by_contra outside
      simp only [ByteArray.get?,dif_neg outside] at parsed
      cases parsed
    rw [D_J_scan,dif_pos inside,parsed]
    change D_J_scan code (pc.toNat + 1 + argOnNBytesOfInstr op)
      (if op = .JUMPDEST then acc.push (.ofNat pc.toNat) else acc) = _
    rw [←scanner_next_nat code pc op bound inside,ih]
    by_cases jump : op = .JUMPDEST
    · simp only [if_pos jump]
      rw [List.toArray_cons,scanner_word_rebuild,Array.append_singleton_assoc]
    · simp only [if_neg jump]

theorem ScanPath.vendor_aux {code : ByteArray} {pc : UInt256}
    {destinations : List UInt256} (path : ScanPath code pc destinations)
    (bound : code.size + 33 < W) (acc : Array UInt256) :
    D_J_aux code pc acc = acc ++ destinations.toArray := by
  rw [D_J_aux_bounded code pc acc bound]
  exact path.vendor_scan bound acc

theorem scanResult_actual_destinations {code : ByteArray} {pc : UInt256}
    (scan : ScanResult code pc) (bound : code.size + 33 < W) :
    D_J code pc = scan.destinations.toArray := by
  rw [D_J,scan.path.vendor_aux bound #[],Array.empty_append]

/-- No supplied successful scan/path premise: the published total constructor
produces one from the actual code bound for every initial word PC. -/
theorem bounded_actual_scan (code : ByteArray) (pc : UInt256)
    (bound : code.size + 33 < W) (acc : Array UInt256) :
    ∃ result : ScanResult code pc, D_J_aux code pc acc = acc ++ result.destinations.toArray := by
  have fits : pc.toNat < W := pc.val.isLt
  obtain ⟨scan,hs⟩ := scanFrom_success code bound pc.toNat fits
  have result : ScanResult code pc := by
    simpa only [scanner_word_rebuild] using scan
  exact ⟨result,result.path.vendor_aux bound acc⟩

end Solidity.Evm.External.Assembly
