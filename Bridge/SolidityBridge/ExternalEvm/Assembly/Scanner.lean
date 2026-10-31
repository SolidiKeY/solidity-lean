import SolidityBridge.ExternalEvm.Assembly.Static

/-! A kernel-visible certificate for the upstream scanner's actual
parse/next-PC relation. The pinned partial D_J_aux remains untouched and
opaque. We do not assert an unproved equation for that opaque function.
The certified destination array is suitable as the explicit validJumps input
to the actual upstream X driver; its instruction boundaries are proved.
-/
namespace Solidity.Evm.External.Assembly

inductive ScanPath (code : ByteArray) : EvmYul.UInt256 → List EvmYul.UInt256 → Prop where
  | stop (pc) (h : (code.get? pc.toNat >>= EvmYul.EVM.parseInstr) = none) : ScanPath code pc []
  | step (pc) (op : EvmYul.Operation .EVM) (tail : List EvmYul.UInt256)
      (parsed : (code.get? pc.toNat >>= EvmYul.EVM.parseInstr) = some op)
      (next : ScanPath code (EvmYul.EVM.N pc op) tail) :
      ScanPath code pc (if op = .JUMPDEST then pc :: tail else tail)

structure ScanResult (code : ByteArray) (pc : EvmYul.UInt256) where
  destinations : List EvmYul.UInt256
  path : ScanPath code pc destinations

/-- Every reported destination decodes as JUMPDEST along a genuine sequence
of upstream instruction boundaries, not a search for raw 0x5b bytes. -/
theorem ScanPath.valid {code : ByteArray} {pc : EvmYul.UInt256}
    {destinations : List EvmYul.UInt256} (path : ScanPath code pc destinations) :
    ∀ d ∈ destinations, EvmYul.EVM.decode code d = some (.JUMPDEST, none) := by
  induction path with
  | stop => intro d h; cases h
  | step pc op tail parsed _ ih =>
    intro d hd
    by_cases ho : op = .JUMPDEST
    · subst op
      change d ∈ pc :: tail at hd
      cases hd with
      | head =>
        unfold EvmYul.EVM.decode
        rw [parsed]
        rfl
      | tail _ hd => exact ih d hd
    · simp only [if_neg ho] at hd
      exact ih d hd

/-- The recursion measure is bytes remaining. PUSH payloads are skipped by
actual upstream argOnNBytesOfInstr; no semantic fuel/search bound is added. -/
def scanFrom (code : ByteArray) (pc : Nat) (fits : pc < W) :
    Option (ScanResult code (.ofNat pc)) :=
  if hb : pc < code.size then
    match parsed : code.get? pc >>= EvmYul.EVM.parseInstr with
    | none => some ⟨[], .stop (.ofNat pc) (by rw [word_nat _ fits]; exact parsed)⟩
    | some op => do
      let next := pc + 1 + EvmYul.EVM.argOnNBytesOfInstr op
      if hn : next < W then
        let tail ← scanFrom code next hn
        have he : EvmYul.EVM.N (.ofNat pc) op = .ofNat next := by
          change (EvmYul.UInt256.ofNat pc + .ofNat 1) +
            .ofNat (EvmYul.EVM.argOnNBytesOfInstr op) = .ofNat next
          rw [word_add, word_add]
        return ⟨if op = .JUMPDEST then .ofNat pc :: tail.destinations else tail.destinations,
          .step (.ofNat pc) op tail.destinations
            (by rw [word_nat _ fits]; exact parsed) (by rw [he]; exact tail.path)⟩
      else none
  else
    some ⟨[], .stop (.ofNat pc) (by
      rw [word_nat _ fits]
      unfold ByteArray.get?
      rw [dif_neg hb]
      rfl)⟩
termination_by code.size - pc
decreasing_by simp_wf; omega

def scanCode (code : ByteArray) : Option (ScanResult code (.ofNat 0)) :=
  scanFrom code 0 (by decide)

theorem ScanResult.valid {code : ByteArray} {pc : EvmYul.UInt256} (scan : ScanResult code pc) :
    ∀ d ∈ scan.destinations, EvmYul.EVM.decode code d = some (.JUMPDEST, none) := scan.path.valid

/-- The scanner's step width is the pinned upstream opcode width. -/
theorem argument_width_bound (op : EvmYul.Operation .EVM) :
    EvmYul.EVM.argOnNBytesOfInstr op ≤ 32 := by
  cases op <;> rename_i tag <;> cases tag <;> decide

/-- Scanning a realistically word-bounded byte array cannot fail. The bound
comes from the actual code length and maximum immediate width, not fuel. -/
theorem scanFrom_success (code : ByteArray) (bound : code.size + 33 < W)
    (pc : Nat) (fits : pc < W) : ∃ result, scanFrom code pc fits = some result := by
  rw [scanFrom.eq_def]
  by_cases hb : pc < code.size
  · rw [dif_pos hb]
    split
    next hp => exact ⟨_, rfl⟩
    next op hp =>
      have width := argument_width_bound op
      have hn : pc + 1 + EvmYul.EVM.argOnNBytesOfInstr op < W := by omega
      rw [dif_pos hn]
      obtain ⟨tail, ht⟩ := scanFrom_success code bound
        (pc + 1 + EvmYul.EVM.argOnNBytesOfInstr op) hn
      rw [ht]
      exact ⟨_, rfl⟩
  · rw [dif_neg hb]
    exact ⟨_, rfl⟩
termination_by code.size - pc
decreasing_by omega

/-- Scanner-path destinations are unique for the actual deterministic
upstream parse/next-PC relation. This avoids opaque-function evaluation. -/
theorem ScanPath.unique {code : ByteArray} {pc : EvmYul.UInt256}
    {a b : List EvmYul.UInt256} (pa : ScanPath code pc a) (pb : ScanPath code pc b) : a = b := by
  induction pa generalizing b with
  | stop pc ha =>
    cases pb with
    | stop => rfl
    | step _ _ _ hb _ => rw [ha] at hb; cases hb
  | step pc op tail ha _ ih =>
    cases pb with
    | stop _ hb => rw [hb] at ha; cases ha
    | step _ op' tail' hb next =>
      have hop : op = op' := Option.some.inj (ha.symm.trans hb)
      subst op'
      rw [ih next]

end Solidity.Evm.External.Assembly
