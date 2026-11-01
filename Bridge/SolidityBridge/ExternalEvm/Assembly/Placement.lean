import SolidityBridge.ExternalEvm.Assembly.Composition

namespace Solidity.Evm.External.Assembly

/-- Framing preserves the actual relocated byte slice. -/
theorem Boundary.placed {code : List Instr} {base index : Nat} {image : Image code base}
    {frame s : EvmYul.EVM.State} {m : Machine} (boundary : Boundary image frame index m s)
    (placement : Placed image frame) : Placed image s := by
  unfold Placed at placement ⊢
  have hc : s.executionEnv.code = frame.executionEnv.code :=
    congrArg (fun x : EvmYul.State .EVM => x.executionEnv.code) boundary.state
  rw [hc]
  exact placement

/-- A placed image's local certified byte is the actual ambient code byte. -/
theorem placed_byte {code : List Instr} {base : Nat} (image : Image code base)
    (s : EvmYul.EVM.State) (placement : Placed image s)
    (n : Nat) (lower : base ≤ n) (byte : UInt8) (h : image.bytes[n - base]? = some byte) :
    s.executionEnv.code.get? n = some byte := by
  have hi : n - base < image.bytes.length := (List.getElem?_eq_some_iff.mp h).choose
  have hp := congrArg (fun bytes : List UInt8 => bytes[n - base]?) placement
  change ((s.executionEnv.code.data.toList.drop base).take image.bytes.length)[n - base]? = image.bytes[n - base]? at hp
  rw [List.getElem?_take_of_lt hi, List.getElem?_drop, Nat.add_sub_of_le lower] at hp
  rw [h] at hp
  have ha : s.executionEnv.code.data[n]? = some byte := by
    simpa only [Array.getElem?_toList] using hp
  have hb : n < s.executionEnv.code.data.size := by
    cases hh : s.executionEnv.code.data[n]? with
    | none => rw [hh] at ha; cases ha
    | some b => exact Array.getElem?_eq_some_iff.mp hh |>.choose
  unfold ByteArray.get?
  have hb' : n < s.executionEnv.code.size := hb
  rw [dif_pos hb']
  apply congrArg some
  exact (Array.getElem?_eq_some_iff.mp ha).choose_spec

/-- Raw JUMPDEST bytes plus real placement prove actual destination decoding.
This is distinct from membership in the upstream scanner's result. -/
theorem Image.decoded_destination {code : List Instr} {base : Nat} (image : Image code base)
    (s : EvmYul.EVM.State) (placement : Placed image s) (label : Label code) :
    ∃ n : Fin W, address code base label = some n.val ∧
      EvmYul.EVM.decode s.executionEnv.code (.ofNat n.val) = some (.JUMPDEST, none) := by
  obtain ⟨n, ha, hd⟩ := image.destinations label
  have lower : base ≤ n := by
    unfold address at ha
    cases hs : span (code.take label.val) with
    | none => simp only [hs, Option.map_none, reduceCtorEq] at ha
    | some k =>
      simp only [hs, Option.map_some, Option.some.injEq] at ha
      omega
  have hb : n - base < image.bytes.length := (List.getElem?_eq_some_iff.mp hd).choose
  have hn : n < W := by rw [image.length_eq] at hb; have hf := image.fits; omega
  refine ⟨⟨n, hn⟩, ha, ?_⟩
  have byte := placed_byte image s placement n lower 0x5b hd
  have pc : (EvmYul.UInt256.ofNat n).toNat = n := Nat.mod_eq_of_lt hn
  unfold EvmYul.EVM.decode
  rw [pc, byte]
  rfl

end Solidity.Evm.External.Assembly

/-- info: 'Solidity.Evm.External.Assembly.Image.decoded_destination' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Solidity.Evm.External.Assembly.Image.decoded_destination
