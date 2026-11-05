import SolidityBridge.HashBridge.Prefix

/-! Constructed explicit-step controls, not X/source/native fixtures. In
particular cost zero is the supplied evaluator cost, not a claim that KECCAK
has zero gas cost. No canonical padded-memory equality is used. -/
namespace Solidity.HashBridge
open EvmYul

/-- Two real direct hashes separated by POP record the SAME symbolic bytes.
This is an importing client of the receipt, not a selected native digest or a
successful whole X run. Repeated inputs must not be treated as fresh queries. -/
theorem repeated_query_prefix (s : EVM.State) (offset size : UInt256)
    (tail : List UInt256)
    (hs : s.stack = offset :: size :: offset :: size :: tail) :
    ∃ out, ExplicitPrefix 3 s out
      [byteQuery (machineQuery s.toMachineState offset size),
       byteQuery (machineQuery s.toMachineState offset size)] ∧
      out.stack = actualDigest (machineQuery s.toMachineState offset size) :: tail ∧
      out.toState = s.toState ∧ out.memory = s.memory := by
  obtain ⟨first,hfirst,hstack1,hworld1,hmem1,_,_,_,_,_,_⟩ :=
    keccak_step_cost 0 0 s offset size (offset :: size :: tail) hs
  obtain ⟨middle,hpop,hstack2,hworld2,hmem2⟩ :=
    Evm.StorageSlots.pop_step first (actualDigest (machineQuery s.toMachineState offset size))
      (offset :: size :: tail) hstack1
  obtain ⟨out,hlast,hstack3,hworld3,hmem3,_,_,_,_,_,_⟩ :=
    keccak_step_cost 0 0 middle offset size tail hstack2
  have hbytes : machineQuery middle.toMachineState offset size =
      machineQuery s.toMachineState offset size := by
    change middle.memory.readWithPadding offset.toNat size.toNat =
      s.memory.readWithPadding offset.toNat size.toNat
    rw [hmem2,hmem1]
  have hp : ExplicitPrefix 3 s out
      (directQueries .KECCAK256 s ++ (directQueries .POP first ++
        (directQueries .KECCAK256 middle ++ []))) :=
    .cons hfirst (.cons hpop (.cons hlast (.nil out)))
  have hpopop : ((Operation.POP : Operation .EVM) == .KECCAK256) = false := rfl
  have htrace : ExplicitPrefix 3 s out
      [byteQuery (machineQuery s.toMachineState offset size),
       byteQuery (machineQuery s.toMachineState offset size)] := by
    simpa only [directQueries, hs, hstack2, beq_self_eq_true, hpopop,
      Bool.false_eq_true, if_false, if_pos rfl, List.cons_append, List.nil_append, hbytes] using hp
  rw [hbytes] at hstack3
  exact ⟨out,htrace,hstack3,hworld3.trans (hworld2.trans hworld1),
    hmem3.trans (hmem2.trans hmem1)⟩

/-- Repeated preimages satisfy the per-run collision premise without asserting
injectivity on different inputs or any distribution of the native provider. -/
theorem repeated_input_collision_free (bytes : ByteArray) :
    Hash.CollisionFree actualHash [byteQuery bytes,byteQuery bytes] := by
  apply (Hash.CollisionFree.singleton (f:=actualHash) (byteQuery bytes)).mono
  intro x hx
  simpa only [List.mem_cons, List.not_mem_nil, or_false, or_self] using hx

/-- A failed fuel-zero step cannot supply a successful prefix edge, even when
its input stack would make the pure query extractor nonempty. -/
theorem no_zero_fuel_edge (cost : Nat) (s : EVM.State) :
    ¬ ∃ out, EVM.step 0 cost (some (.KECCAK256,none)) s = .ok out := by
  rintro ⟨out,h⟩
  cases h

end Solidity.HashBridge
