import SolidityBridge.ExternalEvm.Assembly.Layout

/-! Executable layout controls. These deliberately make no source/target
execution-simulation claim; the actual core runs below pin branch polarity. -/
namespace Solidity.Evm.External.Assembly

private def branch : List Instr :=
  [.push w[1], .jumpi 1, .push w[7], .push w[9]]

#guard span branch = some 137
#guard (resolve branch 0 1 1).map (fun r => r.pc.val) = some 103
#guard (resolve branch 0 1 2).map (fun r => r.pc.val) = some 137
#guard (resolve branch 0 1 3).isNone
#guard (resolve branch 0 0 0).map (fun r => r.pc.val) = some 34
#guard (assemble branch).isSome
#guard (assemble [.jump 0]).isSome
#guard (assemble [.jump 1]).isNone
#guard (assemble [.jumpi 1]).isNone
#guard (assemble [.sload]).isNone
#guard (assemble [.push (.slot (.root 0))]).isNone

-- A continuation at the greatest word PC fits; advancing beyond it refuses.
#guard (assemble [] (W - 1)).isSome
#guard (assemble [] W).isNone
#guard (assemble [.jump 0] (W - 36)).isSome
#guard (assemble [.jump 0] (W - 35)).isNone

-- Loop code has its own forward-label scopes and two absolute loop edges.
#guard span [.loop [.push w[0]] []] = some 106
#guard targets [.loop [.push w[0]] []] 0 = some [0, 106]
#guard (assemble [.loop [.push w[0]] []]).isSome
#guard (assemble [.loop [.push w[1]] [.loop [.push w[0]] []]]).isSome
#guard (assemble [.loop [.jump 1] []]).isNone

private def branchBytes : List UInt8 :=
  [0x5b] ++ push32 ⟨1, by decide⟩ ++ [0x5b] ++
  push32 ⟨103, by decide⟩ ++ [0x57, 0x5b] ++
  push32 ⟨7, by decide⟩ ++ [0x5b] ++ push32 ⟨9, by decide⟩ ++ [0x5b]

private theorem branch_emitted : emit branch 0 = some branchBytes := by
  simp only [branch, emit.eq_def, emitInstr.eq_def, width, resolve, address]
  rfl

private theorem branch_targets : targets branch 0 = some [103] := by
  simp only [branch, targets.eq_def, instrTargets.eq_def, width, resolve, address]
  rfl

-- An inhabited layout certificate for a real branch, checked by the kernel.
private def branchImage : Image branch 0 where
  bytes := branchBytes
  size := 137
  span_eq := rfl
  emitted := branch_emitted
  length_eq := by decide +kernel
  fits := by decide
  destinations := by
    have hd : ∀ l : Label branch, (address branch 0 l).any
        (fun n => branchBytes[n]? == some 0x5b) = true := by decide +kernel
    intro l
    have hh := hd l
    cases ha : address branch 0 l with
    | none => simp only [ha, Option.any_none, Bool.false_eq_true] at hh
    | some n =>
      refine ⟨n, rfl, ?_⟩
      simpa only [ha, Option.any_some, beq_iff_eq, Nat.sub_zero] using hh
  refs := [103]
  targets_eq := branch_targets
  validRefs := by decide +kernel

example : Nonempty (Image branch 0) := ⟨branchImage⟩
example : resolve [.jump 1] 0 0 1 = none :=
  resolve_out_of_bounds _ _ _ _ (by decide)

example : run branch Machine.init = .ok {Machine.init with stack := [w[9]]} 0 := rfl

example : run [.push w[0], .jumpi 1, .push w[7], .push w[9]] Machine.init =
    .ok {Machine.init with stack := [w[9], w[7]]} 0 := rfl

example : (Instr.loop [.push w[0]] []).step Machine.init = .ok Machine.init 0 := by
  exact loopRun_of_iterN (n := 1) rfl

end Solidity.Evm.External.Assembly

/-- info: 'Solidity.Evm.External.Assembly.resolve_in_bounds' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms Solidity.Evm.External.Assembly.resolve_in_bounds
/-- info: 'Solidity.Evm.External.Assembly.resolve_out_of_bounds' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Solidity.Evm.External.Assembly.resolve_out_of_bounds
/-- info: 'Solidity.Evm.External.Assembly.push32_length' depends on axioms: [propext] -/
#guard_msgs in #print axioms Solidity.Evm.External.Assembly.push32_length
/-- info: 'Solidity.Evm.External.Assembly.assembled_destination' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms Solidity.Evm.External.Assembly.assembled_destination
