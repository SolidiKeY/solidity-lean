import SolidityBridge.RoadmapV15.P10.WordPushConsumer

/-! Jump-table transport for the actual charged dispatcher. The existing emitter,
decoder and PUSH32 producer are consumed read-only. The result is a single
fetched step/X continuation, not table correctness for a later jump or callee. -/
namespace SolidityBridge.RoadmapV15.P10
open Solidity Solidity.Backend EvmYul Solidity.Evm.External

/-- Every original gas/stack/static/memory check is retained; only the unused
jump-destination array changes. JUMP and JUMPI remain explicitly excluded. -/
theorem nonbranch_gate_tables_eq (left right : Array UInt256) (s : EVM.State)
    (op : Operation .EVM) (jump : op ≠ .JUMP) (jumpi : op ≠ .JUMPI) :
    Assembly.driverGate left s op = Assembly.driverGate right s op := by
  simp only [Assembly.driverGate,jump,jumpi,false_and,if_false]

private theorem checked_tables (left right : Array UInt256) (s : EVM.State)
    (packet : Assembly.Packet) (decoded : EVM.decode s.executionEnv.code s.pc = some packet)
    (jump : packet.1 ≠ .JUMP) (jumpi : packet.1 ≠ .JUMPI) (fuel : Nat) :
    Assembly.driverSteps 1 (fuel+2) left s = Assembly.driverSteps 1 (fuel+2) right s := by
  simp only [Assembly.driverSteps,decoded,Option.option,bind,Except.bind]
  rw [nonbranch_gate_tables_eq left right s packet.1 jump jumpi]

/-- Actual fetched PUSH32 has identical success or failure for all tables,
including low fuel, low gas and full input stacks. No execution premise. -/
theorem word_push_checked_tables (left right : Array UInt256) (seed : EVM.State)
    (before after : Backend.Program) (w : Scalar.Word) (words : Scalar.Stack)
    (fits : (Backend.encode before).length < UInt256.size) (fuel : Nat) :
    Assembly.driverSteps 1 fuel left (wordPushInput seed before after w words) =
      Assembly.driverSteps 1 fuel right (wordPushInput seed before after w words) := by
  cases fuel with
  | zero => rfl
  | succ fuel =>
    cases fuel with
    | zero => rfl
    | succ fuel =>
      exact checked_tables left right _ (.Push .PUSH32,some (UInt256.mk w.toFin,32))
        (decode_word_push seed before after w words fits)
        (by change (Operation.Push .PUSH32 : Operation .EVM) ≠ .JUMP;decide)
        (by change (Operation.Push .PUSH32 : Operation .EVM) ≠ .JUMPI;decide) fuel

private theorem counted_continuation (valid : Array UInt256) (s next : EVM.State)
    (packet : Assembly.Packet) (fuel : Nat)
    (decoded : EVM.decode s.executionEnv.code s.pc = some packet)
    (running : Assembly.NonhaltingOpcode packet.1)
    (counted : Assembly.driverSteps 1 (fuel+2) valid s = .ok next) :
    EVM.X (fuel+2) valid s = EVM.X (fuel+1) valid next := by
  simp only [Assembly.driverSteps,decoded,Option.option,bind,Except.bind] at counted
  cases gate : Assembly.driverGate valid s packet.1 with
  | error e =>
    simp only [gate] at counted
    cases counted
  | ok pair =>
    rcases pair with ⟨charged,cost⟩
    rw [gate] at counted
    dsimp only at counted
    cases step : EVM.step (fuel+1) cost (some packet) charged with
    | error e =>
      simp only [step] at counted
      cases counted
    | ok actual =>
      simp only [step] at counted
      have same : actual = next := Except.ok.inj counted
      subst next
      exact Assembly.X_continue fuel valid s charged actual packet cost decoded gate step running

/-- Consume the actual emitted big-endian word, checked PUSH producer and native
step. No decoder, charged gate, successful run or caller-frame fact is assumed. -/
theorem word_push_table_agreement (valid : Array UInt256) (seed : EVM.State)
    (before after : Backend.Program) (w : Scalar.Word) (words : Scalar.Stack)
    (fits : (Backend.encode before).length < UInt256.size)
    (gas : 3 ≤ seed.gasAvailable.toNat) (room : words.length+1 ≤ 1024) (fuel : Nat) :
    let input := wordPushInput seed before after w words
    let next := (Assembly.chargedPrepare input 3).replaceStackAndIncrPC
      ((w::words).map (fun x => UInt256.mk x.toFin)) 33
    Scalar.step (Scalar.pushWord w) words = some (w::words) ∧
    Assembly.driverSteps 1 (fuel+2) valid input = .ok next ∧
    EVM.X (fuel+2) valid input = EVM.X (fuel+1) valid next := by
  dsimp only
  have producer := word_push_agreement seed before after w words fits gas room fuel
  let input := wordPushInput seed before after w words
  let next := (Assembly.chargedPrepare input 3).replaceStackAndIncrPC
    ((w::words).map (fun x => UInt256.mk x.toFin)) 33
  have decoded := decode_word_push seed before after w words fits
  have table := checked_tables valid #[] input
    (.Push .PUSH32,some (UInt256.mk w.toFin,32)) decoded
    (by change (Operation.Push .PUSH32 : Operation .EVM) ≠ .JUMP;decide)
    (by change (Operation.Push .PUSH32 : Operation .EVM) ≠ .JUMPI;decide) fuel
  have counted : Assembly.driverSteps 1 (fuel+2) valid input = .ok next :=
    table.trans producer.2.1
  exact ⟨producer.1,counted,counted_continuation valid input next _ fuel decoded
    (by change Assembly.NonhaltingOpcode (.Push .PUSH32);unfold Assembly.NonhaltingOpcode;decide) counted⟩

#print axioms nonbranch_gate_tables_eq
#print axioms word_push_checked_tables
#print axioms word_push_table_agreement
end SolidityBridge.RoadmapV15.P10
