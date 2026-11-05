import SolidityBridge.HashBridge.Step
import SolidityBridge.HashBridge.Layout

/-!
# Direct query receipts for actual explicit EVM evaluator steps (G46.05)

A proof-only prefix records successful uses of EXISTING step with an explicit
instruction, cost and fuel. Query bytes are computed from that step's input
memory/operands, never supplied as an oracle reply. This does not evaluate code,
replace X, prove its checks/fetch/charging, or observe hashes hidden inside a
child call/native provider. Failed steps cannot instantiate a successful edge.
Random-oracle bounds do not assert distribution of the fixed native hash.
-/
namespace Solidity.HashBridge
open EvmYul

/-- Only a direct KECCAK256 instruction with its two actual operands emits here.
This extractor alone asserts no execution: ExplicitPrefix additionally requires
the real step result, so fuel-zero input cannot fabricate a hashed query. -/
def directQueries (op : Operation .EVM) (s : EVM.State) : List (List Nat) :=
  if op == .KECCAK256 then
    match s.stack with
    | offset :: size :: _ => [byteQuery (machineQuery s.toMachineState offset size)]
    | _ => []
  else []

/-- Instrumentation receipts, not a new evaluator or source execution judgment.
Each edge carries a checked equality to the original actual EVM.step. The count
is successful explicit steps, not fuel or total/nested oracle query count. -/
inductive ExplicitPrefix : Nat → EVM.State → EVM.State → List (List Nat) → Prop where
  | nil (s : EVM.State) : ExplicitPrefix 0 s s []
  | cons {n fuel cost : Nat} {op : Operation .EVM}
      {arg : Option (UInt256 × Nat)} {s mid last : EVM.State} {queries : List (List Nat)}
      (actual : EVM.step fuel cost (some (op,arg)) s = .ok mid)
      (rest : ExplicitPrefix n mid last queries) :
      ExplicitPrefix (n+1) s last (directQueries op s ++ queries)

/-- A concrete producer of a nonempty query receipt. No successful result or
selected digest/state is a premise. This is an evaluator component; X guards,
fetch and memory/base affordability remain separate obligations. -/
theorem recorded_keccak (fuel cost : Nat) (s : EVM.State) (offset size : UInt256)
    (tail : List UInt256) (hs : s.stack = offset :: size :: tail) :
    ∃ out, ExplicitPrefix 1 s out [byteQuery (machineQuery s.toMachineState offset size)] ∧
      out.stack = actualDigest (machineQuery s.toMachineState offset size) :: tail ∧
      out.toState = s.toState ∧ out.memory = s.memory ∧
      out.activeWords = .ofNat (MachineState.M s.activeWords.toNat offset.toNat size.toNat) ∧
      out.gasAvailable = s.gasAvailable - .ofNat cost ∧ out.pc = s.pc + .ofNat 1 ∧
      out.execLength = s.execLength + 1 ∧ out.returnData = s.returnData ∧ out.H_return = s.H_return := by
  obtain ⟨out,he,hstack,hworld,hmem,hactive,hgas,hpc,hexec,hret,hh⟩ :=
    keccak_step_cost fuel cost s offset size tail hs
  refine ⟨out,?_,hstack,hworld,hmem,hactive,hgas,hpc,hexec,hret,hh⟩
  have hp : ExplicitPrefix 1 s out (directQueries .KECCAK256 s ++ []) :=
    .cons he (.nil out)
  simpa only [directQueries, hs, beq_self_eq_true, if_pos rfl, List.append_nil] using hp

/-- Every recorded input is genuinely byte-valued, unlike arbitrary Nat lists
which queryBytes truncates. No allocation/padding/native law is used. -/
theorem byte_query_bounded (bytes : ByteArray) :
    ∀ n ∈ byteQuery bytes, n < 256 := by
  intro n hn
  obtain ⟨b,hb,rfl⟩ := List.mem_map.mp hn
  exact UInt8.toNat_lt_size b

end Solidity.HashBridge
