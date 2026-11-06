import SolidityBridge.RoadmapV15.P10.ExponentConsumer
import SolidityBridge.ExternalEvm.StackOps

/-! Typed scalar consumers for every legal DUP/SWAP depth. Actual backend bytes,
charged fetched State and X are preserved; no compiler frame-origin assumed. -/
namespace SolidityBridge.RoadmapV15.P10
open Solidity Solidity.Backend EvmYul Solidity.Evm.External

private theorem byte_at {op : Backend.Op} (site : Site op) :
    site.state.executionEnv.code.get? (Backend.encode site.before).length = some op.code := by
  change (Backend.encode (site.before ++ .op op :: site.after)).toArray[(Backend.encode site.before).length]? = _
  rw [List.getElem?_toArray]
  simp only [Backend.encode_append,Backend.encode_cons,Instr.encode,List.singleton_append]
  rw [List.getElem?_append_right (Nat.le_refl _)]
  simp only [Nat.sub_self,List.getElem?_cons_zero]

theorem decode_dup_family (n : Fin 16) (site : Site (.DUP n)) :
    EVM.decode site.state.executionEnv.code site.state.pc = some (dupCode n,none) := by
  have byte := byte_at site
  simp only [EVM.decode,Site.pc_nat,byte]
  fin_cases n <;> rfl

theorem decode_swap_family (n : Fin 16) (site : Site (.SWAP n)) :
    EVM.decode site.state.executionEnv.code site.state.pc = some (swapCode n,none) := by
  have byte := byte_at site
  simp only [EVM.decode,Site.pc_nat,byte]
  fin_cases n <;> rfl

theorem scalar_dup_split (pre tail : Scalar.Stack) (a : Scalar.Word) :
    Scalar.duplicate pre.length (pre ++ a::tail) = some (a::(pre ++ a::tail)) := by
  simp only [Scalar.duplicate,List.getElem?_append_right (Nat.le_refl pre.length),
    Nat.sub_self,List.getElem?_cons_zero,Option.map_some]

private theorem exchange_split (middle tail : Scalar.Stack) (a b : Scalar.Word) :
    Scalar.exchange a middle.length (middle ++ b::tail) = some (b,middle ++ a::tail) := by
  induction middle with
  | nil => rfl
  | cons c middle ih =>
    simp only [List.length_cons,List.cons_append,Scalar.exchange,ih,Option.map_some]

theorem scalar_swap_split (middle tail : Scalar.Stack) (a b : Scalar.Word) :
    Scalar.swap middle.length (a::(middle ++ b::tail)) = some (b::(middle ++ a::tail)) := by
  simp only [Scalar.swap,exchange_split,Option.map_some]

private theorem dup_facts (n : Fin 16) (s : EVM.State) :
    EVM.memoryExpansionCost s (dupCode n) = 0 ∧ EVM.C' s (dupCode n) = 3 ∧
    EVM.δ (dupCode n) = some (n.val+1) ∧ EVM.α (dupCode n) = some (n.val+2) := by
  fin_cases n <;> refine ⟨?_,rfl,rfl,rfl⟩ <;>
    change EVM.Cₘ s.activeWords - EVM.Cₘ s.activeWords = 0
  all_goals exact Nat.sub_self _

private theorem swap_facts (n : Fin 16) (s : EVM.State) :
    EVM.memoryExpansionCost s (swapCode n) = 0 ∧ EVM.C' s (swapCode n) = 3 ∧
    EVM.δ (swapCode n) = some (n.val+2) ∧ EVM.α (swapCode n) = some (n.val+2) := by
  fin_cases n <;> refine ⟨?_,rfl,rfl,rfl⟩ <;>
    change EVM.Cₘ s.activeWords - EVM.Cₘ s.activeWords = 0
  all_goals exact Nat.sub_self _

private theorem stack_gate (s : EVM.State) (op : Operation .EVM) (arity output : Nat)
    (mem : EVM.memoryExpansionCost s op = 0) (cost : EVM.C' s op = 3)
    (delta : EVM.δ op = some arity) (alpha : EVM.α op = some output)
    (gas : 3 ≤ s.gasAvailable.toNat) (enough : arity ≤ s.stack.length)
    (room : s.stack.length-arity+output ≤ 1024)
    (allowed : (∃ n, op = dupCode n) ∨ (∃ n, op = swapCode n)) :
    Assembly.driverGate #[] s op = .ok (s,3) := by
  have charge : s.gasAvailable-UInt256.ofNat 0 = s.gasAvailable := by
    change UInt256.mk (s.gasAvailable.val-0) = s.gasAvailable
    rw [sub_zero]
  simp only [Assembly.driverGate]
  rw [mem,charge]
  simp only [cost,delta,alpha,Option.getD_some,if_neg (Nat.not_lt_zero _),
    if_neg (Nat.not_lt_of_ge gas),if_neg (Nat.not_lt_of_ge enough),if_neg (Nat.not_lt_of_ge room)]
  rcases allowed with ⟨n,rfl⟩|⟨n,rfl⟩ <;> fin_cases n <;> cases s.executionEnv.perm <;> rfl

private theorem charged_dup (n : Fin 16) (s : EVM.State) (fuel : Nat) :
    EVM.step (fuel+1) 3 (some (dupCode n,none)) s =
      EvmYul.dup (n.val+1) (Assembly.chargedPrepare s 3) := by
  fin_cases n <;> rfl

private theorem charged_swap (n : Fin 16) (s : EVM.State) (fuel : Nat) :
    EVM.step (fuel+1) 3 (some (swapCode n,none)) s =
      EvmYul.swap (n.val+1) (Assembly.chargedPrepare s 3) := by
  fin_cases n <;> rfl

private theorem checked_stack (input next : EVM.State) (op : Operation .EVM) (fuel : Nat)
    (decoded : EVM.decode input.executionEnv.code input.pc = some (op,none))
    (gate : Assembly.driverGate #[] input op = .ok (input,3))
    (step : EVM.step (fuel+1) 3 (some (op,none)) input = .ok next)
    (nonhalting : Assembly.NonhaltingOpcode op) :
    Assembly.driverSteps 1 (fuel+2) #[] input = .ok next ∧
    EVM.X (fuel+2) #[] input = EVM.X (fuel+1) #[] next := by
  constructor
  · simp only [Assembly.driverSteps]
    rw [decoded]
    dsimp only [Option.option,bind,Except.bind]
    rw [gate]
    dsimp only
    rw [step]
  · exact Assembly.X_continue fuel #[] input input next (op,none) 3 decoded gate step nonhalting

theorem dup_family_agreement (n : Fin 16) (site : Site (.DUP n))
    (pre tail : Scalar.Stack) (a : Scalar.Word) (depth : pre.length = n.val)
    (room : pre.length+tail.length+2 ≤ 1024) (gas : 3 ≤ site.seed.gasAvailable.toNat) (fuel : Nat) :
    let input := (modularSite site (pre ++ a::tail)).state
    let next := (Assembly.chargedPrepare input 3).replaceStackAndIncrPC
      ((a::(pre ++ a::tail)).map (fun w => UInt256.mk w.toFin))
    Scalar.step (.op (.DUP n)) (pre ++ a::tail) = some (a::(pre ++ a::tail)) ∧
      Assembly.driverSteps 1 (fuel+2) #[] input = .ok next ∧
      EVM.X (fuel+2) #[] input = EVM.X (fuel+1) #[] next := by
  dsimp only
  refine ⟨?_,?_⟩
  · simp only [Scalar.step]
    rw [←depth];exact scalar_dup_split pre tail a
  let input := (modularSite site (pre ++ a::tail)).state
  have facts := dup_facts n input
  have gate : Assembly.driverGate #[] input (dupCode n) = .ok (input,3) := by
    apply stack_gate input (dupCode n) (n.val+1) (n.val+2) facts.1 facts.2.1 facts.2.2.1 facts.2.2.2 gas
    · change n.val+1 ≤ ((pre ++ a::tail).map (fun w => UInt256.mk w.toFin)).length
      simp only [List.length_map,List.length_append,List.length_cons];omega
    · change ((pre ++ a::tail).map (fun w => UInt256.mk w.toFin)).length-(n.val+1)+(n.val+2) ≤ 1024
      simp only [List.length_map,List.length_append,List.length_cons];omega
    · exact Or.inl ⟨n,rfl⟩
  have step : EVM.step (fuel+1) 3 (some (dupCode n,none)) input =
      .ok ((Assembly.chargedPrepare input 3).replaceStackAndIncrPC
        ((a::(pre ++ a::tail)).map (fun w => UInt256.mk w.toFin))) := by
    rw [charged_dup,←depth]
    have h := reference_dup_pre (Assembly.chargedPrepare input 3)
      (pre.map (fun w => UInt256.mk w.toFin)) (tail.map (fun w => UInt256.mk w.toFin)) (UInt256.mk a.toFin)
    simp only [List.length_map,List.map_cons,List.map_append] at h ⊢
    simpa only [input,modularSite,Site.state,Assembly.chargedPrepare,List.map_append,List.map_cons] using h
  exact checked_stack input _ (dupCode n) fuel (decode_dup_family n _) gate step
    (by fin_cases n <;> unfold Assembly.NonhaltingOpcode <;> decide)

theorem swap_family_agreement (n : Fin 16) (site : Site (.SWAP n))
    (middle tail : Scalar.Stack) (a b : Scalar.Word) (depth : middle.length = n.val)
    (room : middle.length+tail.length+2 ≤ 1024) (gas : 3 ≤ site.seed.gasAvailable.toNat) (fuel : Nat) :
    let input := (modularSite site (a::(middle ++ b::tail))).state
    let next := (Assembly.chargedPrepare input 3).replaceStackAndIncrPC
      ((b::(middle ++ a::tail)).map (fun w => UInt256.mk w.toFin))
    Scalar.step (.op (.SWAP n)) (a::(middle ++ b::tail)) = some (b::(middle ++ a::tail)) ∧
      Assembly.driverSteps 1 (fuel+2) #[] input = .ok next ∧
      EVM.X (fuel+2) #[] input = EVM.X (fuel+1) #[] next := by
  dsimp only
  refine ⟨?_,?_⟩
  · simp only [Scalar.step]
    rw [←depth];exact scalar_swap_split middle tail a b
  let input := (modularSite site (a::(middle ++ b::tail))).state
  have facts := swap_facts n input
  have gate : Assembly.driverGate #[] input (swapCode n) = .ok (input,3) := by
    apply stack_gate input (swapCode n) (n.val+2) (n.val+2) facts.1 facts.2.1 facts.2.2.1 facts.2.2.2 gas
    · change n.val+2 ≤ ((a::(middle ++ b::tail)).map (fun w => UInt256.mk w.toFin)).length
      simp only [List.length_map,List.length_append,List.length_cons];omega
    · change ((a::(middle ++ b::tail)).map (fun w => UInt256.mk w.toFin)).length-(n.val+2)+(n.val+2) ≤ 1024
      simp only [List.length_map,List.length_append,List.length_cons];omega
    · exact Or.inr ⟨n,rfl⟩
  have step : EVM.step (fuel+1) 3 (some (swapCode n,none)) input =
      .ok ((Assembly.chargedPrepare input 3).replaceStackAndIncrPC
        ((b::(middle ++ a::tail)).map (fun w => UInt256.mk w.toFin))) := by
    rw [charged_swap,←depth]
    have h := reference_swap_pre (Assembly.chargedPrepare input 3)
      (middle.map (fun w => UInt256.mk w.toFin)) (tail.map (fun w => UInt256.mk w.toFin))
      (UInt256.mk a.toFin) (UInt256.mk b.toFin)
    simp only [List.length_map,List.map_cons,List.map_append] at h ⊢
    simpa only [input,modularSite,Site.state,Assembly.chargedPrepare,List.map_append,List.map_cons] using h
  exact checked_stack input _ (swapCode n) fuel (decode_swap_family n _) gate step
    (by fin_cases n <;> unfold Assembly.NonhaltingOpcode <;> decide)

#print axioms decode_dup_family
#print axioms decode_swap_family
#print axioms scalar_dup_split
#print axioms scalar_swap_split
#print axioms dup_family_agreement
#print axioms swap_family_agreement
end SolidityBridge.RoadmapV15.P10
