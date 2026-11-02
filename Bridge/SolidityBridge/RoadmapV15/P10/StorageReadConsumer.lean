import SolidityBridge.RoadmapV15.P10.Interface
import SolidityBridge.ExternalEvm.Assembly.Driver
import SolidityBridge.ExternalEvm.StorageOpcode
import Solidity.Storage.Representation.Transport
import Solidity.Backend.Scalar.Typed

/-! Actual charged/fetched persistent and transient reads, consuming published
slot/representation interfaces without a second memory or account semantics. -/
namespace SolidityBridge.RoadmapV15.P10
open Solidity Solidity.Backend EvmYul Solidity.Evm.External

def slotReadSite {op : Backend.Op} (site : Site op) (key : UInt256) (tail : List UInt256) : Site op :=
  {site with seed := {site.seed with stack := key::tail}}

private theorem read_byte {op : Backend.Op} (site : Site op) :
    site.state.executionEnv.code.get? (Backend.encode site.before).length = some op.code := by
  change (Backend.encode (site.before ++ .op op :: site.after)).toArray[(Backend.encode site.before).length]? = _
  rw [List.getElem?_toArray]
  simp only [Backend.encode_append,Backend.encode_cons,Instr.encode,List.singleton_append]
  rw [List.getElem?_append_right (Nat.le_refl _)]
  simp only [Nat.sub_self,List.getElem?_cons_zero]

theorem decode_sload (site : Site .SLOAD) :
    EVM.decode site.state.executionEnv.code site.state.pc = some (.SLOAD,none) := by
  have byte := read_byte site
  simp only [EVM.decode,Site.pc_nat,byte]
  rfl

theorem decode_tload (site : Site .TLOAD) :
    EVM.decode site.state.executionEnv.code site.state.pc = some (.TLOAD,none) := by
  have byte := read_byte site
  simp only [EVM.decode,Site.pc_nat,byte]
  rfl

theorem sload_cost (site : Site .SLOAD) (key : UInt256) (tail : List UInt256) :
    EVM.C' (slotReadSite site key tail).state .SLOAD =
      if site.seed.substate.accessedStorageKeys.contains (site.seed.executionEnv.codeOwner,key)
      then 100 else 2100 := by rfl

theorem sload_cost_bound (site : Site .SLOAD) (key : UInt256) (tail : List UInt256) :
    EVM.C' (slotReadSite site key tail).state .SLOAD ≤ 2100 := by
  rw [sload_cost]
  split <;> decide

theorem tload_cost (site : Site .TLOAD) (key : UInt256) (tail : List UInt256) :
    EVM.C' (slotReadSite site key tail).state .TLOAD = 100 := by rfl

private theorem read_gate (s : EVM.State) (op : Operation .EVM)
    (allowed : op = .SLOAD ∨ op = .TLOAD)
    (gas : EVM.C' s op ≤ s.gasAvailable.toNat)
    (enough : 1 ≤ s.stack.length) (room : s.stack.length ≤ 1024) :
    Assembly.driverGate #[] s op = .ok (s,EVM.C' s op) := by
  have expansion : EVM.memoryExpansionCost s op = 0 := by
    rcases allowed with rfl|rfl <;>
      simp only [EVM.memoryExpansionCost,EVM.memoryExpansionCost.μᵢ',Nat.sub_self]
  have delta : EVM.δ op = some 1 := by rcases allowed with rfl|rfl <;> rfl
  have alpha : EVM.α op = some 1 := by rcases allowed with rfl|rfl <;> rfl
  have capacity : s.stack.length-1+1 ≤ 1024 := by omega
  have charge : s.gasAvailable-UInt256.ofNat 0 = s.gasAvailable := by
    change UInt256.mk (s.gasAvailable.val-0) = s.gasAvailable
    rw [sub_zero]
  simp only [Assembly.driverGate]
  rw [expansion,charge]
  simp only [delta,alpha,Option.getD_some,if_neg (Nat.not_lt_zero _),
    if_neg (Nat.not_lt_of_ge gas),if_neg (Nat.not_lt_of_ge enough),if_neg (Nat.not_lt_of_ge capacity)]
  rcases allowed with rfl|rfl <;> cases s.executionEnv.perm <;> rfl

private theorem checked_read (input next : EVM.State) (op : Operation .EVM) (fuel cost : Nat)
    (decoded : EVM.decode input.executionEnv.code input.pc = some (op,none))
    (gate : Assembly.driverGate #[] input op = .ok (input,cost))
    (step : EVM.step (fuel+1) cost (some (op,none)) input = .ok next)
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
  · exact Assembly.X_continue fuel #[] input input next (op,none) cost decoded gate step nonhalting

theorem sload_agreement (site : Site .SLOAD) (key : UInt256) (tail : List UInt256)
    (room : tail.length+1 ≤ 1024) (gas : EVM.C' (slotReadSite site key tail).state .SLOAD ≤ site.seed.gasAvailable.toNat) (fuel : Nat) :
    let input := (slotReadSite site key tail).state
    let cost := EVM.C' input .SLOAD
    let read := EvmYul.State.sload input.toState key
    let next := ({Assembly.chargedPrepare input cost with toState := read.1}).replaceStackAndIncrPC (read.2::tail)
    Assembly.driverSteps 1 (fuel+2) #[] input = .ok next ∧
      EVM.X (fuel+2) #[] input = EVM.X (fuel+1) #[] next := by
  dsimp only
  let input := (slotReadSite site key tail).state
  let cost := EVM.C' input .SLOAD
  have gate : Assembly.driverGate #[] input .SLOAD = .ok (input,cost) := by
    apply read_gate input .SLOAD (Or.inl rfl)
    · exact gas
    · change 1 ≤ (key::tail).length
      simp only [List.length_cons];omega
    · change (key::tail).length ≤ 1024
      exact room
  have step : EVM.step (fuel+1) cost (some (.SLOAD,none)) input =
      .ok (({Assembly.chargedPrepare input cost with toState := (EvmYul.State.sload input.toState key).1}).replaceStackAndIncrPC ((EvmYul.State.sload input.toState key).2::tail)) := by
    rfl
  exact checked_read input _ .SLOAD fuel cost (decode_sload _) gate step
    (by unfold Assembly.NonhaltingOpcode;decide)

theorem tload_agreement (site : Site .TLOAD) (key : UInt256) (tail : List UInt256)
    (room : tail.length+1 ≤ 1024) (gas : 100 ≤ site.seed.gasAvailable.toNat) (fuel : Nat) :
    let input := (slotReadSite site key tail).state
    let cost := EVM.C' input .TLOAD
    let read := EvmYul.State.tload input.toState key
    let next := ({Assembly.chargedPrepare input cost with toState := read.1}).replaceStackAndIncrPC (read.2::tail)
    Assembly.driverSteps 1 (fuel+2) #[] input = .ok next ∧
      EVM.X (fuel+2) #[] input = EVM.X (fuel+1) #[] next := by
  dsimp only
  let input := (slotReadSite site key tail).state
  let cost := EVM.C' input .TLOAD
  have gate : Assembly.driverGate #[] input .TLOAD = .ok (input,cost) := by
    apply read_gate input .TLOAD (Or.inr rfl)
    · exact gas
    · change 1 ≤ (key::tail).length
      simp only [List.length_cons];omega
    · change (key::tail).length ≤ 1024
      exact room
  have step : EVM.step (fuel+1) cost (some (.TLOAD,none)) input =
      .ok (({Assembly.chargedPrepare input cost with toState := (EvmYul.State.tload input.toState key).1}).replaceStackAndIncrPC ((EvmYul.State.tload input.toState key).2::tail)) := by
    rfl
  exact checked_read input _ .TLOAD fuel cost (decode_tload _) gate step
    (by unfold Assembly.NonhaltingOpcode;decide)

/-- Observation of the actual pinned read value as the existing intrinsic word. -/
def slotWord (value : UInt256) : Semantics.Word :=
  ⟨(value.toNat : Int),by
    have bound : value.toNat < 2^256 := value.val.isLt
    simp only [PrimTy.inRange,decide_eq_true_eq]
    constructor <;> omega⟩

def persistentWords (s : EvmYul.State .EVM) : Solidity.Storage.Representation.WordStore :=
  fun n => slotWord (EvmYul.State.sload s (.ofNat n)).2

theorem slotWord_scalar {p : PrimTy} (v : p.Denote) (value : UInt256)
    (observed : slotWord value = PrimTy.toWord v) :
    UInt256.mk (Scalar.encodeValue p v).toFin = value := by
  rw [Scalar.encodeValue_toWord,←observed]
  change UInt256.mk (BitVec.ofInt 256 (value.toNat : Int)).toFin = value
  rw [BitVec.ofInt_natCast]
  cases value with
  | mk value =>
    apply congrArg UInt256.mk
    apply Fin.ext
    change value.val % 2^256 = value.val
    exact Nat.mod_eq_of_lt value.isLt

/-- Consume existing finite representation coverage at the actual pinned read.
Hash interpretation/compiled path production are not established by this read. -/
theorem source_sload_word {T : Ty} {p : PrimTy} {source : SVal T}
    {path : Path T (.prim p)} {v : p.Denote} {l : Solidity.Storage.Loc}
    {words : Solidity.Storage.Representation.Store} {H : Solidity.Storage.Pre → Nat}
    {touched : List Solidity.Storage.Loc} (s : EvmYul.State .EVM)
    (found : source.find path = some (.prim v))
    (represented : Solidity.Storage.Representation.ValueRep (.prim v) .word l words)
    (transported : Solidity.Storage.Representation.Transport (2^256) H touched words (persistentWords s))
    (covered : l ∈ touched) :
    (EvmYul.State.sload s (.ofNat (Solidity.Storage.Loc.word (2^256) H l))).2 =
      UInt256.mk (Scalar.encodeValue p (source.obs.word path)).toFin := by
  have observed := Solidity.Storage.Representation.source_word_observation found represented transported covered
  exact (slotWord_scalar (source.obs.word path) _ observed).symm

theorem source_sload_execution {T : Ty} {p : PrimTy} {source : SVal T}
    {path : Path T (.prim p)} {v : p.Denote} {l : Solidity.Storage.Loc}
    {words : Solidity.Storage.Representation.Store} {H : Solidity.Storage.Pre → Nat}
    {touched : List Solidity.Storage.Loc} (site : Site .SLOAD) (tail : List UInt256)
    (room : tail.length+1 ≤ 1024)
    (gas : EVM.C' (slotReadSite site (.ofNat (Solidity.Storage.Loc.word (2^256) H l)) tail).state .SLOAD ≤
      site.seed.gasAvailable.toNat)
    (found : source.find path = some (.prim v))
    (represented : Solidity.Storage.Representation.ValueRep (.prim v) .word l words)
    (transported : Solidity.Storage.Representation.Transport (2^256) H touched words
      (persistentWords (slotReadSite site (.ofNat (Solidity.Storage.Loc.word (2^256) H l)) tail).state.toState))
    (covered : l ∈ touched) (fuel : Nat) :
    let key := UInt256.ofNat (Solidity.Storage.Loc.word (2^256) H l)
    let input := (slotReadSite site key tail).state
    let cost := EVM.C' input .SLOAD
    let next := ({Assembly.chargedPrepare input cost with
      toState := (EvmYul.State.sload input.toState key).1}).replaceStackAndIncrPC
        (UInt256.mk (Scalar.encodeValue p (source.obs.word path)).toFin::tail)
    Assembly.driverSteps 1 (fuel+2) #[] input = .ok next ∧
      EVM.X (fuel+2) #[] input = EVM.X (fuel+1) #[] next := by
  have word := source_sload_word
    (slotReadSite site (.ofNat (Solidity.Storage.Loc.word (2^256) H l)) tail).state.toState
    found represented transported covered
  have execution := sload_agreement site (.ofNat (Solidity.Storage.Loc.word (2^256) H l)) tail room gas fuel
  dsimp only at execution ⊢
  rw [word] at execution
  exact execution

/-- Expose only the fields actually changed by the existing charged read.
This keeps fixture proofs from normalizing complete populated account maps. -/
theorem sload_read_shape (s : EVM.State) (key : UInt256) (tail : List UInt256) (cost : Nat) :
    ({Assembly.chargedPrepare s cost with toState := (EvmYul.State.sload s.toState key).1}).replaceStackAndIncrPC ((EvmYul.State.sload s.toState key).2::tail) =
    {s with
      pc := s.pc + .ofNat 1,gasAvailable := s.gasAvailable - .ofNat cost,
      execLength := s.execLength+1,stack := (EvmYul.State.sload s.toState key).2::tail,
      substate := s.substate.addAccessedStorageKey (s.executionEnv.codeOwner,key)} := by rfl

theorem tload_read_shape (s : EVM.State) (key : UInt256) (tail : List UInt256) (cost : Nat) :
    ({Assembly.chargedPrepare s cost with toState := (EvmYul.State.tload s.toState key).1}).replaceStackAndIncrPC ((EvmYul.State.tload s.toState key).2::tail) =
    {s with
      pc := s.pc + .ofNat 1,gasAvailable := s.gasAvailable - .ofNat cost,
      execLength := s.execLength+1,stack := (EvmYul.State.tload s.toState key).2::tail} := by rfl

#print axioms sload_read_shape
#print axioms tload_read_shape
#print axioms decode_sload
#print axioms decode_tload
#print axioms sload_cost
#print axioms sload_cost_bound
#print axioms tload_cost
#print axioms sload_agreement
#print axioms tload_agreement
#print axioms slotWord_scalar
#print axioms source_sload_word
#print axioms source_sload_execution
end SolidityBridge.RoadmapV15.P10
