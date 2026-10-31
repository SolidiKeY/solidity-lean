import SolidityBridge.ExternalEvm.Assembly.CodeLayout
import EvmYul.EVM.Semantics

/-!
Control macros against the actual pinned upstream dispatcher. These local
lemmas supply their decoded packets, positive evaluator fuel, and zero
charged gas. They do not discharge fetching, valid-jump, gas, or driver
halting obligations. In particular no equality between core divergence
(.fault) and the upstream finite-fuel driver is asserted.
-/
namespace Solidity.Evm.External.Assembly

abbrev Packet := EvmYul.Operation .EVM × Option (EvmYul.UInt256 × Nat)

/-- Zero charged gas, exactly as in the existing opcode bridges. -/
def prepare (s : EvmYul.EVM.State) : EvmYul.EVM.State :=
  {s with execLength := s.execLength + 1, gasAvailable := s.gasAvailable - .ofNat 0}

def pushState (s : EvmYul.EVM.State) (target : EvmYul.UInt256) : EvmYul.EVM.State :=
  (prepare s).replaceStackAndIncrPC (target :: s.stack) (pcΔ := 33)

def jumpState (s : EvmYul.EVM.State) (target : EvmYul.UInt256) : EvmYul.EVM.State :=
  {prepare (pushState s target) with pc := target, stack := s.stack}

/-- PUSH32 is essential: same-stack JUMP cannot implement a core jump. -/
def jumpMacro (fuel : Nat) (target : EvmYul.UInt256) (s : EvmYul.EVM.State) := do
  let s ← EvmYul.EVM.step (fuel + 1) 0 (some (.Push .PUSH32, some (target, 32))) s
  EvmYul.EVM.step (fuel + 1) 0 (some (.JUMP, none)) s

theorem jumpMacro_eq (fuel : Nat) (target : EvmYul.UInt256) (s : EvmYul.EVM.State) :
    jumpMacro fuel target s = .ok (jumpState s target) := by
  rfl

def jumpiState (s : EvmYul.EVM.State) (target c : EvmYul.UInt256)
    (tail : List EvmYul.UInt256) : EvmYul.EVM.State :=
  let pushed := pushState s target
  {prepare pushed with
    pc := if c != ⟨0⟩ then target else pushed.pc + ⟨1⟩
    stack := tail}

def jumpiMacro (fuel : Nat) (target : EvmYul.UInt256) (s : EvmYul.EVM.State) := do
  let s ← EvmYul.EVM.step (fuel + 1) 0 (some (.Push .PUSH32, some (target, 32))) s
  EvmYul.EVM.step (fuel + 1) 0 (some (.JUMPI, none)) s

theorem jumpiMacro_eq (fuel : Nat) (target c : EvmYul.UInt256)
    (tail : List EvmYul.UInt256) (s : EvmYul.EVM.State) :
    jumpiMacro fuel target {s with stack := c :: tail} =
      .ok (jumpiState {s with stack := c :: tail} target c tail) := by
  rfl

theorem jumpiMacro_underflow (fuel : Nat) (target : EvmYul.UInt256)
    (s : EvmYul.EVM.State) :
    jumpiMacro fuel target {s with stack := []} = .error .StackUnderflow := by
  rfl

/-- The macro neither loses nor duplicates the old stack. -/
theorem jump_stack (s : EvmYul.EVM.State) (target : EvmYul.UInt256) :
    (jumpState s target).stack = s.stack := rfl

/-- A resolved word PC is never silently reduced modulo the word size. -/
theorem jump_pc (s : EvmYul.EVM.State) (target : Fin W) :
    (jumpState s (.ofNat target.val)).pc.toNat = target.val := by
  change target.val % W = target.val
  exact Nat.mod_eq_of_lt target.isLt

/-- All account/environment state is framed by the jump macro. -/
theorem jump_frame (s : EvmYul.EVM.State) (target : EvmYul.UInt256) :
    (jumpState s target).toState = s.toState ∧
    (jumpState s target).memory = s.memory := ⟨rfl, rfl⟩

theorem jumpi_frame (s : EvmYul.EVM.State) (target c : EvmYul.UInt256)
    (tail : List EvmYul.UInt256) :
    (jumpiState s target c tail).toState = s.toState ∧
    (jumpiState s target c tail).memory = s.memory := ⟨rfl, rfl⟩

/-- Finite traces of actual dispatcher executions, with their decoded
packets retained. This does not synthesize an upstream driver success. -/
inductive Trace (fuel : Nat) : EvmYul.EVM.State → EvmYul.EVM.State → Prop where
  | nil (s) : Trace fuel s s
  | cons {s t u} (packet : Packet)
      (head : EvmYul.EVM.step (fuel + 1) 0 (some packet) s = .ok t)
      (tail : Trace fuel t u) : Trace fuel s u

theorem Trace.trans {fuel : Nat} {s t u : EvmYul.EVM.State}
    (a : Trace fuel s t) (b : Trace fuel t u) : Trace fuel s u := by
  induction a generalizing u with
  | nil => exact b
  | cons packet head _ ih => exact .cons packet head (ih b)

theorem jump_trace (fuel : Nat) (target : EvmYul.UInt256) (s : EvmYul.EVM.State) :
    Trace fuel s (jumpState s target) := by
  exact .cons (.Push .PUSH32, some (target, 32)) rfl
    (.cons (.JUMP, none) rfl (.nil _))

theorem jumpi_trace (fuel : Nat) (target c : EvmYul.UInt256)
    (tail : List EvmYul.UInt256) (s : EvmYul.EVM.State) :
    Trace fuel {s with stack := c :: tail}
      (jumpiState {s with stack := c :: tail} target c tail) := by
  exact .cons (.Push .PUSH32, some (target, 32)) rfl
    (.cons (.JUMPI, none) rfl (.nil _))


/-- Numeric stack interpretation used at macro boundaries. -/
def words (stack : List EvmYul.UInt256) : List Word :=
  stack.map (fun x => .val ⟨x.toNat, by
    change x.val.val < W
    exact x.val.isLt⟩)

/-- A jump macro takes two actual dispatcher steps to a resolved absolute
PC, while core and upstream stacks are unchanged. This local lemma does
not relate the entry PC to the source boundary.
Fetching and driver-validity remain the separate layout assumptions. -/
theorem relative_jump_macro {code : List Instr} {base origin offset : Nat}
    (r : Relocation code base origin offset) (fuel : Nat)
    (m : Machine) (s : EvmYul.EVM.State) (hs : m.stack = words s.stack) :
    (Instr.jump offset).step m = .ok m offset ∧
    Trace fuel s (jumpState s (.ofNat r.pc.val)) ∧
    m.stack = words (jumpState s (.ofNat r.pc.val)).stack ∧
    (jumpState s (.ofNat r.pc.val)).pc = .ofNat r.pc.val := by
  exact ⟨rfl, jump_trace _ _ _, hs, rfl⟩


/-- Conditional counterpart: actual core pop/skip behavior and actual
upstream macro trace, retaining the full numeric condition and stack tail.
This local result does not assert code-layout simulation. -/
theorem relative_jumpi_macro (offset fuel : Nat) (target c : EvmYul.UInt256)
    (tail : List EvmYul.UInt256) (m : Machine) (s : EvmYul.EVM.State) :
    (Instr.jumpi offset).step {m with stack := words (c :: tail)} =
      .ok {m with stack := words tail} (if c.toNat = 0 then 0 else offset) ∧
    Trace fuel {s with stack := c :: tail}
      (jumpiState {s with stack := c :: tail} target c tail) ∧
    words (jumpiState {s with stack := c :: tail} target c tail).stack = words tail := by
  exact ⟨rfl, jumpi_trace _ _ _ _ _, rfl⟩


/-- Explicit fetch assumption. In addition to code placement, a driver
correspondence must separately assume/check validJumps, gas and limits. -/
def Fetches (s : EvmYul.EVM.State) (packet : Packet) : Prop :=
  EvmYul.EVM.fetchInstr s.executionEnv s.pc = .ok packet

theorem fetched_step (fuel : Nat) (s : EvmYul.EVM.State) (packet : Packet)
    (h : Fetches s packet) :
    EvmYul.EVM.step (fuel + 1) 0 none s =
      EvmYul.EVM.step (fuel + 1) 0 (some packet) s := by
  unfold Fetches at h
  unfold EvmYul.EVM.step
  rw [h]
  rfl

/-- Traces whose packets are fetched from the state's actual code and PC. -/
inductive FetchedTrace (fuel : Nat) : EvmYul.EVM.State → EvmYul.EVM.State → Prop where
  | nil (s) : FetchedTrace fuel s s
  | cons {s t u}
      (head : EvmYul.EVM.step (fuel + 1) 0 none s = .ok t)
      (tail : FetchedTrace fuel t u) : FetchedTrace fuel s u

theorem FetchedTrace.trans {fuel : Nat} {s t u : EvmYul.EVM.State}
    (a : FetchedTrace fuel s t) (b : FetchedTrace fuel t u) : FetchedTrace fuel s u := by
  induction a generalizing u with
  | nil => exact b
  | cons head _ ih => exact .cons head (ih b)

/-- Fetch assumptions name both macro instructions and their actual PCs;
this is stronger than merely finding 0x5b at the requested destination. -/
theorem fetched_jump_trace (fuel : Nat) (target : EvmYul.UInt256)
    (s : EvmYul.EVM.State)
    (hp : Fetches s (.Push .PUSH32, some (target, 32)))
    (hj : Fetches (pushState s target) (.JUMP, none)) :
    FetchedTrace fuel s (jumpState s target) := by
  refine .cons (t := pushState s target) ?_ (.cons ?_ (.nil _))
  · rw [fetched_step fuel s _ hp]
    rfl
  · rw [fetched_step fuel (pushState s target) _ hj]
    rfl

/-- Conditional macro with both packets fetched from actual code. -/
theorem fetched_jumpi_trace (fuel : Nat) (target c : EvmYul.UInt256)
    (tail : List EvmYul.UInt256) (s : EvmYul.EVM.State)
    (hp : Fetches {s with stack := c :: tail} (.Push .PUSH32, some (target, 32)))
    (hj : Fetches (pushState {s with stack := c :: tail} target) (.JUMPI, none)) :
    FetchedTrace fuel {s with stack := c :: tail}
      (jumpiState {s with stack := c :: tail} target c tail) := by
  refine .cons (t := pushState {s with stack := c :: tail} target) ?_ (.cons ?_ (.nil _))
  · rw [fetched_step fuel _ _ hp]
    rfl
  · rw [fetched_step fuel _ _ hj]
    rfl


/-- Finite sequencing uses both the actual core runner and actual fetched
upstream traces. This lemma does not assume a driver success result. -/
theorem sequence {c d : List Instr} {m m' m'' : Machine}
    {fuel : Nat} {s t u : EvmYul.EVM.State}
    (hc : run c m = .ok m' 0) (hd : run d m' = .ok m'' 0)
    (tc : FetchedTrace fuel s t) (td : FetchedTrace fuel t u) :
    run (c ++ d) m = .ok m'' 0 ∧ FetchedTrace fuel s u := by
  exact ⟨(run_append_ok hc).trans hd, tc.trans td⟩

end Solidity.Evm.External.Assembly
