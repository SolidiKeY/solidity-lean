import SolidityBridge.ExternalEvm.SignedOps
import SolidityBridge.ExternalEvm.Power
import SolidityBridge.ExternalEvm.Environment
import EvmYul.EVM.Semantics

/-!
Direct opcode agreement against the pinned upstream dispatcher, rather than
an adapter-selected transformer. Positive evaluator fuel and zero charged
gas isolate the opcode step; gas/stack-limit/static-mode checks belong to
the upstream execution driver `X` and are not assumed to exist in the core.
-/
namespace Solidity.Evm.External

inductive BinaryOpcode where
  | add | sub | mul | div | mod | and | or | xor
  | lt | gt | eq | shl | shr | slt | sgt | sdiv | smod | exp
  deriving DecidableEq, Repr

def BinaryOpcode.instr : BinaryOpcode → Instr
  | .add => .add | .sub => .sub | .mul => .mul | .div => .div | .mod => .mod
  | .and => .and | .or => .or | .xor => .xor | .lt => .lt | .gt => .gt
  | .eq => .eq | .shl => .shl | .shr => .shr | .slt => .slt | .sgt => .sgt
  | .sdiv => .sdiv | .smod => .smod | .exp => .exp

def BinaryOpcode.code : BinaryOpcode → EvmYul.Operation .EVM
  | .add => .ADD | .sub => .SUB | .mul => .MUL | .div => .DIV | .mod => .MOD
  | .and => .AND | .or => .OR | .xor => .XOR | .lt => .LT | .gt => .GT
  | .eq => .EQ | .shl => .SHL | .shr => .SHR | .slt => .SLT | .sgt => .SGT
  | .sdiv => .SDIV | .smod => .SMOD | .exp => .EXP

def BinaryOpcode.value : BinaryOpcode → EvmYul.UInt256 → EvmYul.UInt256 → EvmYul.UInt256
  | .add => EvmYul.UInt256.add | .sub => EvmYul.UInt256.sub | .mul => EvmYul.UInt256.mul
  | .div => EvmYul.UInt256.div | .mod => EvmYul.UInt256.mod
  | .and => EvmYul.UInt256.land | .or => EvmYul.UInt256.lor | .xor => EvmYul.UInt256.xor
  | .lt => EvmYul.UInt256.lt | .gt => EvmYul.UInt256.gt | .eq => EvmYul.UInt256.eq
  | .shl => fun n a => EvmYul.UInt256.shiftLeft a n
  | .shr => fun n a => EvmYul.UInt256.shiftRight a n
  | .slt => EvmYul.UInt256.slt | .sgt => EvmYul.UInt256.sgt
  | .sdiv => EvmYul.UInt256.sdiv | .smod => EvmYul.UInt256.smod | .exp => EvmYul.UInt256.exp

def prepare (s : EvmYul.EVM.State) : EvmYul.EVM.State :=
  {s with execLength := s.execLength + 1, gasAvailable := s.gasAvailable - .ofNat 0}

theorem prepare_agrees {m : Machine} {s : EvmYul.EVM.State} (h : EnvironmentAgrees m s) :
    EnvironmentAgrees m (prepare s) :=
  ⟨h.stack, h.self, h.caller, h.value, h.time, h.balances⟩

theorem BinaryOpcode.dispatch (op : BinaryOpcode) (s : EvmYul.EVM.State) (fuel : Nat) :
    EvmYul.EVM.step (fuel + 1) 0 (some (op.code, none)) s =
      EvmYul.EVM.execBinOp op.value (prepare s) := by
  cases op <;> rfl

theorem BinaryOpcode.core_step (op : BinaryOpcode) (m : Machine)
    (a b : EvmYul.UInt256) (st : List Word) :
    op.instr.step {m with stack := .val (decode a) :: .val (decode b) :: st} =
      m.next (.val (decode (op.value a b)) :: st) := by
  cases op <;> simp only [BinaryOpcode.instr, BinaryOpcode.value, add_step, sub_step, mul_step,
    div_step, mod_step, and_step, or_step, xor_step, lt_step, gt_step, eq_step,
    shl_step, shr_step, slt_step, sgt_step, sdiv_step, smod_step, exp_step, encode_decode]

inductive ResultAgrees : Out → Except EvmYul.EVM.ExecutionException EvmYul.EVM.State → Prop where
  | ok {m : Machine} {s : EvmYul.EVM.State} (h : EnvironmentAgrees m s) :
      ResultAgrees (.ok m 0) (.ok s)
  | underflow : ResultAgrees .fault (.error .StackUnderflow)

/-- Total opcode correspondence on every represented numeric stack,
including underflow. Successful steps preserve the full shared environment. -/
theorem BinaryOpcode.agrees (op : BinaryOpcode) (m : Machine) (s : EvmYul.EVM.State)
    (h : EnvironmentAgrees m s) (fuel : Nat) :
    ResultAgrees (op.instr.step m) (EvmYul.EVM.step (fuel + 1) 0 (some (op.code, none)) s) := by
  rw [op.dispatch]
  cases hs : s.stack with
  | nil =>
    have hm : m.stack = [] := by simpa only [hs, List.map_nil] using h.stack
    have hc : op.instr.step m = .fault := by cases op <;> simp only [BinaryOpcode.instr, Instr.step, hm]
    rw [hc]
    simp only [EvmYul.EVM.execBinOp, prepare, hs, EvmYul.Stack.pop2]
    exact .underflow
  | cons a rest =>
    cases rest with
    | nil =>
      have hm : m.stack = [.val (decode a)] := by simpa only [hs, List.map_cons, List.map_nil] using h.stack
      have hc : op.instr.step m = .fault := by cases op <;> simp only [BinaryOpcode.instr, Instr.step, hm]
      rw [hc]
      simp only [EvmYul.EVM.execBinOp, prepare, hs, EvmYul.Stack.pop2]
      exact .underflow
    | cons b st =>
      have hm : m.stack = .val (decode a) :: .val (decode b) :: st.map (fun x => .val (decode x)) :=
        by simpa only [hs, List.map_cons] using h.stack
      have hc : op.instr.step
          {m with stack := .val (decode a) :: .val (decode b) :: st.map (fun x => .val (decode x))} =
          m.next (.val (decode (op.value a b)) :: st.map (fun x => .val (decode x))) :=
        op.core_step m a b (st.map (fun x => .val (decode x)))
      rw [← hm] at hc
      rw [hc]
      have hr : EvmYul.EVM.execBinOp op.value (prepare s) =
          .ok ((prepare s).replaceStackAndIncrPC (op.value a b :: st)) := by
        simp only [EvmYul.EVM.execBinOp, prepare, hs, EvmYul.Stack.pop2]
        rfl
      rw [hr]
      exact .ok ⟨rfl, h.self, h.caller, h.value, h.time, h.balances⟩

inductive UnaryOpcode where
  | iszero | not
  deriving DecidableEq, Repr

def UnaryOpcode.instr : UnaryOpcode → Instr
  | .iszero => .iszero | .not => .not

def UnaryOpcode.code : UnaryOpcode → EvmYul.Operation .EVM
  | .iszero => .ISZERO | .not => .NOT

def UnaryOpcode.value : UnaryOpcode → EvmYul.UInt256 → EvmYul.UInt256
  | .iszero => EvmYul.UInt256.isZero | .not => EvmYul.UInt256.lnot

theorem UnaryOpcode.dispatch (op : UnaryOpcode) (s : EvmYul.EVM.State) (fuel : Nat) :
    EvmYul.EVM.step (fuel + 1) 0 (some (op.code, none)) s =
      EvmYul.EVM.execUnOp op.value (prepare s) := by
  cases op <;> rfl

theorem UnaryOpcode.core_step (op : UnaryOpcode) (m : Machine)
    (a : EvmYul.UInt256) (st : List Word) :
    op.instr.step {m with stack := .val (decode a) :: st} =
      m.next (.val (decode (op.value a)) :: st) := by
  cases op <;> simp only [UnaryOpcode.instr, UnaryOpcode.value, iszero_step,
    not_step, encode_decode]

theorem UnaryOpcode.agrees (op : UnaryOpcode) (m : Machine) (s : EvmYul.EVM.State)
    (h : EnvironmentAgrees m s) (fuel : Nat) :
    ResultAgrees (op.instr.step m) (EvmYul.EVM.step (fuel + 1) 0 (some (op.code, none)) s) := by
  rw [op.dispatch]
  cases hs : s.stack with
  | nil =>
    have hm : m.stack = [] := by simpa only [hs, List.map_nil] using h.stack
    have hc : op.instr.step m = .fault := by
      cases op <;> simp only [UnaryOpcode.instr, Instr.step, hm]
    rw [hc]
    simp only [EvmYul.EVM.execUnOp, prepare, hs, EvmYul.Stack.pop]
    exact .underflow
  | cons a st =>
    have hm : m.stack = .val (decode a) :: st.map (fun x => .val (decode x)) :=
      by simpa only [hs, List.map_cons] using h.stack
    have hc : op.instr.step {m with stack := .val (decode a) :: st.map (fun x => .val (decode x))} =
        m.next (.val (decode (op.value a)) :: st.map (fun x => .val (decode x))) :=
      op.core_step m a _
    rw [← hm] at hc
    rw [hc]
    have hr : EvmYul.EVM.execUnOp op.value (prepare s) =
        .ok ((prepare s).replaceStackAndIncrPC (op.value a :: st)) := by
      simp only [EvmYul.EVM.execUnOp, prepare, hs, EvmYul.Stack.pop]
      rfl
    rw [hr]
    exact .ok ⟨rfl, h.self, h.caller, h.value, h.time, h.balances⟩

inductive EnvironmentOpcode where
  | selfbalance | address | caller | callvalue | timestamp
  deriving DecidableEq, Repr

def EnvironmentOpcode.instr : EnvironmentOpcode → Instr
  | .selfbalance => .selfbalance | .address => .address | .caller => .caller
  | .callvalue => .callvalue | .timestamp => .timestamp

def EnvironmentOpcode.code : EnvironmentOpcode → EvmYul.Operation .EVM
  | .selfbalance => .SELFBALANCE | .address => .ADDRESS | .caller => .CALLER
  | .callvalue => .CALLVALUE | .timestamp => .TIMESTAMP

def EnvironmentOpcode.transform : EnvironmentOpcode → EvmYul.EVM.Transformer
  | .selfbalance => EvmYul.EVM.stateOp EvmYul.State.selfbalance
  | .address => EvmYul.EVM.executionEnvOp (fun e => .ofNat e.codeOwner.val)
  | .caller => EvmYul.EVM.executionEnvOp (fun e => .ofNat e.source.val)
  | .callvalue => EvmYul.EVM.executionEnvOp (fun e => e.weiValue)
  | .timestamp => EvmYul.EVM.stateOp EvmYul.State.timeStamp

theorem EnvironmentOpcode.dispatch (op : EnvironmentOpcode) (s : EvmYul.EVM.State) (fuel : Nat) :
    EvmYul.EVM.step (fuel + 1) 0 (some (op.code, none)) s = op.transform (prepare s) := by
  cases op <;> rfl

theorem EnvironmentOpcode.agrees (op : EnvironmentOpcode) (m : Machine) (s : EvmYul.EVM.State)
    (h : EnvironmentAgrees m s) (fuel : Nat) :
    ResultAgrees (op.instr.step m) (EvmYul.EVM.step (fuel + 1) 0 (some (op.code, none)) s) := by
  rw [op.dispatch]
  have hp : EnvironmentAgrees m (prepare s) := prepare_agrees h
  have he : ∃ m' s', op.instr.step m = .ok m' 0 ∧
      op.transform (prepare s) = .ok s' ∧ EnvironmentAgrees m' s' := by
    cases op with
    | selfbalance => exact selfbalance_upstream m (prepare s) hp
    | address => exact address_upstream m (prepare s) hp
    | caller => exact caller_upstream m (prepare s) hp
    | callvalue => exact callvalue_upstream m (prepare s) hp
    | timestamp => exact timestamp_upstream m (prepare s) hp
  obtain ⟨m', s', hc, hr, hout⟩ := he
  rw [hc, hr]
  exact .ok hout

theorem push_agrees (a : Fin W) (m : Machine) (s : EvmYul.EVM.State)
    (h : EnvironmentAgrees m s) (fuel : Nat) :
    ResultAgrees ((Instr.push (.val a)).step m)
      (EvmYul.EVM.step (fuel + 1) 0 (some (.Push .PUSH32, some (encode a, 32))) s) := by
  have hc : (Instr.push (.val a)).step m = .ok {m with stack := .val a :: m.stack} 0 := rfl
  have hr : EvmYul.EVM.step (fuel + 1) 0 (some (.Push .PUSH32, some (encode a, 32))) s =
      .ok ((prepare s).replaceStackAndIncrPC (encode a :: s.stack) (pcΔ := 33)) := rfl
  rw [hc, hr]
  refine .ok ⟨?_, h.self, h.caller, h.value, h.time, h.balances⟩
  change .val a :: m.stack = .val (decode (encode a)) :: s.stack.map (fun x => .val (decode x))
  rw [decode_encode, h.stack]

theorem pop_dispatch (s : EvmYul.EVM.State) (fuel : Nat) :
    EvmYul.EVM.step (fuel + 1) 0 (some (.POP, none)) s =
      match s.stack.pop with
      | some (st, _) => .ok ((prepare s).replaceStackAndIncrPC st)
      | none => .error .StackUnderflow := by
  change EvmYul.step (τ := .EVM) .POP none (prepare s) = _
  unfold EvmYul.step
  dsimp only
  simp only [Id.run, prepare]
  cases s.stack.pop <;> rfl

theorem pop_agrees (m : Machine) (s : EvmYul.EVM.State)
    (h : EnvironmentAgrees m s) (fuel : Nat) :
    ResultAgrees (Instr.pop.step m)
      (EvmYul.EVM.step (fuel + 1) 0 (some (.POP, none)) s) := by
  cases hs : s.stack with
  | nil =>
    have hm : m.stack = [] := by simpa only [hs, List.map_nil] using h.stack
    have hc : Instr.pop.step m = .fault := by simp only [Instr.step, hm]
    have hr : EvmYul.EVM.step (fuel + 1) 0 (some (.POP, none)) s = .error .StackUnderflow := by
      rw [pop_dispatch]
      simp only [hs, EvmYul.Stack.pop]
    rw [hc, hr]
    exact .underflow
  | cons a st =>
    have hm : m.stack = .val (decode a) :: st.map (fun x => .val (decode x)) :=
      by simpa only [hs, List.map_cons] using h.stack
    have hc : Instr.pop.step m = .ok {m with stack := st.map (fun x => .val (decode x))} 0 := by
      simp only [Instr.step, hm, Machine.next]
    have hr : EvmYul.EVM.step (fuel + 1) 0 (some (.POP, none)) s =
        .ok ((prepare s).replaceStackAndIncrPC st) := by
      rw [pop_dispatch]
      simp only [hs, EvmYul.Stack.pop]
    rw [hc, hr]
    exact .ok ⟨rfl, h.self, h.caller, h.value, h.time, h.balances⟩

end Solidity.Evm.External

/-- info: 'Solidity.Evm.External.BinaryOpcode.agrees' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Solidity.Evm.External.BinaryOpcode.agrees

/-- info: 'Solidity.Evm.External.UnaryOpcode.agrees' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Solidity.Evm.External.UnaryOpcode.agrees

/-- info: 'Solidity.Evm.External.EnvironmentOpcode.agrees' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Solidity.Evm.External.EnvironmentOpcode.agrees

/-- info: 'Solidity.Evm.External.push_agrees' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Solidity.Evm.External.push_agrees

/-- info: 'Solidity.Evm.External.pop_agrees' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Solidity.Evm.External.pop_agrees
