import Solidity.Backend.Passes.SourceCallProducer
import Solidity.Backend.Passes.SourceCallBytes

/-! G42.02 producer on the versioned EVM machine (`Evm.MachineV2`, H57 pair of
the frozen `Evm.Machine`).

The emission stores the invocation's captured input bytes in memory from cell
`o`, then `CALLIN(value, receiver, o, length)` and `POP`. On every machine it
returns with the caller's stack and storage. An entered call journals exactly
the captured input (`call_run`) and leaves the callee oracle's reply in the
return buffer. An unentered call preserves the journal and empties the buffer.

`Returndata` is a fixed relation, not a supplier-chosen `Prop`: whenever the
source outcome has a payload `d` and the machine's reply oracle answers `d`
for the captured input (`OracleAgrees`), the target run leaves `d` in the
return buffer and journals the input. `returndata_holds` proves it for every
invocation and machine. It holds for every result (`returndata_any`): its
content is input transport and `CALLIN`'s buffer law, not a link from the
source world's callee to the oracle (V15). The caller must be able to pay;
the `CALLIN` status word is popped and not compared with the source flag.

Limits, inherited from `MachineV2`: the callee's code is not run; its answer is
the `reply`/`accepts` oracle; there is no gas and no call depth; memory is
word-addressed. Source halts (timeout, depth, static refusal) have no payload
and no CALL correspondence here. The input length must be below `2^256`. -/
namespace Solidity.Backend.Passes.SourceCallProducerV2
open Solidity.Source Solidity.Evm
open Solidity.Roadmap (Outcome)
open Solidity.Lowering.Readonly
open Solidity.Backend.Passes.SourceCallBytes
variable {E : Env} {Γ : RCtx} {dn : DeclName} {ps rs : List STy}

def receiver (i : InvocationFrame.Invocation E Γ dn ps rs) : Fin W :=
  ⟨i.captured.receiver.val, SourceCallProducer.address_lt _⟩
def amount (i : InvocationFrame.Invocation E Γ dn ps rs) : Fin W :=
  ⟨i.captured.value.val, i.captured.value.isLt⟩
def input (i : InvocationFrame.Invocation E Γ dn ps rs) : List UInt8 := i.captured.input

/-- The four `CALLIN` operands, value on top. -/
def operands (i : InvocationFrame.Invocation E Γ dn ps rs) (o : Fin W) : List InstrV2 :=
  [.base (.push (.val (wmod (input i).length))), .base (.push (.val o)),
    .base (.push (.val (receiver i))), .base (.push (.val (amount i)))]

def code (i : InvocationFrame.Invocation E Γ dn ps rs) (o : Fin W) : List InstrV2 :=
  lift (stores o.1 (chunks (input i))) ++ (operands i o ++ [.callIn, .base .pop])

/-- The machine after the stores. -/
def stored (i : InvocationFrame.Invocation E Γ dn ps rs) (o : Fin W) (m : MachineV2) : MachineV2 :=
  m.withBase {m.base with mem := storeMem m.base.mem o.1 (chunks (input i))}

/-- The machine at `CALLIN`. -/
def atCall (i : InvocationFrame.Invocation E Γ dn ps rs) (o : Fin W) (m : MachineV2) : MachineV2 :=
  let s := stored i o m
  s.withBase {s.base with stack := (Word.val (amount i) :: Word.val (receiver i) :: Word.val o ::
    Word.val (wmod (input i).length) :: m.base.stack)}

theorem wmod_small (n : Nat) (small : n < W) : (wmod n).1 = n := by
  simp only [wmod, Nat.mod_eq_of_lt small]

theorem prefix_run (i : InvocationFrame.Invocation E Γ dn ps rs) (o : Fin W) (m : MachineV2) :
    runV2 (lift (stores o.1 (chunks (input i))) ++ operands i o) m = .ok (atCall i o m) 0 := by
  rw [runV2_append_ok (run_lift_ok (run_stores o.1 (chunks (input i)) m.base))]
  rfl

/-- **Input transport**: `CALLIN` reads exactly the captured input. -/
theorem callIn_input (i : InvocationFrame.Invocation E Γ dn ps rs) (o : Fin W) (m : MachineV2)
    (small : (input i).length < W) :
    InstrV2.callIn.step (atCall i o m) =
      callInStep (atCall i o m) (amount i) (receiver i) (input i) m.base.stack := by
  have read : readBytes (stored i o m).base.mem o.1 (wmod (input i).length).1 = some (input i) := by
    rw [wmod_small _ small]
    exact readBytes_stores _ _ _
  rw [atCall, callIn_step, read]

/-- The frozen `CALL` pushes one status word and may move balances. -/
theorem call_shape (b : Machine) (v a : Fin W) (st : List Word) :
    ∃ (status : Word) (bal : Fin W → Nat),
      Instr.call.step {b with stack := .val v :: .val a :: st} = .ok {b with stack := status :: st, bal := bal} 0 := by
  simp only [Instr.step]
  split
  · exact ⟨_, b.bal, rfl⟩
  · split
    · exact ⟨_, b.bal, rfl⟩
    · exact ⟨_, _, rfl⟩

/-- **The emitted call on every machine**: it returns with the caller's stack,
storage and oracles; an entered call leaves the reply to the captured input
in the buffer and journals that input; an unentered one empties the buffer. -/
theorem call_run (i : InvocationFrame.Invocation E Γ dn ps rs) (o : Fin W) (m : MachineV2)
    (small : (input i).length < W) :
    ∃ m', runV2 (code i o) m = .ok m' 0 ∧ m'.base.stack = m.base.stack ∧
      m'.base.store = m.base.store ∧ m'.reply = m.reply ∧
      (((amount i).1 ≤ m.base.bal m.base.self ∧
          m'.returndata = m.reply (receiver i) (amount i) (input i) ∧
          m'.calls = m.calls ++ [⟨receiver i, amount i, input i,
            m.base.accepts (receiver i) (amount i), m.reply (receiver i) (amount i) (input i)⟩]) ∨
        (m.base.bal m.base.self < (amount i).1 ∧ m'.returndata = [] ∧ m'.calls = m.calls)) := by
  obtain ⟨m1, step1, cases, reply1⟩ :=
    callIn_returndata (atCall i o m) (amount i) (receiver i) (input i) m.base.stack
  have forget := callIn_forget (atCall i o m) (amount i) (receiver i) (input i) m.base.stack
  obtain ⟨status, bal, shape⟩ := call_shape (stored i o m).base (amount i) (receiver i) m.base.stack
  rw [step1] at forget
  have base1 : m1.base = {(stored i o m).base with stack := status :: m.base.stack, bal := bal} := by
    have h : (OutV2.ok m1 0).forget = Out.ok {(stored i o m).base with stack := status :: m.base.stack, bal := bal} 0 :=
      forget.trans shape
    simp only [OutV2.forget, Out.ok.injEq, and_true] at h
    exact h
  have pop : runV2 [.base .pop] m1 = .ok (m1.withBase {m1.base with stack := m.base.stack}) 0 := by
    show (OutV2.ofOut m1 (Instr.pop.step m1.base)).bind (fun m' k' => execV2 [] k' m') = _
    rw [base1]
    rfl
  refine ⟨m1.withBase {m1.base with stack := m.base.stack}, ?_, rfl, ?_, reply1, cases⟩
  · have split : code i o = (lift (stores o.1 (chunks (input i))) ++ operands i o) ++ (.callIn :: [.base .pop]) := by
      simp only [code, List.append_assoc]
    rw [split, runV2_append_ok (prefix_run i o m)]
    show (InstrV2.callIn.step (atCall i o m)).bind (fun m' k' => execV2 [.base .pop] k' m') = _
    rw [callIn_input i o m small, step1]
    exact pop
  · show m1.base.store = m.base.store
    rw [base1]
    rfl

/-! ## The source link -/

/-- The bytes and success flag of a source outcome; halts have none. -/
def payload : Except Halt Outcome → Option (Bool × List UInt8)
  | .ok (.success d) => some (true, d)
  | .ok (.revert d) => some (false, d)
  | .error _ => none

/-- The machine's callee oracles answer this call with `d` (accepting iff
`ok`), and the caller can pay the value. This premise names the source payload;
it does not refer to the source world's callee, so the buffer equality it
yields is `callIn_returndata` plus this premise (see `returndata_any`). -/
structure OracleAgrees (i : InvocationFrame.Invocation E Γ dn ps rs) (m : MachineV2)
    (ok : Bool) (d : List UInt8) : Prop where
  reply : m.reply (receiver i) (amount i) (input i) = d
  accepts : m.base.accepts (receiver i) (amount i) = ok
  funded : (amount i).1 ≤ m.base.bal m.base.self

/-- The pinned CALL/RETURNDATA relation for this emission: a source payload,
under agreeing oracles, is the return buffer and the journaled call. -/
def Returndata (i : InvocationFrame.Invocation E Γ dn ps rs) (m : MachineV2) (out : OutV2)
    (result : Except Halt Outcome) : Prop :=
  ∀ ok d, payload result = some (ok, d) → OracleAgrees i m ok d →
    ∃ m', out = .ok m' 0 ∧ m'.returndata = d ∧ m'.base.stack = m.base.stack ∧
      m'.calls = m.calls ++ [⟨receiver i, amount i, input i, ok, d⟩]

/-- Agreeing oracles: answer `d` on exactly the captured input (and `[]` on
any other), accept iff `ok`, and fund only the caller. -/
def oracle (i : InvocationFrame.Invocation E Γ dn ps rs) (m : MachineV2) (ok : Bool)
    (d : List UInt8) : MachineV2 :=
  { m with reply := fun _ _ x => if x = input i then d else [],
           base := {m.base with accepts := fun _ _ => ok, bal := upd m.base.bal m.base.self W} }

/-- **Joint satisfiability**: every source payload has agreeing oracles. -/
theorem oracle_agrees (i : InvocationFrame.Invocation E Γ dn ps rs) (m : MachineV2)
    (ok : Bool) (d : List UInt8) : OracleAgrees i (oracle i m ok d) ok d :=
  ⟨if_pos rfl, rfl, by
    show (amount i).1 ≤ upd m.base.bal m.base.self W m.base.self
    rw [upd_same]
    exact Nat.le_of_lt (amount i).isLt⟩

/-- Disclosure: the pinned relation holds for every source result, not only
`raw i`. Its content is input transport plus `CALLIN`'s buffer law; the
source outcome only names which payload the oracle premise must give. -/
theorem returndata_any (i : InvocationFrame.Invocation E Γ dn ps rs) (o : Fin W) (m : MachineV2)
    (small : (input i).length < W) (result : Except Halt Outcome) :
    Returndata i m (runV2 (code i o) m) result := by
  intro ok d _ agree
  obtain ⟨m', run, stack, _, _, cases⟩ := call_run i o m small
  rcases cases with ⟨_, buffer, calls⟩ | ⟨poor, _, _⟩
  · refine ⟨m', run, buffer.trans agree.reply, stack, ?_⟩
    rw [calls, agree.reply, agree.accepts]
  · exact absurd agree.funded (Nat.not_le_of_lt poor)

/-- **The relation holds for every invocation and machine.** -/
theorem returndata_holds (i : InvocationFrame.Invocation E Γ dn ps rs) (o : Fin W) (m : MachineV2)
    (small : (input i).length < W) :
    Returndata i m (runV2 (code i o) m) (SourceCallProducer.raw i) :=
  returndata_any i o m small _

/-- Non-vacuity: under the agreeing oracle the pinned relation's conclusion
holds for the actual source payload. -/
theorem transported (i : InvocationFrame.Invocation E Γ dn ps rs) (o : Fin W) (m : MachineV2)
    (small : (input i).length < W) (ok : Bool) (d : List UInt8)
    (h : payload (SourceCallProducer.raw i) = some (ok, d)) :
    ∃ m', runV2 (code i o) (oracle i m ok d) = .ok m' 0 ∧ m'.returndata = d ∧
      m'.base.stack = m.base.stack ∧
      m'.calls = m.calls ++ [⟨receiver i, amount i, input i, ok, d⟩] :=
  returndata_holds i o (oracle i m ok d) small ok d h (oracle_agrees i m ok d)

/-- The source half of the pair is still produced: raw outcome and history. -/
theorem source (i : InvocationFrame.Invocation E Γ dn ps rs) :
    i.RawAt (SourceCallProducer.raw i) (SourceCallProducer.final i) ∧
      StaticJournal.History i.after.2.ex i.mode (SourceCallProducer.final i).ex :=
  ⟨SourceCallProducer.rawAt i, SourceCallProducer.history i⟩

end Solidity.Backend.Passes.SourceCallProducerV2

/-- info: 'Solidity.Backend.Passes.SourceCallProducerV2.wmod_small' depends on axioms: [propext] -/
#guard_msgs in
#print axioms Solidity.Backend.Passes.SourceCallProducerV2.wmod_small
/-- info: 'Solidity.Backend.Passes.SourceCallProducerV2.prefix_run' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Solidity.Backend.Passes.SourceCallProducerV2.prefix_run
/-- info: 'Solidity.Backend.Passes.SourceCallProducerV2.callIn_input' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Solidity.Backend.Passes.SourceCallProducerV2.callIn_input
/-- info: 'Solidity.Backend.Passes.SourceCallProducerV2.call_shape' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Solidity.Backend.Passes.SourceCallProducerV2.call_shape
/-- info: 'Solidity.Backend.Passes.SourceCallProducerV2.call_run' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Solidity.Backend.Passes.SourceCallProducerV2.call_run
/-- info: 'Solidity.Backend.Passes.SourceCallProducerV2.returndata_holds' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms Solidity.Backend.Passes.SourceCallProducerV2.returndata_holds
/-- info: 'Solidity.Backend.Passes.SourceCallProducerV2.oracle_agrees' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Solidity.Backend.Passes.SourceCallProducerV2.oracle_agrees
/-- info: 'Solidity.Backend.Passes.SourceCallProducerV2.transported' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Solidity.Backend.Passes.SourceCallProducerV2.transported
/-- info: 'Solidity.Backend.Passes.SourceCallProducerV2.source' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Solidity.Backend.Passes.SourceCallProducerV2.source

/-- info: 'Solidity.Backend.Passes.SourceCallProducerV2.returndata_any' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Solidity.Backend.Passes.SourceCallProducerV2.returndata_any
