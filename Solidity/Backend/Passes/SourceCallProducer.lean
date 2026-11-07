import Solidity.Backend.WorldCalls.ClosedSourceFrame

/-! G42.02 reached-call/frame producer for every typed source invocation.

Source side: the raw pre-decoder outcome (P3, `SourceBridge.evaluated_raw`)
and the P2 journal history (`ClosedSourceFrame.history_of_raw`, through the
H69 V2 induction `SourceDispatchV2.all_at`) of the actual `callAddr` run.

Target side: one fixed emission `push receiver; push value; CALL; POP` of the
existing core interpreter. Its CALL is reached on every machine, and the whole
code returns on every machine with stack, storage and memory restored (only
balances may move). The core CALL is payment-only: selector/argument bytes are
not passed and no callee code or RETURNDATA exists, and the target returns
whatever the source outcome is. `Step` is the graph of the produced source
outcome and the actual target run, so the `Premises` duties hold by
construction; their content is `rawAt` and `history`. `FetchedPremises` takes
one `ReturndataDuty`, whose relation is unconstrained (inherited). The
physical P1 frame contract (`InterfaceV3.Pending*`) remains a separate
compiler-consumer parameter; nothing here instantiates it. -/
namespace Solidity.Backend.Passes.SourceCallProducer
open Solidity.Source
open Solidity.Roadmap (Outcome)
open Solidity.Lowering.Readonly
open Solidity.Backend.WorldCalls
variable {E : Env} {Γ : RCtx} {dn : DeclName} {ps rs : List STy}

/-! ## Source: the existing raw/history producers, reused -/

def raw (i : InvocationFrame.Invocation E Γ dn ps rs) : Except Halt Outcome :=
  (SourceBridge.evaluated i).1
def final (i : InvocationFrame.Invocation E Γ dn ps rs) : St E := (SourceBridge.evaluated i).2

theorem rawAt (i : InvocationFrame.Invocation E Γ dn ps rs) : i.RawAt (raw i) (final i) :=
  SourceBridge.evaluated_raw i

theorem history (i : InvocationFrame.Invocation E Γ dn ps rs) :
    StaticJournal.History i.after.2.ex i.mode (final i).ex :=
  ClosedSourceFrame.history_of_raw i (raw i) (final i) (rawAt i)

/-! ## Target: the emitted CALL is reached and returns on every machine -/

theorem address_lt (a : Solidity.Roadmap.Address) : a.val < Evm.W :=
  Nat.lt_of_lt_of_le a.isLt (Nat.pow_le_pow_right (by decide) (by decide))

def addressWord (a : Solidity.Roadmap.Address) : Evm.Word := .val ⟨a.val, address_lt a⟩
def valueWord (v : Solidity.Roadmap.Word) : Evm.Word := .val ⟨v.val, v.isLt⟩

def code (i : InvocationFrame.Invocation E Γ dn ps rs) : Code :=
  ⟨[], [.push (addressWord i.captured.receiver), .push (valueWord i.captured.value), .call], [.pop]⟩

/-- The machine at the CALL: receiver and value on top of the caller's stack. -/
def atCall (i : InvocationFrame.Invocation E Γ dn ps rs) (m : Evm.Machine) : Evm.Machine :=
  {m with stack := valueWord i.captured.value :: addressWord i.captured.receiver :: m.stack}

/-- The reached CALL, for every initial machine. -/
def fetchedCall (i : InvocationFrame.Invocation E Γ dn ps rs) (m : Evm.Machine) :
    FetchedCall (code i).full m where
  pc := 2
  reached := atCall i m
  result := Evm.Instr.step .call (atCall i m)
  instruction := rfl
  prefixRun := rfl
  execute := rfl

/-- The CALL never faults: it pushes one status word and may move balances. -/
theorem call_step (i : InvocationFrame.Invocation E Γ dn ps rs) (m : Evm.Machine) :
    ∃ (status : Evm.Word) (bal : Fin Evm.W → Nat),
      Evm.Instr.step .call (atCall i m) = .ok {m with stack := status :: m.stack, bal := bal} 0 := by
  simp only [atCall, valueWord, addressWord, Evm.Instr.step]
  split
  · exact ⟨_, m.bal, rfl⟩
  · split
    · exact ⟨_, m.bal, rfl⟩
    · exact ⟨_, _, rfl⟩

/-- Frame restoration: the emitted code returns on every machine, restoring
stack, storage, memory and every other field except balances. -/
theorem restored (i : InvocationFrame.Invocation E Γ dn ps rs) (m : Evm.Machine) :
    ∃ bal : Fin Evm.W → Nat, Evm.run (code i).full m = .ok {m with bal := bal} 0 := by
  obtain ⟨status, bal, step⟩ := call_step i m
  refine ⟨bal, ?_⟩
  have prefixRun : Evm.run ((code i).full.take 3) m =
      .ok {m with stack := status :: m.stack, bal := bal} 0 := by
    show (Evm.Instr.step .call (atCall i m)).bind (fun m' k' => Evm.exec [] k' m') = _
    rw [step]
    rfl
  have split : (code i).full = (code i).full.take 3 ++ [.pop] := rfl
  rw [split, Evm.run_append_ok prefixRun]
  rfl

theorem returns (i : InvocationFrame.Invocation E Γ dn ps rs) (m : Evm.Machine) :
    ∃ m', Evm.run (code i).full m = .ok m' 0 ∧ m'.stack = m.stack ∧
      m'.store = m.store ∧ m'.mem = m.mem ∧ m'.self = m.self := by
  obtain ⟨bal, h⟩ := restored i m
  exact ⟨_, h, rfl, rfl, rfl, rfl⟩

/-! ## The `Premises` instance -/

/-- Structural observation only: a fetched CALL and the actual target run. -/
def Observed (i : InvocationFrame.Invocation E Γ dn ps rs) (key : Identity) (m : Evm.Machine)
    (out : Evm.Out) (_raw : Except Halt Outcome) : Prop :=
  key = identity i ∧ Nonempty (FetchedCall (code i).full m) ∧ out = Evm.run (code i).full m

/-- One step: this invocation's identity, its produced source outcome, and the
actual target run of the emitted code. -/
def Step (i : InvocationFrame.Invocation E Γ dn ps rs) (key : Identity) (m : Evm.Machine)
    (result : Except Halt Outcome) (state : St E) (out : Evm.Out) : Prop :=
  key = identity i ∧ result = raw i ∧ state = final i ∧ out = Evm.run (code i).full m

def premises (i : InvocationFrame.Invocation E Γ dn ps rs) : Premises i where
  code := code i
  Observed := Observed i
  Step := Step i
  bound _ _ _ _ _ h := h.1
  execution _ _ _ _ _ h := h.2.2.2.symm
  observed _ m _ _ _ h := ⟨h.1, ⟨fetchedCall i m⟩, h.2.2.2⟩
  sourceRaw _ _ _ _ _ h := by
    rw [h.2.1, h.2.2.1]
    exact rawAt i
  p2History _ _ _ _ _ h := by
    rw [h.2.2.1]
    exact history i

/-- Non-vacuity: the step holds on every machine. -/
theorem step_total (i : InvocationFrame.Invocation E Γ dn ps rs) (m : Evm.Machine) :
    (premises i).Step (identity i) m (raw i) (final i) (Evm.run (code i).full m) :=
  ⟨rfl, rfl, rfl, rfl⟩

/-- A step admits no other raw outcome or final state. -/
theorem step_unique (i : InvocationFrame.Invocation E Γ dn ps rs) {key : Identity}
    {m : Evm.Machine} {result : Except Halt Outcome} {state : St E} {out : Evm.Out}
    (h : (premises i).Step key m result state out) :
    key = identity i ∧ result = raw i ∧ state = final i :=
  ⟨h.1, h.2.1, h.2.2.1⟩

/-! ## `FetchedPremises` from the single CALL/RETURNDATA duty -/

/-- Placeholder for V15's CALL/RETURNDATA correspondence. The relation is
chosen by the supplier and unconstrained, as in `FetchedPremises.Returndata`,
so `fun _ _ _ _ => True` meets it (`Controls.trivial_duty`); it carries content
only once the relation is pinned to a validated correspondence. -/
structure ReturndataDuty (i : InvocationFrame.Invocation E Γ dn ps rs) where
  Returndata : Identity → {m : Evm.Machine} → FetchedCall (code i).full m →
    Evm.Out → Except Halt Outcome → Prop
  holds : ∀ m, Returndata (identity i) (fetchedCall i m) (Evm.run (code i).full m) (raw i)

def fetchedPremises (i : InvocationFrame.Invocation E Γ dn ps rs) (duty : ReturndataDuty i) :
    FetchedPremises i (premises i) where
  Returndata := duty.Returndata
  Fetched := fun m result state out => Step i (identity i) m result state out
  fetch := fun m _ _ _ _ => fetchedCall i m
  returndata := by
    intro m result state out h
    obtain ⟨_, r, _, o⟩ := h
    rw [r, o]
    exact duty.holds m
  step := fun _ _ _ _ h => h

theorem fetched_total (i : InvocationFrame.Invocation E Γ dn ps rs) (duty : ReturndataDuty i)
    (m : Evm.Machine) :
    (fetchedPremises i duty).Fetched m (raw i) (final i) (Evm.run (code i).full m) :=
  step_total i m

end Solidity.Backend.Passes.SourceCallProducer

/-- info: 'Solidity.Backend.Passes.SourceCallProducer.rawAt' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Solidity.Backend.Passes.SourceCallProducer.rawAt

/-- info: 'Solidity.Backend.Passes.SourceCallProducer.history' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Solidity.Backend.Passes.SourceCallProducer.history

/-- info: 'Solidity.Backend.Passes.SourceCallProducer.call_step' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Solidity.Backend.Passes.SourceCallProducer.call_step

/-- info: 'Solidity.Backend.Passes.SourceCallProducer.restored' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Solidity.Backend.Passes.SourceCallProducer.restored

/-- info: 'Solidity.Backend.Passes.SourceCallProducer.returns' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Solidity.Backend.Passes.SourceCallProducer.returns

/-- info: 'Solidity.Backend.Passes.SourceCallProducer.step_total' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Solidity.Backend.Passes.SourceCallProducer.step_total

/-- info: 'Solidity.Backend.Passes.SourceCallProducer.step_unique' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Solidity.Backend.Passes.SourceCallProducer.step_unique

/-- info: 'Solidity.Backend.Passes.SourceCallProducer.fetched_total' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Solidity.Backend.Passes.SourceCallProducer.fetched_total
