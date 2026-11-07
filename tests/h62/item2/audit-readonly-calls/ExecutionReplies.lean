import Solidity.Backend.Passes.SourceCallBytes

/-! Guard a source-named oracle reply being mistaken for executed callee code.
This target-only adapter derives acceptance/data from actual runV2 execution on
an explicit callee image and prepared input memory. Fault/pending execution has
no adapter; funded and unfunded CALLIN remain distinct. The caller memory/store
frame is proved for callInStep, not an emitted caller program. Child final state
is discarded. This adapter is for one selected input: accepts(a,v) has no input
argument. No Source-to-core compiler, world code selection, nested-call,
gas/fork, heap/allocator P1 or full G42.02 adequacy is asserted. -/
namespace Solidity.H62.ReadonlyCalls.ExecutionReplies
open Solidity.Evm Solidity.Backend.Passes.SourceCallBytes

/-- The actual child header and exact input window, rather than a source payload. -/
def prepare (caller child : MachineV2) (a v o : Fin W) (input : List UInt8) : MachineV2 :=
  child.withBase {child.base with
    stack := []
    self := a
    caller := caller.base.self
    callvalue := v
    mem := storeMem child.base.mem o.1 (chunks input)}

/-- Reuse the canonical existing frame-exit observation. -/
abbrev observe : OutV2 → Option (Bool × List UInt8) := OutV2.exit

/-- Internal single-input adapter: reply is input-specific, while accepts affects
every input at the selected address/value pair, as required by MachineV2. -/
def configure (caller : MachineV2) (a v : Fin W) (input : List UInt8)
    (accepted : Bool) (data : List UInt8) : MachineV2 :=
  {caller with
    reply := fun a' v' input' => if a'=a ∧ v'=v ∧ input'=input then data else caller.reply a' v' input',
    base := {caller.base with accepts := fun a' v' =>
      if a'=a ∧ v'=v then accepted else caller.base.accepts a' v'}}

/-- No source outcome or supplier-chosen bytes are arguments of this adapter. -/
noncomputable def attach (code : List InstrV2) (caller child : MachineV2)
    (a v o : Fin W) (input : List UInt8) : Option MachineV2 :=
  (observe (runV2 code (prepare caller child a v o input))).map
    (fun result => configure caller a v input result.1 result.2)

theorem prepare_input (caller child : MachineV2) (a v o : Fin W) (input : List UInt8) :
    readBytes (prepare caller child a v o input).base.mem o.1 input.length = some input :=
  readBytes_stores _ _ _

theorem prepare_context (caller child : MachineV2) (a v o : Fin W) (input : List UInt8) :
    (prepare caller child a v o input).base.self = a ∧
    (prepare caller child a v o input).base.caller = caller.base.self ∧
    (prepare caller child a v o input).base.callvalue = v ∧
    (prepare caller child a v o input).base.stack = [] := ⟨rfl,rfl,rfl,rfl⟩

theorem configured_reply (caller : MachineV2) (a v : Fin W) (input data : List UInt8) (ok : Bool) :
    (configure caller a v input ok data).reply a v input = data :=
  if_pos ⟨rfl,rfl,rfl⟩

theorem configured_accepts (caller : MachineV2) (a v : Fin W) (input data : List UInt8) (ok : Bool) :
    (configure caller a v input ok data).base.accepts a v = ok := if_pos ⟨rfl,rfl⟩

/-- Caller physical memory/storage survive every CALLIN branch, including poverty. -/
theorem callIn_frame (m final : MachineV2) (a v : Fin W) (input : List UInt8) (tail : List Word)
    (actual : callInStep m v a input tail = .ok final 0) :
    final.base.mem = m.base.mem ∧ final.base.store = m.base.store := by
  by_cases poor : m.base.bal m.base.self < v.1
  · rw [callInStep,if_pos poor] at actual
    cases actual
    exact ⟨rfl,rfl⟩
  · rw [callInStep,if_neg poor] at actual
    dsimp only at actual
    by_cases accepted : m.base.accepts a v = false
    · rw [if_pos accepted] at actual
      cases actual
      exact ⟨rfl,rfl⟩
    · rw [if_neg accepted] at actual
      by_cases own : a = m.base.self
      · rw [if_pos own] at actual
        cases actual
        exact ⟨rfl,rfl⟩
      · rw [if_neg own] at actual
        cases actual
        exact ⟨rfl,rfl⟩

/-- All native outcomes are accounted for, without a desired source/target result
premise. Entered calls transport actual native bytes/status; poor callers do not
enter. No adapter exists for a fault or pending jump. -/
theorem execution_transport (code : List InstrV2) (caller child : MachineV2)
    (a v o : Fin W) (input : List UInt8) (tail : List Word) :
    match observe (runV2 code (prepare caller child a v o input)) with
    | none => attach code caller child a v o input = none
    | some (ok,data) => ∃ configured final,
        attach code caller child a v o input = some configured ∧
        callInStep configured v a input tail = .ok final 0 ∧
        final.base.mem = caller.base.mem ∧ final.base.store = caller.base.store ∧
        ((v.1 ≤ caller.base.bal caller.base.self ∧ final.returndata = data ∧
          final.calls = caller.calls ++ [⟨a,v,input,ok,data⟩]) ∨
         (caller.base.bal caller.base.self < v.1 ∧ final.returndata = [] ∧ final.calls = caller.calls)) := by
  cases result : observe (runV2 code (prepare caller child a v o input)) with
  | none => simp only [attach,result,Option.map_none]
  | some pair =>
    rcases pair with ⟨ok,data⟩
    let configured := configure caller a v input ok data
    obtain ⟨final,run,cases,_⟩ := callIn_returndata configured v a input tail
    have frame := callIn_frame configured final a v input tail run
    refine ⟨configured,final,?_,run,frame.1,frame.2,?_⟩
    · simp only [attach,result,Option.map_some]
      rfl
    · rcases cases with good | poor
      · refine .inl ⟨good.1,good.2.1.trans (configured_reply _ _ _ _ _ _),?_⟩
        rw [good.2.2]
        change _ = caller.calls ++ [⟨a,v,input,ok,data⟩]
        rw [configured_reply,configured_accepts]
        rfl
      · exact .inr poor

/-- A concrete native image returns the prepared input bytes. -/
def echo (o : Fin W) (input : List UInt8) : List InstrV2 :=
  [.base (.push (.val (wmod input.length))), .base (.push (.val o)), .ret]

def revertInput (o : Fin W) (input : List UInt8) : List InstrV2 :=
  [.base (.push (.val (wmod input.length))), .base (.push (.val o)), .revertData]

theorem echo_success (caller child : MachineV2) (a v o : Fin W) (input : List UInt8)
    (small : input.length < W) :
    observe (runV2 (echo o input) (prepare caller child a v o input)) = some (true,input) := by
  have length : (wmod input.length).1 = input.length := Nat.mod_eq_of_lt small
  have read : readBytes (prepare caller child a v o input).base.mem o.1
      (wmod input.length).1 = some input := by
    rw [length]
    exact prepare_input caller child a v o input
  simp only [runV2,echo,execV2,InstrV2.step,Instr.step,Machine.next,
    OutV2.ofOut,OutV2.bind,MachineV2.withBase,read,observe,OutV2.exit]

theorem echo_revert (caller child : MachineV2) (a v o : Fin W) (input : List UInt8)
    (small : input.length < W) :
    observe (runV2 (revertInput o input) (prepare caller child a v o input)) = some (false,input) := by
  have length : (wmod input.length).1 = input.length := Nat.mod_eq_of_lt small
  have read : readBytes (prepare caller child a v o input).base.mem o.1
      (wmod input.length).1 = some input := by
    rw [length]
    exact prepare_input caller child a v o input
  simp only [runV2,revertInput,execV2,InstrV2.step,Instr.step,Machine.next,
    OutV2.ofOut,OutV2.bind,MachineV2.withBase,read,observe,OutV2.exit]

theorem fault_refused (caller child : MachineV2) (a v o : Fin W) (input : List UInt8) :
    attach [.ret] caller child a v o input = none := rfl

theorem pending_refused (m : MachineV2) (n : Nat) : observe (.ok m (n+1)) = none := rfl

theorem not_always_revert (caller child : MachineV2) (a v o : Fin W) (input : List UInt8)
    (small : input.length < W) :
    observe (runV2 (echo o input) (prepare caller child a v o input)) ≠ some (false,input) := by
  rw [echo_success caller child a v o input small]
  intro same
  cases same

end Solidity.H62.ReadonlyCalls.ExecutionReplies
