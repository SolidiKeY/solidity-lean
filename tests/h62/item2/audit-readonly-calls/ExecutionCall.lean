import ExecutionReplies

/-! Guard step-only reply transport being reported as an executed caller image.
The generic word-memory input stores, operand pushes, CALLIN and POP really run;
caller stack/storage and every memory cell outside the input window are framed.
Reply/status come from the preceding explicit native callee execution adapter.
This remains single-input, pre-decoder target transport: no Source/compiler/world
code selection, child state commit, nested-call, gas/fork or full P1 adequacy. -/
namespace Solidity.H62.ReadonlyCalls.ExecutionCall
open Solidity.Evm Solidity.Backend.Passes.SourceCallBytes
open Solidity.H62.ReadonlyCalls.ExecutionReplies

/-- Generic form of the existing caller operand sequence, without Source dependencies. -/
def operands (a v o : Fin W) (input : List UInt8) : List InstrV2 :=
  [.base (.push (.val (wmod input.length))), .base (.push (.val o)),
   .base (.push (.val a)), .base (.push (.val v))]

def prefixCode (a v o : Fin W) (input : List UInt8) : List InstrV2 :=
  lift (stores o.1 (chunks input)) ++ operands a v o input

def code (a v o : Fin W) (input : List UInt8) : List InstrV2 :=
  prefixCode a v o input ++ [.callIn,.base .pop]

def atCall (caller : MachineV2) (a v o : Fin W) (input : List UInt8) : MachineV2 :=
  caller.withBase {caller.base with
    mem := storeMem caller.base.mem o.1 (chunks input)
    stack := .val v :: .val a :: .val o :: .val (wmod input.length) :: caller.base.stack}

theorem prefix_run (caller : MachineV2) (a v o : Fin W) (input : List UInt8) :
    runV2 (prefixCode a v o input) caller = .ok (atCall caller a v o input) 0 := by
  rw [prefixCode,runV2_append_ok (run_lift_ok (run_stores o.1 (chunks input) caller.base))]
  rfl

theorem input_read (caller : MachineV2) (a v o : Fin W) (input : List UInt8)
    (small : input.length < W) :
    InstrV2.callIn.step (atCall caller a v o input) =
      callInStep (atCall caller a v o input) v a input caller.base.stack := by
  have read : readBytes (atCall caller a v o input).base.mem o.1 (wmod input.length).1 = some input := by
    have length : (wmod input.length).1 = input.length := Nat.mod_eq_of_lt small
    rw [length]
    exact readBytes_stores _ _ _
  change (match readBytes (atCall caller a v o input).base.mem o.1 (wmod input.length).1 with
    | some bytes => callInStep (atCall caller a v o input) v a bytes caller.base.stack
    | none => .fault) = _
  rw [read]

/-- Every CALLIN branch leaves one status word above the same tail. -/
theorem callIn_stack (m final : MachineV2) (a v : Fin W) (input : List UInt8) (tail : List Word)
    (actual : callInStep m v a input tail = .ok final 0) :
    ∃ status : Word, final.base.stack = status :: tail := by
  by_cases poor : m.base.bal m.base.self < v.1
  · rw [callInStep,if_pos poor] at actual
    cases actual
    exact ⟨_,rfl⟩
  · rw [callInStep,if_neg poor] at actual
    dsimp only at actual
    by_cases accepted : m.base.accepts a v = false
    · rw [if_pos accepted] at actual
      cases actual
      exact ⟨_,rfl⟩
    · rw [if_neg accepted] at actual
      by_cases own : a = m.base.self
      · rw [if_pos own] at actual
        cases actual
        exact ⟨_,rfl⟩
      · rw [if_neg own] at actual
        cases actual
        exact ⟨_,rfl⟩

/-- The whole caller image executes; poverty is observed rather than excluded. -/
theorem run_code (caller : MachineV2) (a v o : Fin W) (input : List UInt8)
    (small : input.length < W) :
    ∃ final, runV2 (code a v o input) caller = .ok final 0 ∧
      final.base.stack = caller.base.stack ∧ final.base.store = caller.base.store ∧
      final.base.mem = storeMem caller.base.mem o.1 (chunks input) ∧
      ((v.1 ≤ caller.base.bal caller.base.self ∧ final.returndata = caller.reply a v input ∧
        final.calls = caller.calls ++ [⟨a,v,input,caller.base.accepts a v,caller.reply a v input⟩]) ∨
       (caller.base.bal caller.base.self < v.1 ∧ final.returndata = [] ∧ final.calls = caller.calls)) := by
  obtain ⟨returned,step,branches,_⟩ :=
    callIn_returndata (atCall caller a v o input) v a input caller.base.stack
  have frame := callIn_frame (atCall caller a v o input) returned a v input caller.base.stack step
  obtain ⟨status,stack⟩ := callIn_stack (atCall caller a v o input) returned a v input caller.base.stack step
  let final := returned.withBase {returned.base with stack := caller.base.stack}
  have pop : runV2 [.base .pop] returned = .ok final 0 := by
    simp only [runV2,execV2,InstrV2.step,Instr.step,stack,Machine.next,
      OutV2.ofOut,OutV2.bind]
    rfl
  refine ⟨final,?_,rfl,frame.2,frame.1,branches⟩
  rw [code,runV2_append_ok (prefix_run caller a v o input)]
  show (InstrV2.callIn.step (atCall caller a v o input)).bind (fun m k => execV2 [.base .pop] k m) = _
  rw [input_read caller a v o input small,step]
  exact pop

/-- The existing lower-window frame is complemented by the upper-window frame. -/
theorem storeMem_above (mem : Nat → Word) (o : Nat) (cs : List (List UInt8)) (x : Nat)
    (above : o + cs.length ≤ x) : storeMem mem o cs x = mem x := by
  induction cs generalizing mem o with
  | nil => rfl
  | cons c cs ih =>
    have bound : (o+1)+cs.length ≤ x := by simp only [List.length_cons] at above; omega
    have different : x ≠ o := by simp only [List.length_cons] at above; omega
    rw [storeMem,ih _ _ bound,upd_other _ _ different]

theorem memory_outside (caller final : MachineV2) (a v o : Fin W) (input : List UInt8)
    (small : input.length < W) (actual : runV2 (code a v o input) caller = .ok final 0)
    (x : Nat) (outside : x < o.1 ∨ o.1 + (chunks input).length ≤ x) :
    final.base.mem x = caller.base.mem x := by
  obtain ⟨reached,run,_,_,memory,_⟩ := run_code caller a v o input small
  have same : reached = final := (OutV2.ok.inj (run.symm.trans actual)).1
  rw [← same,memory]
  exact outside.elim (storeMem_below _ _ _ _) (storeMem_above _ _ _ _)

/-- Actual native exit drives an actual caller image, without a desired Source
outcome premise. Caller code returns normally even for child revert: this is the
pre-decoder call prefix; the recorded child flag/data are retained verbatim. -/
theorem native_call (callee : List InstrV2) (caller child : MachineV2) (a v o : Fin W)
    (input : List UInt8) (small : input.length < W) :
    match observe (runV2 callee (prepare caller child a v o input)) with
    | none => attach callee caller child a v o input = none
    | some (ok,data) => ∃ configured final,
        attach callee caller child a v o input = some configured ∧
        runV2 (code a v o input) configured = .ok final 0 ∧
        final.base.stack = caller.base.stack ∧ final.base.store = caller.base.store ∧
        final.base.mem = storeMem caller.base.mem o.1 (chunks input) ∧
        ((v.1 ≤ caller.base.bal caller.base.self ∧ final.returndata = data ∧
          final.calls = caller.calls ++ [⟨a,v,input,ok,data⟩]) ∨
         (caller.base.bal caller.base.self < v.1 ∧ final.returndata = [] ∧ final.calls = caller.calls)) := by
  cases native : observe (runV2 callee (prepare caller child a v o input)) with
  | none => simp only [attach,native,Option.map_none]
  | some pair =>
    rcases pair with ⟨ok,data⟩
    let configured := configure caller a v input ok data
    obtain ⟨final,run,stack,store,memory,branches⟩ := run_code configured a v o input small
    refine ⟨configured,final,?_,run,stack,store,memory,?_⟩
    · simp only [attach,native,Option.map_some]
      rfl
    · rcases branches with good | poor
      · refine .inl ⟨good.1,good.2.1.trans (configured_reply _ _ _ _ _ _),?_⟩
        rw [good.2.2,configured_reply,configured_accepts]
        rfl
      · exact .inr poor

/-- A funded corollary; the observation is an actual native execution equation,
which the success/revert controls discharge using concrete code images. -/
theorem funded_native (callee : List InstrV2) (caller child : MachineV2) (a v o : Fin W)
    (input data : List UInt8) (ok : Bool) (small : input.length < W)
    (funded : v.1 ≤ caller.base.bal caller.base.self)
    (native : observe (runV2 callee (prepare caller child a v o input)) = some (ok,data)) :
    ∃ configured final, attach callee caller child a v o input = some configured ∧
      runV2 (code a v o input) configured = .ok final 0 ∧ final.returndata = data ∧
      final.calls = caller.calls ++ [⟨a,v,input,ok,data⟩] ∧
      final.base.stack = caller.base.stack ∧ final.base.store = caller.base.store := by
  have linked := native_call callee caller child a v o input small
  rw [native] at linked
  obtain ⟨configured,final,attached,run,stack,store,_,branches⟩ := linked
  rcases branches with good | poor
  · exact ⟨configured,final,attached,run,good.2.1,good.2.2,stack,store⟩
  · exact False.elim (Nat.not_lt_of_le funded poor.1)

theorem native_echo (caller child : MachineV2) (a v o : Fin W) (input : List UInt8)
    (small : input.length < W) (funded : v.1 ≤ caller.base.bal caller.base.self) :
    ∃ configured final, attach (echo o input) caller child a v o input = some configured ∧
      runV2 (code a v o input) configured = .ok final 0 ∧ final.returndata = input ∧
      final.calls = caller.calls ++ [⟨a,v,input,true,input⟩] ∧
      final.base.stack = caller.base.stack ∧ final.base.store = caller.base.store :=
  funded_native _ _ _ _ _ _ _ _ _ small funded (echo_success _ _ _ _ _ _ small)

theorem native_revert (caller child : MachineV2) (a v o : Fin W) (input : List UInt8)
    (small : input.length < W) (funded : v.1 ≤ caller.base.bal caller.base.self) :
    ∃ configured final, attach (revertInput o input) caller child a v o input = some configured ∧
      runV2 (code a v o input) configured = .ok final 0 ∧ final.returndata = input ∧
      final.calls = caller.calls ++ [⟨a,v,input,false,input⟩] ∧
      final.base.stack = caller.base.stack ∧ final.base.store = caller.base.store :=
  funded_native _ _ _ _ _ _ _ _ _ small funded (echo_revert _ _ _ _ _ _ small)

/-- Native success cannot force an unfunded outer CALLIN to enter. -/
theorem poor_native (caller child : MachineV2) (a v o : Fin W) (input : List UInt8)
    (small : input.length < W) (poor : caller.base.bal caller.base.self < v.1) :
    ∃ configured final, attach (echo o input) caller child a v o input = some configured ∧
      runV2 (code a v o input) configured = .ok final 0 ∧
      final.returndata = [] ∧ final.calls = caller.calls ∧ final.base.stack = caller.base.stack := by
  have linked := native_call (echo o input) caller child a v o input small
  rw [echo_success caller child a v o input small] at linked
  obtain ⟨configured,final,attached,run,stack,_,_,branches⟩ := linked
  rcases branches with good | refused
  · exact False.elim (Nat.not_le_of_lt poor good.1)
  · exact ⟨configured,final,attached,run,refused.2.1,refused.2.2,stack⟩

end Solidity.H62.ReadonlyCalls.ExecutionCall
