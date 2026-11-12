import Solidity.Yul.Composition.CatchFunctionPhysical

/-! Consumer of actual EM.attempt, with explicit old callee locals and existing
raw caller companion. No raw→clean conversion, rollback or Source dispatcher is
invented. Panic remains revert bytes; timeout/stuck are propagated unchanged. -/
namespace Solidity.Yul.Composition.AttemptPhysical
open Solidity.Yul.Views Solidity.Yul.Views.Controls LocalPhysicalControls

/-- Exact producer operation, for arbitrary computations and typed states. -/
theorem attempt_run {E Γ α} (m : Source.EM E Γ α) (state : Source.EMState E Γ) :
    (Source.EM.attempt m).run state = (.ok (m.run state).1,(m.run state).2) := rfl

def companion {E Γ Δ α} (m : Source.EM E Δ α) (callee : Source.Locals E.layout Δ)
    (raw : LocalState E Γ) :=
  let actual := (Source.EM.attempt m).run (callee,raw.2)
  (actual,(raw.1,actual.2.2))

theorem companion_actual {E Γ Δ α} (m : Source.EM E Δ α) (callee : Source.Locals E.layout Δ)
    (raw : LocalState E Γ) :
    companion m callee raw = ((.ok (m.run (callee,raw.2)).1,(m.run (callee,raw.2)).2),
      (raw.1,(m.run (callee,raw.2)).2.2)) := rfl

theorem caller_raw_retained {E Γ Δ α} (m : Source.EM E Δ α) (callee : Source.Locals E.layout Δ)
    (raw : LocalState E Γ) : (companion m callee raw).2.1 = raw.1 := rfl

theorem full_poststate {E Γ Δ α} (m : Source.EM E Δ α) (callee : Source.Locals E.layout Δ)
    (raw : LocalState E Γ) : (companion m callee raw).2.2 = (m.run (callee,raw.2)).2.2 := rfl

/-- Consumer routing only, not Source.Syntax.tryStmt semantics. No halt lost. -/
def classify {α} : Except Source.Halt α → Except Source.Halt (Except (List UInt8) α)
  | .ok value => .ok (.ok value)
  | .error (.revert data) => .ok (.error data)
  | .error halt => .error halt

theorem classify_success {α} (value : α) : classify (.ok value) = .ok (.ok value) := rfl
theorem classify_revert {α} (data : List UInt8) : classify (α:=α) (.error (.revert data)) = .ok (.error data) := rfl
theorem classify_timeout {α} : classify (α:=α) (.error .timeout) = .error .timeout := rfl
theorem classify_stuck {α} (why : String) : classify (α:=α) (.error (.stuck why)) = .error (.stuck why) := rfl
theorem classify_panic {α} (code : Source.PanicCode) : classify (α:=α) (Source.panic code) =
    .ok (.error (Source.panicData code)) := rfl

/-- Only length is bound through an existing word literal; full data is retained
separately. No catch-memory allocation/pointer or general byte binding asserted. -/
def continuationCode (data : List UInt8) : Stmt [] X ⟨false,false⟩ 0 :=
  .seq (assign _ small (FunctionPhysical.binary .add (.external small.readRef) (.literal (word data.length))))
    (CatchFunctionPhysical.code true false)
def continuationPolicy (data : List UInt8) : Policy.StmtP .A (continuationCode data) :=
  (Policy.stmt_iff .A _).mp rfl

def route {α} (fuel : Nat) (raw : LocalState originEnv ctx.tys)
    (result : Except Source.Halt α) : Except Source.Halt (α ⊕ (List UInt8 × Option (LocalBlockOutcome ctx ⟨false,false⟩))) :=
  match classify result with
  | .ok (.ok value) => .ok (.inl value)
  | .ok (.error data) => .ok (.inr (data,runLocalBlock ctx (continuationCode data) (continuationPolicy data) fuel raw))
  | .error halt => .error halt

def consume {Δ α} (m : Source.EM originEnv Δ α) (callee : Source.Locals originEnv.layout Δ)
    (raw : LocalState originEnv ctx.tys) (fuel : Nat) :=
  let actual := companion m callee raw
  (actual,actual.1.1.bind (route fuel actual.2))

theorem consume_actual {Δ α} (m : Source.EM originEnv Δ α) (callee : Source.Locals originEnv.layout Δ)
    (raw : LocalState originEnv ctx.tys) (fuel : Nat) :
    (consume m callee raw fuel).2 = route fuel (raw.1,(m.run (callee,raw.2)).2.2) (m.run (callee,raw.2)).1 := rfl

theorem route_timeout {α} (fuel : Nat) (raw : LocalState originEnv ctx.tys) :
    route (α:=α) fuel raw (.error .timeout) = .error .timeout := rfl
theorem route_stuck {α} (fuel : Nat) (raw : LocalState originEnv ctx.tys) (why : String) :
    route (α:=α) fuel raw (.error (.stuck why)) = .error (.stuck why) := rfl

theorem continuation_rebase (data : List UInt8) (fuel : Nat) (values : LocalValues originEnv ctx.tys)
    (first last : Source.St originEnv) :
    runLocalBlock ctx (continuationCode data) (continuationPolicy data) fuel (values,last) =
      (runLocalBlock ctx (continuationCode data) (continuationPolicy data) fuel (values,first)).map
        (fun result => ⟨(result.state.1,last),result.flow⟩) :=
  local_rebase ctx (continuationCode data) (continuationPolicy data) fuel values first last

/-- Actual EM modification before success/any halt. attempt must RETAIN log99. -/
def action (result : Except Source.Halt (List UInt8)) : Source.EM originEnv [] (List UInt8) := do
  Source.EM.modSt fun s => {s with logs := (account,[0x99])::s.logs}
  Source.EM.lift result

def input := CatchFunctionPhysical.completed.state

def run (result : Except Source.Halt (List UInt8)) (fuel : Nat) := consume (action result) .nil input fuel

theorem captured_outcome (result : Except Source.Halt (List UInt8)) :
    (run result 32).1.1.1 = .ok result := by cases result <;> rfl

theorem captured_post (result : Except Source.Halt (List UInt8)) :
    (run result 32).1.2 = (input.1,{input.2 with logs := (account,[0x99])::input.2.logs}) := by cases result <;> rfl

def continued (data : List UInt8) (fuel : Nat) := runLocalBlock ctx (continuationCode data) (continuationPolicy data) fuel
  (companion (action (.error (.revert data))) .nil input).2

theorem binds_actual_revert (data : List UInt8) (fuel : Nat) :
    (run (.error (.revert data)) fuel).2 = .ok (.inr (data,continued data fuel)) := rfl

theorem continues_nonempty : (continued [0xde,0xad] 32).isSome := by decide +kernel
def completed : LocalBlockOutcome ctx ⟨false,false⟩ := (continued [0xde,0xad] 32).get continues_nonempty

theorem words_nonempty : snapshot completed.state =
    [2,2^256-1,2309737967,2307,22136,2^256-1,171*2^248] := by decide +kernel

theorem words_empty : (continued [] 32).map (fun result=>snapshot result.state) =
    some [2,2^256-1,2309737967,2305,22136,2^256-1,171*2^248] := by decide +kernel

theorem words_panic : (continued (Source.panicData .assert) 32).map (fun result=>snapshot result.state) =
    some [2,2^256-1,2309737967,2341,22136,2^256-1,171*2^248] := by decide +kernel

theorem no_implicit_rollback : completed.state.2.logs = [(account,[0x99]),(account,[0x55])] := by
  have kept : completed.state.2 = (companion (action (.error (.revert [0xde,0xad]))) .nil input).2.2 :=
    runLocalBlock_world ctx (continuationCode [0xde,0xad]) (continuationPolicy [0xde,0xad]) 32 _ (Option.some_get continues_nonempty).symm
  rw [kept]
  change (account,[0x99])::CatchFunctionPhysical.completed.state.2.logs = _
  rw [CatchFunctionPhysical.caller_source_retained]
  rfl

theorem nonword_retained : completed.state.1.get memoryRef.index = (LocalValues.ofClean locals).get memoryRef.index := by
  have kept : completed.state.1.get memoryRef.index = input.1.get memoryRef.index :=
    runLocalBlock_nonword ctx (continuationCode [0xde,0xad]) (continuationPolicy [0xde,0xad]) 32 _ (Option.some_get continues_nonempty).symm memoryRef memoryShape rfl
  exact kept.trans CatchFunctionPhysical.nonword_retained

theorem completed_unique (fuel : Nat) (result : LocalBlockOutcome ctx ⟨false,false⟩)
    (done : continued [0xde,0xad] fuel = some result) : result=completed :=
  runLocalBlock_unique ctx (continuationCode [0xde,0xad]) (continuationPolicy [0xde,0xad]) _ done (Option.some_get continues_nonempty).symm

theorem continuation_raw (data : List UInt8) (fuel : Nat) (state : LocalState originEnv ctx.tys)
    (result : LocalBlockOutcome ctx ⟨false,false⟩)
    (done : runLocalBlock ctx (continuationCode data) (continuationPolicy data) fuel state = some result) :
    LocalState.clean? result.state = none := by
  unfold runLocalBlock at done
  cases actual : WordAdapter.run (continuationCode data) (continuationPolicy data) fuel ⟨Fin.elim0,localWordCells ctx state.1⟩ with
  | none => rw [actual] at done; cases done
  | some raw =>
      rw [actual] at done
      cases done
      change (LocalValues.clean? ctx.tys (writebackLocalWords ctx state.1 raw.state.cells)).map _ = none
      rw [RawCatchPhysical.writeback_raw]
      rfl

theorem raw_not_clean : LocalState.clean? completed.state = none :=
  continuation_raw _ 32 _ completed (Option.some_get continues_nonempty).symm

theorem no_clean_resume (action : Source.EM originEnv ctx.tys Unit) :
    LocalState.runClean action completed.state = none := LocalState.runClean_refuses action _ raw_not_clean

theorem route_success {α} (fuel : Nat) (raw : LocalState originEnv ctx.tys) (value : α) :
    route fuel raw (.ok value) = .ok (.inl value) := rfl

theorem explicit_physical_rollback : revertedCore = ⟨LocalPhysicalControls.initial.2.ex,ownedOriginResidual⟩ ∧
    revertedEncoding = boolEncodingInitial := three_journals_restore

#print axioms attempt_run
#print axioms consume_actual
#print axioms words_nonempty
#print axioms words_panic
#print axioms no_implicit_rollback
#print axioms explicit_physical_rollback
end Solidity.Yul.Composition.AttemptPhysical
