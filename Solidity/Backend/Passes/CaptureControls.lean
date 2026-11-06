import Solidity.Backend.Passes.CaptureTransport
import Solidity.Backend.Passes.CaptureAliases
import Solidity.Backend.Passes.ReachabilityControls

/-! Fresh-state-reachable primitive/reference captures and effect ordering.
All programs/statements are existing intrinsic objects compiled by the
published entry. General Source tuples/function references remain open. -/
namespace Solidity.Backend.Passes.CaptureControls
open Solidity.Evm Solidity.Evm.Memory Solidity.Evm.Compiler
open Solidity.Backend.Passes.Controls.Fixture
private abbrev A : RefTy := .array (.prim .uint)
private abbrev first : Idx Γ (.mem A) := .there .here
private abbrev second : Idx Γ (.mem A) := .there (.there .here)
private abbrev F : Frag Γ := Frag.init Γ

def location : OpLoc C Γ .uint := .mindex .dyn (.var first rfl) (.local .here)
def capture : Stmt C Γ Γ := .assignIncDec .here .postInc rfl location rfl
def value : CompiledVal (C := C) 0 F
    (bumpResultValue .postInc rfl (.readMem (.index .dyn (.var first rfl) (.simple (.local .here))))) :=
  (compileVal 0 F _).get (by decide +kernel)
def step : CompiledStmt 0 F (.incDec .postInc rfl location) :=
  (compileStmt 0 F _).get (by decide +kernel)
def captureCode : List Instr := value.code ++ step.code ++ [.mstore 3]
def captureCert : StmtFrag 0 F F capture captureCode :=
  .captureMemory F .here .postInc rfl .dyn (.var first rfl) (.local .here) rfl
    value.code step.code value.cert step.cert
def compiledCapture : CompiledStmt 0 F capture :=
  (compileStmt 0 F _).get (by decide +kernel)
theorem actual_capture_code : captureCode = compiledCapture.code := rfl

private def u (n : Int) (h : PrimTy.uint.inRange n = true) : PrimTy.uint.Denote := ⟨n, h⟩
def afterCapture : State C Γ :=
  { σ with
    heap :=
      (⟨[u 8 rfl, u 9 rfl], by decide⟩, ⟨[u 4 rfl], by decide⟩, ()),
    env := (u 7 rfl, some CompileExamples.r0, some CompileExamples.r0,
      some CompileExamples.r1, ()) }

theorem source_capture : capture.run σ = .ok ⟨afterCapture, List.prefix_refl _⟩ := by
  with_unfolding_all rfl

def aliasStmt : Stmt C Γ (.mem A :: Γ) :=
  .declMem A (.user "saved") (some (.alias (.var first rfl))) rfl rfl
def afterAlias : State C (.mem A :: Γ) :=
  afterCapture.push (t := .mem A) (some CompileExamples.r0)
private def freshRead : Val C (.mem A :: Γ) .uint :=
  .readMem (.index .dyn (.var .here rfl) (.simple (.lit 0 rfl)))
def valueStmt : Stmt C (.mem A :: Γ) (.val .uint :: .mem A :: Γ) :=
  .declLocal .uint (.user "after") (some freshRead)
def afterValue : State C (.val .uint :: .mem A :: Γ) :=
  afterAlias.push (t := .val .uint) (u 8 rfl)

private theorem alias_source : aliasStmt.run afterCapture =
    .ok ⟨afterAlias, List.prefix_refl _⟩ := by with_unfolding_all rfl
private theorem value_source : valueStmt.run afterAlias =
    .ok ⟨afterValue, List.prefix_refl _⟩ := by with_unfolding_all rfl

def mixed : Prog C Γ (.val .uint :: .mem A :: Γ) :=
  .cons capture (.cons aliasStmt (.cons valueStmt .nil))
def checked : Compilation 0 F mixed :=
  (Compiler.compile 0 F mixed).get (by decide +kernel)

theorem source_success : mixed.run σ = .ok ⟨afterValue, List.prefix_refl _⟩ := by
  rw [mixed, Prog.run_cons_ok source_capture, Prog.run_cons_ok alias_source,
    Prog.run_cons_ok value_source, Prog.run_nil]
  rfl

theorem fresh_reaches :
    (ReachabilityControls.populatedBuilder.join mixed).run (State.init C) =
      .ok ⟨afterValue, ⟨σ.H, rfl⟩⟩ := by
  rw [DeferredSource.join_run]
  simp only [TRun.seq, ReachabilityControls.fresh_state_reaches_fixture, source_success, Except.map]

theorem input : checked.Input 1 6 base σ machine :=
  (checked.memory_input (by decide +kernel) _ _ _ _ _).mpr
    ⟨LinkedControls.frame_six, by decide +kernel, .inl (by decide +kernel)⟩

/-- The generic capture adapter is inhabited with two live aliases and an
index overwritten only after the bump; its emitted code is pinned above. -/
theorem generic_capture (tail : List Word) :
    GrowingResult 1 0 6 0 F σ base {machine with stack := tail}
      (capture.run σ) (run captureCode {machine with stack := tail}) :=
  capture_memory_frame .here .postInc rfl .dyn (.var first rfl) (.local .here) rfl
    value.code step.code value.cert step.cert fixture_repr (by decide)
    LinkedControls.frame_six.heap.above LinkedControls.frame_six.structs.above tail

/-- A real new reference local follows the effect using the generic
context/frame theorem, not just a separately observed tuple of words. -/
theorem generic_alias_context (tail : List Word) :
    GrowingResult 1 0 6 0 (F.push (.mem A) .ok) σ base {machine with stack := tail}
      ((Prog.cons capture (.cons aliasStmt .nil)).run σ)
      (run (captureCode ++ (declareAliasCode 0 first ++ [])) {machine with stack := tail}) :=
  capture_then_alias_frame .here .postInc rfl location rfl captureCode captureCert
    (.user "saved") first rfl fixture_repr (by decide)
    LinkedControls.frame_six.heap.above LinkedControls.frame_six.structs.above tail

theorem source_aliases :
    HEq (TEnv.get first afterCapture.env) (TEnv.get first σ.env) ∧
    HEq (TEnv.get second afterCapture.env) (TEnv.get second σ.env) := by
  exact ⟨capture_memory_alias .here .postInc .dyn (.var first rfl) (.local .here)
    source_capture first,
    capture_memory_alias .here .postInc .dyn (.var first rfl) (.local .here)
    source_capture second⟩

/-- One complete non-stack output and the full mixed-context Rep at every tail. -/
theorem shared_output :
    ∃ canonical : Machine, canonical.stack = [] ∧
      ∀ tail, run checked.code {machine with stack := tail} =
          .ok {canonical with stack := tail} 0 ∧
        checked.Rep 1 6 base σ {machine with stack := tail}
          afterValue {canonical with stack := tail} := by
  obtain ⟨m, _, hstack, hs⟩ := compilation_success_shared checked input rfl source_success
  exact ⟨m, hstack, hs⟩

private def targetCell (n : Nat) : Evm.Out → Option Nat
  | .ok m _ => match m.mem n with | .val w => some w.val | _ => none
  | _ => none

/-- Capture7, then mutate8, then fresh alias16 and fresh observed value8.
Both old aliases16 and independent array20 survive. -/
theorem ordered_values :
    ([3, 4, 5, 17, 1, 2, 0, 21].mapM (fun n => targetCell n (run checked.code machine))) =
      some [7, 16, 8, 8, 16, 16, 20, 4] := by decide +kernel

private def readZero : Val C Γ .uint :=
  .readMem (.index .dyn (.var first rfl) (.simple (.lit 0 rfl)))
def readValue : CompiledVal (C := C) 0 F readZero :=
  (compileVal 0 F readZero).get (by decide +kernel)

/-- The generic fresh primitive-context adapter is inhabited as well:
this expression reads8 after the captured old value7 has been saved. -/
theorem generic_value_context (tail : List Word) :
    GrowingResult 1 0 6 0 (F.push (.val .uint) .ok) σ base {machine with stack := tail}
      ((Prog.cons capture (.cons (.declLocal .uint (.user "after") (some readZero)) .nil)).run σ)
      (run (captureCode ++ ((readValue.code ++ [.mstore 4]) ++ []))
        {machine with stack := tail}) :=
  capture_then_value_frame .here .postInc rfl location rfl captureCode captureCert
    (.user "after") readZero readValue.code readValue.cert fixture_repr (by decide)
    LinkedControls.frame_six.heap.above LinkedControls.frame_six.structs.above tail

theorem after_effect_read : readZero.evalT afterCapture = .ok (u 8 rfl) := by
  with_unfolding_all rfl

private def wrongRecapture : Prog C Γ Γ :=
  .cons (.incDec .postInc rfl location) (.cons (.assignLocal .here readZero) .nil)
private def wrongOrder : Prog C Γ Γ :=
  .cons (.assignLocal .here readZero) (.cons (.incDec .postInc rfl location) .nil)
private def recaptured := (Compiler.compile 0 F wrongRecapture).get (by decide +kernel)
private def reordered := (Compiler.compile 0 F wrongOrder).get (by decide +kernel)

theorem wrong_recapture :
    targetCell 3 (run recaptured.code machine) = some 8 ∧
    targetCell 3 (run checked.code machine) = some 7 := by
  constructor <;> decide +kernel

/-- Writing7 to the index before the bump reaches an out-of-bounds access. -/
theorem wrong_order :
    wrongOrder.run σ = .error .revert ∧ run reordered.code machine = .revert := by
  constructor
  · with_unfolding_all rfl
  · exact Evm.Out.eq_revert (by decide +kernel)

def failing : Prog C Γ Γ :=
  .cons capture (.cons (.assignLocal .here ExpressionControls.badRead) .nil)
def failed := (Compiler.compile 0 F failing).get (by decide +kernel)

private theorem bad_after : (Stmt.assignLocal .here ExpressionControls.badRead).run afterCapture =
    .error .revert := by with_unfolding_all rfl

theorem source_failure_after_effect :
    capture.run σ = .ok ⟨afterCapture, List.prefix_refl _⟩ ∧
      failing.run σ = .error .revert := by
  refine ⟨source_capture, ?_⟩
  rw [failing, Prog.run_cons_ok source_capture, Prog.run_cons_error bad_after]
  rfl

theorem target_effect_before_failure :
    targetCell 17 (run compiledCapture.code machine) = some 8 ∧
    targetCell 3 (run compiledCapture.code machine) = some 7 := by
  constructor <;> decide +kernel

theorem failure_all_tails (tail : List Word) :
    run failed.code {machine with stack := tail} = .revert := by
  have hi : failed.Input 1 6 base σ machine :=
    (failed.memory_input (by decide +kernel) _ _ _ _ _).mpr
      ⟨LinkedControls.frame_six, by decide +kernel, .inl (by decide +kernel)⟩
  exact (compilation_revert_iff failed (compilation_input_stack failed hi tail) rfl).mpr
    (.inl source_failure_after_effect.2)

theorem stack_corruption :
    ∃ canonical : Machine,
      run checked.code {machine with stack := [w[41], w[19]]} =
        .ok {canonical with stack := [w[41], w[19]]} 0 ∧
      run (checked.code ++ [.pop]) {machine with stack := [w[41], w[19]]} =
        .ok {canonical with stack := [w[19]]} 0 := by
  obtain ⟨m, _, hs⟩ := shared_output
  refine ⟨m, (hs _).1, ?_⟩
  rw [run_append_ok (hs _).1]
  rfl

end Solidity.Backend.Passes.CaptureControls
