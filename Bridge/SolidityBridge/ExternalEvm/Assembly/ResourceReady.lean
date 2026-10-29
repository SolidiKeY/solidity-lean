import SolidityBridge.ExternalEvm.Assembly.SafeStructured
import SolidityBridge.ExternalEvm.Assembly.Termination

namespace Solidity.Evm.External.Assembly
open EvmYul EvmYul.EVM

/-- All original driver resource checks, with the destination array containing
only the current operand. Scanner safety separately justifies the real array.
This is an adapter for the same gate, not a source gas semantics. -/
def resourceGate (s : EVM.State) (op : Operation .EVM) :=
  driverGate s.stack[0]?.toList.toArray s op

private theorem gate_irrel (a b : Array UInt256) (s : EVM.State) (op : Operation .EVM)
    (jump : op ≠ .JUMP) (jumpi : op ≠ .JUMPI) : driverGate a s op = driverGate b s op := by
  unfold driverGate
  dsimp only
  simp only [jump, jumpi, false_and, if_false]

private theorem gate_same_invalid (a b : Array UInt256) (s : EVM.State) (op : Operation .EVM)
    (same : X.notIn s.stack[0]? a = X.notIn s.stack[0]? b) : driverGate a s op = driverGate b s op := by
  unfold driverGate
  dsimp only
  simp only [bind, Except.bind]
  rw [same]

/-- The certified target membership discharges the actual driver's destination
checks. Every other original gate remains identical. -/
theorem resourceGate_eq (destinations : List UInt256) (s : EVM.State) (packet : Packet)
    (pure : PurePacket packet) (safe : JumpSafe destinations packet s) :
    resourceGate s packet.1 = driverGate destinations.toArray s packet.1 := by
  cases pure with
  | dest => exact gate_irrel _ _ s .JUMPDEST (by decide) (by decide)
  | push w => exact gate_irrel _ _ s (.Push .PUSH32) (by decide) (by decide)
  | pop => exact gate_irrel _ _ s .POP (by decide) (by decide)
  | zero => exact gate_irrel _ _ s .ISZERO (by decide) (by decide)
  | jump | jumpi =>
    change X.notIn s.stack[0]? destinations.toArray = false at safe
    have own : X.notIn s.stack[0]? s.stack[0]?.toList.toArray = false := by
      cases hh : s.stack[0]? with
      | none => simp only [hh, X.notIn, X.belongs, Bool.not_false, Bool.true_eq_false] at safe
      | some target =>
        exact notIn_of_member (destinations := [target]) (List.mem_cons_self)
    exact gate_same_invalid _ _ s _ (own.trans safe.symm)

/-- Resource-only readiness: the real destination set is absent. Its validity
is supplied by the compiled safe trace rather than a checked-gate premise. -/
def ResourceReady : Nat → Nat → EVM.State → Prop
  | 0, _, _ => True
  | _ + 1, 0, _ => False
  | _ + 1, 1, _ => False
  | n + 1, fuel + 2, s => match EVM.decode s.executionEnv.code s.pc with
    | none => False
    | some packet => PurePacket packet ∧ match resourceGate s packet.1 with
      | .error _ => False
      | .ok (charged, cost) => match EVM.step (fuel + 1) cost (some packet) charged with
        | .error _ => True
        | .ok next => ResourceReady n (fuel + 1) next

def checkResources : (n fuel : Nat) → (s : EVM.State) → Option (PLift (ResourceReady n fuel s))
  | 0, _, _ => some ⟨trivial⟩
  | _ + 1, 0, _ => none
  | _ + 1, 1, _ => none
  | n + 1, fuel + 2, s => match hd : EVM.decode s.executionEnv.code s.pc with
    | none => none
    | some packet => do
      let pure ← checkPure packet
      match hg : resourceGate s packet.1 with
      | .error _ => none
      | .ok (charged, cost) => match hs : EVM.step (fuel + 1) cost (some packet) charged with
        | .error _ => return ⟨by simp only [ResourceReady, hd, hg, hs]; exact ⟨pure.down, trivial⟩⟩
        | .ok next => do
          let tail ← checkResources n (fuel + 1) next
          return ⟨by simp only [ResourceReady, hd, hg, hs]; exact ⟨pure.down, tail.down⟩⟩

private theorem decoded_same {s actual : EVM.State} (same : observeState actual = observeState s)
    {packet : Packet} (fetch : Fetches s packet) :
    EVM.decode actual.executionEnv.code actual.pc = some packet := by
  have hc : actual.executionEnv.code = s.executionEnv.code :=
    congrArg (fun v : StateView => v.world.executionEnv.code) same
  have hp : actual.pc = s.pc := congrArg StateView.pc same
  rw [hc, hp]
  unfold Fetches EVM.fetchInstr at fetch
  cases hd : EVM.decode s.executionEnv.code s.pc with
  | none => rw [hd] at fetch; cases fetch
  | some actual => rw [hd] at fetch; cases Except.ok.inj fetch; rfl

/-- Actual driver readiness follows from resource-only checks and compiled
scanner-safe microsteps. No real-array destination gate is assumed. -/
theorem SafeTrace.driver_ready {destinations : List UInt256} {n : Nat} {s t : EVM.State}
    (trace : SafeTrace destinations n s t) : ∀ fuel actual,
      observeState actual = observeState s → ResourceReady n fuel actual →
      DriverReady n fuel destinations.toArray actual := by
  induction trace with
  | nil => intro fuel actual same ready; trivial
  | cons packet fetch pure safe head tail ih =>
    rename_i count start next out
    intro fuel actual same ready
    cases fuel with
    | zero => exact False.elim ready
    | succ fuel =>
      cases fuel with
      | zero => exact False.elim ready
      | succ fuel =>
        have hd := decoded_same same fetch
        have safeActual : JumpSafe destinations packet actual := by
          have hs : actual.stack = start.stack := congrArg StateView.stack same
          unfold JumpSafe
          rw [hs]
          exact safe
        have hgates := resourceGate_eq destinations actual packet pure safeActual
        simp only [ResourceReady, hd, hgates] at ready
        simp only [DriverReady, hd]
        cases hg : driverGate destinations.toArray actual packet.1 with
        | error e =>
          simp only [hg] at ready
          exact False.elim ready.2
        | ok pair =>
          obtain ⟨charged, cost⟩ := pair
          simp only [hg] at ready ⊢
          cases step : EVM.step (fuel + 1) cost (some packet) charged with
          | error e => exact ⟨pure, trivial⟩
          | ok actualNext =>
            have zero : EVM.step 1 0 (some packet) start = .ok next := by
              rw [← fetched_step 0 _ _ fetch]
              exact head
            have observed := pure_step_congr fuel cost charged start packet pure
              ((driverGate_observe destinations.toArray actual charged packet.1 cost hg).trans same)
            rw [step, zero] at observed
            have hn : observeState actualNext = observeState next := Except.ok.inj observed
            exact ⟨pure, ih (fuel + 1) actualNext hn (by simpa only [step] using ready.2)⟩

/-- Common scanner-safe prefix/terminal path used by both the general
compiler theorem and inhabited executable controls. -/
theorem ExitLayout.resource_success_of_fetched {code : List Instr} {program : LinkedProgram code}
    (layout : ExitLayout program) (n fuel : Nat) (m' : Machine)
    (s t actual : EVM.State) (trace : SafeTrace program.scanner.destinations n s t)
    (boundary : Boundary program.checked.image program.frame code.length m' t)
    (same : observeState actual = observeState s) (resources : ResourceReady n (n + fuel + 3) actual) :
    ∃ terminal, driverSteps n (n + fuel + 3) program.validJumps actual = .ok terminal ∧
      Boundary program.checked.image program.frame code.length m' terminal ∧
      ∀ _gates : TerminalGates program.validJumps terminal,
        ∃ out, X (n + fuel + 3) program.validJumps actual = .ok (.success out .empty) ∧
          SuccessBoundary layout m' out :=
  layout.success_of_fetched n fuel m' s t actual trace.forget boundary same
    (trace.driver_ready (n + fuel + 3) actual same resources)

/-- End-to-end scanner-consuming compiler refinement. Only resource checks
are premises; the real destination safety is derived from ScannedCode. -/
theorem LinkedProgram.resource_success_simulation {code : List Instr} (program : LinkedProgram code)
    (layout : ExitLayout program) (m m' : Machine) (s : EVM.State)
    (entry : Boundary program.checked.image program.frame 0 m s) (source : run code m = .ok m' 0) :
    ∃ n, ∀ fuel actual, observeState actual = observeState s → ResourceReady n (n + fuel + 3) actual →
      ∃ terminal, driverSteps n (n + fuel + 3) program.validJumps actual = .ok terminal ∧
        Boundary program.checked.image program.frame code.length m' terminal ∧
        ∀ _gates : TerminalGates program.validJumps terminal,
          ∃ out, X (n + fuel + 3) program.validJumps actual = .ok (.success out .empty) ∧
            SuccessBoundary layout m' out := by
  obtain ⟨n, t, safe, related⟩ := program.safe_simulation m m' s entry source
  refine ⟨n, ?_⟩
  intro fuel actual same resources
  exact layout.resource_success_of_fetched n fuel m' s t actual safe related same resources

end Solidity.Evm.External.Assembly

/-- info: 'Solidity.Evm.External.Assembly.LinkedProgram.resource_success_simulation' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in #print axioms Solidity.Evm.External.Assembly.LinkedProgram.resource_success_simulation
