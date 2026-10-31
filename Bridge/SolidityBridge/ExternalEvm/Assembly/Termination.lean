import SolidityBridge.ExternalEvm.Assembly.Driver

namespace Solidity.Evm.External.Assembly
open EvmYul EvmYul.EVM

/-- Actual terminal placement, including the nonwrapping STOP after the
linked source-end JUMPDEST. No driver execution is assumed. -/
structure ExitLayout {code : List Instr} (program : LinkedProgram code) where
  pc : Fin W
  address : address code program.base ⟨code.length, Nat.lt_succ_self _⟩ = some pc.val
  nextFits : pc.val + 1 < W
  stop : EVM.decode program.frame.executionEnv.code (.ofNat (pc.val + 1)) = some (.STOP, none)

local instance : DecidableEq UInt256
  | ⟨a⟩, ⟨b⟩ => if h : a = b then .isTrue (congrArg UInt256.mk h)
    else .isFalse (fun he => h (congrArg UInt256.val he))

def checkExit {code : List Instr} (program : LinkedProgram code) : Option (ExitLayout program) := do
  let a ← readAddress code program.base code.length
  if hn : a.pc.val + 1 < W then
    if hd : EVM.decode program.frame.executionEnv.code (.ofNat (a.pc.val + 1)) = some (.STOP, none) then
      return ⟨a.pc, a.exactAddress, hn, hd⟩
    else none
  else none

/-- Only the two original resource gates at the terminal JD/STOP. The
states follow the actual pure JD semantics; neither X nor its result appears. -/
structure TerminalGates (valid : Array UInt256) (s : EVM.State) where
  charged : EVM.State
  cost : Nat
  dest : driverGate valid s .JUMPDEST = .ok (charged, cost)
  chargedStop : EVM.State
  costStop : Nat
  stop : driverGate valid ((chargedPrepare charged cost).incrPC) .STOP = .ok (chargedStop, costStop)

def checkTerminalGates (valid : Array UInt256) (s : EVM.State) : Option (TerminalGates valid s) := do
  match hd : driverGate valid s .JUMPDEST with
  | .error _ => none
  | .ok (charged, cost) =>
    match hs : driverGate valid ((chargedPrepare charged cost).incrPC) .STOP with
    | .error _ => none
    | .ok (chargedStop, costStop) => return ⟨charged, cost, hd, chargedStop, costStop, hs⟩

private theorem TerminalGates.observe {valid : Array UInt256} {s : EVM.State}
    (gates : TerminalGates valid s) :
    observeState gates.chargedStop = observeState {s with pc := s.pc + .ofNat 1} := by
  have hd := driverGate_observe valid s gates.charged .JUMPDEST gates.cost gates.dest
  have hs := driverGate_observe valid ((chargedPrepare gates.charged gates.cost).incrPC)
    gates.chargedStop .STOP gates.costStop gates.stop
  exact hs.trans (congrArg (fun v : StateView => {v with pc := v.pc + UInt256.ofNat 1}) hd)

/-- Source-related successful terminal observation. STOP clears returnData
and advances past the source-end JD; all other framed observations persist. -/
structure SuccessBoundary {code : List Instr} {program : LinkedProgram code}
    (layout : ExitLayout program) (m : Machine) (out : EVM.State) : Prop where
  stack : m.stack = words out.stack
  world : out.toState = program.frame.toState
  memory : out.memory = program.frame.memory
  pc : out.pc.toNat = layout.pc.val + 1
  returnData : out.returnData = .empty

theorem ExitLayout.finish {code : List Instr} {program : LinkedProgram code}
    (layout : ExitLayout program) (fuel : Nat) (m : Machine) (s : EVM.State)
    (boundary : Boundary program.checked.image program.frame code.length m s)
    (gates : TerminalGates program.validJumps s) :
    ∃ out, EVM.X (fuel + 3) program.validJumps s = .ok (.success out .empty) ∧
      SuccessBoundary layout m out := by
  have hp : s.pc = .ofNat layout.pc.val := boundary_pc boundary layout.pc layout.address
  have hc : s.executionEnv.code = program.frame.executionEnv.code :=
    congrArg (fun w : EvmYul.State .EVM => w.executionEnv.code) boundary.state
  obtain ⟨n, ha, _, hd⟩ := program.destination ⟨code.length, Nat.lt_succ_self _⟩
  have hn : n.val = layout.pc.val := Option.some.inj (ha.symm.trans layout.address)
  have decoded : EVM.decode s.executionEnv.code s.pc = some (.JUMPDEST, none) := by
    rw [hc, hp, ← hn]
    exact hd
  have first := driverGate_observe program.validJumps s gates.charged .JUMPDEST gates.cost gates.dest
  have hpc : gates.charged.pc = s.pc := congrArg StateView.pc first
  have hcode : gates.charged.executionEnv.code = s.executionEnv.code :=
    congrArg (fun v : StateView => v.world.executionEnv.code) first
  have stopDecoded : (EVM.decode (chargedPrepare gates.charged gates.cost).executionEnv.code
      ((chargedPrepare gates.charged gates.cost).incrPC).pc).getD (.STOP, none) = (.STOP, none) := by
    change (EVM.decode gates.charged.executionEnv.code (gates.charged.pc + .ofNat 1)).getD _ = _
    rw [hcode, hc, hpc, hp, word_add, layout.stop]
    rfl
  refine ⟨stopAfter gates.chargedStop gates.costStop,
    X_destination_stop fuel _ s _ _ _ _ decoded gates.dest stopDecoded gates.stop, ?_⟩
  have obs := gates.observe
  have stack : gates.chargedStop.stack = s.stack := congrArg StateView.stack obs
  have world : gates.chargedStop.toState = s.toState := congrArg StateView.world obs
  have mem : gates.chargedStop.memory = s.memory := congrArg StateView.memory obs
  have pc : gates.chargedStop.pc = s.pc + .ofNat 1 := congrArg StateView.pc obs
  refine ⟨?_, world.trans boundary.state, mem.trans boundary.memory, ?_, rfl⟩
  · change m.stack = words gates.chargedStop.stack
    rw [stack]
    exact boundary.stack
  · change gates.chargedStop.pc.toNat = _
    rw [pc, hp, word_add, word_nat _ layout.nextFits]

/-- Shared proof path for compiler-derived and concretely counted prefixes.
The actual charged prefix endpoint is exposed, so executable resource/terminal
certificates can inhabit this theorem without inspecting classical witnesses. -/
theorem ExitLayout.success_of_fetched {code : List Instr} {program : LinkedProgram code}
    (layout : ExitLayout program) (n fuel : Nat) (m' : Machine)
    (s t actual : EVM.State) (trace : fetchedSteps n s = .ok t)
    (boundary : Boundary program.checked.image program.frame code.length m' t)
    (same : observeState actual = observeState s)
    (ready : DriverReady n (n + fuel + 3) program.validJumps actual) :
    ∃ terminal, driverSteps n (n + fuel + 3) program.validJumps actual = .ok terminal ∧
      Boundary program.checked.image program.frame code.length m' terminal ∧
      ∀ _gates : TerminalGates program.validJumps terminal,
        ∃ out, EVM.X (n + fuel + 3) program.validJumps actual = .ok (.success out .empty) ∧
          SuccessBoundary layout m' out := by
  obtain ⟨terminal, counted, observed, hx⟩ := fetchedSteps_driver_exact n (n + fuel + 3)
    program.validJumps s t actual trace same ready
  have related := boundary.of_observe observed
  refine ⟨terminal, counted, related, ?_⟩
  intro gates
  obtain ⟨out, finish, result⟩ := layout.finish fuel m' terminal related gates
  refine ⟨out, ?_, result⟩
  have subtract : n + fuel + 3 - n = fuel + 3 := by omega
  rw [hx, subtract, finish]

/-- General source-to-actual-X success composition, for any accepted linked
sequence/branch/nested loop and any successful source input. Resource checks
remain explicit and executable; no target outcome is a premise. -/
theorem LinkedProgram.success_simulation {code : List Instr} (program : LinkedProgram code)
    (layout : ExitLayout program) (m m' : Machine) (s : EVM.State)
    (entry : Boundary program.checked.image program.frame 0 m s)
    (source : run code m = .ok m' 0) :
    ∃ n, ∀ fuel actual, observeState actual = observeState s →
      DriverReady n (n + fuel + 3) program.validJumps actual →
      ∃ terminal, driverSteps n (n + fuel + 3) program.validJumps actual = .ok terminal ∧
        Boundary program.checked.image program.frame code.length m' terminal ∧
        ∀ _gates : TerminalGates program.validJumps terminal,
          ∃ out, EVM.X (n + fuel + 3) program.validJumps actual = .ok (.success out .empty) ∧
            SuccessBoundary layout m' out := by
  obtain ⟨n, t, trace, boundary, _⟩ := program.simulation m m' s entry source
  refine ⟨n, ?_⟩
  intro fuel actual same ready
  exact layout.success_of_fetched n fuel m' s t actual trace boundary same ready

end Solidity.Evm.External.Assembly
