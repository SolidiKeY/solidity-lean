import Solidity.Evm.MemoryRecursiveHorizon
import Solidity.Evm.MemoryExprExamples

namespace Solidity.Evm.Memory.Recursive.Controls
open CompileExamples ExprExamples
private abbrev D := StorageCase.D
private def condition : Val D Γ .bool :=
  .binop .lt rfl rfl (.simple (.local .here)) (.simple (.lit 1 rfl))
private def effects : Prog D Γ Γ :=
  .cons (.block StorageCase.sequence) (.cons (.assignLocal .here (.simple (.lit 1 rfl))) .nil)
private def leaf : CompiledProg 0 (Frag.init Γ) effects :=
  (compileProg 0 effects (Frag.init Γ)).get (by decide +kernel)
private theorem leaf_frag : leaf.frag=Frag.init Γ := by decide +kernel
attribute [irreducible] leaf
private def cond := (Memory.compileVal 0 (Frag.init Γ) condition).get (by decide +kernel)

attribute [irreducible] cond

/-- Arbitrary finite nesting of the actual loop constructor, without a depth cap. -/
def nested : Nat → Prog D Γ Γ
  | 0=>effects
  | n+1=>.cons (.loop .auto condition (nested n)) .nil

def nestedCode : Nat → List Instr
  | 0=>leaf.code
  | n+1=>[.loop cond.code (nestedCode n)]

/-- Constructed certificates, not supplied soundness or readback premises. -/
def nestedCert : (n : Nat) → ProgCert 0 (Frag.init Γ) (Frag.init Γ) (nested n) (nestedCode n)
  | 0=>by
    have cert := leaf.cert
    rw [leaf_frag] at cert
    exact cert
  | n+1=>.cons (.loop .auto cond.cert (nestedCert n) (by decide +kernel)) (.nil _)

private theorem nonallocating (n : Nat) : (nestedCert n).allocates=false := by
  induction n with
  | zero=>unfold nestedCert leaf;decide +kernel
  | succ n ih=>simpa only [nestedCert,ProgCert.allocates,StmtCert.allocates,Bool.or_false] using ih
private theorem capacity (n : Nat) : 0+(nestedCert n).need≤6 := by
  induction n with
  | zero=>unfold nestedCert leaf;decide +kernel
  | succ n ih=>
    change 0+max (max Γ.length (nestedCert n).need) Γ.length≤6
    change 0+(nestedCert n).need≤6 at ih
    have : Γ.length≤6 := by decide
    omega

/-- Every nesting depth transports the complete actual execution result. -/
theorem every_depth (n : Nat) :
    LoopScopes.Result 1 0 6 (Frag.init Γ) StorageCase.state base machine
      (fun out amount=>Cost (nestedCert n) StorageCase.state out amount)
      ((nested n).run StorageCase.state) (run (nestedCode n) machine) :=
  (nestedCert n).correct StorageCase.state base machine StorageCase.fixture (capacity n)
    (room_nonallocating (nestedCert n) (nonallocating n) 6 StorageCase.state base machine)

private theorem stable : (Frag.init Γ).restrict Γ=Frag.init Γ := by decide +kernel

/-- Every body depth and every OUTER horizon, with only reached finite room. -/
theorem finite_every_depth (depth turns : Nat) :
    RecursiveLift.CountedHorizon (loopKit cond.cert (nestedCert depth) stable) 1 6
      StorageCase.state base machine turns
      (TLoop.iterN (horizonBody (nested depth)) (fun o=>condition.evalT o.st) turns
        ⟨StorageCase.state,List.prefix_refl _⟩)
      (loopIterN (fun m=>exec cond.code 0 m) (fun m=>exec (nestedCode depth) 0 m) turns machine) :=
  (nestedCert depth).loop_finite_horizon cond.cert stable turns StorageCase.fixture (capacity depth)
    ((loop_room_nonallocating (nestedCert depth) cond.cert stable (nonallocating depth)
      6 StorageCase.state base machine).finite turns)

/-- Zero horizon does not require any future allocation room. -/
theorem zero_without_future_room (depth : Nat) :
    RecursiveLift.CountedHorizon (loopKit cond.cert (nestedCert depth) stable) 1 6
      StorageCase.state base machine 0
      (TLoop.iterN (horizonBody (nested depth)) (fun o=>condition.evalT o.st) 0
        ⟨StorageCase.state,List.prefix_refl _⟩)
      (loopIterN (fun m=>exec cond.code 0 m) (fun m=>exec (nestedCode depth) 0 m) 0 machine) :=
  (nestedCert depth).loop_finite_horizon cond.cert stable 0 StorageCase.fixture (capacity depth)
    (RecursiveLift.finiteRoom_zero _ StorageCase.state base machine)

private def compiledFive : CompiledProg 0 (Frag.init Γ) (nested 5) :=
  (compileProg 0 (nested 5) (Frag.init Γ)).get (by decide +kernel)
attribute [irreducible] compiledFive

theorem actual_compiler_five : compiledFive.frag=Frag.init Γ := by unfold compiledFive;decide +kernel

theorem old_refuses : (LoopScopes.compileProg 0 (nested 5) (Frag.init Γ)).isNone=true := by decide +kernel

private def sourceObserve (r : TRes (Solidity.Out D CompileExamples.H Γ)) : Option (List Int) := do
  let o←r.toOption
  let total←(Val.read (.root "total" rfl) : Val D Γ .uint).evalT o.st |>.toOption
  let first←(Val.readMem (.index .dyn (.var (.there .here) rfl) (.simple (.lit 0 rfl))) : Val D Γ .uint).evalT o.st |>.toOption
  pure [(TEnv.get (.here : Idx Γ (.val .uint)) o.st.env).val,total.val,first.val]
private def targetObserve (r : Out) : Option (List Nat) := do
  match r with
  | .ok m _=>
    let count←match m.mem 3 with | .val w=>some w.val | _=>none
    let first←match m.mem 17 with | .val w=>some w.val | _=>none
    let neighbor←match m.mem 21 with | .val w=>some w.val | _=>none
    pure [count,m.store (rootSlot D "total"),first,neighbor]
  | _=>none
/-- info: (some [1, 16, 16], some [1, 16, 16, 4], some [1, 16, 16, 4]) -/
#guard_msgs in
#eval (sourceObserve ((nested 5).run StorageCase.state),
  targetObserve (run (nestedCode 5) machine),targetObserve (run compiledFive.code machine))

private def aborted : Prog D Γ Γ := .cons (.block (nested 3)) (.cons .revert (.cons (.block effects) .nil))
private def abortedCompiled : CompiledProg 0 (Frag.init Γ) aborted :=
  (compileProg 0 aborted (Frag.init Γ)).get (by decide +kernel)
attribute [irreducible] abortedCompiled

theorem early_revert_transport :
    LoopScopes.Result 1 0 6 abortedCompiled.frag StorageCase.state base machine
      (fun out amount=>Cost abortedCompiled.cert StorageCase.state out amount)
      (aborted.run StorageCase.state) (run abortedCompiled.code machine) :=
  abortedCompiled.correct ⟨StorageCase.fixture,by unfold abortedCompiled;decide +kernel,
    room_nonallocating abortedCompiled.cert (by unfold abortedCompiled;decide +kernel) 6 StorageCase.state base machine⟩

private def reverted {α : Type} : TRes α → Bool | .error .revert=>true | _=>false
private def targetReverted : Out → Bool | .revert=>true | _=>false
/-- info: (true, true, false) -/
#guard_msgs in
#eval (reverted (aborted.run StorageCase.state),targetReverted (run abortedCompiled.code machine),
  targetObserve (run compiledFive.code machine)==some [1,15,16,4])

theorem exhausted : (compileProg 0 (.cons .assumeFalse (.nil : Prog D Γ Γ)) (Frag.init Γ)).isNone=true := by decide +kernel

end Solidity.Evm.Memory.Recursive.Controls
