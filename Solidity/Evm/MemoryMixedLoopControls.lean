import Solidity.Evm.MemoryMixedLoopCompile
import Solidity.Evm.MemoryMixedLoopFinite
import Solidity.Evm.MemoryExprExamples

namespace Solidity.Evm.Memory.MixedLoops.Controls
open CompileExamples ExprExamples
private abbrev D := StorageCase.D
private def condition : Val D Γ .bool :=
  .binop .lt rfl rfl (.simple (.local .here)) (.simple (.lit 1 rfl))
private def reset : Stmt D Γ Γ := .assignLocal .here (.simple (.lit 1 rfl))
private def effects : Prog D Γ Γ :=
  .cons (.block StorageCase.sequence) (.cons reset .nil)
private def inner : Prog D Γ Γ := .cons (.loop .auto condition effects) .nil
private def body : Prog D Γ Γ :=
  .cons (.block (.cons (.ite (.simple (.bool true)) inner (.cons .revert .nil)) .nil)) .nil
private def compiled : Compiled 0 (Frag.init Γ) condition body :=
  (compile 0 (Frag.init Γ) condition body).get (by decide +kernel)
attribute [irreducible] compiled
private theorem cap : 0+compiled.cert.bodyCert.need≤6 := by unfold compiled;decide +kernel
private theorem room : Room compiled.cert 6 StorageCase.state base machine :=
  room_nonallocating compiled.cert (by unfold compiled;decide +kernel) StorageCase.state base machine

/-- The old finite-body route cannot compile this actual outer/nested body. -/
theorem old_refuses : (Loops.compileProg 0 (Frag.init Γ)
    (.cons (.loop .auto condition body) .nil)).isNone=true := by decide +kernel

theorem every_horizon (n : Nat) : Horizon compiled.cert 1 6 StorageCase.state base machine
    (TLoop.iterN (horizonBody body) (fun o=>condition.evalT o.st) n ⟨StorageCase.state,List.prefix_refl _⟩)
    (loopIterN (fun m=>exec compiled.cond 0 m) (fun m=>exec compiled.code 0 m) n machine) :=
  compiled.cert.correct_horizon StorageCase.fixture cap room n

theorem full_execution : LoopScopes.Result 1 0 6 (Frag.init Γ) StorageCase.state base machine
    (fun o cost=>Prefix compiled.cert StorageCase.state o cost)
    ((Stmt.loop .auto condition body).run StorageCase.state) (run [.loop compiled.cond compiled.code] machine) :=
  compiled.cert.correct .auto StorageCase.fixture cap room

private def sourceObserve (out : TRes (Solidity.Out D CompileExamples.H Γ)) : Option (List Int) := do
  let o ← out.toOption
  let total ← (Val.read (.root "total" rfl) : Val D Γ .uint).evalT o.st |>.toOption
  let first ← (Val.readMem (.index .dyn (.var (.there .here) rfl) (.simple (.lit 0 rfl))) : Val D Γ .uint).evalT o.st |>.toOption
  pure [(TEnv.get (.here : Idx Γ (.val .uint)) o.st.env).val,total.val,first.val]
private def targetObserve (out : Out) : Option (List Nat) := do
  match out with
  | .ok next _ =>
    let count ← match next.mem 3 with | .val w=>some w.val | _=>none
    let first ← match next.mem 17 with | .val w=>some w.val | _=>none
    let neighbor ← match next.mem 21 with | .val w=>some w.val | _=>none
    pure [count,next.store (rootSlot D "total"),first,neighbor]
  | _ => none

/-- info: (some [1, 16, 16], some [1, 16, 16, 4]) -/
#guard_msgs in
#eval (sourceObserve ((Stmt.loop .auto condition body).run StorageCase.state),
  targetObserve (run [.loop compiled.cond compiled.code] machine))

/-- The zero horizon is exactly the initial pending state, in the kernel. -/
theorem zero_pending :
    TLoop.iterN (horizonBody body) (fun o=>condition.evalT o.st) 0 ⟨StorageCase.state,List.prefix_refl _⟩=
      .inl ⟨StorageCase.state,List.prefix_refl _⟩ ∧
    loopIterN (fun m=>exec compiled.cond 0 m) (fun m=>exec compiled.code 0 m) 0 machine=.inl machine := ⟨rfl,rfl⟩

private def pending {α β : Type} : α ⊕ β → Bool
  | .inl _=>true
  | .inr _=>false
/- One successful OUTER turn remains pending; the next condition completes.
These closed observations execute the actual nested-loop evaluators. -/
/-- info: (true, true, false, false) -/
#guard_msgs in
#eval (pending (TLoop.iterN (horizonBody body) (fun o=>condition.evalT o.st) 1 ⟨StorageCase.state,List.prefix_refl _⟩),
  pending (loopIterN (fun m=>exec compiled.cond 0 m) (fun m=>exec compiled.code 0 m) 1 machine),
  pending (TLoop.iterN (horizonBody body) (fun o=>condition.evalT o.st) 2 ⟨StorageCase.state,List.prefix_refl _⟩),
  pending (loopIterN (fun m=>exec compiled.cond 0 m) (fun m=>exec compiled.code 0 m) 2 machine))

private def failedBody : Prog D Γ Γ := .cons (.block inner) (.cons .revert (.cons reset .nil))
private def failed : Compiled 0 (Frag.init Γ) condition failedBody :=
  (compile 0 (Frag.init Γ) condition failedBody).get (by decide +kernel)
attribute [irreducible] failed

theorem early_abort_simulates : LoopScopes.Result 1 0 6 (Frag.init Γ) StorageCase.state base machine
    (fun o cost=>Prefix failed.cert StorageCase.state o cost)
    ((Stmt.loop .auto condition failedBody).run StorageCase.state) (run [.loop failed.cond failed.code] machine) :=
  failed.cert.correct .auto StorageCase.fixture (by unfold failed;decide +kernel)
    (room_nonallocating failed.cert (by unfold failed;decide +kernel) StorageCase.state base machine)

private def sourceRevert {α : Type} : TRes α → Bool
  | .error .revert=>true
  | _=>false
private def targetRevert : Out → Bool
  | .revert=>true
  | _=>false
/-- info: (true, true) -/
#guard_msgs in
#eval (sourceRevert ((Stmt.loop .auto condition failedBody).run StorageCase.state),
  targetRevert (run [.loop failed.cond failed.code] machine))

/- Runtime negative: changing the expected store is discriminated. This is
NOT a native evaluator invoked as a logical proof. -/
/-- info: false -/
#guard_msgs in
#eval (targetObserve (run [.loop compiled.cond compiled.code] machine)==some [1,15,16,4])

/-- Unsupported exhausted bodies retain the original compiler boundary. -/
theorem exhausted_preparation : (compile 0 (Frag.init Γ) condition
    (.cons .assumeFalse (.nil : Prog D Γ Γ))).isNone=true := by decide +kernel

theorem finite_only (n : Nat) : CountedHorizon compiled.cert 1 6 StorageCase.state base machine n
    (TLoop.iterN (horizonBody body) (fun o=>condition.evalT o.st) n ⟨StorageCase.state,List.prefix_refl _⟩)
    (loopIterN (fun m=>exec compiled.cond 0 m) (fun m=>exec compiled.code 0 m) n machine) :=
  compiled.cert.correct_finite_horizon n StorageCase.fixture cap (room.finite n)

theorem zero_without_future_room : CountedHorizon compiled.cert 1 6 StorageCase.state base machine 0
    (TLoop.iterN (horizonBody body) (fun o=>condition.evalT o.st) 0 ⟨StorageCase.state,List.prefix_refl _⟩)
    (loopIterN (fun m=>exec compiled.cond 0 m) (fun m=>exec compiled.code 0 m) 0 machine) :=
  compiled.cert.correct_finite_horizon 0 StorageCase.fixture cap (finiteRoom_zero compiled.cert StorageCase.state base machine)

end Solidity.Evm.Memory.MixedLoops.Controls
