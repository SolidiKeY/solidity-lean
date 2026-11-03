import Solidity.Lowering.StorageOps.SourceArrayDeleteTarget

/-! Operation-side Source readback removes intermediate read premises from
actual storage operation sequencing. Source and runtime semantics stay unchanged. -/
namespace Solidity.Backend.StorageOps.SourceArrayReadback
open SourceScalarDeleteLog SourceArrayDeleteTarget

private theorem default_length {D : Source.Layout} {M : Type → Type}
    [Monad M] [LawfulMonad M] (τ : Source.STy)
    (typed : τ = .int Source.IntTy.u256)
    (failure : {t : Source.STy} → M (Source.Val D t)) :
    (do
      let v ← (match Source.Val.default D τ with
        | some v => pure v
        | none => failure)
      let w ← pure (typed ▸ v)
      match w with
      | .int n _ => pure n.toNat) = (pure 0 : M Nat) := by
  cases typed
  simp only [Source.Val.default,Source.Val.defaultElem,pure_bind]
  rfl

theorem readLen_after_clear {E : Source.Env} {Γ : Source.RCtx}
    (frame : Source.Fr) (path : Source.SPath)
    (locals : Source.Locals E.layout Γ) (state : Source.St E)
    (ordinary : E.transientRoot path = false)
    (typed : E.cellTy path = .int Source.IntTy.u256) :
    (Source.readLen (E := E) (Γ := Γ) frame path).run
      (locals,{state with ex := state.ex.apply (clearOp E frame path)}) =
      (.ok 0,(locals,{state with ex := state.ex.apply (clearOp E frame path)})) := by
  have computation := default_length (D := E.layout) (M := Source.EM E Γ) (E.cellTy path) typed
    (fun {t} => Source.EM.halt (.stuck "storage cell without a value"))
  simp only [pure_bind] at computation
  have result := congrArg (fun (m : Source.EM E Γ Nat) => m.run
    (locals,{state with ex := state.ex.apply (clearOp E frame path)})) computation
  simp only [Source.readLen,Source.readAt,dif_pos typed,bind_assoc,pure_bind]
  simp only [Source.readCell,Source.EM.st,
    bind,pure,get,getThe,liftM,MonadLiftT.monadLift,MonadLift.monadLift,
    Functor.map,StateT.map,MonadStateOf.get,ExceptT.mk,ExceptT.run,
    ExceptT.bind,ExceptT.bindCont,ExceptT.pure,ExceptT.lift,StateT.bind,StateT.pure,StateT.get,
    clearOp,ordinary,Bool.false_eq_true,if_false,Source.ExecState.apply,
    Source.World.set_get,Source.Storage.read,Source.Storage.set,dif_pos,Source.Env.lay]
    at result ⊢
  unfold Source.readCell.match_1 Source.readLen.match_1
  unfold default_length.match_1 default_length.match_3 at result
  exact result

/-- The next input read is derived from actual first execution, not assumed. -/
theorem source_array_readback {E : Source.Env} {Γ : Source.RCtx}
    (frame : Source.Fr) (writable : frame.static = false) (path : Source.SPath)
    (count : Nat) (locals : Source.Locals E.layout Γ) (state : Source.St E)
    (ordinary : E.transientRoot path = false)
    (typed : E.cellTy path = .int Source.IntTy.u256)
    (input : (Source.readLen (E := E) (Γ := Γ) frame path).run (locals,state) =
      (.ok count,(locals,state))) :
    let first := (Source.deleteStor (E := E) (Γ := Γ) frame (count + 2)
      (.array .storage (.int Source.IntTy.u256) none) path).run (locals,state)
    (Source.readLen frame path).run first.2 = (.ok 0,first.2) := by
  dsimp only
  rw [source_array_run frame writable Source.IntTy.u256 path count locals state input]
  simpa only [Source.run_append,Source.ExecState.run] using
    readLen_after_clear frame path locals
      {state with ex := state.ex.run ((List.range' 0 count).map
        (fun i => clearOp E frame (path.go (.index i))))} ordinary typed

/-- Actual second deletion consumes the derived zero length and still journals
one header clear. This is not full-state idempotence or automatic rollback. -/
theorem repeated_array_run {E : Source.Env} {Γ : Source.RCtx}
    (frame : Source.Fr) (writable : frame.static = false) (path : Source.SPath)
    (count : Nat) (locals : Source.Locals E.layout Γ) (state : Source.St E)
    (ordinary : E.transientRoot path = false)
    (typed : E.cellTy path = .int Source.IntTy.u256)
    (input : (Source.readLen (E := E) (Γ := Γ) frame path).run (locals,state) =
      (.ok count,(locals,state))) :
    let first := (Source.deleteStor (E := E) (Γ := Γ) frame (count + 2)
      (.array .storage (.int Source.IntTy.u256) none) path).run (locals,state)
    (Source.deleteStor frame 2 (.array .storage (.int Source.IntTy.u256) none) path).run
      first.2 = (.ok (), (locals,{first.2.2 with ex := first.2.2.ex.apply (clearOp E frame path)})) := by
  dsimp only
  have readback := source_array_readback frame writable path count locals state ordinary typed input
  rw [source_array_run frame writable Source.IntTy.u256 path count locals state input] at readback ⊢
  rw [source_array_run frame writable Source.IntTy.u256 path 0 _ _ readback]
  rfl

namespace Controls
private def uintSyntax : Source.Syn .typeName := .elem (.int false 256 (by decide))
private def unit : Source.Syn .unit := .unit (.cons (.contract false "C" .none .nil
  (.cons (.stateVar (.array uintSyntax .none) none none none false "values" .none)
    (.cons (.stateVar uintSyntax none none none false "sentinel" .none) .nil))) .nil)
private def env : Source.Env := unit.env
private def path : Source.SPath := ⟨⟨some "C","values"⟩,[]⟩
private def sentinel : Source.SPath := ⟨⟨some "C","sentinel"⟩,[]⟩
private def elem (i : Nat) : Source.SPath := path.go (.index i)
private def address : Roadmap.Address := ⟨7,by decide⟩
private def storage : Source.Storage env.layout env.cellTy :=
  let s := (Source.Storage.empty : Source.Storage env.layout env.cellTy).write path (.int 2 (by decide))
  let s := s.write (elem 0) (.int 53 (by decide))
  let s := s.write (elem 1) (.int 59 (by decide))
  let s := s.write (elem 2) (.int 61 (by decide))
  s.write sentinel (.int 99 (by decide))
private def state : Source.St env :=
  { ex :=
      { world := ⟨fun a => if a = address then
          { balance := ⟨19,by decide⟩, nonce := 3, code := some 0, storage := storage }
          else Source.Account.empty _⟩
        transient := Source.Transient.empty
        journal := [] }
    heap := Source.Heap.empty
    events := []
    logs := []
    fnLocals := ⟨[],.nil⟩ }
private def frame : Source.Fr :=
  {this := address,sender := ⟨13,by decide⟩,value := ⟨0,by decide⟩,static := false,contract := "C"}
private def initial : Source.Locals env.layout [] × Source.St env := (.nil,state)
private def first := (Source.deleteStor (E := env) (Γ := []) frame 4
  (.array .storage (.int Source.IntTy.u256) none) path).run initial
private def second := (Source.deleteStor (E := env) (Γ := []) frame 2
  (.array .storage (.int Source.IntTy.u256) none) path).run first.2
private def view (s : Source.St env) := [path,elem 0,elem 1,elem 2,sentinel].map (wordAt frame s.ex)

theorem witnessed_readback :
    (Source.readLen (E := env) (Γ := []) frame path).run first.2 = (.ok 0,first.2) := by
  exact source_array_readback frame rfl path 2 .nil state rfl rfl rfl

theorem witnessed_second : second =
    (.ok (),(.nil,{first.2.2 with ex := first.2.2.ex.apply (clearOp env frame path)})) := by
  exact repeated_array_run frame rfl path 2 .nil state rfl rfl rfl

/-- Complete ordered observations include retained child61 and outside99. -/
theorem ordered_observations :
    (first.1,second.1,view state,view first.2.2,view second.2.2,
      first.2.2.ex.journal.length,second.2.2.ex.journal.length) =
    (.ok (),.ok (),[some 2,some 53,some 59,some 61,some 99],
      [some 0,some 0,some 0,some 61,some 99],
      [some 0,some 0,some 0,some 61,some 99],3,4) := by rfl

theorem not_state_idempotent : second.2.2 ≠ first.2.2 := by
  intro same
  have journals := congrArg (fun s : Source.St env => s.ex.journal.length) same
  change 4 = 3 at journals
  omega

/-- A failed too-short deletion retains the former header and cleared prefix;
replacing a failed input read by zero would erase these actual outcomes. -/
theorem short_failure :
    let failed := (Source.deleteStor (E := env) (Γ := []) frame 3
      (.array .storage (.int Source.IntTy.u256) none) path).run initial
    (failed.1,view failed.2.2,failed.2.2.ex.journal.length,
      (Source.readLen (E := env) (Γ := []) frame path).run failed.2) =
    (.error .timeout,[some 2,some 0,some 59,some 61,some 99],1,(.ok 2,failed.2)) := by rfl

end Controls

/-- info: 'Solidity.Backend.StorageOps.SourceArrayReadback.readLen_after_clear' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in #print axioms readLen_after_clear

/-- info: 'Solidity.Backend.StorageOps.SourceArrayReadback.source_array_readback' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in #print axioms source_array_readback

/-- info: 'Solidity.Backend.StorageOps.SourceArrayReadback.repeated_array_run' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in #print axioms repeated_array_run

/-- info: 'Solidity.Backend.StorageOps.SourceArrayReadback.Controls.witnessed_readback' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in #print axioms Controls.witnessed_readback

/-- info: 'Solidity.Backend.StorageOps.SourceArrayReadback.Controls.witnessed_second' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in #print axioms Controls.witnessed_second

/-- info: 'Solidity.Backend.StorageOps.SourceArrayReadback.Controls.ordered_observations' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in #print axioms Controls.ordered_observations

/-- info: 'Solidity.Backend.StorageOps.SourceArrayReadback.Controls.not_state_idempotent' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in #print axioms Controls.not_state_idempotent

/-- info: 'Solidity.Backend.StorageOps.SourceArrayReadback.Controls.short_failure' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in #print axioms Controls.short_failure

end Solidity.Backend.StorageOps.SourceArrayReadback
