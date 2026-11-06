import Solidity.Backend.Passes.ReferenceCallReadback
import Solidity.Backend.InternalFlow.RuntimeFrameV3CallProducerRefTupleControls
import Solidity.Backend.InternalFlow.RuntimeFrameRestoredRepresentation

namespace Solidity.Backend.Passes.ReferenceCallReadback.Controls
open Evm Evm.Memory Evm.Compiler
open Solidity.Backend.InternalFlow.RuntimeFrame
open V3CallProducerRef.Tuple.Controls
abbrev Δ : Ctx := rs ++ Γ
abbrev caller := V3CallProducerRef.ArrayControls.caller (wmod 0)
abbrev bases := V3CallProducerRef.ArrayControls.bases
abbrev initial := V3CallProducerRef.ArrayControls.machine (wmod 0)

private def successOut : TRes (Solidity.Out C caller.H Δ) → Option (Solidity.Out C caller.H Δ)
  | .ok out => some out | _ => none
@[irreducible] def output : Solidity.Out C caller.H Δ :=
  (successOut (call.run caller)).get (by decide +kernel)
theorem source_run : call.run caller = .ok output := by
  have h : some output = successOut (call.run caller) := by
    unfold output
    exact Option.some_get _
  generalize call.run caller = result at h ⊢
  cases result with
  | ok out => exact congrArg Except.ok (Option.some.inj h).symm
  | error err => cases h

abbrev dst : Idx Δ (.val .uint) := .there (.there .here)
def value : Val C Δ .uint := .simple (.local .here)
def vc : CompiledVal 1 selected.checked.frag value := ⟨_,.core _ rfl⟩
def update : Val C (.val .uint :: Δ) .uint := .simple (.lit 9 rfl)
def uc : CompiledVal 1 (selected.checked.frag.push (.val .uint) .ok) update := ⟨_,.core _ rfl⟩
theorem evaluated : value.evalT output.st = .ok (indexValue (wmod 7)) := by
  change Except.ok output.st.env.1 = Except.ok (indexValue (wmod 7))
  apply congrArg Except.ok
  apply Subtype.ext
  unfold output
  decide +kernel

def chosen : Composition.Program 1 F
    (.cons (Stmt.call "tupleAlias" V3CallProducerRef.ArrayControls.args (.rets binders)
      V3CallProducerRef.Tuple.Controls.body) .nil) := selected

def application := Solidity.Backend.Passes.ReferenceCallReadback.execution
  (body := V3CallProducerRef.Tuple.Controls.body) (f := "tupleAlias")
  (L := 1) (frame := 64) form chosen 16 16 flags (entered (wmod 0)) output source_run
  (.user "tupleCapture") value vc dst update uc (indexValue (wmod 7)) (indexValue (wmod 9))
  evaluated rfl (by decide)

private def successMachine : Evm.Out → Option Machine
  | .ok m 0 => some m | _ => none
@[irreducible] def returned : Machine :=
  (successMachine (run (V3CallProducerRef.plan selected 16 16).code initial)).get (by decide +kernel)
theorem returned_run : run (V3CallProducerRef.plan selected 16 16).code initial = .ok returned 0 := by
  have h : some returned = successMachine (run (V3CallProducerRef.plan selected 16 16).code initial) := by
    unfold returned
    exact Option.some_get _
  generalize run (V3CallProducerRef.plan selected 16 16).code initial = result at h ⊢
  cases result with
  | ok m skip => cases skip with
    | zero => exact congrArg (fun m => Evm.Out.ok m 0) (Option.some.inj h).symm
    | succ n => cases h
  | revert => cases h
  | fault => cases h

def suffix := CapturedValueStability.compiled (.user "tupleCapture") value vc dst update uc
def after (tail : List Word) : Machine :=
  writeMachine (writeMachine (appendTail returned tail) 5 w[7]) 2 w[9]
def code := (V3CallProducerRef.plan selected 16 16).code ++ suffix.code ++ [.mload 5]

theorem reached : ∃ addresses,
    StateRepr 1 1 64 selected.checked.frag output.st addresses returned ∧
    BaseExtends caller.H bases addresses ∧ ∀ tail,
      suffix.Input 1 64 addresses output.st (appendTail returned tail) ∧
      run (V3CallProducerRef.plan selected 16 16).code (appendTail initial tail) =
        .ok (appendTail returned tail) 0 ∧
      MappedOutput suffix 1 64 addresses output.st (appendTail returned tail)
        ((output.st.push (t := .val .uint) (indexValue (wmod 7))).setLocal (.there dst) (indexValue (wmod 9)))
        (after tail) addresses ∧
      GrowsAllocator 1 64 1 caller bases (appendTail initial tail)
        ((output.st.push (t := .val .uint) (indexValue (wmod 7))).setLocal (.there dst) (indexValue (wmod 9)))
        addresses (after tail) ∧
      (after tail).mem 16 = w[20] ∧ Footprint.Words 16 20 (appendTail initial tail) (after tail) ∧
      run code (appendTail initial tail) = .ok ((after tail).push w[7]) 0 := by
  obtain ⟨_,actual,addresses,captured,updated,hcall,repr,_,extension,_,_,_,hc,hu,runs⟩ := application
  have same : actual = returned := (Evm.Out.ok.inj (hcall.symm.trans returned_run)).1
  subst actual
  have cap : captured = w[7] := Restored.value_unique hc (ReprV.uint_of rfl)
  have upd : updated = w[9] := Restored.value_unique hu (ReprV.uint_of rfl)
  subst captured
  subst updated
  refine ⟨addresses,repr,extension,?_⟩
  intro tail
  simpa only [cost] using runs tail

def sourceFinal := (output.st.push (t := .val .uint) (indexValue (wmod 7))).setLocal
  (.there dst) (indexValue (wmod 9))
def sourceVector : Option (List Nat) := do
  let pointer ← sourceFinal.env.2.2.1
  let old ← sourceFinal.env.2.2.2.2.1
  pure [sourceFinal.env.1.val.toNat,sourceFinal.env.2.1.val.toNat,pointer.id,
    sourceFinal.env.2.2.2.1.val.toNat,old.id,sourceFinal.H.length,sourceFinal.heap.len pointer .dyn]
theorem source_observations : sourceVector = some [7,7,0,9,0,2,1] := by
  unfold sourceVector sourceFinal output
  decide +kernel

def cells : List Nat := [0,1,2,3,4,5,16,20,21,22,63,128,129,130]
theorem complete_observations (tail : List Word) :
    (cells.map ((after tail).push w[7]).mem,((after tail).push w[7]).stack) =
      ([w[131],w[128],w[9],w[128],w[7],w[7],w[20],w[128],w[0],w[0],w[99],w[1],w[0],w[0]],
        w[7] :: w[77] :: tail) := by
  apply Prod.ext
  · change cells.map (after []).mem =
      [w[131],w[128],w[9],w[128],w[7],w[7],w[20],w[128],w[0],w[0],w[99],w[1],w[0],w[0]]
    unfold cells after appendTail returned
    decide +kernel
  · change w[7] :: returned.stack ++ tail = _
    have stack : returned.stack = [w[77]] := by unfold returned; decide +kernel
    rw [stack]
    rfl

theorem wrong_recapture : (after []).mem 2 ≠ (after []).mem 5 := by
  unfold after appendTail returned
  decide +kernel

theorem body_failure (tail : List Word) :
    run ((V3CallProducerRef.plan selected 16 16).code ++ suffix.code ++ [.mload 5])
      (appendTail (V3CallProducerRef.ArrayControls.machine (wmod 2)) tail) = .revert := by
  rw [List.append_assoc]
  exact call_revert selected 16 16 (entered (wmod 2)) source_revert _ tail

theorem private_frame_refused :
    ¬ InterfaceV1.Entry (V3CallProducerRef.plan selected 16 16) 1 1 15 F caller bases initial 20 := by
  intro entry
  have room := entry.pointerBelow
  change 16 < 15 at room
  omega

/-- The fresh default object exists even though the body returned the old alias.
The caller's original address map cannot represent that reached heap. -/
def fresh : HRef output.st.H A := ⟨1,by unfold output; decide +kernel⟩
theorem stale_map_refused (machine : Machine) :
    ¬ StateRepr 1 1 64 selected.checked.frag output.st bases machine := by
  intro represented
  have above := represented.heap.above fresh
  change 64 ≤ 0 at above
  omega

end Solidity.Backend.Passes.ReferenceCallReadback.Controls
