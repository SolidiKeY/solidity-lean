import Solidity.Backend.PrimitivePackets.UnsignedCast.Boundaries
import Solidity.Evm.Correct

/-! Inhabited Source and positive-offset physical inputs. General controls
cover every legal width/value/pipeline and preserve a two-word saved stack,
the allocator cursor and protected memory. No assumed execution is supplied. -/
namespace Solidity.Backend.PrimitivePackets.UnsignedCast.Controls
open Solidity.Lowering.V07
open Evm Evm.Memory

def E : Source.Env := ⟨[]⟩
def program : Source.Program E where
  body _ := none
  consts _ := none
  inits _ := []
  ctor _ := none
  ctorLocals _ := []
  baseArgs _ := []
  contracts := []

def fixed : Roadmap.Fixed where
  evm := {
    keccak := fun _ => 0
    keccak_lt := fun _ => by decide
    precompile := fun _ _ => none
    precompileGas := fun _ _ => 0
  }
  ledger := fun bal _ a => bal a
  regionLen := 1
  rootSlots := 1

def globals (pipeline : Roadmap.Pipeline) : Source.Glob E :=
  ⟨program,pipeline,fixed,fun _ => ⟨0,by decide⟩,fun _ _ => false,
    fun _ => .answer (.success []),⟨0,by decide⟩⟩

def frame (checked : Bool) : Source.Fr :=
  {this := ⟨1,by decide⟩,sender := ⟨2,by decide⟩,value := ⟨0,by decide⟩,
    static := false,contract := "C",checked := checked}

def sourceState : Source.St E :=
  ⟨⟨⟨fun _ => Source.Account.empty _⟩, Source.Transient.empty, []⟩,
    Source.Heap.empty,[],[],⟨[],.nil⟩,Source.FailureExecution.Cursor.empty⟩

def source (n : Int) (range : Source.IntTy.u256.lo ≤ n ∧ n ≤ Source.IntTy.u256.hi) :
    Source.EMState E [.int Source.IntTy.u256] := (.cons (.int n range) .nil,sourceState)

def C : Contract := {vars := []}
abbrev Γ : Ctx := [.val .uint]
abbrev frag : Frag Γ := Frag.init Γ

def target (n : Int) (range : Source.IntTy.u256.lo ≤ n ∧ n ≤ Source.IntTy.u256.hi) : State C Γ :=
  (State.init C).push (t := .val .uint) (integerValue Source.IntTy.u256 n range)

def base : Nat → Fin W := fun _ => wmod 0

def initialMachine : Machine :=
  {Machine.init with stack := [w[77],w[88]],mem := fun address =>
    if address = 0 then w[64] else if address = 8 then w[10]
    else if address = 9 then w[99] else w[0]}

def machine (n : Int) (range : Source.IntTy.u256.lo ≤ n ∧ n ≤ Source.IntTy.u256.hi) : Machine :=
  writeMachine initialMachine 1 (.val (integerValue Source.IntTy.u256 n range).word)

theorem represented (n : Int) (range : Source.IntTy.u256.lo ≤ n ∧ n ≤ Source.IntTy.u256.hi) :
    StateRepr 1 1 16 frag (target n range) base (machine n range) := by
  have absent {R : RefTy} (r : HRef [] R) : False := by
    simpa only [List.getElem?_nil,reduceCtorEq] using r.get?
  have heap : HeapRepr (State.init C).heap base 16 initialMachine :=
    ⟨fun r => (absent r).elim,fun r => (absent r).elim,fun r _ _ => (absent r).elim⟩
  have empty : StateRepr 1 1 16 (Frag.init []) (State.init C) base initialMachine := by
    refine ⟨?_,heap,(fun i => nomatch i),by decide,
      ⟨fun r => (absent r).elim,fun r => (absent r).elim,fun r => (absent r).elim⟩,
      (fun _ r => (absent r).elim),RefFieldsRepr.withoutStructs _ _ _ (fun r => absent r)⟩
    have core := Sim.init C 0 W_pos (fun _ => 0) ⟨0,W_pos⟩ rfl
    exact ⟨core.store,(fun i => nomatch i),(fun i _ => nomatch i),core.net,
      core.netSelf,core.bound,(fun i _ => nomatch i),core.env,core.funds,core.oracle⟩
  exact empty.consVal _ _ (ReprV.uint_of (word_val _).symm) (by decide)

/-- Actual Source and selected-machine execution with no desired-run premise. -/
theorem executions (bits : Nat) (legal : Legal bits) (pipeline : Roadmap.Pipeline)
    (checked : Bool) (fuel : Nat) (n : Int)
    (range : Source.IntTy.u256.lo ≤ n ∧ n ≤ Source.IntTy.u256.hi) :
    let result := integerValue (targetTy bits legal) ((targetTy bits legal).wrap n)
      ((targetTy bits legal).wrap_mem n)
    (Source.evalE (globals pipeline) (frame checked) (fuel+2)
      (expression bits legal .here)).run (source n range) =
      (.ok (.val (Source.intWrap (targetTy bits legal) n)),source n range) ∧
    Memory.compileVal 1 frag (value (C := C) bits legal .here) = some (selected 1 frag bits legal .here) ∧
    run (instructions 1 bits (.here : Idx Γ (.val .uint))) (machine n range) =
      .ok ((machine n range).push (.val result.word)) 0 := by
  have application := transport (globals pipeline) (frame checked) fuel (source n range)
    (target n range) bits legal .here .here n range rfl rfl 1 1 16 frag base
    (machine n range) (represented n range) w[77] [w[88]]
  exact ⟨application.1,application.2.2.2.1,application.2.2.2.2.1⟩

/-- Cursor, unrelated cells and the exact saved tail remain protected. -/
theorem protected_observations (n : Int) (range : Source.IntTy.u256.lo ≤ n ∧ n ≤ Source.IntTy.u256.hi)
    (result : Word) :
    ([0,8,9].map ((machine n range).push result).mem,
      ((machine n range).push result).stack) = ([w[64],w[10],w[99]],[result,w[77],w[88]]) := rfl

theorem wrong_saved_tail : ([w[77],w[88]] : List Word) ≠ [w[77],w[89]] := by decide

theorem wrong_uint8_unmasked : (targetTy 8 (by decide)).wrap 256 ≠ 256 := by decide

end Solidity.Backend.PrimitivePackets.UnsignedCast.Controls
