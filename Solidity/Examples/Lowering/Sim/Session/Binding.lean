import Solidity.Correctness.Lowering.Sim.Session.Binding
import Solidity.Source.SemanticsExamples

/-!
# The machine-free parts of the session lift on one accepted program

`contract C { uint x; }` as a Source program over its canonical unit and as a
compilation without entries: in t0's accepted fragment (`inFragment`), with
each declaration of `Sim/Session/Binding.lean` and its helpers used on it. It
has no function, so the binding (`bound`) binds no site, and
`Sim.diagram.Total` stays a hypothesis.
-/
namespace Solidity.Examples.Lowering.Sim.Session.Binding

open Solidity.Goals.Shrink.Lowering
open Solidity.Correctness.Lowering
open Solidity.Correctness.Lowering.Sim
open Solidity.Correctness.Lowering.Sim.Session
open Solidity.Roadmap (SessionEnv)
open Solidity.Semantics.IntrinsicSession (spec)

/-- `contract C { uint x; }`. -/
def C : Contract := { vars := [("x", .prim .uint)] }

/-- The canonical Source unit of `C` (`Total.Decode.unit`). -/
def unit : Source.Syn .unit := (Total.Decode.unit C).get rfl

abbrev E : Source.Env := unit.env

/-- The Source program: no bodies, no initializers, no constructor. -/
def program : Source.Program E where
  body _ := none
  consts _ := none
  inits _ := []
  ctor _ := none
  ctorLocals _ := []
  baseArgs _ := []
  contracts := [Total.Decode.contractName]

def P : Source.SrcProg E :=
  ⟨program, .legacy, Source.SemanticsExamples.toyFixed, Total.Decode.contractName⟩

/-- The compilation: the contract, no deployment input and no entry resolved. -/
def c : Compilation := ⟨C, fun _ => none, fun _ => none⟩

theorem names : c.Names P :=
  ⟨fun _ _ fn => (nomatch fn.1), fun _ _ mem => (nomatch mem)⟩

theorem accepted : c.Accepted :=
  ⟨fun _ _ h => (nomatch h), fun _ _ h => (nomatch h)⟩

/-- The program is in t0's accepted fragment. -/
theorem inFragment : InFragment P := ⟨c, names, accepted⟩

/-- The unit types the contract's storage. -/
theorem typed : StorageTyped E C := fun x T mem => by
  obtain ⟨rfl, rfl⟩ : x = "x" ∧ T = .prim .uint := by simpa [C] using mem
  exact ⟨.uint, rfl, rfl⟩

example (F : Roadmap.Fixed) (e : SessionEnv) (allowed : (spec F).lang.Allowed e) :
    (Source.sourceLangEvents E).Allowed (envAbs e) := envSound F E e allowed

example (F : Roadmap.Fixed) (e : SessionEnv) (allowed : (Source.sourceLangEvents E).Allowed e) :
    ∃ e', (spec F).lang.Allowed e' ∧ envAbs e' = e := envOnto F E e allowed

/-- The first three conjuncts of `SessionLift Sim.diagram` at `P`. -/
theorem bound (total : diagram.Total) :
    ∃ c : Compilation, c.Names P ∧ c.Accepted ∧ BodiesBound diagram P c :=
  ⟨c, names, accepted, bodiesBound total P c⟩

/-- The model state a frame of `C` at the address `self` starts from. -/
def start (self : PrimTy.uint.Denote) : State C [] :=
  { State.init C with tx := { selfAddress := self } }

/-- The Source state before the session is related to the model start at address 7. -/
theorem start_related : diagram.globRel (Source.St.init E) (start ⟨7, by decide⟩) :=
  initial_globRel typed ⟨7, by decide⟩ rfl rfl rfl

/-- The deployment frame of the lowered world, at an unfunded address. -/
example (F : Roadmap.Fixed) (e : SessionEnv) {payable : Bool} {σ : State c.C []} :=
  deploy_initial (payable := payable) (σ := σ) c typed F e

abbrev contracts : Fin 1 → Contract := Semantics.IntrinsicSession.catalog [C]

/-- The fresh account of `C` in the catalog of the lowered world's code. -/
def account : ContractWorld.Account contracts := ⟨0, Storage.init C⟩

/-- At the goal's boundary state both sides are read at address zero. -/
theorem boundary_related : diagram.globRel (Source.St.init E) (boundaryState account) :=
  (globRel_boundaryState _ account).2 ⟨fields_fresh typed rfl rfl, fun _ => rfl⟩

/-- A committed frame leaves a related account at its address and funds. -/
example {w t : ContractWorld.World contracts} {self : ContractWorld.Address}
    (commit : w.finish (k := 0) self (start ⟨7, by decide⟩) = .ok t) :
    ∃ a, t.accounts self = some a ∧
      diagram.globRel (Source.St.init E) (boundaryAt a ⟨7, by decide⟩ (PrimTy.dflt .uint)) :=
  globRel_committed start_related commit

/-- The relation ignores the locals of the model state. -/
example : diagram.globRel (Source.St.init E) ((start ⟨7, by decide⟩).push (t := .val .bool) true) :=
  globRel_congr start_related rfl rfl rfl

/-- The agreement conjunct of the lift at `P` is its unfolding. -/
example (F : Roadmap.Fixed) (h : Agrees diagram F P (loweredWorld c)) :=
  (agrees_iff F P (loweredWorld c)).1 h

end Solidity.Examples.Lowering.Sim.Session.Binding
