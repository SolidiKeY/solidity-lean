import Solidity.Lowering.Readonly.PrimitiveFields

/-! Guard empty layouts and unrelated source endpoints replacing caller-storage
transport premises. One actual captured nonself call returns [7], retains a true
persistent Bool cell and changes its event trace. Caller-owned layout, raw run,
structural history and both representations are supplied together. The resulting
reflexive storage equality is premise satisfiability, not compiler/world/physical
frame adequacy or general Source-call history production. -/
namespace Solidity.H62.ReadonlyAudit.CallerStorageWitnesses
open Solidity.Source
open Solidity.Backend.Passes.SourceTypedCall
open Solidity.Lowering.Readonly
open PrimitiveFields InvocationFrame

def flag : Decl := ⟨.stateVar, "flag", some "C", false,
  .stateVar (.elem .bool) none none none false "flag" .none⟩
def declaration : Decl := ⟨.function, "ping", some "I", false,
  .function (.ident "ping") .nil (some .external) (some .view) .nil false none .nil .none⟩
def environment : Env := ⟨[declaration, flag]⟩
def caller : Solidity.Roadmap.Address := ⟨0, by decide⟩
def receiver : Solidity.Roadmap.Address := ⟨2, by decide⟩
def frame : Fr := { this := caller, sender := caller, value := ⟨0, by decide⟩, static := false, contract := "C" }
def state : St environment :=
  { ex := { world := ⟨fun a => { Account.empty (D := environment.layout) (environment.lay a) with
        storage := (Solidity.Source.Storage.empty : Solidity.Source.Storage environment.layout (environment.lay a)).write flag.path (.bool true) }⟩
            transient := ⟨fun _ => Storage.empty⟩, journal := [] }
    heap := Solidity.Source.Heap.empty, events := [], logs := [], fnLocals := ⟨[], .nil⟩ }
def global : Glob environment where
  prog := { body := fun _ => none, consts := fun _ => none, inits := fun _ => [],
            ctor := fun _ => none, ctorLocals := fun _ => [], baseArgs := fun _ => [], contracts := [] }
  pipeline := .legacy
  fixed := { evm := { keccak := fun _ => 0, keccak_lt := fun _ => by decide,
                      precompile := fun _ _ => none, precompileGas := fun _ _ => 0 },
             ledger := fun balance _ a => balance a, regionLen := 1, rootSlots := 1 }
  balance0 := fun _ => ⟨0, by decide⟩
  hasCode := fun _ _ => true
  callee := fun _ => .answer (.success [7])
  timestamp := ⟨0, by decide⟩
def target : RExpr environment [.address false] (.contract ⟨none, "I"⟩) :=
  .convExplicit (.local .here) (by rfl)
def zero : RExpr environment [.address false] (.int IntTy.u256) :=
  .conv (.const (Q.ofInt 0)) (.inl (by rfl))
def before : Locals environment.layout [.address false] × St environment :=
  (.cons (.address receiver) .nil, state)
def captured : Captured environment [] :=
  ⟨receiver, ⟨0, by decide⟩, .nil, global.selector (sigOf environment.layout "ping" [])⟩
def invocation : Invocation environment [.address false] ⟨none, "I"⟩ [] [] where
  global := global
  frame := frame
  horizon := 2
  declaration := declaration
  declared := rfl
  signature := rfl
  target := target
  value := zero
  arguments := .nil
  before := before
  after := before
  captured := captured
  execution := rfl

def final : St environment := { state with events :=
  [.call receiver ⟨0, by decide⟩ captured.input true, .answer (.success [7]) none] }
def contract : Solidity.Contract := { vars := [("flag", .prim .bool)] }
def fields : Fields environment contract.vars :=
  .field "flag" .bool flag rfl rfl rfl rfl rfl rfl .nil
def layout : PrimitiveFields.Layout environment contract := ⟨fields, rfl⟩
def ownedLayout : CallLayout invocation contract :=
  ⟨layout, ⟨⟨"C", rfl, rfl⟩, True.intro⟩⟩
def stored : Solidity.Storage contract := .cons (.prim (p := .bool) true) .nil

theorem raw : invocation.RawAt (.ok (.success [7])) final := rfl

theorem frames : invocation.RuntimeFrames final := ⟨rfl, .start _ _⟩

theorem entry : Rel fields caller (state.ex.world.accounts caller).storage stored := ⟨rfl, True.intro⟩

theorem exit : Rel fields caller (final.ex.world.accounts caller).storage stored := ⟨rfl, True.intro⟩

theorem storage_joint : stored = stored :=
  caller_storage invocation (.ok (.success [7])) final raw frames layout stored stored entry exit

theorem exit_joint : ∃ after : Solidity.Storage contract,
    Rel fields caller (final.ex.world.accounts caller).storage after ∧ after = stored :=
  caller_exit invocation (.ok (.success [7])) final raw frames layout stored entry

theorem owned_exit_joint : ∃ after : Solidity.Storage contract,
    Rel fields caller (final.ex.world.accounts caller).storage after ∧ after = stored :=
  lowered_caller_exit invocation (.ok (.success [7])) final raw frames ownedLayout stored entry

/-- The actual successful call changed the event trace. -/
theorem changed_events : final.events ≠ state.events := by decide

/-- A false/default target cell does not represent this true source cell. -/
theorem erased_representation_refused :
    ¬ Rel fields caller (final.ex.world.accounts caller).storage
      (.cons (.prim (p := .bool) false) .nil) := by
  intro related
  have same : (some (Solidity.Source.Val.bool true) : Option (Solidity.Source.Val environment.layout .bool)) = some (.bool false) := related.1
  cases same

end Solidity.H62.ReadonlyAudit.CallerStorageWitnesses
