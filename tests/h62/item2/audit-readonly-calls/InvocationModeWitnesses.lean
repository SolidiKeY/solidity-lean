import Solidity.Lowering.Readonly.InvocationFrame

/-! Guard detached view/pure labels replacing actual checked invocations. Each
invocation contains declaration membership/signature and a successful Source
capture to a distinct receiver. Pure mode is tested with an ordinary parent;
inherited mode is tested with an actual static frame. Capture is not evidence
of callee execution, compiler/world binding or physical-frame preservation. -/
namespace Solidity.H62.ReadonlyAudit.InvocationModeWitnesses
open Solidity.Source
open Solidity.Backend.Passes.SourceTypedCall
open Solidity.Lowering.Readonly.InvocationFrame

def declaration (m : Solidity.Source.Mutability) : Decl := ⟨.function, "ping", some "I", false,
  .function (.ident "ping") .nil (some .external) (some m) .nil false none .nil .none⟩
def environment (m : Solidity.Source.Mutability) : Env := ⟨[declaration m]⟩
def caller : Solidity.Roadmap.Address := ⟨0, by decide⟩
def receiver : Solidity.Roadmap.Address := ⟨2, by decide⟩
def frame (static : Bool) : Fr := { this := caller, sender := caller, value := ⟨0, by decide⟩, static := static, contract := "" }
def state (m : Solidity.Source.Mutability) : St (environment m) :=
  { ex := { world := ⟨fun a => Account.empty (D := (environment m).layout) ((environment m).lay a)⟩,
            transient := ⟨fun _ => Storage.empty⟩, journal := [] }
    heap := Solidity.Source.Heap.empty, events := [], logs := [], fnLocals := ⟨[], .nil⟩ }
def global (m : Solidity.Source.Mutability) : Glob (environment m) where
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
def target (m : Solidity.Source.Mutability) : RExpr (environment m) [.address false] (.contract ⟨none, "I"⟩) :=
  .convExplicit (.local .here) (by rfl)
def zero (m : Solidity.Source.Mutability) : RExpr (environment m) [.address false] (.int IntTy.u256) :=
  .conv (.const (Q.ofInt 0)) (.inl (by rfl))
def before (m : Solidity.Source.Mutability) : Locals (environment m).layout [.address false] × St (environment m) :=
  (.cons (.address receiver) .nil, state m)
def captured (m : Solidity.Source.Mutability) : Captured (environment m) [] :=
  ⟨receiver, ⟨0, by decide⟩, .nil, (global m).selector (sigOf (environment m).layout "ping" [])⟩
def invocation (m : Solidity.Source.Mutability) (static : Bool) :
    Invocation (environment m) [.address false] ⟨none, "I"⟩ [] [] where
  global := global m
  frame := frame static
  horizon := 2
  declaration := declaration m
  declared := rfl
  signature := rfl
  target := target m
  value := zero m
  arguments := .nil
  before := before m
  after := before m
  captured := captured m
  execution := by cases m <;> rfl

theorem inherited_joint : (invocation .payable true).frame.static = true ∧
    (invocation .payable true).mode = true :=
  ⟨rfl, Invocation.inherited (invocation .payable true) rfl⟩

theorem view_joint : (invocation .view false).declaration.fnMut = some .view ∧
    (invocation .view false).mode = true :=
  ⟨rfl, Invocation.view_mode (invocation .view false) rfl⟩

theorem pure_joint : (invocation .pure false).declaration.fnMut = some .pure ∧
    (invocation .pure false).mode = true :=
  ⟨rfl, Invocation.pure_mode (invocation .pure false) rfl⟩

theorem view_capture_observed :
    (capture (global .view) (frame false) 2 (target .view) (declaration .view) (zero .view) .nil).run
      (before .view) = (.ok (captured .view), before .view) := rfl

theorem pure_capture_observed :
    (capture (global .pure) (frame false) 2 (target .pure) (declaration .pure) (zero .pure) .nil).run
      (before .pure) = (.ok (captured .pure), before .pure) := rfl

theorem receiver_not_self : (captured .pure).receiver ≠ (invocation .pure false).frame.this := by decide

theorem ordinary_parent : (invocation .pure false).frame.static = false := rfl

theorem pure_downgrade_refused : (invocation .pure false).mode ≠ false := by
  rw [pure_joint.2]
  intro same
  cases same

end Solidity.H62.ReadonlyAudit.InvocationModeWitnesses
