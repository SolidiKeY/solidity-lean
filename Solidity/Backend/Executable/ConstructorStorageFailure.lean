import Solidity.Backend.Executable.ConstructorArgumentFailure

/-! Storage-effect argument failure at the native constructor boundary.
Uses existing Source storage/journal operations; no balance assumptions, World
rollback, canonical elaboration or executable-byte correspondence is asserted. -/
namespace Solidity.Backend.Executable.ConstructorStorageFailure
open Solidity Source
namespace Prior
abbrev unit := Solidity.Backend.Executable.ConstructorBaseArgumentControls.unit
abbrev fixed := Solidity.Backend.Executable.ConstructorBaseArgumentControls.fixed
abbrev frame := Solidity.Backend.Executable.ConstructorBaseArgumentControls.frame
end Prior

def savedSyntax : Syn (.part false) :=
  .stateVar (.elem (.int false 8 (by decide))) none none none false "saved" .none
def unit : Syn .unit :=
  match Prior.unit with
  | .unit (.cons (.contract abstract name layout bases parts) rest) =>
    .unit (.cons (.contract abstract name layout bases (.cons savedSyntax parts)) rest)
  | other => other

def E : Env := unit.env
def saved : Decl := ⟨.stateVar,"saved",some "Base",false,savedSyntax⟩
def signed16 : IntTy := ⟨true,16,by decide⟩
def contexts (name : String) : RCtx := tysOf (E.ctorFrameLocals name)
def caller : Locals E.layout (contexts "Derived") :=
  .cons (.int 255 (by decide)) (.cons (.int (-32768) (by decide))
    (.cons (.memRef rfl 0) (.cons (.memRef rfl 0) .nil)))
def arguments : RConvArgs E (contexts "Derived") [.int IntTy.u8,.int signed16] :=
  .cons (.assign (.state saved rfl rfl) (.unary .bitNot (.state saved rfl))) (by decide)
    (.cons (.unary .neg (.local (.there .here))) (by decide) .nil)
def baseArgument : RBaseArg E (contexts "Derived") :=
  ⟨"Base",[.int IntTy.u8,.int signed16],arguments⟩
def program : Program E where
  body _ := none
  consts _ := none
  inits _ := []
  ctor _ := none
  ctorLocals := contexts
  baseArgs name := if h : name = "Derived" then h.symm ▸ [baseArgument] else []
  contracts := E.contracts
def global (p : Roadmap.Pipeline) : Glob E :=
  ⟨program,p,Prior.fixed,fun _ => ⟨0,by decide⟩,fun _ _ => false,
    fun _ => .answer (.success []),⟨0,by decide⟩⟩
def before : St E :=
  { St.init E with
    ex := (St.init E).ex.apply (.account Prior.frame.this (fun account =>
      { account with storage := account.storage.write saved.path (.int 255 (by decide)) }))
    heap := ((Heap.empty.alloc ⟨.bytes .memory,.bytes [170,187]⟩).1.alloc
      ⟨.bytes .memory,.bytes [204]⟩).1 }
def written : St E :=
  { before with ex := before.ex.apply (.account Prior.frame.this (fun account =>
    { account with storage := account.storage.write saved.path (.int 0 (by decide)) })) }
def initial (p : Roadmap.Pipeline) : CtorLocals (global p) := [⟨"Derived",caller⟩]
/-- Actual state-effect producer. The local frame is unchanged, but the
storage write and its journal entry survive the later arithmetic panic. -/
theorem run_inner :
∀ p : Solidity.Roadmap.Pipeline,
 (Solidity.Source.evalConvArgs (Solidity.Backend.Executable.ConstructorStorageFailure.global p)
  Solidity.Backend.Executable.ConstructorStorageFailure.Prior.frame 4
  Solidity.Backend.Executable.ConstructorStorageFailure.arguments).run
  (Solidity.Backend.Executable.ConstructorStorageFailure.caller,
   Solidity.Backend.Executable.ConstructorStorageFailure.before) =
 (.error (.revert (Solidity.Source.panicData .arithmetic)),
  (Solidity.Backend.Executable.ConstructorStorageFailure.caller,
   Solidity.Backend.Executable.ConstructorStorageFailure.written)) := by
  intro p
  cases p <;> rfl

theorem giveArgs_failed :
∀ p : Roadmap.Pipeline,
 (Source.giveArgs (global p)
  Prior.frame 4 "Derived"
  caller
  [baseArgument]
  (initial p)).run
  (Source.L0 E,
   before) =
 (.error (.revert (Source.panicData .arithmetic)),
  (Source.L0 E,
   written)) := by
  intro p
  exact ConstructorArgumentFailure.transport_failure (global p) Prior.frame 4 "Derived"
    caller caller baseArgument [] (initial p) before written
    (.revert (panicData .arithmetic)) rfl (run_inner p)

theorem observations :
∀ p : Roadmap.Pipeline,
 (Source.construct (global p)
  Prior.frame 4 "Derived"
  caller).run
  (Source.L0 E,
   before) =
 (.error (.revert (Source.panicData .arithmetic)),
  (Source.L0 E,
   written)) ∧
 ((before.ex.world.accounts
   Prior.frame.this).storage.read
   saved.path) = some (.int 255 (by decide)) ∧
 ((written.ex.world.accounts
   Prior.frame.this).storage.read
   saved.path) = some (.int 0 (by decide)) ∧
 before.ex.journal.length = 1 ∧
 written.ex.journal.length = 2 ∧
 written.heap.get 0 =
 some ⟨.bytes .memory,.bytes [170,187]⟩ := by
  intro p
  cases p <;> exact ⟨rfl,rfl,rfl,rfl,rfl,rfl⟩

theorem state_distinct :
written ≠
 before := by
  intro h
  have counts := congrArg (fun s : Source.St E => s.ex.journal.length) h
  change (2 : Nat) = 1 at counts
  omega

end Solidity.Backend.Executable.ConstructorStorageFailure
