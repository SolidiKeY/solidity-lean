import Solidity.Lowering.Readonly.ReadStatement

/-! Guard vacuous empty layouts and constant/head-only primitive readers.
The SAME two declared Bool fields, nonempty locals, Source store and intrinsic
store instantiate primitive read interfaces and their read-statement extension.
True at the head and false
at the tail distinguish selected names and actual values. This is joint premise
satisfiability and primitive evaluator checking, not compiler/call/frame adequacy. -/
namespace Solidity.H62.ReadonlyAudit.PrimitiveReadWitnesses
open Solidity Solidity.Source Solidity.Lowering.Readonly
open PrimitiveValues PrimitiveFields

def first : Decl := ⟨.stateVar,"a",none,false,
  .stateVar (.elem .bool) none none none false "a" .none⟩
def second : Decl := ⟨.stateVar,"b",none,false,
  .stateVar (.elem .bool) none none none false "b" .none⟩
def environment : Env := ⟨[first,second]⟩
def contract : Contract := { vars := [("a",.prim .bool),("b",.prim .bool)] }
def fields : Fields environment contract.vars :=
  .field "a" .bool first rfl rfl rfl rfl rfl rfl
    (.field "b" .bool second rfl rfl rfl rfl rfl rfl .nil)
def address : Solidity.Roadmap.Address := ⟨0,by decide⟩
def frame : Fr := { this := address, sender := address, value := ⟨0,by decide⟩, static := true, contract := "" }
def source : St environment :=
  { ex := { world := ⟨fun a => { Account.empty (D := environment.layout) (environment.lay a) with
        storage := (Solidity.Source.Storage.empty : Solidity.Source.Storage environment.layout (environment.lay a)).write first.path (.bool true) }⟩
            transient := ⟨fun _ => Storage.empty⟩, journal := [] }
    heap := Solidity.Source.Heap.empty, events := [], logs := [], fnLocals := ⟨[],.nil⟩ }
def locals : Locals environment.layout [.bool] := .cons (.bool true) .nil
def target : Solidity.Storage contract := .cons (.prim (p := .bool) true) (.cons (.prim (p := .bool) false) .nil)
def targetState : Solidity.State contract [] := Solidity.State.ofStorage target

theorem related : Rel fields address (source.ex.world.accounts address).storage target :=
  ⟨rfl,rfl,True.intro⟩

theorem read_value_joint : ∃ value : PrimTy.bool.Denote,
    (source.ex.world.accounts address).storage.read second.path =
      some (show Solidity.Source.Val environment.layout (environment.cellTy second.path) from
        (rfl : environment.cellTy second.path = sourceTy .bool).symm ▸ toSource environment.layout .bool value) :=
  PrimitiveFields.read_value address _ second.path .bool rfl

theorem total_joint : ∃ out : SFields contract.vars,
    Rel fields address (source.ex.world.accounts address).storage out :=
  PrimitiveFields.total fields address _

theorem unique_joint :
    Rel fields address (source.ex.world.accounts address).storage target ∧
    Rel fields address (source.ex.world.accounts address).storage target ∧ target = target :=
  ⟨related,related,PrimitiveFields.unique fields address _ target target related related⟩

theorem select_joint : ∃ binding : Binding environment "b" .bool, ∃ value : PrimTy.bool.Denote,
    (source.ex.world.accounts address).storage.read binding.declaration.path = some
      (show Solidity.Source.Val environment.layout (environment.cellTy binding.declaration.path) from
        binding.typed.symm ▸ toSource environment.layout .bool value) ∧
    target.get (f := "b") (by rfl) = .prim value :=
  PrimitiveFields.select fields address _ target "b" .bool rfl related

theorem read_of_read_joint :
    (readAt frame second.path (sourceTy .bool) : EM environment [.bool] _).run (locals,source) =
      (.ok (.bool false),(locals,source)) :=
  PrimitiveReads.read_of_read frame second.path .bool rfl rfl locals source false rfl

theorem read_head_joint :
    (readAt frame first.path (sourceTy .bool) : EM environment [.bool] _).run (locals,source) =
      (.ok (.bool true),(locals,source)) :=
  PrimitiveReads.read_head frame "a" .bool first rfl rfl rfl rfl rfl rfl
    (.field "b" .bool second rfl rfl rfl rfl rfl rfl .nil) true
    (.cons (.prim (p := .bool) false) .nil) locals source related

theorem target_read_head_joint :
    (target.get (f := "a") (by rfl)).find .nil = some (.prim (p := .bool) true) :=
  PrimitiveReads.target_read_head "a" .bool true (.cons (.prim (p := .bool) false) .nil) rfl

theorem target_expression_joint :
    (Solidity.Val.read (.root "b" rfl) : Solidity.Val contract [] .bool).evalT targetState = .ok false :=
  PrimitiveReads.target_expression targetState "b" .bool rfl false rfl

/-- Nonempty state and different values are observable at both evaluators. -/
theorem distinct_reads :
    (readAt frame first.path (sourceTy .bool) : EM environment [.bool] _).run (locals,source) =
      (.ok (.bool true),(locals,source)) ∧
    (readAt frame second.path (sourceTy .bool) : EM environment [.bool] _).run (locals,source) =
      (.ok (.bool false),(locals,source)) := ⟨read_head_joint,read_of_read_joint⟩

/-- A head-only/constant-true target reader cannot satisfy the tail outcome. -/
theorem head_only_refused :
    (Solidity.Val.read (.root "b" rfl) : Solidity.Val contract [] .bool).evalT targetState ≠ .ok true := by
  rw [target_expression_joint]
  intro same
  cases same


/-- Explicit global records are inhabited at the SAME actual expression inputs.
No callee/body execution is inferred from their existence. -/
def global : Glob environment where
  prog := { body := fun _ => none, consts := fun _ => none, inits := fun _ => [],
            ctor := fun _ => none, ctorLocals := fun _ => [], baseArgs := fun _ => [], contracts := [] }
  pipeline := .legacy
  fixed := { evm := { keccak := fun _ => 0, keccak_lt := fun _ => by decide,
                      precompile := fun _ _ => none, precompileGas := fun _ _ => 0 },
             ledger := fun balance _ a => balance a, regionLen := 1, rootSlots := 1 }
  balance0 := fun _ => ⟨0,by decide⟩
  hasCode := fun _ _ => false
  callee := fun _ => .answer (.success [])
  timestamp := ⟨0,by decide⟩

def targetWithLocal : Solidity.State contract [.val .bool] := targetState.push (t := .val .bool) true

def writing : Prog contract [.val .bool] [.val .bool] :=
  .cons (.assign (.root "a" rfl) (.val (.simple (.bool false)))) .nil

theorem source_expression_joint :
    (evalE global frame 1 (.state second rfl)).run (locals,source) =
      (.ok (.val (.bool false)),(locals,source)) :=
  PrimitiveReads.source_expression global frame 0 second .bool rfl rfl rfl rfl locals source false rfl

theorem root_expression_joint : ∃ binding : Binding environment "b" .bool, ∃ value : PrimTy.bool.Denote,
    (evalE global frame 1 (.state binding.declaration binding.signature)).run (locals,source) =
      (.ok (.val (toSource environment.layout .bool value)),(locals,source)) ∧
    (Solidity.Val.read (.root "b" rfl) : Solidity.Val contract [.val .bool] .bool).evalT targetWithLocal = .ok value :=
  PrimitiveReads.root_expression global frame 0 fields locals source targetWithLocal "b" .bool rfl related

theorem source_statement_joint :
    (execS global frame 2 0 none
      (RStmt.expr (R := []) (M := false) (k := .body) (.state second rfl)) locals).run (L0 environment,source) =
      (.ok (.normal locals),(L0 environment,source)) :=
  ReadStatement.source_run global frame 0 0 none second .bool rfl locals source false source_expression_joint

theorem target_statement_joint :
    (ReadStatement.target "b" .bool (C := contract) (Ξ := [.val .bool]) rfl).run targetWithLocal =
      .ok ⟨targetWithLocal,List.prefix_refl _⟩ :=
  ReadStatement.target_run targetWithLocal "b" .bool rfl false
    (PrimitiveReads.target_expression targetWithLocal "b" .bool rfl false rfl)

theorem statement_simulation_joint : ∃ binding : Binding environment "b" .bool,
    (execS global frame 2 0 none
      (RStmt.expr (R := []) (M := false) (k := .body) (.state binding.declaration binding.signature))
      locals).run (L0 environment,source) = (.ok (.normal locals),(L0 environment,source)) ∧
    (ReadStatement.target "b" .bool (C := contract) (Ξ := [.val .bool]) rfl).run targetWithLocal =
      .ok ⟨targetWithLocal,List.prefix_refl _⟩ :=
  ReadStatement.simulation global frame 0 0 none fields locals source targetWithLocal "b" .bool rfl related

theorem continuation_joint :
    Prog.run targetWithLocal (.cons (ReadStatement.target "b" .bool rfl) writing) =
      Prog.run targetWithLocal writing :=
  ReadStatement.target_then targetWithLocal "b" .bool rfl false
    (PrimitiveReads.target_expression targetWithLocal "b" .bool rfl false rfl) writing

/-- The following write and original typed local survive the read/discard block. -/
theorem continuation_writes : ∃ out,
    Prog.run targetWithLocal (.cons (ReadStatement.target "b" .bool rfl) writing) = .ok out ∧
      out.st.env.1 = true ∧ out.st.storage.get (f := "a") (by rfl) = .prim (p := .bool) false :=
  ⟨_,rfl,rfl,rfl⟩

/-- A following revert cannot be erased by removing the proved read/discard. -/
theorem continuation_reverts :
    Prog.run targetWithLocal (.cons (ReadStatement.target "b" .bool rfl) (.cons .revert .nil)) = .error .revert := by
  rw [ReadStatement.target_then targetWithLocal "b" .bool rfl false
    (PrimitiveReads.target_expression targetWithLocal "b" .bool rfl false rfl)]
  rfl

end Solidity.H62.ReadonlyAudit.PrimitiveReadWitnesses
