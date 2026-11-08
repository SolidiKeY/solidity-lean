import Solidity.Lowering.Readonly.PrimitiveReads

/-! A nonempty primitive read statement lowered to an actual typed block
which evaluates the read and then drops its temporary. It does not replace a
call by an empty body or assert absence of reentry. P1 still links whole bodies. -/
namespace Solidity.Lowering.Readonly.ReadStatement
open Solidity.Source PrimitiveValues PrimitiveFields
variable {E : Env} {Γ : RCtx}

def target {C : Contract} {Ξ : Ctx} (name : Name) (p : PrimTy)
    (root : C.rootType name = some (.prim p)) : Solidity.Stmt C Ξ Ξ :=
  .block (.cons (.declLocal p (Var.ofName "_readonly_result")
    (some (.read (.root name root)))) .nil)

/-- The actual source expression statement returns its unchanged locals/state. -/
theorem source_run (global : Glob E) (frame : Fr) (n nps : Nat) (ph : Option (Ph E))
    {R : List STy} {M : Bool} {k : SCtx} (d : Decl) (p : PrimTy)
    (signature : d.varTy E = some (sourceTy p)) (locals : Locals E.layout Γ) (state : St E)
    (value : p.Denote)
    (evaluation : (evalE global frame (n + 1) (.state d signature)).run (locals, state) =
      (.ok (.val (toSource E.layout p value)), (locals, state))) :
    (execS global frame (n + 2) nps ph
      (RStmt.expr (R := R) (M := M) (k := k) (.state d signature)) locals).run (L0 E, state) =
      (.ok (.normal locals), (L0 E, state)) := by
  change evalE (plan := none) (calldataKnown := true) global frame (n + 1) (.state d signature) (locals, state) = _ at evaluation
  simp only [execS, EM.sub, bind, pure, ExceptT.bind, ExceptT.pure,
    ExceptT.bindCont, ExceptT.run, ExceptT.mk, StateT.bind, StateT.pure, evaluation]

/-- The target really evaluates the root, then restores all old typed locals
and state fields. The temporary cannot mask a failing read. -/
theorem target_run {C : Contract} {Ξ : Ctx} (state : Solidity.State C Ξ)
    (name : Name) (p : PrimTy) (root : C.rootType name = some (.prim p)) (value : p.Denote)
    (evaluation : (Solidity.Val.read (.root name root) : Solidity.Val C Ξ p).evalT state = .ok value) :
    (target name p root).run state = .ok ⟨state, List.prefix_refl _⟩ := by
  change TRun.block _ (TRun.seq (TRun.declLocal p (some (.read (.root name root)))) TRun.nil) state = _
  simp only [TRun.block, TRun.seq, TRun.declLocal]
  rw [evaluation]
  rfl

/-- Both actual statement runs follow from a complete checked field relation. -/
theorem simulation {C : Contract} {Ξ : Ctx} (global : Glob E) (frame : Fr)
    (n nps : Nat) (ph : Option (Ph E)) {R : List STy} {M : Bool} {k : SCtx}
    (fields : Fields E C.vars) (locals : Locals E.layout Γ) (source : St E)
    (targetState : Solidity.State C Ξ) (name : Name) (p : PrimTy)
    (root : C.rootType name = some (.prim p))
    (related : Rel fields frame.this (source.ex.world.accounts frame.this).storage targetState.storage) :
    ∃ binding : Binding E name p,
      (execS global frame (n + 2) nps ph
        (RStmt.expr (R := R) (M := M) (k := k) (.state binding.declaration binding.signature))
        locals).run (L0 E, source) = (.ok (.normal locals), (L0 E, source)) ∧
      (target name p root).run targetState = .ok ⟨targetState, List.prefix_refl _⟩ := by
  obtain ⟨binding, value, sourceRead, targetRead⟩ :=
    PrimitiveReads.root_expression global frame n fields locals source targetState name p root related
  exact ⟨binding, source_run global frame n nps ph binding.declaration p binding.signature locals source value sourceRead,
    target_run targetState name p root value targetRead⟩

/-- Arbitrary following code keeps its exact behavior, including its writes
and halts; only this proved primitive read/discard block is removed. -/
theorem target_then {C : Contract} {Ξ Δ : Ctx} (state : Solidity.State C Ξ)
    (name : Name) (p : PrimTy) (root : C.rootType name = some (.prim p)) (value : p.Denote)
    (evaluation : (Solidity.Val.read (.root name root) : Solidity.Val C Ξ p).evalT state = .ok value)
    (next : Prog C Ξ Δ) :
    Prog.run state (.cons (target name p root) next) = Prog.run state next := by
  rw [Prog.run_cons_ok (target_run state name p root value evaluation)]
  cases result : Prog.run state next with
  | error halt => rfl
  | ok output => cases output; rfl

end Solidity.Lowering.Readonly.ReadStatement
