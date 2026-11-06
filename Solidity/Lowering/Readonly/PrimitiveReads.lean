import Solidity.Lowering.Readonly.PrimitiveFields
import Solidity.Semantics.Run

/-! Actual source primitive reads under a checked field relation. No body,
compiler or ABI result is supplied by a detached observation function. -/
namespace Solidity.Lowering.Readonly.PrimitiveReads
open Solidity.Source PrimitiveValues PrimitiveFields
variable {E : Env} {Γ : RCtx}

private theorem cancel {D : Solidity.Source.Layout} {τ σ : STy} (h : τ = σ)
    (value : Solidity.Source.Val D σ) : h ▸ (h.symm ▸ value) = value := by
  cases h
  rfl

theorem read_of_read (frame : Fr) (path : Solidity.Source.SPath) (p : PrimTy)
    (typed : E.cellTy path = sourceTy p) (persistent : E.transientRoot path = false)
    (locals : Locals E.layout Γ) (state : St E) (value : p.Denote)
    (read : (state.ex.world.accounts frame.this).storage.read path = some
      (show Solidity.Source.Val E.layout (E.cellTy path) from typed.symm ▸ toSource E.layout p value)) :
    (readAt frame path (sourceTy p) : EM E Γ _).run (locals, state) =
      (.ok (toSource E.layout p value), (locals, state)) := by
  simp only [readAt, readCell, EM.st, persistent, Bool.false_eq_true, ↓reduceIte, read, dif_pos typed,
    cancel, EM.halt, bind, pure, ExceptT.bind, ExceptT.pure, ExceptT.bindCont,
    ExceptT.run, ExceptT.mk, StateT.bind, StateT.pure, StateT.get, get, getThe,
    MonadStateOf.get, liftM, monadLift, MonadLift.monadLift, ExceptT.lift,
    Functor.map, StateT.map]

theorem read_head (frame : Fr) (name : Name) (p : PrimTy) (d : Decl)
    (declared : E.declOf .stateVar ⟨d.scope, d.name⟩ = some d)
    (named : name = d.name) (signature : d.varTy E = some (sourceTy p))
    (typed : E.cellTy d.path = sourceTy p) (persistent : E.transientRoot d.path = false)
    (notConst : d.isConst = false) {fs : List (Name × Ty)} (tail : Fields E fs)
    (value : p.Denote) (rest : SFields fs) (locals : Locals E.layout Γ) (state : St E)
    (related : Rel (.field name p d declared named signature typed persistent notConst tail)
      frame.this (state.ex.world.accounts frame.this).storage (.cons (.prim value) rest)) :
    (readAt frame d.path (sourceTy p) : EM E Γ _).run (locals, state) =
      (.ok (toSource E.layout p value), (locals, state)) := by
  exact read_of_read frame d.path p typed persistent locals state value related.1

/-- The corresponding actual intrinsic root-read operations return that same
primitive value. This is a semantic read fact, not a byte observation oracle. -/
theorem target_read_head (name : Name) (p : PrimTy) {fs : List (Name × Ty)}
    (value : p.Denote) (rest : SFields fs)
    (lookup : Solidity.Semantics.lookupBy name ((name, .prim p) :: fs) = some (.prim p)) :
    ((SFields.cons (.prim value) rest).get lookup).find .nil = some (.prim value) := by
  rw [SFields.get_cons]
  simp only []
  rfl

private theorem run_bind {α β : Type} (m : EM E Γ α) (k : α → EM E Γ β)
    (x : Locals E.layout Γ × St E) :
    (m >>= k).run x = match m.run x with
      | (.ok a, y) => (k a).run y
      | (.error h, y) => (.error h, y) := by
  rw [ExceptT.run_bind]
  show StateT.bind (ExceptT.run m) _ x = _
  simp only [StateT.bind]
  rcases m.run x with ⟨r, y⟩
  cases r <;> rfl

/-- The actual source state expression follows the certified primitive read;
constant and reference branches cannot be silently selected. -/
theorem source_expression (global : Glob E) (frame : Fr) (n : Nat) (d : Decl) (p : PrimTy)
    (signature : d.varTy E = some (sourceTy p)) (notConst : d.isConst = false)
    (typed : E.cellTy d.path = sourceTy p) (persistent : E.transientRoot d.path = false)
    (locals : Locals E.layout Γ) (state : St E) (value : p.Denote)
    (read : (state.ex.world.accounts frame.this).storage.read d.path = some
      (show Solidity.Source.Val E.layout (E.cellTy d.path) from typed.symm ▸ toSource E.layout p value)) :
    (evalE global frame (n + 1) (.state d signature)).run (locals, state) =
      (.ok (.val (toSource E.layout p value)), (locals, state)) := by
  have byValue : (sourceTy p).byRef = false := by cases p <;> rfl
  simp only [evalE, notConst, Bool.false_eq_true, ↓reduceIte, byValue]
  rw [run_bind, read_of_read frame d.path p typed persistent locals state value read]
  rfl

/-- Actual intrinsic expression execution at the same primitive root value. -/
theorem target_expression {C : Contract} {Ξ : Ctx} (state : Solidity.State C Ξ)
    (name : Name) (p : PrimTy) (root : C.rootType name = some (.prim p)) (value : p.Denote)
    (read : state.storage.find (SRef.ofRoot name root) = some (.prim value)) :
    (Solidity.Val.read (.root name root) : Solidity.Val C Ξ p).evalT state = .ok value := by
  simp only [Solidity.Val.evalT, Loc.resolveT]
  change (do let v ← TRes.ofOpt (state.storage.find (SRef.ofRoot name root)); pure v.view) = _
  rw [read]
  rfl

/-- Full primitive named-root read simulation between the ACTUAL evaluators.
The checked relation selects the source declaration and target value, so neither
read equality is assumed separately. Frame/code/whole-body lowering is separate. -/
theorem root_expression {C : Contract} {Ξ : Ctx} (global : Glob E) (frame : Fr) (n : Nat)
    (fields : Fields E C.vars) (locals : Locals E.layout Γ) (source : St E)
    (target : Solidity.State C Ξ) (name : Name) (p : PrimTy)
    (root : C.rootType name = some (.prim p))
    (related : Rel fields frame.this (source.ex.world.accounts frame.this).storage target.storage) :
    ∃ binding : Binding E name p, ∃ value : p.Denote,
      (evalE global frame (n + 1) (.state binding.declaration binding.signature)).run (locals, source) =
        (.ok (.val (toSource E.layout p value)), (locals, source)) ∧
      (Solidity.Val.read (.root name root) : Solidity.Val C Ξ p).evalT target = .ok value := by
  obtain ⟨binding, value, sourceRead, targetRead⟩ :=
    PrimitiveFields.select fields frame.this (source.ex.world.accounts frame.this).storage
      target.storage name p root related
  refine ⟨binding, value, ?_, ?_⟩
  · exact source_expression global frame n binding.declaration p binding.signature binding.notConst
      binding.typed binding.persistent locals source value sourceRead
  · apply target_expression target name p root value
    change (target.storage.get root).find .nil = some (.prim value)
    rw [targetRead]
    rfl

end Solidity.Lowering.Readonly.PrimitiveReads
