import Solidity.Yul.RawGrowingBlock

/-! One typed LOCAL binder can close without changing the raw frame type.
Restoration and closure use actual Source operations. This supplies no
initializer execution, physical layout or general admission theorem.
Scope metadata and projection laws below are generic in the binder type; the
projection uses existing clean backups, not dirty-readback Source semantics. -/
namespace Solidity.Yul.RawTypedScope

def functionRead {ctx : Solidity.Source.Ctx} (state : RawFrame.State ctx)
    (cell : SourceFunctionCell ctx) : Word × Word :=
  cell.fields (RawCoherent.prepare state).1

def liftFunction {ctx : Solidity.Source.Ctx} (name : String) (ty : Solidity.Source.STy)
    (cell : SourceFunctionCell ctx) : SourceFunctionCell (ctx.push name ty) :=
  ⟨⟨.there cell.ref.index⟩,cell.shape⟩


/-- Read an occurrence from the authoritative raw view through actual preparation. -/
def scalarRead {ctx : Solidity.Source.Ctx} (state : RawFrame.State ctx)
    (cell : SourceScalarCell ctx) : Word :=
  cell.wordRead (RawCoherent.prepare state).1

/-- The same scalar occurrence under one intrinsically typed binder. -/
def liftScalar {ctx : Solidity.Source.Ctx} (name : String) (ty : Solidity.Source.STy)
    (cell : SourceScalarCell ctx) : SourceScalarCell (ctx.push name ty) :=
  ⟨⟨.there cell.ref.index⟩,cell.encoding,cell.shape⟩

def drop {ctx : Solidity.Source.Ctx} {name : String} {ty : Solidity.Source.STy}
    (state : RawFrame.State (ctx.push name ty)) : RawFrame.State ctx :=
  RawDeclarationFrame.ofSnapshot
    ⟨state.clean.drop 1,(RawCoherent.prepare state).1.2,state.world⟩
def close {ctx : Solidity.Source.Ctx} {name : String} {ty : Solidity.Source.STy}
    (result : Solidity.Source.R RawLoopBody.Flow × RawFrame.State (ctx.push name ty)) :
    Solidity.Source.R RawLoopBody.Flow × RawFrame.State ctx :=
  (result.1,drop result.2)
def project {ctx : Solidity.Source.Ctx} {name : String} {ty : Solidity.Source.STy}
    (result : Solidity.Source.R RawLoopBody.Flow × RawFrame.State (ctx.push name ty)) :
    Solidity.Source.R (Solidity.Source.Out ctx.env.layout ctx.tys ctx.tys) ×
      (Solidity.Source.Locals ctx.env.layout [] × Solidity.Source.St ctx.env) :=
  let actual := RawLoopBody.represented result
  ((actual.1.bind (fun out => out.up ctx.tys)).bind Solidity.Source.Out.close,actual.2)
end Solidity.Yul.RawTypedScope

namespace Solidity.Yul.RawTypedScope
theorem restore_drop : ∀ (ctx : Solidity.Source.Ctx) (name : String) (ty : Solidity.Source.STy)
 (locals : Solidity.Source.Locals ctx.env.layout (ctx.push name ty).tys),
 locals.restore ctx.tys = .ok (locals.drop 1) := by
  intro ctx name ty locals
  unfold Solidity.Source.Locals.restore
  have count : (ctx.push name ty).tys.length - ctx.tys.length = 1 := by
    change (ty :: ctx.tys).length - ctx.tys.length = 1
    simp only [List.length_cons]
    omega
  have suffix : (ctx.push name ty).tys.drop
      ((ctx.push name ty).tys.length - ctx.tys.length) = ctx.tys := by
    rw [count]
    rfl
  rw [dif_pos suffix]
  have dropped : ∀ (k : Nat) (one : k = 1)
      (back : (ctx.push name ty).tys.drop k = ctx.tys),
      ((back ▸ Solidity.Source.Locals.drop k locals) : Solidity.Source.Locals ctx.env.layout ctx.tys) = locals.drop 1 := by
    intro k one back
    subst k
    rfl
  rw [dropped _ count suffix]
  rfl

theorem drop_coherent : ∀ (ctx : Solidity.Source.Ctx) (name : String) (ty : Solidity.Source.STy)
 (state : Solidity.Yul.RawFrame.State (ctx.push name ty)),
 Solidity.Yul.RawCoherent.coherent state = true →
 Solidity.Yul.RawCoherent.coherent (Solidity.Yul.RawTypedScope.drop state) = true := by
  intro ctx name ty state same
  unfold drop
  rw [RawCoherent.prepare_coherent state same]
  apply (RawCoherent.coherent_iff _).mpr
  change localWordCells ctx (LocalValues.ofClean state.clean).2 =
    localWordCells ctx (LocalValues.ofClean (state.clean.drop 1))
  exact congrArg (localWordCells ctx)
    (LocalBoolItemScope.drop_clean ctx.env 1 (ctx.push name ty).tys state.clean)

/-- Existing scope projection commutes with typed closure even for incoherent raw inputs. This equates clean-backup projections, not Source execution or dirty-readback adequacy. -/
theorem project_close :
 ∀ (ctx : Solidity.Source.Ctx) (name : String) (ty : Solidity.Source.STy)
 (result : Solidity.Source.R Solidity.Yul.RawLoopBody.Flow × Solidity.Yul.RawFrame.State (ctx.push name ty)),
 Solidity.Yul.RawTypedScope.project result =
 Solidity.Yul.RawLoopBody.represented (Solidity.Yul.RawTypedScope.close result) := by
  intros ctx name ty result
  cases tag : result.1 with
  | error halt =>
    simp only [Solidity.Yul.RawTypedScope.close, Solidity.Yul.RawTypedScope.project,
      Solidity.Yul.RawLoopBody.represented, tag, Except.map]
    rfl
  | ok flow =>
    cases flow with
    | normal =>
      simp only [Solidity.Yul.RawTypedScope.close, Solidity.Yul.RawTypedScope.project,
        Solidity.Yul.RawLoopBody.represented, tag, Except.map,
        Solidity.Yul.RawLoopBody.out, Solidity.Source.Out.up, Solidity.Source.Out.close,
        Solidity.Yul.RawTypedScope.restore_drop ctx name ty, Except.bind]
      rfl
    | break_ h =>
      simp only [Solidity.Yul.RawTypedScope.close, Solidity.Yul.RawTypedScope.project,
        Solidity.Yul.RawLoopBody.represented, tag, Except.map,
        Solidity.Yul.RawLoopBody.out, Solidity.Source.Out.up, Solidity.Source.Out.close,
        Solidity.Yul.RawTypedScope.restore_drop ctx name ty, Except.bind]
      rfl
    | continue_ h =>
      simp only [Solidity.Yul.RawTypedScope.close, Solidity.Yul.RawTypedScope.project,
        Solidity.Yul.RawLoopBody.represented, tag, Except.map,
        Solidity.Yul.RawLoopBody.out, Solidity.Source.Out.up, Solidity.Source.Out.close,
        Solidity.Yul.RawTypedScope.restore_drop ctx name ty, Except.bind]
      rfl
    | leave_ h => cases h

theorem close_correct : ∀ (ctx : Solidity.Source.Ctx) (name : String) (ty : Solidity.Source.STy)
 (result : Solidity.Source.R Solidity.Yul.RawLoopBody.Flow × Solidity.Yul.RawFrame.State (ctx.push name ty)),
 Solidity.Yul.RawCoherent.coherent result.2 = true →
 Solidity.Yul.RawCoherent.coherent (Solidity.Yul.RawTypedScope.close result).2 = true ∧
 Solidity.Yul.RawTypedScope.project result = Solidity.Yul.RawLoopBody.represented (Solidity.Yul.RawTypedScope.close result) := by
  intro ctx name ty result same
  exact ⟨drop_coherent ctx name ty result.2 same, project_close ctx name ty result⟩

theorem bool_drop_eq : ∀ (ctx : Solidity.Source.Ctx) (name : String)
 (state : Solidity.Yul.RawFrame.State (ctx.push name .bool)),
 Solidity.Yul.RawTypedScope.drop state = Solidity.Yul.RawGrowingBlock.drop state := by
  intro ctx name state
  rfl

theorem bool_close_eq : ∀ (ctx : Solidity.Source.Ctx) (name : String)
 (result : Solidity.Source.R Solidity.Yul.RawLoopBody.Flow × Solidity.Yul.RawFrame.State (ctx.push name .bool)),
 Solidity.Yul.RawTypedScope.close result = Solidity.Yul.RawGrowingBlock.close (.inr result) := by
  intro ctx name result
  rfl

theorem lift_scalar_read : ∀ (ctx : Solidity.Source.Ctx) (name : String) (ty : Solidity.Source.STy)
 (cell : Solidity.Yul.SourceScalarCell ctx)
 (locals : Solidity.Yul.LocalValues ctx.env (ctx.push name ty).tys),
 (Solidity.Yul.RawTypedScope.liftScalar name ty cell).wordRead locals = cell.wordRead locals.2 := by
  intro ctx name ty cell locals
  rfl

/-- Capture preserves every scalar word, including dirty high bits. -/
theorem scalarRead_capture : ∀ (ctx : Solidity.Source.Ctx) (state : Solidity.Yul.RawFrame.State ctx)
 (next : Solidity.Yul.LocalState ctx.env ctx.tys) (cell : Solidity.Yul.SourceScalarCell ctx),
 Solidity.Yul.RawTypedScope.scalarRead (Solidity.Yul.RawCoherent.capture state next) cell =
 cell.wordRead next.1 := by
  intro ctx state next cell
  obtain ⟨ref,selected⟩ := sourceScalarAt_surjective ctx cell
  rw [← selected]
  change localWordCells ctx (RawCoherent.prepare (RawCoherent.capture state next)).1 (.scalar ref) =
    localWordCells ctx next.1 (.scalar ref)
  rw [RawCoherent.prepare_view,RawCoherent.capture_view]

theorem scalarRead_agrees : ∀ (ctx : Solidity.Source.Ctx) (first second : Solidity.Yul.RawFrame.State ctx),
 Solidity.Yul.RawFrame.view first = Solidity.Yul.RawFrame.view second →
 ∀ (cell : Solidity.Yul.SourceScalarCell ctx),
 Solidity.Yul.RawTypedScope.scalarRead first cell = Solidity.Yul.RawTypedScope.scalarRead second cell := by
  intro ctx first second same cell
  obtain ⟨ref,selected⟩ := sourceScalarAt_surjective ctx cell
  rw [← selected]
  change localWordCells ctx (RawCoherent.prepare first).1 (.scalar ref) =
    localWordCells ctx (RawCoherent.prepare second).1 (.scalar ref)
  rw [RawCoherent.prepare_view,RawCoherent.prepare_view,same]

/-- Scalar projection through one binder close needs no coherence premise. -/
theorem drop_scalar_read : ∀ (ctx : Solidity.Source.Ctx) (name : String) (ty : Solidity.Source.STy)
 (state : Solidity.Yul.RawFrame.State (ctx.push name ty)) (cell : Solidity.Yul.SourceScalarCell ctx),
 Solidity.Yul.RawTypedScope.scalarRead (Solidity.Yul.RawTypedScope.drop state) cell =
 Solidity.Yul.RawTypedScope.scalarRead state (Solidity.Yul.RawTypedScope.liftScalar name ty cell) := by
  intro ctx name ty state cell
  obtain ⟨ref,selected⟩ := sourceScalarAt_surjective ctx cell
  rw [← selected]
  change localWordCells ctx (RawCoherent.prepare (drop state)).1 (.scalar ref) =
    (liftScalar name ty (sourceScalarAt ctx ref)).wordRead (RawCoherent.prepare state).1
  rw [RawCoherent.prepare_view]
  change (sourceScalarAt ctx ref).wordRead (RawCoherent.prepare state).1.2 =
    (liftScalar name ty (sourceScalarAt ctx ref)).wordRead (RawCoherent.prepare state).1
  exact (lift_scalar_read ctx name ty (sourceScalarAt ctx ref) (RawCoherent.prepare state).1).symm

theorem drop_scalar_agrees : ∀ (ctx : Solidity.Source.Ctx) (name : String) (ty : Solidity.Source.STy)
 (first second : Solidity.Yul.RawFrame.State (ctx.push name ty)),
 Solidity.Yul.RawFrame.view first = Solidity.Yul.RawFrame.view second →
 ∀ (cell : Solidity.Yul.SourceScalarCell ctx),
 Solidity.Yul.RawTypedScope.scalarRead (Solidity.Yul.RawTypedScope.drop first) cell =
 Solidity.Yul.RawTypedScope.scalarRead (Solidity.Yul.RawTypedScope.drop second) cell := by
  intro ctx name ty first second same cell
  rw [drop_scalar_read,drop_scalar_read]
  exact scalarRead_agrees _ _ _ same _

theorem lift_function_fields : ∀ (ctx : Solidity.Source.Ctx) (name : String) (ty : Solidity.Source.STy)
 (cell : Solidity.Yul.SourceFunctionCell ctx)
 (locals : Solidity.Yul.LocalValues ctx.env (ctx.push name ty).tys),
 (Solidity.Yul.RawTypedScope.liftFunction name ty cell).fields locals = cell.fields locals.2 := by
  intro ctx name ty cell locals
  rfl

theorem functionRead_at : ∀ (ctx : Solidity.Source.Ctx) (state : Solidity.Yul.RawFrame.State ctx)
 (index : Solidity.Yul.Member (Solidity.Yul.localExternalTypes ctx) .externalFunction),
 Solidity.Yul.RawTypedScope.functionRead state (Solidity.Yul.sourceFunctionAt ctx index) =
 (Solidity.Yul.RawFrame.view state (.address index),Solidity.Yul.RawFrame.view state (.selector index)) := by
  intro ctx state index
  apply Prod.ext
  · change localWordCells ctx (RawCoherent.prepare state).1 (.address index) =
      RawFrame.view state (.address index)
    exact congrFun (RawCoherent.prepare_view state) _
  · change localWordCells ctx (RawCoherent.prepare state).1 (.selector index) =
      RawFrame.view state (.selector index)
    exact congrFun (RawCoherent.prepare_view state) _

theorem functionRead_capture : ∀ (ctx : Solidity.Source.Ctx) (state : Solidity.Yul.RawFrame.State ctx)
 (next : Solidity.Yul.LocalState ctx.env ctx.tys) (cell : Solidity.Yul.SourceFunctionCell ctx),
 Solidity.Yul.RawTypedScope.functionRead (Solidity.Yul.RawCoherent.capture state next) cell =
 cell.fields next.1 := by
  intro ctx state next cell
  obtain ⟨index,selected⟩ := sourceFunctionAt_surjective ctx cell
  rw [← selected,functionRead_at]
  rfl

theorem functionRead_agrees : ∀ (ctx : Solidity.Source.Ctx) (first second : Solidity.Yul.RawFrame.State ctx),
 Solidity.Yul.RawFrame.view first = Solidity.Yul.RawFrame.view second →
 ∀ (cell : Solidity.Yul.SourceFunctionCell ctx),
 Solidity.Yul.RawTypedScope.functionRead first cell = Solidity.Yul.RawTypedScope.functionRead second cell := by
  intro ctx first second same cell
  obtain ⟨index,selected⟩ := sourceFunctionAt_surjective ctx cell
  rw [← selected,functionRead_at,functionRead_at,same]

theorem drop_function_read : ∀ (ctx : Solidity.Source.Ctx) (name : String) (ty : Solidity.Source.STy)
 (state : Solidity.Yul.RawFrame.State (ctx.push name ty)) (cell : Solidity.Yul.SourceFunctionCell ctx),
 Solidity.Yul.RawTypedScope.functionRead (Solidity.Yul.RawTypedScope.drop state) cell =
 Solidity.Yul.RawTypedScope.functionRead state (Solidity.Yul.RawTypedScope.liftFunction name ty cell) := by
  intro ctx name ty state cell
  obtain ⟨index,selected⟩ := sourceFunctionAt_surjective ctx cell
  rw [← selected,functionRead_at]
  change (sourceFunctionAt ctx index).fields (RawCoherent.prepare state).1.2 =
    (liftFunction name ty (sourceFunctionAt ctx index)).fields (RawCoherent.prepare state).1
  exact (lift_function_fields ctx name ty (sourceFunctionAt ctx index) (RawCoherent.prepare state).1).symm

theorem drop_function_agrees : ∀ (ctx : Solidity.Source.Ctx) (name : String) (ty : Solidity.Source.STy)
 (first second : Solidity.Yul.RawFrame.State (ctx.push name ty)),
 Solidity.Yul.RawFrame.view first = Solidity.Yul.RawFrame.view second →
 ∀ (cell : Solidity.Yul.SourceFunctionCell ctx),
 Solidity.Yul.RawTypedScope.functionRead (Solidity.Yul.RawTypedScope.drop first) cell =
 Solidity.Yul.RawTypedScope.functionRead (Solidity.Yul.RawTypedScope.drop second) cell := by
  intro ctx name ty first second same cell
  rw [drop_function_read,drop_function_read]
  exact functionRead_agrees _ _ _ same _

/-- Actual binder close respects the complete authoritative word view. -/
theorem drop_view_agrees : ∀ (ctx : Solidity.Source.Ctx) (name : String) (ty : Solidity.Source.STy)
 (first second : Solidity.Yul.RawFrame.State (ctx.push name ty)),
 Solidity.Yul.RawFrame.view first = Solidity.Yul.RawFrame.view second →
 Solidity.Yul.RawFrame.view (Solidity.Yul.RawTypedScope.drop first) =
 Solidity.Yul.RawFrame.view (Solidity.Yul.RawTypedScope.drop second) := by
  intro ctx name ty first second same
  funext cell
  cases cell with
  | scalar ref =>
    have projected := drop_scalar_agrees ctx name ty first second same (sourceScalarAt ctx ref)
    change localWordCells ctx (RawCoherent.prepare (drop first)).1 (.scalar ref) =
      localWordCells ctx (RawCoherent.prepare (drop second)).1 (.scalar ref) at projected
    rw [RawCoherent.prepare_view,RawCoherent.prepare_view] at projected
    exact projected
  | address index =>
    have projected := drop_function_agrees ctx name ty first second same (sourceFunctionAt ctx index)
    rw [functionRead_at,functionRead_at] at projected
    exact congrArg Prod.fst projected
  | selector index =>
    have projected := drop_function_agrees ctx name ty first second same (sourceFunctionAt ctx index)
    rw [functionRead_at,functionRead_at] at projected
    exact congrArg Prod.snd projected


/-- Typed scope removal retains the existing clean backup tail. -/
theorem drop_clean :
 ∀ (ctx : Solidity.Source.Ctx) (name : String) (ty : Solidity.Source.STy)
 (state : Solidity.Yul.RawFrame.State (ctx.push name ty)), (Solidity.Yul.RawTypedScope.drop state).clean = state.clean.drop 1 := by
  intros; rfl

/-- Typed scope removal preserves the complete represented world. -/
theorem drop_world :
 ∀ (ctx : Solidity.Source.Ctx) (name : String) (ty : Solidity.Source.STy)
 (state : Solidity.Yul.RawFrame.State (ctx.push name ty)), (Solidity.Yul.RawTypedScope.drop state).world = state.world := by
  intros; rfl

/-- Scope closure produces the existing full word snapshot, not a sparse write set. -/
theorem close_captured :
 ∀ (ctx : Solidity.Source.Ctx) (name : String) (ty : Solidity.Source.STy)
 (result : Solidity.Source.R Solidity.Yul.RawLoopBody.Flow × Solidity.Yul.RawFrame.State (ctx.push name ty)),
 Solidity.Yul.RawFrame.capture (Solidity.Yul.RawTypedScope.close result).2
   (Solidity.Yul.RawFrame.view (Solidity.Yul.RawTypedScope.close result).2) =
 (Solidity.Yul.RawTypedScope.close result).2 := by
  intros; rfl



end Solidity.Yul.RawTypedScope
