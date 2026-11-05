import Solidity.Yul.RawGrowingForPost
import Solidity.Yul.Checks.RawGrowingBlock
/-! Kernel-only growing for/post witnesses. The initializer binds the guard's
Boolean, body changes an older local, post clears the bound guard and scope
exit retains older changes. No general initializer/admission claim. -/
namespace Solidity.Yul.Checks.RawGrowingForPost
namespace Old
export Solidity.Yul.Checks.RawGrowingBlock.Old (ctx env grown initial clean canonical declaration)
export Solidity.Yul.Checks.RawGrowingBlock (copyItems copyTail afterClean captured)
export Solidity.Yul.Checks.RawPreparedDeclaration (test breakBody)
export Solidity.Yul.Checks.RawGrowingSequence (continueBody)
end Old
def clear : LocalBoolControl.Supported Old.env Old.grown.tys
 (.assign (.local .here) (.bool false)) := .assign .here (.base (.literal false))
def clearOuter : LocalBoolControl.Supported Old.env Old.grown.tys
 (.assign (.local (.there (.there (.there .here)))) (.bool false)) :=
 .assign (.there (.there (.there .here))) (.base (.literal false))
def partialPost : LocalBoolControl.Supported Old.env Old.grown.tys
 (.binary .or (.assign (.local .here) (.bool false))
  (.unary .not (.unary .not (.local .here)))) := .or clear (.not (.not Old.test))
def body : RawCheckedAdapter.Adapter Old.grown [] false false (.block Old.copyItems) :=
 RawCheckedAdapterSequence.block Old.copyTail
def packed := RawGrowingForPost.adapter Old.ctx "tmp" true [] false false _ _ _ Old.test clear body
def frame (value : Bool) (locals : Solidity.Source.Locals Old.env.layout Old.ctx.tys)
 (world : Solidity.Source.St Old.env) : RawFrame.State Old.grown :=
 RawDeclarationFrame.ofSnapshot
  ⟨.cons (.bool value) locals,LocalValues.ofClean (.cons (.bool value) locals),world⟩
def program : Solidity.Source.RStmt Old.env [] false ⟨true,false⟩ Old.ctx.tys Old.ctx.tys :=
 .forLoop (l := true) Old.declaration (.some (.local .here))
  (.some (.assign (.local .here) (.bool false))) (.block Old.copyItems)
def witness : Nonempty (RawCheckedAdapter.Adapter Old.ctx [] false false program) := ⟨packed⟩
end Solidity.Yul.Checks.RawGrowingForPost

namespace Solidity.Yul.Checks.RawGrowingForPost
theorem guardTrue10 : ∀ (world : Solidity.Source.St Solidity.Yul.Checks.RawGrowingForPost.Old.env), Solidity.Yul.RawCondition.eval Solidity.Yul.Checks.RawGrowingForPost.Old.test 10 (Solidity.Yul.Checks.RawGrowingForPost.frame true Solidity.Yul.Checks.RawGrowingForPost.Old.clean world) = (.ok true,Solidity.Yul.Checks.RawGrowingForPost.frame true Solidity.Yul.Checks.RawGrowingForPost.Old.clean world) := by
  intro world
  rfl

theorem guardTrue3 : ∀ (world : Solidity.Source.St Solidity.Yul.Checks.RawGrowingForPost.Old.env), Solidity.Yul.RawCondition.eval Solidity.Yul.Checks.RawGrowingForPost.Old.test 3 (Solidity.Yul.Checks.RawGrowingForPost.frame true Solidity.Yul.Checks.RawGrowingForPost.Old.clean world) = (.ok true,Solidity.Yul.Checks.RawGrowingForPost.frame true Solidity.Yul.Checks.RawGrowingForPost.Old.clean world) := by
  intro world
  rfl

theorem bodyCopy10 : ∀ (pipeline : Solidity.Roadmap.Pipeline) (world : Solidity.Source.St Solidity.Yul.Checks.RawGrowingForPost.Old.env), Solidity.Yul.Checks.RawGrowingForPost.body.run pipeline 10 (Solidity.Yul.Checks.RawGrowingForPost.frame true Solidity.Yul.Checks.RawGrowingForPost.Old.clean world) = (.ok .normal,Solidity.Yul.Checks.RawGrowingForPost.frame true Solidity.Yul.Checks.RawGrowingForPost.Old.afterClean world) := by
  intro pipeline world
  rfl

theorem clearCopy10 : ∀ (world : Solidity.Source.St Solidity.Yul.Checks.RawGrowingForPost.Old.env), Solidity.Yul.RawSourceForPost.discard Solidity.Yul.Checks.RawGrowingForPost.clear 10 (Solidity.Yul.Checks.RawGrowingForPost.frame true Solidity.Yul.Checks.RawGrowingForPost.Old.afterClean world) = (.ok (),Solidity.Yul.Checks.RawGrowingForPost.frame false Solidity.Yul.Checks.RawGrowingForPost.Old.afterClean world) := by
  intro world
  rfl

theorem falseCopy9 : ∀ (world : Solidity.Source.St Solidity.Yul.Checks.RawGrowingForPost.Old.env), Solidity.Yul.RawCondition.eval Solidity.Yul.Checks.RawGrowingForPost.Old.test 9 (Solidity.Yul.Checks.RawGrowingForPost.frame false Solidity.Yul.Checks.RawGrowingForPost.Old.afterClean world) = (.ok false,Solidity.Yul.Checks.RawGrowingForPost.frame false Solidity.Yul.Checks.RawGrowingForPost.Old.afterClean world) := by
  intro world
  rfl

theorem clearOld10 : ∀ (world : Solidity.Source.St Solidity.Yul.Checks.RawGrowingForPost.Old.env), Solidity.Yul.RawSourceForPost.discard Solidity.Yul.Checks.RawGrowingForPost.clear 10 (Solidity.Yul.Checks.RawGrowingForPost.frame true Solidity.Yul.Checks.RawGrowingForPost.Old.clean world) = (.ok (),Solidity.Yul.Checks.RawGrowingForPost.frame false Solidity.Yul.Checks.RawGrowingForPost.Old.clean world) := by
  intro world
  rfl

theorem falseOld9 : ∀ (world : Solidity.Source.St Solidity.Yul.Checks.RawGrowingForPost.Old.env), Solidity.Yul.RawCondition.eval Solidity.Yul.Checks.RawGrowingForPost.Old.test 9 (Solidity.Yul.Checks.RawGrowingForPost.frame false Solidity.Yul.Checks.RawGrowingForPost.Old.clean world) = (.ok false,Solidity.Yul.Checks.RawGrowingForPost.frame false Solidity.Yul.Checks.RawGrowingForPost.Old.clean world) := by
  intro world
  rfl

theorem partialOld3 : ∀ (world : Solidity.Source.St Solidity.Yul.Checks.RawGrowingForPost.Old.env), Solidity.Yul.RawSourceForPost.discard Solidity.Yul.Checks.RawGrowingForPost.partialPost 3 (Solidity.Yul.Checks.RawGrowingForPost.frame true Solidity.Yul.Checks.RawGrowingForPost.Old.clean world) = (.error .timeout,Solidity.Yul.Checks.RawGrowingForPost.frame false Solidity.Yul.Checks.RawGrowingForPost.Old.clean world) := by
  intro world
  rfl

theorem dropFrame : ∀ (value : Bool) (locals : Solidity.Source.Locals Solidity.Yul.Checks.RawGrowingForPost.Old.env.layout Solidity.Yul.Checks.RawGrowingForPost.Old.ctx.tys) (world : Solidity.Source.St Solidity.Yul.Checks.RawGrowingForPost.Old.env),
 Solidity.Yul.RawGrowingBlock.drop (Solidity.Yul.Checks.RawGrowingForPost.frame value locals world) = Solidity.Yul.Checks.RawGrowingForPost.Old.captured locals world := by
  intro value locals world
  have same : RawCoherent.coherent (frame value locals world) = true :=
    (RawCoherent.coherent_iff _).mpr rfl
  unfold RawGrowingBlock.drop
  rw [RawCoherent.prepare_coherent _ same]
  rfl

end Solidity.Yul.Checks.RawGrowingForPost

namespace Solidity.Yul.Checks.RawGrowingForPost
theorem prepared (value : Bool) (fuel : Nat) (world : Solidity.Source.St Old.env) :
 RawPreparedDeclaration.run "tmp" value (fuel+2) (Old.canonical world) =
 .inr (frame value Old.clean world) := by
  rfl

def dirtyFrame (world : Solidity.Source.St Old.env) : RawFrame.State Old.grown :=
 RawDeclarationFrame.ofSnapshot
   ⟨.cons (.bool false) (Old.initial 2 257 2 world).clean,
    (.clean (.bool false),(RawCoherent.prepare (Old.initial 2 257 2 world)).1),world⟩
def dirtyNext (world : Solidity.Source.St Old.env) : RawFrame.State Old.grown :=
 RawCoherent.capture (dirtyFrame world) (RawCoherent.prepare (dirtyFrame world))
theorem dirtyGuard (world : Solidity.Source.St Old.env) :
 RawCondition.eval Old.test 9 (dirtyFrame world) = (.ok false,dirtyNext world) := by
  first | rfl | decide | omega | simp only
theorem dirtyIteration (pipeline : Solidity.Roadmap.Pipeline) (world : Solidity.Source.St Old.env) :
 RawCheckedForPost.run Old.test clearOuter body pipeline 10 (dirtyFrame world) = (.ok (),dirtyNext world) := by
  rfl


theorem dropArgView (state : RawFrame.State Old.grown) :
 RawFrame.view (RawGrowingBlock.drop state) Solidity.Yul.Checks.RawU8Statement.argCell =
 RawFrame.view state (.scalar ⟨.unsigned 0,.there (.there .here)⟩) := by
  change localWordCells Old.grown (RawCoherent.prepare state).1
    (.scalar ⟨.unsigned 0,.there (.there .here)⟩) = _
  exact congrFun (RawCoherent.prepare_view state) _
theorem extendArgView (state : RawFrame.State Old.ctx) (world : Solidity.Source.St Old.env) :
 RawFrame.view (RawDeclarationFrame.ofSnapshot (ctx := Old.grown)
  ⟨.cons (.bool false) state.clean,(.clean (.bool false),(RawCoherent.prepare state).1),world⟩)
    (.scalar ⟨.unsigned 0,.there (.there .here)⟩) = RawFrame.view state Solidity.Yul.Checks.RawU8Statement.argCell := by
  change localWordCells Old.ctx (RawCoherent.prepare state).1 Solidity.Yul.Checks.RawU8Statement.argCell = _
  exact congrFun (RawCoherent.prepare_view state) _
theorem dirtyArg (world : Solidity.Source.St Old.env) :
 (RawFrame.view (RawGrowingBlock.drop (dirtyNext world))
  Solidity.Yul.Checks.RawU8Statement.argCell).val = 257 := by
  rw [dropArgView,dirtyNext,RawCoherent.capture_view,RawCoherent.prepare_view]
  unfold dirtyFrame
  rw [extendArgView]
  rfl

theorem dropFlagView (state : RawFrame.State Old.grown) :
 RawFrame.view (RawGrowingBlock.drop state) Solidity.Yul.Checks.RawU8Statement.flagCell =
 RawFrame.view state (.scalar ⟨.boolean,.there (.there (.there .here))⟩) := by
  change localWordCells Old.grown (RawCoherent.prepare state).1
    (.scalar ⟨.boolean,.there (.there (.there .here))⟩) = _
  exact congrFun (RawCoherent.prepare_view state) _
theorem extendFlagView (state : RawFrame.State Old.ctx) (world : Solidity.Source.St Old.env) :
 RawFrame.view (RawDeclarationFrame.ofSnapshot (ctx := Old.grown)
  ⟨.cons (.bool false) state.clean,(.clean (.bool false),(RawCoherent.prepare state).1),world⟩)
    (.scalar ⟨.boolean,.there (.there (.there .here))⟩) = RawFrame.view state Solidity.Yul.Checks.RawU8Statement.flagCell := by
  change localWordCells Old.ctx (RawCoherent.prepare state).1 Solidity.Yul.Checks.RawU8Statement.flagCell = _
  exact congrFun (RawCoherent.prepare_view state) _
theorem dirtyFlag (world : Solidity.Source.St Old.env) :
 (RawFrame.view (RawGrowingBlock.drop (dirtyNext world))
  Solidity.Yul.Checks.RawU8Statement.flagCell).val = 2 := by
  rw [dropFlagView,dirtyNext,RawCoherent.capture_view,RawCoherent.prepare_view]
  unfold dirtyFrame
  rw [extendFlagView]
  rfl

theorem normal : ∀ (pipeline : Solidity.Roadmap.Pipeline) (world : Solidity.Source.St Solidity.Yul.Checks.RawGrowingForPost.Old.env),Solidity.Yul.RawGrowingForPost.run true Solidity.Yul.Checks.RawGrowingForPost.Old.test Solidity.Yul.Checks.RawGrowingForPost.clear Solidity.Yul.Checks.RawGrowingForPost.body pipeline 12 (Solidity.Yul.Checks.RawGrowingForPost.Old.canonical world) = (.ok (),Solidity.Yul.Checks.RawGrowingForPost.Old.captured Solidity.Yul.Checks.RawGrowingForPost.Old.afterClean world) := by
  intro pipeline world
  have iteration : RawCheckedForPost.run Old.test clear body pipeline 11 (frame true Old.clean world) =
      (.ok (),frame false Old.afterClean world) := by
    rw [RawCheckedForPost.run,guardTrue10,bodyCopy10]
    dsimp only
    rw [RawSourceForPost.after,clearCopy10]
    rw [RawCheckedForPost.run.eq_def]
    dsimp only
    rw [falseCopy9]
    rfl
  rw [RawGrowingForPost.run,prepared]
  dsimp only
  rw [iteration]
  change ((.ok () : Solidity.Source.R Unit),RawGrowingBlock.drop (frame false Old.afterClean world)) = _
  rw [dropFrame]

theorem packedNormal : ∀ (pipeline : Solidity.Roadmap.Pipeline) (world : Solidity.Source.St Solidity.Yul.Checks.RawGrowingForPost.Old.env),Solidity.Yul.Checks.RawGrowingForPost.packed.run pipeline 12 (Solidity.Yul.Checks.RawGrowingForPost.Old.canonical world) = (.ok .normal,Solidity.Yul.Checks.RawGrowingForPost.Old.captured Solidity.Yul.Checks.RawGrowingForPost.Old.afterClean world) := by
  intro pipeline world
  change ((RawGrowingForPost.run true Old.test clear body pipeline 12 (Old.canonical world)).1.map
    (fun _ => (Closed.Flow.normal : RawLoopBody.Flow)),
    (RawGrowingForPost.run true Old.test clear body pipeline 12 (Old.canonical world)).2) = _
  rw [normal]
  rfl

theorem continued : ∀ (pipeline : Solidity.Roadmap.Pipeline) (world : Solidity.Source.St Solidity.Yul.Checks.RawGrowingForPost.Old.env),Solidity.Yul.RawGrowingForPost.run true Solidity.Yul.Checks.RawGrowingForPost.Old.test Solidity.Yul.Checks.RawGrowingForPost.clear Solidity.Yul.Checks.RawGrowingForPost.Old.continueBody pipeline 12 (Solidity.Yul.Checks.RawGrowingForPost.Old.canonical world) = (.ok (),Solidity.Yul.Checks.RawGrowingForPost.Old.captured Solidity.Yul.Checks.RawGrowingForPost.Old.clean world) := by
  intro pipeline world
  have iteration : RawCheckedForPost.run Old.test clear Old.continueBody pipeline 11 (frame true Old.clean world) =
      (.ok (),frame false Old.clean world) := by
    rw [RawCheckedForPost.run,guardTrue10]
    have resumed : Old.continueBody.run pipeline 10 (frame true Old.clean world) =
      (.ok (.continue_ rfl),frame true Old.clean world) := by rfl
    rw [resumed]
    dsimp only
    rw [RawSourceForPost.after,clearOld10]
    rw [RawCheckedForPost.run.eq_def]
    dsimp only
    rw [falseOld9]
    rfl
  rw [RawGrowingForPost.run,prepared]
  dsimp only
  rw [iteration]
  change ((.ok () : Solidity.Source.R Unit),RawGrowingBlock.drop (frame false Old.clean world)) = _
  rw [dropFrame]

theorem breakSkips : ∀ (pipeline : Solidity.Roadmap.Pipeline) (world : Solidity.Source.St Solidity.Yul.Checks.RawGrowingForPost.Old.env),Solidity.Yul.RawGrowingForPost.run true Solidity.Yul.Checks.RawGrowingForPost.Old.test Solidity.Yul.Checks.RawGrowingForPost.clearOuter Solidity.Yul.Checks.RawGrowingForPost.Old.breakBody pipeline 12 (Solidity.Yul.Checks.RawGrowingForPost.Old.canonical world) = (.ok (),Solidity.Yul.Checks.RawGrowingForPost.Old.captured Solidity.Yul.Checks.RawGrowingForPost.Old.clean world) := by
  intro pipeline world
  have iteration : RawCheckedForPost.run Old.test clearOuter Old.breakBody pipeline 11 (frame true Old.clean world) =
      (.ok (),frame true Old.clean world) := by
    rw [RawCheckedForPost.run,guardTrue10]
    rfl
  rw [RawGrowingForPost.run,prepared]
  dsimp only
  rw [iteration]
  change ((.ok () : Solidity.Source.R Unit),RawGrowingBlock.drop (frame true Old.clean world)) = _
  rw [dropFrame]

theorem falseSkips : ∀ (pipeline : Solidity.Roadmap.Pipeline) (world : Solidity.Source.St Solidity.Yul.Checks.RawGrowingForPost.Old.env),Solidity.Yul.RawGrowingForPost.run false Solidity.Yul.Checks.RawGrowingForPost.Old.test Solidity.Yul.Checks.RawGrowingForPost.clearOuter Solidity.Yul.Checks.RawGrowingForPost.body pipeline 11 (Solidity.Yul.Checks.RawGrowingForPost.Old.canonical world) = (.ok (),Solidity.Yul.Checks.RawGrowingForPost.Old.captured Solidity.Yul.Checks.RawGrowingForPost.Old.clean world) := by
  intro pipeline world
  have iteration : RawCheckedForPost.run Old.test clearOuter body pipeline 10 (frame false Old.clean world) =
      (.ok (),frame false Old.clean world) := by
    rw [RawCheckedForPost.run,falseOld9]
    rfl
  rw [RawGrowingForPost.run,prepared]
  dsimp only
  rw [iteration]
  change ((.ok () : Solidity.Source.R Unit),RawGrowingBlock.drop (frame false Old.clean world)) = _
  rw [dropFrame]

theorem postTimeout : ∀ (pipeline : Solidity.Roadmap.Pipeline) (world : Solidity.Source.St Solidity.Yul.Checks.RawGrowingForPost.Old.env),Solidity.Yul.RawGrowingForPost.run true Solidity.Yul.Checks.RawGrowingForPost.Old.test Solidity.Yul.Checks.RawGrowingForPost.partialPost Solidity.Yul.Checks.RawGrowingForPost.Old.continueBody pipeline 5 (Solidity.Yul.Checks.RawGrowingForPost.Old.canonical world) = (.error .timeout,Solidity.Yul.Checks.RawGrowingForPost.Old.captured Solidity.Yul.Checks.RawGrowingForPost.Old.clean world) := by
  intro pipeline world
  have iteration : RawCheckedForPost.run Old.test partialPost Old.continueBody pipeline 4 (frame true Old.clean world) =
      (.error .timeout,frame false Old.clean world) := by
    rw [RawCheckedForPost.run,guardTrue3]
    change RawSourceForPost.after partialPost (RawCheckedForPost.run Old.test partialPost Old.continueBody pipeline 3)
      3 (frame true Old.clean world) = _
    rw [RawSourceForPost.after,partialOld3]
  rw [RawGrowingForPost.run,prepared]
  dsimp only
  rw [iteration]
  change ((.error .timeout : Solidity.Source.R Unit),RawGrowingBlock.drop (frame false Old.clean world)) = _
  rw [dropFrame]

theorem preTimeout : ∀ (pipeline : Solidity.Roadmap.Pipeline) (world : Solidity.Source.St Solidity.Yul.Checks.RawGrowingForPost.Old.env),Solidity.Yul.RawGrowingForPost.run true Solidity.Yul.Checks.RawGrowingForPost.Old.test Solidity.Yul.Checks.RawGrowingForPost.clear Solidity.Yul.Checks.RawGrowingForPost.body pipeline 0 (Solidity.Yul.Checks.RawGrowingForPost.Old.canonical world) = (.error .timeout,Solidity.Yul.Checks.RawGrowingForPost.Old.canonical world) ∧ Solidity.Yul.RawGrowingForPost.run true Solidity.Yul.Checks.RawGrowingForPost.Old.test Solidity.Yul.Checks.RawGrowingForPost.clear Solidity.Yul.Checks.RawGrowingForPost.body pipeline 2 (Solidity.Yul.Checks.RawGrowingForPost.Old.canonical world) = (.error .timeout,Solidity.Yul.Checks.RawGrowingForPost.Old.canonical world) := by
  intro pipeline world
  exact ⟨rfl,rfl⟩

theorem dirtyNarrow : ∀ (pipeline : Solidity.Roadmap.Pipeline) (world : Solidity.Source.St Solidity.Yul.Checks.RawGrowingForPost.Old.env),(Solidity.Yul.RawGrowingForPost.run false Solidity.Yul.Checks.RawGrowingForPost.Old.test Solidity.Yul.Checks.RawGrowingForPost.clearOuter Solidity.Yul.Checks.RawGrowingForPost.body pipeline 11 (Solidity.Yul.Checks.RawGrowingForPost.Old.initial 2 257 2 world)).1 = .ok () ∧
 (Solidity.Yul.RawFrame.view (Solidity.Yul.RawGrowingForPost.run false Solidity.Yul.Checks.RawGrowingForPost.Old.test Solidity.Yul.Checks.RawGrowingForPost.clearOuter Solidity.Yul.Checks.RawGrowingForPost.body pipeline 11 (Solidity.Yul.Checks.RawGrowingForPost.Old.initial 2 257 2 world)).2 Solidity.Yul.Checks.RawU8Statement.argCell).val = 257 ∧
 (Solidity.Yul.RawFrame.view (Solidity.Yul.RawGrowingForPost.run false Solidity.Yul.Checks.RawGrowingForPost.Old.test Solidity.Yul.Checks.RawGrowingForPost.clearOuter Solidity.Yul.Checks.RawGrowingForPost.body pipeline 11 (Solidity.Yul.Checks.RawGrowingForPost.Old.initial 2 257 2 world)).2 Solidity.Yul.Checks.RawU8Statement.flagCell).val = 2 ∧
 (Solidity.Yul.RawGrowingForPost.run false Solidity.Yul.Checks.RawGrowingForPost.Old.test Solidity.Yul.Checks.RawGrowingForPost.clearOuter Solidity.Yul.Checks.RawGrowingForPost.body pipeline 11 (Solidity.Yul.Checks.RawGrowingForPost.Old.initial 2 257 2 world)).2.world = world := by
  intro pipeline world
  rw [RawGrowingForPost.run,RawPreparedDeclaration.run_success]
  dsimp only
  have next : RawDeclarationFrame.ofSnapshot (ctx := Old.grown)
    ⟨.cons (.bool false) (Old.initial 2 257 2 world).clean,
     (.clean (.bool false),(RawCoherent.prepare (Old.initial 2 257 2 world)).1),
     (Old.initial 2 257 2 world).world⟩ = dirtyFrame world := by rfl
  rw [next,dirtyIteration]
  exact ⟨rfl,dirtyArg world,dirtyFlag world,rfl⟩

theorem sourceAll : ∀ (glob : Solidity.Source.Glob Solidity.Yul.Checks.RawGrowingForPost.Old.env) (frame : Solidity.Source.Fr), frame.checked = true →
 ∀ (fuel nps : Nat) (ph : Option (Solidity.Source.Ph Solidity.Yul.Checks.RawGrowingForPost.Old.env)) (world : Solidity.Source.St Solidity.Yul.Checks.RawGrowingForPost.Old.env),
 Solidity.Yul.RawCoherent.coherent (Solidity.Yul.Checks.RawGrowingForPost.packed.run glob.pipeline fuel (Solidity.Yul.Checks.RawGrowingForPost.Old.canonical world)).2 = true ∧
 (Solidity.Source.execS glob frame fuel nps ph Solidity.Yul.Checks.RawGrowingForPost.program Solidity.Yul.Checks.RawGrowingForPost.Old.clean).run
 (Solidity.Source.L0 Solidity.Yul.Checks.RawGrowingForPost.Old.env,world) =
 Solidity.Yul.RawLoopBody.represented (Solidity.Yul.Checks.RawGrowingForPost.packed.run glob.pipeline fuel (Solidity.Yul.Checks.RawGrowingForPost.Old.canonical world)) := by
  intro glob frame checked fuel nps ph world
  exact packed.correct glob frame checked fuel nps ph (Old.canonical world)
    (Solidity.Yul.Checks.RawPreparedDeclaration.canonicalCoherent world)

theorem sourceCompletes : ∀ (glob : Solidity.Source.Glob Solidity.Yul.Checks.RawGrowingForPost.Old.env) (frame : Solidity.Source.Fr)
 (nps : Nat) (ph : Option (Solidity.Source.Ph Solidity.Yul.Checks.RawGrowingForPost.Old.env)) (world : Solidity.Source.St Solidity.Yul.Checks.RawGrowingForPost.Old.env),
 (Solidity.Source.execS glob frame 12 nps ph Solidity.Yul.Checks.RawGrowingForPost.program Solidity.Yul.Checks.RawGrowingForPost.Old.clean).run
 (Solidity.Source.L0 Solidity.Yul.Checks.RawGrowingForPost.Old.env,world) =
 (.ok (.normal Solidity.Yul.Checks.RawGrowingForPost.Old.afterClean),(Solidity.Source.L0 Solidity.Yul.Checks.RawGrowingForPost.Old.env,world)) := by
  intro glob frame nps ph world
  rfl

end Solidity.Yul.Checks.RawGrowingForPost
#print axioms Solidity.Yul.RawGrowingForPost.correct
#print axioms Solidity.Yul.RawGrowingForPost.adapter
#print axioms Solidity.Yul.Checks.RawGrowingForPost.guardTrue10
#print axioms Solidity.Yul.Checks.RawGrowingForPost.guardTrue3
#print axioms Solidity.Yul.Checks.RawGrowingForPost.bodyCopy10
#print axioms Solidity.Yul.Checks.RawGrowingForPost.clearCopy10
#print axioms Solidity.Yul.Checks.RawGrowingForPost.falseCopy9
#print axioms Solidity.Yul.Checks.RawGrowingForPost.clearOld10
#print axioms Solidity.Yul.Checks.RawGrowingForPost.falseOld9
#print axioms Solidity.Yul.Checks.RawGrowingForPost.partialOld3
#print axioms Solidity.Yul.Checks.RawGrowingForPost.dropFrame
#print axioms Solidity.Yul.Checks.RawGrowingForPost.normal
#print axioms Solidity.Yul.Checks.RawGrowingForPost.packedNormal
#print axioms Solidity.Yul.Checks.RawGrowingForPost.continued
#print axioms Solidity.Yul.Checks.RawGrowingForPost.breakSkips
#print axioms Solidity.Yul.Checks.RawGrowingForPost.falseSkips
#print axioms Solidity.Yul.Checks.RawGrowingForPost.postTimeout
#print axioms Solidity.Yul.Checks.RawGrowingForPost.preTimeout
#print axioms Solidity.Yul.Checks.RawGrowingForPost.dirtyNarrow
#print axioms Solidity.Yul.Checks.RawGrowingForPost.sourceAll
#print axioms Solidity.Yul.Checks.RawGrowingForPost.sourceCompletes

#print axioms Solidity.Yul.Checks.RawGrowingForPost.prepared
#print axioms Solidity.Yul.Checks.RawGrowingForPost.dirtyGuard
#print axioms Solidity.Yul.Checks.RawGrowingForPost.dirtyIteration
#print axioms Solidity.Yul.Checks.RawGrowingForPost.dirtyArg
#print axioms Solidity.Yul.Checks.RawGrowingForPost.dirtyFlag

#print axioms Solidity.Yul.Checks.RawGrowingForPost.dropArgView
#print axioms Solidity.Yul.Checks.RawGrowingForPost.dropFlagView
#print axioms Solidity.Yul.Checks.RawGrowingForPost.extendArgView
#print axioms Solidity.Yul.Checks.RawGrowingForPost.extendFlagView
