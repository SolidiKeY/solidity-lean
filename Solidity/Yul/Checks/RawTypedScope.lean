import Solidity.Yul.RawTypedScope
import Solidity.Source.Semantics
import Solidity.Yul.Checks.RawControlGrowingBlock

/-! Integer LOCAL binder witnesses and dirty-word refusal controls.
No integer initializer execution or physical layout is inferred. -/
namespace Solidity.Yul.Checks.RawTypedScope
namespace Old
export Solidity.Yul.Checks.RawControlGrowingBlock.Old (ctx env clean captured afterClean)
end Old
def signed8 : Solidity.Source.IntTy := { Solidity.Source.IntTy.u8 with signed := true }
def unsignedCtx := Old.ctx.push "n" (.int Solidity.Source.IntTy.u8)
def signedCtx := Old.ctx.push "n" (.int signed8)
def unsigned (world : Solidity.Source.St Old.env) : RawFrame.State unsignedCtx :=
 RawFrame.ofClean (.cons (.int 255 (by decide)) Old.afterClean) world
def signed (world : Solidity.Source.St Old.env) : RawFrame.State signedCtx :=
 RawFrame.ofClean (.cons (.int (-128) (by decide)) Old.afterClean) world
def newCell : WordCell (localExternalTypes unsignedCtx) := .scalar ⟨.unsigned 0,.here⟩
def signedCell : WordCell (localExternalTypes signedCtx) := .scalar ⟨.signed 0,.here⟩
def grownX : WordCell (localExternalTypes unsignedCtx) := .scalar ⟨.unsigned 0,.there .here⟩
def grownArg : WordCell (localExternalTypes unsignedCtx) := .scalar ⟨.unsigned 0,.there (.there .here)⟩
def grownFlag : WordCell (localExternalTypes unsignedCtx) := .scalar ⟨.boolean,.there (.there (.there .here))⟩
def dirty (world : Solidity.Source.St Old.env) : RawFrame.State unsignedCtx :=
 RawFrame.write (RawFrame.write (RawFrame.write (RawFrame.write
  (RawFrame.ofClean (.cons (.int 255 (by decide)) Old.clean) world)
  newCell (word 511)) grownX (word 2)) grownArg (word 257)) grownFlag (word 2)
def witness : Nonempty (RawFrame.State signedCtx) := ⟨signed (Solidity.Source.St.init Old.env)⟩
end Solidity.Yul.Checks.RawTypedScope

namespace Solidity.Yul.Checks.RawTypedScope
theorem unsignedDrop : ∀ (world : Solidity.Source.St Solidity.Yul.Checks.RawTypedScope.Old.env), Solidity.Yul.RawTypedScope.drop (Solidity.Yul.Checks.RawTypedScope.unsigned world) = Solidity.Yul.Checks.RawTypedScope.Old.captured Solidity.Yul.Checks.RawTypedScope.Old.afterClean world := by
  intro world
  have same : RawCoherent.coherent (unsigned world) = true :=
    RawCoherent.coherent_ofClean (ctx := unsignedCtx) _ world
  unfold RawTypedScope.drop
  rw [RawCoherent.prepare_coherent _ same]
  rfl

theorem signedDrop : ∀ (world : Solidity.Source.St Solidity.Yul.Checks.RawTypedScope.Old.env), Solidity.Yul.RawTypedScope.drop (Solidity.Yul.Checks.RawTypedScope.signed world) = Solidity.Yul.Checks.RawTypedScope.Old.captured Solidity.Yul.Checks.RawTypedScope.Old.afterClean world := by
  intro world
  have same : RawCoherent.coherent (signed world) = true :=
    RawCoherent.coherent_ofClean (ctx := signedCtx) _ world
  unfold RawTypedScope.drop
  rw [RawCoherent.prepare_coherent _ same]
  rfl

theorem unsignedWord : ∀ (world : Solidity.Source.St Solidity.Yul.Checks.RawTypedScope.Old.env), (Solidity.Yul.RawFrame.view (Solidity.Yul.Checks.RawTypedScope.unsigned world) Solidity.Yul.Checks.RawTypedScope.newCell).val = 255 := by
  intro world
  rfl

theorem signedWord : ∀ (world : Solidity.Source.St Solidity.Yul.Checks.RawTypedScope.Old.env), (Solidity.Yul.RawFrame.view (Solidity.Yul.Checks.RawTypedScope.signed world) Solidity.Yul.Checks.RawTypedScope.signedCell).val = 2^256-128 := by
  intro world
  rfl

theorem coherentUnsigned : ∀ (world : Solidity.Source.St Solidity.Yul.Checks.RawTypedScope.Old.env), Solidity.Yul.RawCoherent.coherent (Solidity.Yul.Checks.RawTypedScope.unsigned world) = true := by
  intro world
  exact RawCoherent.coherent_ofClean (ctx := unsignedCtx) _ world

theorem normalClose : ∀ (world : Solidity.Source.St Solidity.Yul.Checks.RawTypedScope.Old.env), Solidity.Yul.RawTypedScope.close ((.ok .normal : Solidity.Source.R Solidity.Yul.RawLoopBody.Flow),Solidity.Yul.Checks.RawTypedScope.unsigned world) = (.ok .normal,Solidity.Yul.Checks.RawTypedScope.Old.captured Solidity.Yul.Checks.RawTypedScope.Old.afterClean world) := by
  intro world
  unfold RawTypedScope.close
  rw [unsignedDrop]

theorem breakClose : ∀ (world : Solidity.Source.St Solidity.Yul.Checks.RawTypedScope.Old.env), Solidity.Yul.RawTypedScope.close ((.ok (.break_ rfl) : Solidity.Source.R Solidity.Yul.RawLoopBody.Flow),Solidity.Yul.Checks.RawTypedScope.signed world) = (.ok (.break_ rfl),Solidity.Yul.Checks.RawTypedScope.Old.captured Solidity.Yul.Checks.RawTypedScope.Old.afterClean world) := by
  intro world
  unfold RawTypedScope.close
  rw [signedDrop]

theorem continueClose : ∀ (world : Solidity.Source.St Solidity.Yul.Checks.RawTypedScope.Old.env), Solidity.Yul.RawTypedScope.close ((.ok (.continue_ rfl) : Solidity.Source.R Solidity.Yul.RawLoopBody.Flow),Solidity.Yul.Checks.RawTypedScope.signed world) = (.ok (.continue_ rfl),Solidity.Yul.Checks.RawTypedScope.Old.captured Solidity.Yul.Checks.RawTypedScope.Old.afterClean world) := by
  intro world
  unfold RawTypedScope.close
  rw [signedDrop]

theorem errorClose : ∀ (world : Solidity.Source.St Solidity.Yul.Checks.RawTypedScope.Old.env), Solidity.Yul.RawTypedScope.close ((.error .timeout : Solidity.Source.R Solidity.Yul.RawLoopBody.Flow),Solidity.Yul.Checks.RawTypedScope.unsigned world) = (.error .timeout,Solidity.Yul.Checks.RawTypedScope.Old.captured Solidity.Yul.Checks.RawTypedScope.Old.afterClean world) := by
  intro world
  unfold RawTypedScope.close
  rw [unsignedDrop]

theorem sourceUnsigned : ∀ (world : Solidity.Source.St Solidity.Yul.Checks.RawTypedScope.Old.env), Solidity.Yul.RawTypedScope.project ((.ok .normal : Solidity.Source.R Solidity.Yul.RawLoopBody.Flow),Solidity.Yul.Checks.RawTypedScope.unsigned world) = (.ok (.normal Solidity.Yul.Checks.RawTypedScope.Old.afterClean),(Solidity.Source.L0 Solidity.Yul.Checks.RawTypedScope.Old.env,world)) := by
  intro world
  rfl

theorem sourceSignedBreak : ∀ (world : Solidity.Source.St Solidity.Yul.Checks.RawTypedScope.Old.env), Solidity.Yul.RawTypedScope.project ((.ok (.break_ rfl) : Solidity.Source.R Solidity.Yul.RawLoopBody.Flow),Solidity.Yul.Checks.RawTypedScope.signed world) = (.ok (.brk Solidity.Yul.Checks.RawTypedScope.Old.afterClean),(Solidity.Source.L0 Solidity.Yul.Checks.RawTypedScope.Old.env,world)) := by
  intro world
  rfl

theorem dirtyBits : ∀ (world : Solidity.Source.St Solidity.Yul.Checks.RawTypedScope.Old.env), (Solidity.Yul.RawFrame.view (Solidity.Yul.Checks.RawTypedScope.dirty world) Solidity.Yul.Checks.RawTypedScope.newCell).val = 511 ∧
 (Solidity.Yul.RawFrame.view (Solidity.Yul.RawTypedScope.drop (Solidity.Yul.Checks.RawTypedScope.dirty world)) Solidity.Yul.Checks.RawU8Statement.xCell).val = 2 ∧
 (Solidity.Yul.RawFrame.view (Solidity.Yul.RawTypedScope.drop (Solidity.Yul.Checks.RawTypedScope.dirty world)) Solidity.Yul.Checks.RawU8Statement.argCell).val = 257 ∧
 (Solidity.Yul.RawFrame.view (Solidity.Yul.RawTypedScope.drop (Solidity.Yul.Checks.RawTypedScope.dirty world)) Solidity.Yul.Checks.RawU8Statement.flagCell).val = 2 ∧
 (Solidity.Yul.RawTypedScope.drop (Solidity.Yul.Checks.RawTypedScope.dirty world)).world = world := by
  intro world
  exact ⟨rfl,rfl,rfl,rfl,rfl⟩

theorem dirtyRefuses : ∀ (world : Solidity.Source.St Solidity.Yul.Checks.RawTypedScope.Old.env), Solidity.Yul.RawCoherent.coherent (Solidity.Yul.Checks.RawTypedScope.dirty world) = false ∧
 Solidity.Yul.RawCoherent.coherent (Solidity.Yul.RawTypedScope.drop (Solidity.Yul.Checks.RawTypedScope.dirty world)) = false := by
  intro world
  exact ⟨rfl,rfl⟩

theorem concreteClosing : ∀ (world : Solidity.Source.St Solidity.Yul.Checks.RawTypedScope.Old.env), Solidity.Yul.RawCoherent.coherent
 (Solidity.Yul.RawTypedScope.close ((.ok .normal : Solidity.Source.R Solidity.Yul.RawLoopBody.Flow),Solidity.Yul.Checks.RawTypedScope.unsigned world)).2 = true ∧
 Solidity.Yul.RawTypedScope.project ((.ok .normal : Solidity.Source.R Solidity.Yul.RawLoopBody.Flow),Solidity.Yul.Checks.RawTypedScope.unsigned world) =
 Solidity.Yul.RawLoopBody.represented (Solidity.Yul.RawTypedScope.close ((.ok .normal : Solidity.Source.R Solidity.Yul.RawLoopBody.Flow),Solidity.Yul.Checks.RawTypedScope.unsigned world)) := by
  intro world
  exact RawTypedScope.close_correct Old.ctx "n" (.int Solidity.Source.IntTy.u8)
    (.ok .normal,unsigned world) (coherentUnsigned world)

end Solidity.Yul.Checks.RawTypedScope
#print axioms Solidity.Yul.RawTypedScope.restore_drop
#print axioms Solidity.Yul.RawTypedScope.drop_coherent
#print axioms Solidity.Yul.RawTypedScope.close_correct
#print axioms Solidity.Yul.RawTypedScope.bool_drop_eq
#print axioms Solidity.Yul.RawTypedScope.bool_close_eq
#print axioms Solidity.Yul.Checks.RawTypedScope.unsignedDrop
#print axioms Solidity.Yul.Checks.RawTypedScope.signedDrop
#print axioms Solidity.Yul.Checks.RawTypedScope.unsignedWord
#print axioms Solidity.Yul.Checks.RawTypedScope.signedWord
#print axioms Solidity.Yul.Checks.RawTypedScope.coherentUnsigned
#print axioms Solidity.Yul.Checks.RawTypedScope.normalClose
#print axioms Solidity.Yul.Checks.RawTypedScope.breakClose
#print axioms Solidity.Yul.Checks.RawTypedScope.continueClose
#print axioms Solidity.Yul.Checks.RawTypedScope.errorClose
#print axioms Solidity.Yul.Checks.RawTypedScope.sourceUnsigned
#print axioms Solidity.Yul.Checks.RawTypedScope.sourceSignedBreak
#print axioms Solidity.Yul.Checks.RawTypedScope.dirtyBits
#print axioms Solidity.Yul.Checks.RawTypedScope.dirtyRefuses
#print axioms Solidity.Yul.Checks.RawTypedScope.concreteClosing
