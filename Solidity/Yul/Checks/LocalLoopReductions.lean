import Solidity.Yul.LocalLoopReductions
import Solidity.Yul.Checks.LocalPostHorizon

namespace Solidity.Yul.Checks.LocalLoopReductions

def bodyWitness : Nonempty (LocalDefaultItems.Supported Solidity.Yul.Checks.LocalDefaultPostIter.Fixture.env [] false ⟨true,false⟩ Solidity.Yul.Checks.LocalDefaultPostIter.items) := ⟨Solidity.Yul.Checks.LocalDefaultPostIter.proof⟩

def falseConcrete (fuel : Nat) (state : LocalState Solidity.Yul.Checks.LocalDefaultPostIter.Fixture.env Solidity.Yul.Checks.LocalDefaultPostIter.Fixture.ctx.tys) :=
 Solidity.Yul.LocalLoopReductions.falseDoWhile Solidity.Yul.Checks.LocalDefaultPostIter.Fixture.env [] false false Solidity.Yul.Checks.LocalDefaultPostIter.Fixture.ctx.tys Solidity.Yul.Checks.LocalDefaultPostIter.Out Solidity.Yul.Checks.LocalDefaultPostIter.items Solidity.Yul.Checks.LocalDefaultPostIter.proof fuel state

def literalConcrete (fuel : Nat) (state : LocalState Solidity.Yul.Checks.LocalDefaultPostIter.Fixture.env Solidity.Yul.Checks.LocalDefaultPostIter.Fixture.ctx.tys) :=
 Solidity.Yul.LocalLoopReductions.literalPost Solidity.Yul.Checks.LocalDefaultPostIter.Fixture.env [] false false Solidity.Yul.Checks.LocalDefaultPostIter.Fixture.ctx.tys Solidity.Yul.Checks.LocalDefaultPostIter.Out (.local .here) Solidity.Yul.Checks.LocalDefaultPostIter.readTest Solidity.Yul.Checks.LocalDefaultPostIter.items Solidity.Yul.Checks.LocalDefaultPostIter.proof fuel state

def rawConcrete (fuel : Nat) (state : LocalState Solidity.Yul.Checks.LocalDefaultPostIter.Fixture.env Solidity.Yul.Checks.LocalDefaultPostIter.Fixture.ctx.tys) :=
 Solidity.Yul.LocalLoopReductions.trueDoWhileTimeout Solidity.Yul.Checks.LocalDefaultPostIter.Fixture.env [] false false Solidity.Yul.Checks.LocalDefaultPostIter.Fixture.ctx.tys Solidity.Yul.Checks.LocalDefaultPostIter.Out Solidity.Yul.Checks.LocalDefaultPostIter.items Solidity.Yul.Checks.LocalDefaultPostIter.proof fuel state

def sourceConcrete (glob : Solidity.Source.Glob Solidity.Yul.Checks.LocalDefaultPostIter.Fixture.env) (frame : Solidity.Source.Fr) (fuel nps : Nat)
 (ph : Option (Solidity.Source.Ph Solidity.Yul.Checks.LocalDefaultPostIter.Fixture.env))
 (locals : Solidity.Source.Locals Solidity.Yul.Checks.LocalDefaultPostIter.Fixture.env.layout Solidity.Yul.Checks.LocalDefaultPostIter.Fixture.ctx.tys) (world : Solidity.Source.St Solidity.Yul.Checks.LocalDefaultPostIter.Fixture.env) :=
 Solidity.Yul.LocalLoopReductions.sourceTrueDoWhileTimeout Solidity.Yul.Checks.LocalDefaultPostIter.Fixture.env [] false false false Solidity.Yul.Checks.LocalDefaultPostIter.Fixture.ctx.tys Solidity.Yul.Checks.LocalDefaultPostIter.Out Solidity.Yul.Checks.LocalDefaultPostIter.items Solidity.Yul.Checks.LocalDefaultPostIter.proof glob frame fuel nps ph locals world

theorem oneBodyCompletes : Solidity.Yul.LocalDefaultDoWhile.run Solidity.Yul.Checks.LocalDefaultPostIter.stopTest Solidity.Yul.Checks.LocalDefaultPostIter.proof 9 Solidity.Yul.Checks.LocalDefaultPostIter.initial = .normal (Solidity.Yul.Checks.LocalDefaultPostIter.assigned false) := by
  rfl

theorem bodyCompletes : Solidity.Yul.LocalDefaultItems.blockRun Solidity.Yul.Checks.LocalDefaultPostIter.proof 8 Solidity.Yul.Checks.LocalDefaultPostIter.initial = .normal (Solidity.Yul.Checks.LocalDefaultPostIter.assigned false) := by
  rfl

theorem literalResultsAgree : Solidity.Yul.LocalDefaultPostIter.run Solidity.Yul.Checks.LocalDefaultPostIter.readTest Solidity.Yul.Checks.LocalDefaultPostIter.postFalse Solidity.Yul.Checks.LocalDefaultPostIter.proof 9 Solidity.Yul.Checks.LocalDefaultPostIter.initial = Solidity.Yul.LocalDefaultPostIter.run Solidity.Yul.Checks.LocalDefaultPostIter.readTest Solidity.Yul.Checks.LocalDefaultPostIter.postTrue Solidity.Yul.Checks.LocalDefaultPostIter.proof 9 Solidity.Yul.Checks.LocalDefaultPostIter.initial := by
  rfl

theorem trueBodyTimeout : Solidity.Yul.LocalDefaultDoWhile.run Solidity.Yul.Checks.LocalDefaultPostIter.guardTrue Solidity.Yul.Checks.LocalDefaultPostIter.proof 9 Solidity.Yul.Checks.LocalDefaultPostIter.initial = .halted .timeout Solidity.Yul.Checks.LocalDefaultPostIter.afterFalsePostBody := by
  rfl

theorem assigningPostTimeout : Solidity.Yul.LocalDefaultPostIter.run Solidity.Yul.Checks.LocalDefaultPostIter.readTest Solidity.Yul.Checks.LocalDefaultPostIter.postSetTrue Solidity.Yul.Checks.LocalDefaultPostIter.proof 9 Solidity.Yul.Checks.LocalDefaultPostIter.initial = .halted .timeout Solidity.Yul.Checks.LocalDefaultDoWhile.afterGuardBodyState := by
  rfl

theorem effectfulPostDiffers : Solidity.Yul.LocalDefaultPostIter.run Solidity.Yul.Checks.LocalDefaultPostIter.readTest Solidity.Yul.Checks.LocalDefaultPostIter.postSetTrue Solidity.Yul.Checks.LocalDefaultPostIter.proof 9 Solidity.Yul.Checks.LocalDefaultPostIter.initial ≠ Solidity.Yul.LocalDefaultPostIter.run Solidity.Yul.Checks.LocalDefaultPostIter.readTest Solidity.Yul.Checks.LocalDefaultPostIter.postTrue Solidity.Yul.Checks.LocalDefaultPostIter.proof 9 Solidity.Yul.Checks.LocalDefaultPostIter.initial := by
  intro bad; cases bad

theorem breakingSourceCompletes : let items : Solidity.Source.RItems Solidity.Yul.Checks.LocalDefaultPostIter.Fixture.env [] false ⟨true,false⟩ Solidity.Yul.Checks.LocalDefaultPostIter.Fixture.ctx.tys Solidity.Yul.Checks.LocalDefaultPostIter.Fixture.ctx.tys := .stmt .brk .nil
∀ (glob : Solidity.Source.Glob Solidity.Yul.Checks.LocalDefaultPostIter.Fixture.env) (frame : Solidity.Source.Fr) (nps : Nat)
 (ph : Option (Solidity.Source.Ph Solidity.Yul.Checks.LocalDefaultPostIter.Fixture.env)) (locals : Solidity.Source.Locals Solidity.Yul.Checks.LocalDefaultPostIter.Fixture.env.layout Solidity.Yul.Checks.LocalDefaultPostIter.Fixture.ctx.tys)
 (world : Solidity.Source.St Solidity.Yul.Checks.LocalDefaultPostIter.Fixture.env),
 (Solidity.Source.execS glob frame 4 nps ph (.doWhile (l := false) (.block items) (.bool true)) locals).run
 (Solidity.Source.L0 Solidity.Yul.Checks.LocalDefaultPostIter.Fixture.env,world) = (.ok (.normal locals),(Solidity.Source.L0 Solidity.Yul.Checks.LocalDefaultPostIter.Fixture.env,world)) := by
  dsimp only []; intro glob frame nps ph locals world; rfl

#print axioms Solidity.Yul.LocalLoopReductions.falseDoWhile
#print axioms Solidity.Yul.LocalLoopReductions.literalPost
#print axioms Solidity.Yul.LocalLoopReductions.trueDoWhileTimeout
#print axioms Solidity.Yul.LocalLoopReductions.sourceTrueDoWhileTimeout
#print axioms oneBodyCompletes
#print axioms bodyCompletes
#print axioms literalResultsAgree
#print axioms trueBodyTimeout
#print axioms assigningPostTimeout
#print axioms effectfulPostDiffers
#print axioms breakingSourceCompletes

end Solidity.Yul.Checks.LocalLoopReductions
