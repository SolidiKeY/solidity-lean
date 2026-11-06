import Solidity.Yul.RawIntegerInitialization
import Solidity.Yul.Checks.RawLiteralInitialization

namespace Solidity.Yul.Checks.RawIntegerInitialization
namespace Fixture
export Solidity.Yul.Checks.RawLiteralInitialization.Fixture (ctx env initial dirty flag small)
def signed8 : Solidity.Source.IntTy := { Solidity.Source.IntTy.u8 with signed := true }
def fraction : Solidity.Source.Q := ⟨1,2,Nat.succ_pos 1⟩
end Fixture



theorem ranges : (Solidity.Source.IntTy.u8.lo ≤ (255 : Int) ∧ (255 : Int) ≤ Solidity.Source.IntTy.u8.hi) ∧
 (Solidity.Yul.Checks.RawIntegerInitialization.Fixture.signed8.lo ≤ (-128 : Int) ∧
 (-128 : Int) ≤ Solidity.Yul.Checks.RawIntegerInitialization.Fixture.signed8.hi) ∧
 (Solidity.Source.IntTy.u256.lo ≤ (2^256-1 : Int) ∧ (2^256-1 : Int) ≤ Solidity.Source.IntTy.u256.hi) := by
  decide +kernel

def afterUnsigned : RawLocalDeclaration.Snapshot Fixture.env (.int Solidity.Source.IntTy.u8 :: Fixture.ctx.tys) :=
  ⟨.cons (.int 255 ranges.1) Fixture.initial.clean,
    (.clean (.int 255 ranges.1),Fixture.initial.values),Fixture.initial.world⟩
def afterPair : RawLocalDeclaration.Snapshot Fixture.env
    (.int Fixture.signed8 :: .int Solidity.Source.IntTy.u8 :: Fixture.ctx.tys) :=
  ⟨.cons (.int (-128) ranges.2.1) afterUnsigned.clean,
    (.clean (.int (-128) ranges.2.1),afterUnsigned.values),afterUnsigned.world⟩
def unsignedDecl : Solidity.Source.RStmt Fixture.env [] false ⟨false,false⟩
    Fixture.ctx.tys (.int Solidity.Source.IntTy.u8 :: Fixture.ctx.tys) :=
  .declInit (.const (Solidity.Source.Q.ofInt 255))
    (Solidity.Yul.RawIntegerInitialization.admissible Fixture.env _ _ ranges.1)
def signedDecl : Solidity.Source.RStmt Fixture.env [] false ⟨false,false⟩
    (.int Solidity.Source.IntTy.u8 :: Fixture.ctx.tys)
    (.int Fixture.signed8 :: .int Solidity.Source.IntTy.u8 :: Fixture.ctx.tys) :=
  .declInit (.const (Solidity.Source.Q.ofInt (-128)))
    (Solidity.Yul.RawIntegerInitialization.admissible Fixture.env _ _ ranges.2.1)
def witness : Nonempty (Solidity.Source.RStmt Fixture.env [] false ⟨false,false⟩
    Fixture.ctx.tys (.int Solidity.Source.IntTy.u8 :: Fixture.ctx.tys)) := ⟨unsignedDecl⟩
def combined : Solidity.Source.RItems Fixture.env [] false ⟨false,false⟩
    Fixture.ctx.tys (.int Fixture.signed8 :: .int Solidity.Source.IntTy.u8 :: Fixture.ctx.tys) :=
  .stmt unsignedDecl (.stmt signedDecl .nil)
def concreteUnsigned (glob : Solidity.Source.Glob Fixture.env) (frame : Solidity.Source.Fr)
    (fuel nps : Nat) (ph : Option (Solidity.Source.Ph Fixture.env)) :=
  Solidity.Yul.RawIntegerInitialization.correct Fixture.env Fixture.ctx.tys
    Solidity.Source.IntTy.u8 255 ranges.1 [] false ⟨false,false⟩ glob frame fuel nps ph Fixture.initial
def concreteWide (glob : Solidity.Source.Glob Fixture.env) (frame : Solidity.Source.Fr)
    (fuel nps : Nat) (ph : Option (Solidity.Source.Ph Fixture.env)) :=
  Solidity.Yul.RawIntegerInitialization.correct Fixture.env Fixture.ctx.tys
    Solidity.Source.IntTy.u256 (2^256-1) ranges.2.2 [] false ⟨false,false⟩ glob frame fuel nps ph Fixture.initial



theorem refusals : Solidity.Source.STy.implicit Solidity.Yul.Checks.RawIntegerInitialization.Fixture.env.isBase Solidity.Yul.Checks.RawIntegerInitialization.Fixture.env.mapFree
 (.rational (Solidity.Source.Q.ofInt 256)) (.int Solidity.Source.IntTy.u8) = false ∧
 Solidity.Source.STy.implicit Solidity.Yul.Checks.RawIntegerInitialization.Fixture.env.isBase Solidity.Yul.Checks.RawIntegerInitialization.Fixture.env.mapFree
 (.rational Solidity.Yul.Checks.RawIntegerInitialization.Fixture.fraction) (.int Solidity.Source.IntTy.u8) = false ∧
 Solidity.Source.constVal (D := Solidity.Yul.Checks.RawIntegerInitialization.Fixture.env.layout)
 (Solidity.Source.Q.ofInt 256) (.int Solidity.Source.IntTy.u8) = .error (.stuck "integer out of range") ∧
 Solidity.Source.constVal (D := Solidity.Yul.Checks.RawIntegerInitialization.Fixture.env.layout)
 Solidity.Yul.Checks.RawIntegerInitialization.Fixture.fraction (.int Solidity.Source.IntTy.u8) =
 .error (.stuck "fractional constant at an integer type") := by
  exact ⟨rfl,rfl,rfl,rfl⟩

theorem outcomes : Solidity.Yul.RawIntegerInitialization.run Solidity.Source.IntTy.u8 255 Solidity.Yul.Checks.RawIntegerInitialization.ranges.1 0 Solidity.Yul.Checks.RawIntegerInitialization.Fixture.initial = .halted .timeout Solidity.Yul.Checks.RawIntegerInitialization.Fixture.initial ∧
 Solidity.Yul.RawIntegerInitialization.run Solidity.Source.IntTy.u8 255 Solidity.Yul.Checks.RawIntegerInitialization.ranges.1 1 Solidity.Yul.Checks.RawIntegerInitialization.Fixture.initial = .halted .timeout Solidity.Yul.Checks.RawIntegerInitialization.Fixture.initial ∧
 Solidity.Yul.RawIntegerInitialization.run Solidity.Source.IntTy.u8 255 Solidity.Yul.Checks.RawIntegerInitialization.ranges.1 2 Solidity.Yul.Checks.RawIntegerInitialization.Fixture.initial = .normal Solidity.Yul.Checks.RawIntegerInitialization.afterUnsigned ∧
 Solidity.Yul.RawIntegerInitialization.run Solidity.Yul.Checks.RawIntegerInitialization.Fixture.signed8 (-128) Solidity.Yul.Checks.RawIntegerInitialization.ranges.2.1 2 Solidity.Yul.Checks.RawIntegerInitialization.afterUnsigned = .normal Solidity.Yul.Checks.RawIntegerInitialization.afterPair := by
  exact ⟨rfl,rfl,rfl,rfl⟩

theorem values : (Solidity.Yul.LocalValues.get Solidity.Yul.Checks.RawIntegerInitialization.afterPair.values .here).clean? = some (Solidity.Source.Val.int (-128) Solidity.Yul.Checks.RawIntegerInitialization.ranges.2.1) ∧
 (Solidity.Yul.LocalValues.get Solidity.Yul.Checks.RawIntegerInitialization.afterPair.values (.there .here)).clean? = some (Solidity.Source.Val.int 255 Solidity.Yul.Checks.RawIntegerInitialization.ranges.1) ∧
 (Solidity.Yul.LocalValues.get Solidity.Yul.Checks.RawIntegerInitialization.afterPair.values (.there (.there .here))).scalar? = some (Solidity.Yul.word 2) ∧
 (Solidity.Yul.LocalValues.get Solidity.Yul.Checks.RawIntegerInitialization.afterPair.values (.there (.there (.there (.there .here))))).scalar? = some (Solidity.Yul.word 257) := by
  exact ⟨rfl,rfl,rfl,rfl⟩

theorem sourcePair : ∀ (glob : Solidity.Source.Glob Solidity.Yul.Checks.RawIntegerInitialization.Fixture.env) (frame : Solidity.Source.Fr)
 (fuel nps : Nat) (ph : Option (Solidity.Source.Ph Solidity.Yul.Checks.RawIntegerInitialization.Fixture.env)),
 (Solidity.Source.execItems glob frame (fuel+4) nps ph Solidity.Yul.Checks.RawIntegerInitialization.combined Solidity.Yul.Checks.RawIntegerInitialization.Fixture.initial.clean).run
 (Solidity.Source.L0 Solidity.Yul.Checks.RawIntegerInitialization.Fixture.env,Solidity.Yul.Checks.RawIntegerInitialization.Fixture.initial.world) =
 (.ok (.normal Solidity.Yul.Checks.RawIntegerInitialization.afterPair.clean),(Solidity.Source.L0 Solidity.Yul.Checks.RawIntegerInitialization.Fixture.env,Solidity.Yul.Checks.RawIntegerInitialization.Fixture.initial.world)) := by
  intro glob frame fuel nps ph; rfl



theorem sourceTimeout : ∀ (glob : Solidity.Source.Glob Solidity.Yul.Checks.RawIntegerInitialization.Fixture.env) (frame : Solidity.Source.Fr)
 (nps : Nat) (ph : Option (Solidity.Source.Ph Solidity.Yul.Checks.RawIntegerInitialization.Fixture.env)),
 (Solidity.Source.execItems glob frame 3 nps ph Solidity.Yul.Checks.RawIntegerInitialization.combined Solidity.Yul.Checks.RawIntegerInitialization.Fixture.initial.clean).run
 (Solidity.Source.L0 Solidity.Yul.Checks.RawIntegerInitialization.Fixture.env,Solidity.Yul.Checks.RawIntegerInitialization.Fixture.initial.world) =
 (.error .timeout,(Solidity.Source.L0 Solidity.Yul.Checks.RawIntegerInitialization.Fixture.env,Solidity.Yul.Checks.RawIntegerInitialization.Fixture.initial.world)) := by
  intro glob frame nps ph; rfl

#print axioms Solidity.Yul.RawIntegerInitialization.fits
#print axioms Solidity.Yul.RawIntegerInitialization.conversion
#print axioms Solidity.Yul.RawIntegerInitialization.admissible
#print axioms Solidity.Yul.RawIntegerInitialization.correct
#print axioms ranges
#print axioms refusals
#print axioms outcomes
#print axioms values
#print axioms sourcePair
#print axioms sourceTimeout
#print axioms concreteUnsigned
#print axioms concreteWide

end Solidity.Yul.Checks.RawIntegerInitialization
