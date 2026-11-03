import Solidity.Yul.RawSourceVoidReturn
import Solidity.Yul.Checks.LocalBlock

namespace Solidity.Yul.Checks.RawSourceVoidReturn
namespace Old
export Solidity.Yul.Checks.LocalBlock (ctx env locals flag small)
end Old

def dirty : RawFrame.State Old.ctx :=
  RawFrame.write (RawFrame.write
    (RawFrame.ofClean Old.locals (Solidity.Source.St.init Old.env))
    Old.flag (word 2)) Old.small (word 257)
def tail : Solidity.Source.RItems Old.env [] false ⟨false,false⟩
    Old.ctx.tys (.bool :: Old.ctx.tys) :=
  .stmt (.declVar .bool) .nil
def body : Solidity.Source.RStmt Old.env [] false ⟨false,false⟩ Old.ctx.tys Old.ctx.tys :=
  .block (.stmt (.ret rfl) tail)
def witness : Nonempty (Solidity.Source.RStmt Old.env [] false ⟨false,false⟩ Old.ctx.tys Old.ctx.tys) :=
  ⟨body⟩

def returned {output} (result : Solidity.Source.R
    (Solidity.Source.Out Old.env.layout Old.ctx.tys output) × RawFrame.State Old.ctx) : Bool :=
  match result.1 with
  | .ok (.ret _) => true
  | _ => false

def timeout {output} (result : Solidity.Source.R
    (Solidity.Source.Out Old.env.layout Old.ctx.tys output) × RawFrame.State Old.ctx) : Bool :=
  match result.1 with
  | .error .timeout => true
  | _ => false

def concrete (glob : Solidity.Source.Glob Old.env) (frame : Solidity.Source.Fr)
    (fuel nps : Nat) (ph : Option (Solidity.Source.Ph Old.env)) :=
  Solidity.Yul.RawSourceVoidReturn.block_correct Old.ctx false ⟨false,false⟩
    glob frame fuel nps ph dirty (.bool :: Old.ctx.tys) tail

theorem horizons : (
Solidity.Yul.Checks.RawSourceVoidReturn.timeout (Solidity.Yul.RawSourceVoidReturn.run (output := Solidity.Yul.Checks.RawSourceVoidReturn.Old.ctx.tys) 0 Solidity.Yul.Checks.RawSourceVoidReturn.dirty) = true ∧
Solidity.Yul.Checks.RawSourceVoidReturn.returned (Solidity.Yul.RawSourceVoidReturn.run (output := Solidity.Yul.Checks.RawSourceVoidReturn.Old.ctx.tys) 1 Solidity.Yul.Checks.RawSourceVoidReturn.dirty) = true ∧
Solidity.Yul.Checks.RawSourceVoidReturn.timeout (Solidity.Yul.RawSourceVoidReturn.items (output := .bool :: Solidity.Yul.Checks.RawSourceVoidReturn.Old.ctx.tys) 1 Solidity.Yul.Checks.RawSourceVoidReturn.dirty) = true ∧
Solidity.Yul.Checks.RawSourceVoidReturn.returned (Solidity.Yul.RawSourceVoidReturn.items (output := .bool :: Solidity.Yul.Checks.RawSourceVoidReturn.Old.ctx.tys) 2 Solidity.Yul.Checks.RawSourceVoidReturn.dirty) = true ∧
Solidity.Yul.Checks.RawSourceVoidReturn.timeout (Solidity.Yul.RawSourceVoidReturn.block 2 Solidity.Yul.Checks.RawSourceVoidReturn.dirty) = true ∧
Solidity.Yul.Checks.RawSourceVoidReturn.returned (Solidity.Yul.RawSourceVoidReturn.block 3 Solidity.Yul.Checks.RawSourceVoidReturn.dirty) = true ∧
 (Solidity.Yul.RawFrame.view (Solidity.Yul.RawSourceVoidReturn.block 3 Solidity.Yul.Checks.RawSourceVoidReturn.dirty).2 Solidity.Yul.Checks.RawSourceVoidReturn.Old.flag).val = 2 ∧
 (Solidity.Yul.RawFrame.view (Solidity.Yul.RawSourceVoidReturn.block 3 Solidity.Yul.Checks.RawSourceVoidReturn.dirty).2 Solidity.Yul.Checks.RawSourceVoidReturn.Old.small).val = 257 ∧
 Solidity.Yul.RawCoherent.coherent Solidity.Yul.Checks.RawSourceVoidReturn.dirty = false
) := by
  decide

theorem retention : (Solidity.Yul.RawSourceVoidReturn.block 0 Solidity.Yul.Checks.RawSourceVoidReturn.dirty).2 =
 Solidity.Yul.Checks.RawSourceVoidReturn.dirty ∧
 (Solidity.Yul.RawSourceVoidReturn.block 3 Solidity.Yul.Checks.RawSourceVoidReturn.dirty).2 =
 Solidity.Yul.Checks.RawSourceVoidReturn.dirty := by
  exact ⟨rfl,rfl⟩

theorem nonvoid : ¬ Nonempty (([Solidity.Source.STy.bool] : List Solidity.Source.STy) = []) := by
  rintro ⟨h⟩; cases h

#print axioms Solidity.Yul.RawSourceVoidReturn.statement_correct
#print axioms Solidity.Yul.RawSourceVoidReturn.items_correct
#print axioms Solidity.Yul.RawSourceVoidReturn.block_correct
#print axioms concrete
#print axioms horizons
#print axioms retention
#print axioms nonvoid

end Solidity.Yul.Checks.RawSourceVoidReturn
