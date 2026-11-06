import Solidity.Lowering.Readonly.ReadStatement
import Solidity.Source.SemanticsExamples

/-! Named non-head root controls, using the ALREADY published source deployment
fixture as a reachable input state. No new creation semantics/lowering is proved. -/
namespace Solidity.Lowering.Readonly.RootControls
open Solidity.Source Solidity.Source.SemanticsExamples
open PrimitiveValues PrimitiveFields

def Pair : Contract := contract!{ uint a; uint b; }
def layout : PrimitiveFields.Layout EAB Pair where
  fields := .field "a" .uint dA (by rfl) rfl dA_ty rfl (by rfl) (by rfl)
    (.field "b" .uint dB (by rfl) rfl dB_ty rfl (by rfl) (by rfl) .nil)
  persistent := rfl

def source : St EAB :=
  (runAt (fun n => deploy (GAB .legacy) n "B" thisC user (word 0) []) (St.init EAB) 20).2

def target : Solidity.Storage Pair :=
  .cons (.prim ⟨2, by decide⟩) (.cons (.prim ⟨1, by decide⟩) .nil)

def frame : Fr := { FC with contract := "B", static := true }

theorem related : Rel layout.fields thisC (source.ex.world.accounts thisC).storage target := by
  exact ⟨rfl, rfl, True.intro⟩

theorem inherited_ownership : Owned layout.fields "B" := by
  exact ⟨⟨"A", rfl, by decide⟩, ⟨"B", rfl, rfl⟩, True.intro⟩

/-- The generic simulation selects the SECOND field with its exact declaration
and value, deriving both actual evaluator runs from the full field relation. -/
theorem tail_simulation : ∃ binding : Binding EAB "b" .uint, ∃ value : PrimTy.uint.Denote,
    (evalE (GAB .legacy) frame 1 (.state binding.declaration binding.signature) : EM EAB [] _).run
      (.nil, source) = (.ok (.val (toSource EAB.layout .uint value)), (.nil, source)) ∧
    (Solidity.Val.read (.root "b" rfl) : Solidity.Val Pair [] .uint).evalT
      (Solidity.State.ofStorage target) = .ok value :=
  PrimitiveReads.root_expression (GAB .legacy) frame 0 layout.fields .nil source
    (Solidity.State.ofStorage target) "b" .uint rfl related

theorem source_tail :
    (evalE (GAB .legacy) frame 1 (.state dB dB_ty) : EM EAB [] _).run (.nil, source) =
      (.ok (.val (toSource EAB.layout .uint ⟨1, by decide⟩)), (.nil, source)) := by rfl

theorem target_tail :
    (Solidity.Val.read (.root "b" rfl) : Solidity.Val Pair [] .uint).evalT
      (Solidity.State.ofStorage target) = .ok ⟨1, by decide⟩ := by rfl

theorem tail_not_head :
    (Solidity.Val.read (.root "b" rfl) : Solidity.Val Pair [] .uint).evalT
      (Solidity.State.ofStorage target) ≠ .ok ⟨2, by decide⟩ := by
  rw [target_tail]
  intro impossible
  cases impossible

def targetWithLocal : Solidity.State Pair [.val .bool] :=
  (Solidity.State.ofStorage target).push (t := .val .bool) true

theorem statement_simulation : ∃ binding : Binding EAB "b" .uint,
    (execS (GAB .legacy) frame 2 0 none
      (RStmt.expr (R := []) (M := false) (k := .body) (.state binding.declaration binding.signature))
      (.cons (.bool true) .nil)).run (L0 EAB, source) =
        (.ok (.normal (.cons (.bool true) .nil)), (L0 EAB, source)) ∧
    (ReadStatement.target "b" .uint rfl : Solidity.Stmt Pair [.val .bool] [.val .bool]).run
      targetWithLocal = .ok ⟨targetWithLocal, List.prefix_refl _⟩ :=
  ReadStatement.simulation (GAB .legacy) frame 0 0 none layout.fields (.cons (.bool true) .nil)
    source targetWithLocal "b" .uint rfl related

def writingTail : Prog Pair [.val .bool] [.val .bool] :=
  .cons (.assign (.root "b" rfl) (.val (.simple (.lit 9 (by decide))))) .nil

theorem continuation_kept :
    Prog.run targetWithLocal (.cons (ReadStatement.target "b" .uint rfl) writingTail) =
      Prog.run targetWithLocal writingTail :=
  ReadStatement.target_then targetWithLocal "b" .uint rfl ⟨1, by decide⟩ (by rfl) writingTail

theorem continuation_halt_kept :
    Prog.run targetWithLocal (.cons (ReadStatement.target "b" .uint rfl)
      (.cons .revert .nil)) = .error .revert := by
  rw [ReadStatement.target_then targetWithLocal "b" .uint rfl ⟨1, by decide⟩ (by rfl)]
  rfl

end Solidity.Lowering.Readonly.RootControls
