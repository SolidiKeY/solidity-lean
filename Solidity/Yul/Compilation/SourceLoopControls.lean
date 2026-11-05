import Solidity.Yul.Compilation.SourceLoop
import Solidity.Yul.Compilation.PureExpressions
import Solidity.Yul.Compilation.ScopedStatements
import Solidity.Yul.Compilation.WordBlockFramed
/-! An actual intrinsic for with normal body/post: decrement counter, NOT the
second word, then ADD3 in the post-step. Same raw words and exact source horizon
are paired with real emitted model code; early control/native/G24 remain open. -/
namespace Solidity.Yul.Compilation.SourceLoop.Controls
open Backend Scalar MachineAdapter Solidity.Yul.Closed ProducerExpressions

def root : Solidity.Yul.Control := ⟨false,false⟩
def test : Solidity.Yul.Expr [] [] 2 1 := .local 0
def work : Solidity.Yul.Stmt [] [] ⟨false,true⟩ 2 := .seq
 (.assign (fun _ : Fin 1 => .local 0)
  (.builtin (.pure .sub) (Fin.cases (.local 0) (fun _ => .literal 1))))
 (.assign (fun _ : Fin 1 => .local 1) (.builtin (.pure .not) (fun _ => .local 1)))
def step : Solidity.Yul.Stmt [] [] ⟨false,false⟩ 2 :=
 .assign (fun _ : Fin 1 => .local 1)
  (.builtin (.pure .add) (Fin.cases (.local 1) (fun _ => .literal 3)))
def condition := (PureExpressions.compile 1 test).get (by rfl)
def body := (ScopedStatements.compile 5 work).get (by rfl)
def post := (ScopedStatements.compile 4 step).get (by rfl)
def source : Solidity.Yul.Stmt [] [] root 2 := .for_ .skip test step work
def words : StmtWordP source := ⟨True.intro,condition.profile,post.profile,body.profile⟩
def dirty : Scalar.Word := BitVec.ofNat 256 (2^200+257)
def block := (emit (c := root) condition post body 0).get (by rfl)
def code := (WordControl.blockCode block).get (by rfl)
def certificate : Backend.Selection.FramedLoweringCertificate code block :=
 WordBlockFramed.certificate block code (Option.some_get (by rfl)).symm

theorem update_eq (a b : Scalar.Word) :
 next (c := root) body post #v[a,b] = #v[a-1,~~~b+3] := rfl

theorem repeat_two (b : Scalar.Word) :
 Nat.repeat (next (c := root) body post) 2 #v[2,b] = #v[0,~~~(~~~b+3)+3] := by
 change next (c := root) body post (next (c := root) body post #v[2,b]) = _
 rewrite [update_eq,update_eq]
 rfl

theorem guards_two (b : Scalar.Word) :
 ∀ j, j < 2 → condition.value (Nat.repeat (next (c := root) body post) j #v[2,b]) ≠ 0 := by
 intro j bound
 have cases : j = 0 ∨ j = 1 := by omega
 rcases cases with rfl | rfl
 · change (2 : Scalar.Word) ≠ 0; decide
 · change condition.value (next (c := root) body post #v[2,b]) ≠ 0
   rewrite [update_eq]
   change (1 : Scalar.Word) ≠ 0
   decide

theorem stopped_two (b : Scalar.Word) :
 condition.value (Nat.repeat (next (c := root) body post) 2 #v[2,b]) = 0 := by
 rewrite [repeat_two]
 rfl

/-- Original for evaluator and the ACTUAL selected artifact jointly succeed;
the source horizon9 is constructed, not a raised proof or execution budget. -/
theorem source_and_target (b : Scalar.Word) (m : Evm.Machine) (caller : List Evm.Word) :
 (evalStmt 9 .nil True.intro source words (sourceLocals #v[2,b]) =
  some ⟨sourceLocals #v[0,~~~(~~~b+3)+3],.normal⟩) ∧
 Evm.run code {m with stack := [coreWord 2,coreWord b]++caller} =
 .ok {m with stack := [coreWord 0,coreWord (~~~(~~~b+3)+3)]++caller} 0 := by
 have both := compiled_finite (c := root) condition post body 0 block code
  (Option.some_get (by rfl)).symm (Option.some_get (by rfl)).symm
  2 #v[2,b] #v[] m caller (guards_two b) (stopped_two b)
 simpa only [Vector.toList_empty,List.nil_append,repeat_two,List.map_cons,List.map_nil] using both

/-- Zero turns still evaluate the original condition and skip initializer;
body and post do not run. -/
theorem source_zero (b : Scalar.Word) :
 evalStmt 7 .nil True.intro source words (sourceLocals #v[0,b]) =
 some ⟨sourceLocals #v[0,b],.normal⟩ :=
 for_finite (c := root) condition post body 0 #v[0,b] (by intro j h; omega) (by rfl)

#guard (evalStmt 0 .nil True.intro source words (sourceLocals #v[2,dirty])).isNone
#guard (evalStmt 1 .nil True.intro source words (sourceLocals #v[2,dirty])).isNone
#guard condition.value (Nat.repeat (next (c := root) body post) 1 #v[2,dirty]) ≠ 0
#guard (emit (c := root) condition post body 15).isNone
#guard next (c := root) body post #v[2,dirty] = #v[1,~~~dirty+3]
#guard Nat.repeat (next (c := root) body post) 2 #v[2,dirty] = #v[0,dirty]
/-- info: 'Solidity.Yul.Compilation.SourceLoop.Controls.certificate' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms certificate
/-- info: 'Solidity.Yul.Compilation.SourceLoop.Controls.update_eq' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms update_eq
/-- info: 'Solidity.Yul.Compilation.SourceLoop.Controls.repeat_two' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms repeat_two
/-- info: 'Solidity.Yul.Compilation.SourceLoop.Controls.guards_two' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms guards_two
/-- info: 'Solidity.Yul.Compilation.SourceLoop.Controls.stopped_two' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms stopped_two
/-- info: 'Solidity.Yul.Compilation.SourceLoop.Controls.source_and_target' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms source_and_target
/-- info: 'Solidity.Yul.Compilation.SourceLoop.Controls.source_zero' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms source_zero
end Solidity.Yul.Compilation.SourceLoop.Controls
