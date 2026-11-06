import Solidity.Yul.Compilation.ScopedVisitorShapes

/-! Actual singleton let plus two zero locals and dependent writes. Fresh
prefixes retire while old-local mutations and caller contents survive. Large
zero prefixes distinguish physical access restrictions from frame capacity. -/
namespace Solidity.Yul.Compilation.ScopedVisitorShapes.Controls
open Backend Scalar LabelExec Closed ProducerExpressions

def innerPair : Fin 2 → Solidity.Yul.Expr [] [] 5 1 :=
  Fin.cases (.local 4) (fun _ => .local 1)
def sumPair : Fin 2 → Solidity.Yul.Expr [] [] 5 1 :=
  Fin.cases (.local 2) (fun _ => .builtin (.pure .add) innerPair)
def orPair : Fin 2 → Solidity.Yul.Expr [] [] 5 1 :=
  Fin.cases (.local 0) (fun _ => .local 2)
def firstStatement : Solidity.Yul.Stmt [] [] ⟨false,false⟩ 5 :=
  .assign (fun _ : Fin 1 => .local 0) (.builtin (.pure .add) sumPair)
def tailStatement : Solidity.Yul.Stmt [] [] ⟨false,false⟩ 5 :=
  .seq (.assign (fun _ : Fin 1 => .local 3) (.builtin (.pure .or) orPair))
    (.assign (fun _ : Fin 1 => .local 4) (.local 0))
def body : Solidity.Yul.Stmt [] [] ⟨false,false⟩ 5 := .seq firstStatement tailStatement
def firstCompiled := (ScopedStatements.compile 4 firstStatement).get (by rfl)
def tailCompiled := (ScopedStatements.compile 4 tailStatement).get (by rfl)
def bodyCompiled := (ScopedStatements.compile 5 body).get (by rfl)
def statement : Solidity.Yul.Stmt [] [] ⟨false,false⟩ 2 := .let_ 1 (.local 0) (.zero 2 body)
def compiled := (ScopedStatements.compile 7 statement).get (by rfl)
def code := (compiled.lowered.code 0).get (by rfl)
def result (a b : Scalar.Word) : Scalar.Word := a+(b+0)
def dirty : Scalar.Word := BitVec.ofNat 256 (2^200+257)

theorem actual_visit : ScopedStatements.compile 7 statement = some compiled :=
  (Option.some_get (by rfl)).symm

theorem shape : CodeShape code 2 2 :=
  visit_shape 7 statement compiled actual_visit 0 code (Option.some_get (by rfl)).symm

private theorem first_update (a b : Scalar.Word) :
    firstCompiled.update #v[0,0,a,a,b] = #v[result a b,0,a,a,b] := by rfl

private theorem tail_update (x a b : Scalar.Word) :
    tailCompiled.update #v[x,0,a,a,b] = #v[x,0,a,x ||| a,x] := by rfl

private theorem body_decomposition : bodyCompiled = ProducerStatements.seq firstCompiled tailCompiled := by rfl

private theorem body_update (a b : Scalar.Word) :
    bodyCompiled.update #v[0,0,a,a,b] = #v[result a b,0,a,result a b ||| a,result a b] := by
  rw [body_decomposition]
  change tailCompiled.update (firstCompiled.update #v[0,0,a,a,b]) = _
  rw [first_update]
  exact tail_update (result a b) a b

private theorem compiled_decomposition :
    compiled = ScopedStatements.letOne (localExpr 5 (0 : Fin 2)) (ScopedStatements.zero bodyCompiled) := by rfl

theorem update (a b : Scalar.Word) : compiled.update #v[a,b] = #v[result a b ||| a,result a b] := by
  rw [compiled_decomposition]
  change outerLocals (fresh := 1) (n := 2)
    (outerLocals (fresh := 2) (n := 3) (bodyCompiled.update #v[0,0,a,a,b])) = _
  rw [body_update]
  rfl

theorem source (a b : Scalar.Word) :
    evalStmt 7 .nil True.intro statement compiled.profile (sourceLocals #v[a,b]) =
      some ⟨sourceLocals #v[result a b ||| a,result a b],.normal⟩ :=
  (compiled.source #v[a,b]).trans
    (congrArg (fun locals : Vector Scalar.Word 2 =>
      some (⟨sourceLocals locals,.normal⟩ : Outcome ⟨false,false⟩ 2)) (update a b))

theorem target_run (a b : Scalar.Word) (caller : Stack) :
    run code ([a,b]++caller) = some ([result a b ||| a,result a b]++caller) := by
  have actual : run code ([a,b]++caller) = some ((compiled.update #v[a,b]).toList++caller) := by
    simpa only [Vector.toList_empty,List.nil_append] using
      compiled.lowered.correct 0 code (Option.some_get (by rfl)).symm #v[a,b] #v[] caller
  exact actual.trans (congrArg (fun locals : Vector Scalar.Word 2 => some (locals.toList++caller)) (update a b))

theorem result_zero (a : Scalar.Word) : result a 0 = a := by
  change a+(0 : Scalar.Word) = a
  exact BitVec.add_zero a

theorem target_zero (a : Scalar.Word) (caller : Stack) :
    run code ([a,0]++caller) = some ([a,a]++caller) := by
  have value : result a 0 ||| a = a := by simp only [result_zero,BitVec.or_self]
  have same : (result a 0 ||| a,result a 0) = (a,a) := Prod.ext value (result_zero a)
  exact (target_run a 0 caller).trans
    (congrArg (fun pair : Scalar.Word × Scalar.Word => some ([pair.1,pair.2]++caller)) same)

theorem dirty_run (caller : Stack) : run code ([dirty,0]++caller) = some ([dirty,dirty]++caller) :=
  target_zero dirty caller

def largeStatement : Solidity.Yul.Stmt [] [] ⟨false,false⟩ 2 := .zero 17 .skip
def largeCompiled := (ScopedStatements.compile 2 largeStatement).get (by rfl)
def largeCode := (largeCompiled.lowered.code 0).get (by rfl)

theorem large_shape : CodeShape largeCode 2 2 :=
  visit_shape 2 largeStatement largeCompiled (Option.some_get (by rfl)).symm
    0 largeCode (Option.some_get (by rfl)).symm

theorem large_run (a b : Scalar.Word) (caller : Stack) :
    run largeCode ([a,b]++caller) = some ([a,b]++caller) := by
  simpa only [Vector.toList_empty,List.nil_append] using
    largeCompiled.lowered.correct 0 largeCode (Option.some_get (by rfl)).symm #v[a,b] #v[] caller

/-- Seventeen fresh locals are legal when no inaccessible slot is addressed. -/
theorem large_capacity_last : stackBound largeCode 1007 = true := by decide

theorem large_capacity_next : stackBound largeCode 1008 = false := by decide

def largePacket : Code 1007 1007 :=
  packet largeStatement largeCompiled (Option.some_get (by rfl)).symm 0 1005 largeCode
    (Option.some_get (by rfl)).symm large_capacity_last

theorem packet_instructions : largePacket.instructions = largeCode := by rfl

theorem large_oversized (a b : Scalar.Word) (caller : Vector Scalar.Word 1006) :
    run largeCode ([a,b]++caller.toList) = some ([a,b]++caller.toList) ∧
      stackBound largeCode 1008 = false := ⟨large_run a b caller.toList,large_capacity_next⟩

def inaccessible : Solidity.Yul.Stmt [] [] ⟨false,false⟩ 2 := .zero 17
  (.assign (fun _ : Fin 1 => .local 16) (.literal (word 99)))
def inaccessibleCompiled := (ScopedStatements.compile 3 inaccessible).get (by rfl)

theorem source_without_emission (a b : Scalar.Word) :
    evalStmt 3 .nil True.intro inaccessible inaccessibleCompiled.profile (sourceLocals #v[a,b]) =
      some ⟨sourceLocals #v[a,b],.normal⟩ := inaccessibleCompiled.source #v[a,b]

#guard (ScopedStatements.compile 6 statement).isNone
#guard compiled.lowered.code 1 = none
#guard inaccessibleCompiled.lowered.code 0 = none
#guard run code [] = none
#guard (ScopedStatements.compile 3 (Solidity.Yul.Stmt.if_ (c := ⟨false,false⟩) (n := 2)
  (.literal (word 1)) .skip)).isNone

/-- info: 'Solidity.Yul.Compilation.ScopedVisitorShapes.Controls.actual_visit' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in #print axioms actual_visit
/-- info: 'Solidity.Yul.Compilation.ScopedVisitorShapes.Controls.shape' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms shape
/-- info: 'Solidity.Yul.Compilation.ScopedVisitorShapes.Controls.update' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in #print axioms update
/-- info: 'Solidity.Yul.Compilation.ScopedVisitorShapes.Controls.source' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in #print axioms source
/-- info: 'Solidity.Yul.Compilation.ScopedVisitorShapes.Controls.target_run' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in #print axioms target_run
/-- info: 'Solidity.Yul.Compilation.ScopedVisitorShapes.Controls.result_zero' depends on axioms: [propext] -/
#guard_msgs in #print axioms result_zero
/-- info: 'Solidity.Yul.Compilation.ScopedVisitorShapes.Controls.target_zero' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in #print axioms target_zero
/-- info: 'Solidity.Yul.Compilation.ScopedVisitorShapes.Controls.dirty_run' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in #print axioms dirty_run
/-- info: 'Solidity.Yul.Compilation.ScopedVisitorShapes.Controls.large_shape' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in #print axioms large_shape
/-- info: 'Solidity.Yul.Compilation.ScopedVisitorShapes.Controls.large_run' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in #print axioms large_run
/-- info: 'Solidity.Yul.Compilation.ScopedVisitorShapes.Controls.large_capacity_last' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in #print axioms large_capacity_last
/-- info: 'Solidity.Yul.Compilation.ScopedVisitorShapes.Controls.large_capacity_next' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in #print axioms large_capacity_next
/-- info: 'Solidity.Yul.Compilation.ScopedVisitorShapes.Controls.packet_instructions' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in #print axioms packet_instructions
/-- info: 'Solidity.Yul.Compilation.ScopedVisitorShapes.Controls.large_oversized' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in #print axioms large_oversized
/-- info: 'Solidity.Yul.Compilation.ScopedVisitorShapes.Controls.source_without_emission' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in #print axioms source_without_emission
/-- info: 'Solidity.Yul.Compilation.ScopedVisitorShapes.Controls.largePacket' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in #print axioms largePacket

end Solidity.Yul.Compilation.ScopedVisitorShapes.Controls
