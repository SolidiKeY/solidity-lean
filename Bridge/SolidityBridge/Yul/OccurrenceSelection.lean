import SolidityBridge.Yul.ByteSelection
/-! Position-indexed proof data over the EXISTING instruction list, not a new
IR/AST or evaluator. Distinct occurrences may carry different real encodings.
Old membership-indexed interfaces remain unchanged. Native/G24 stays separate. -/
namespace SolidityBridge.Yul.OccurrenceSelection
open Solidity Backend Scalar Selection
open Solidity.Yul.Compilation

abbrev Certificates (ir : List Evm.Instr) :=
  (position : Fin ir.length) → InstructionCertificate (ir.get position)

def emit : (ir : List Evm.Instr) → Certificates ir → Backend.Program
  | [],_ => []
  | _i::rest,pick => (pick ⟨0,Nat.zero_lt_succ rest.length⟩).code ++ emit rest (fun j => pick j.succ)

theorem execute :
∀ (ir : List Solidity.Evm.Instr) (pick : SolidityBridge.Yul.OccurrenceSelection.Certificates ir)
 (input : Solidity.Backend.Scalar.Stack) (m : Solidity.Evm.Machine),
 m.stack = Solidity.Backend.Selection.irStack input →
 Solidity.Evm.run ir m = match Solidity.Backend.Scalar.run (SolidityBridge.Yul.OccurrenceSelection.emit ir pick) input with
 | none => .fault
 | some output => .ok {m with stack := Solidity.Backend.Selection.irStack output} 0 := by
  intro ir
  induction ir with
  | nil =>
    intro pick input m represented
    simp only [SolidityBridge.Yul.OccurrenceSelection.emit,Solidity.Backend.Scalar.run,Solidity.Evm.run,Solidity.Evm.exec,←represented]
  | cons i rest ih =>
    intro pick input m represented
    let head := pick ⟨0,Nat.zero_lt_succ rest.length⟩
    let more : SolidityBridge.Yul.OccurrenceSelection.Certificates rest := fun j => pick j.succ
    change Solidity.Evm.run (i::rest) m =
      match Solidity.Backend.Scalar.run (head.code ++ SolidityBridge.Yul.OccurrenceSelection.emit rest more) input with
      | none => .fault
      | some output => .ok {m with stack := Solidity.Backend.Selection.irStack output} 0
    rw [Solidity.Backend.Scalar.run_append]
    cases found : Solidity.Backend.Scalar.run head.code input with
    | none =>
      have fault : i.step m = .fault := (head.refusal input m represented).mpr found
      simp only [Option.bind_none,Solidity.Evm.run,Solidity.Evm.exec,fault,Solidity.Evm.Out.bind]
    | some middle =>
      have step : i.step m = .ok {m with stack := Solidity.Backend.Selection.irStack middle} 0 :=
        (head.success input middle m represented).mpr found
      have next := ih more middle {m with stack := Solidity.Backend.Selection.irStack middle} rfl
      simp only [Option.bind_some,Solidity.Evm.run,Solidity.Evm.exec,step,Solidity.Evm.Out.bind]
      simpa only [Solidity.Evm.run] using next

/-- Proof package for one EXISTING Backend.Instr, not replacement syntax. -/
structure Step (code : Backend.Instr) where
  ir : Evm.Instr
  certificate : InstructionCertificate ir
  origin : certificate.code = [code]

def checkStep (code : Backend.Instr) (ir : Evm.Instr)
    (certificate : InstructionCertificate ir) : Option (Step code) :=
  if origin : certificate.code = [code] then some ⟨ir,certificate,origin⟩ else none

def selectStep (code : Backend.Instr) : Option (Step code) := do
  let ir ← SignedMachine.selectInstr code
  ((ExpSelection.select ir).bind (checkStep code ir)).orElse (fun _ =>
    (ByteSelection.select ir).bind (checkStep code ir))

structure Slice (code : Backend.Program) where
  ir : List Evm.Instr
  certificates : Certificates ir
  origin : emit ir certificates = code

def selectCode : (code : Backend.Program) → Option (Slice code)
  | [] => some ⟨[],(fun position => Fin.elim0 position),rfl⟩
  | i::rest => do
      let head ← selectStep i
      let more ← selectCode rest
      let pick : Certificates (head.ir::more.ir) :=
        fun position => Fin.cases head.certificate (fun j => more.certificates j) position
      pure ⟨head.ir::more.ir,pick,by
        simp only [emit,pick,Fin.zero_eta,Fin.cases_zero,Fin.cases_succ,head.origin,more.origin,List.singleton_append]⟩

def lowering :
∀ (code : Solidity.Backend.Program) (slice : SolidityBridge.Yul.OccurrenceSelection.Slice code), Solidity.Backend.Selection.LoweringCertificate slice.ir (.code code) := by
  intro code slice
  constructor
  intro input output m represented
  have law := SolidityBridge.Yul.OccurrenceSelection.execute slice.ir slice.certificates input m represented
  rw [slice.origin] at law
  constructor
  · intro ran
    cases executed : Solidity.Backend.Scalar.run code input with
    | none =>
      rw [executed] at law
      have impossible : Solidity.Evm.Out.fault = .ok {m with stack := Solidity.Backend.Selection.irStack output} 0 := law.symm.trans ran
      cases impossible
    | some actual =>
      rw [executed] at law
      change Solidity.Evm.run slice.ir m = .ok {m with stack := Solidity.Backend.Selection.irStack actual} 0 at law
      have mapped : Solidity.Backend.Selection.irStack actual = Solidity.Backend.Selection.irStack output :=
        congrArg Solidity.Evm.Machine.stack (Solidity.Evm.Out.ok.inj (law.symm.trans ran)).1
      have same : actual = output := SolidityBridge.Yul.ArithmeticSelection.irStack_injective mapped
      exact Solidity.Backend.Selection.StructuredExec.code (executed.trans (congrArg some same))
  · intro executed
    cases executed with
    | code run => rw [run] at law; exact law

theorem fault_iff :
∀ (code : Solidity.Backend.Program) (slice : SolidityBridge.Yul.OccurrenceSelection.Slice code)
 (input : Solidity.Backend.Scalar.Stack) (m : Solidity.Evm.Machine),
 m.stack = Solidity.Backend.Selection.irStack input →
 (Solidity.Evm.run slice.ir m = .fault ↔ Solidity.Backend.Scalar.run code input = none) := by
  intro code slice input m represented
  have law := SolidityBridge.Yul.OccurrenceSelection.execute slice.ir slice.certificates input m represented
  rw [slice.origin] at law
  rw [law]
  cases Solidity.Backend.Scalar.run code input <;> simp only [reduceCtorEq]

theorem source_model :
∀ {fuel n : Nat} {c : Solidity.Yul.Control} {stmt : Solidity.Yul.Stmt [] [] c n}
 (producer : Solidity.Yul.Compilation.ProducerStatements.Compiled fuel stmt)
 (depth : Nat) (code : Solidity.Backend.Program), producer.lowered.code depth = some code →
 ∀ (slice : SolidityBridge.Yul.OccurrenceSelection.Slice code) (locals : Vector Solidity.Backend.Scalar.Word n)
 (newer : Vector Solidity.Backend.Scalar.Word depth) (tail : Solidity.Backend.Scalar.Stack) (m : Solidity.Evm.Machine),
 m.stack = Solidity.Backend.Selection.irStack (newer.toList ++ (locals.toList ++ tail)) →
 Solidity.Yul.Closed.evalStmt fuel .nil True.intro stmt producer.profile
 (Solidity.Yul.Compilation.ProducerExpressions.sourceLocals locals) =
 some ⟨Solidity.Yul.Compilation.ProducerExpressions.sourceLocals (producer.update locals),.normal⟩ ∧
 Solidity.Evm.run slice.ir m = .ok {m with stack := Solidity.Backend.Selection.irStack (newer.toList ++ ((producer.update locals).toList ++ tail))} 0 := by
  intro fuel n c stmt producer depth code emitted slice locals newer tail m represented
  have scalar := producer.lowered.correct depth code emitted locals newer tail
  have transport := SolidityBridge.Yul.OccurrenceSelection.execute slice.ir slice.certificates
    (newer.toList ++ (locals.toList ++ tail)) m represented
  rw [slice.origin,scalar] at transport
  exact ⟨producer.source locals,transport⟩

/-- Same model PUSH, two genuinely different existing instruction encodings. -/
def mixedCode : Backend.Program := [pushWord 31,pushByte 31,.op .ADD]
def mixedSelected := (selectCode mixedCode).get (by rfl)
def mixedLowering := lowering mixedCode mixedSelected

/-- A real original-source BYTE assignment with PUSH32 argument and PUSH1
expansion constants, including two encodings of the numerical value31. -/
def statement : Solidity.Yul.Stmt [] [] ⟨false,false⟩ 3 :=
  .assign (fun _ : Fin 1 => .local 0)
    (.builtin (.pure .byte) (Fin.cases (.literal (Solidity.Yul.word 31)) (fun _ => .local 1)))
def compiled := (PureStatements.compile 3 statement).get (by rfl)
def code := (compiled.lowered.code 0).get (by rfl)
def selected := (selectCode code).get (by rfl)
def assignmentLowering := lowering code selected
abbrev assignment_model := source_model compiled 0 code (by rfl) selected

def prefixedCode := (compiled.lowered.code 2).get (by rfl)
def prefixed := (selectCode prefixedCode).get (by rfl)
def prefixedLowering := lowering prefixedCode prefixed
abbrev prefixed_model := source_model compiled 2 prefixedCode (by rfl) prefixed

end SolidityBridge.Yul.OccurrenceSelection
