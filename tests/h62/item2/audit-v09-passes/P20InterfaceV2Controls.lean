import Solidity.Backend.Selection.P20Consumer
import Solidity.Yul.Compilation.P20InterfaceV2
import Solidity.Yul.Compilation.P20InterfaceV1Controls
import Solidity.Backend.Passes.AssignmentSubtractionControls

/-! Regression: a nontrivial memory-backed local store must jointly satisfy
actual checked selection, G24 Input/Rep, original Yul execution and environment
readback. The V1 unrestricted stack-only certificate remains a negative control.
This single wide-uint local slice does not establish general P20 adequacy. -/
namespace Solidity.Yul.Compilation.P20.InterfaceV2.Controls
open Backend Scalar Selection Closed ProducerExpressions
open Evm Evm.Compiler
abbrev C := Backend.Passes.AssignmentSubtractionPass.Controls.C
abbrev Γ := Backend.Passes.AssignmentSubtractionPass.Controls.Γ
abbrev F := Backend.Passes.AssignmentSubtractionPass.Controls.F
abbrev target := Backend.Passes.AssignmentSubtractionPass.Controls.target
abbrev machine := Backend.Passes.AssignmentSubtractionPass.Controls.machine
abbrev bases := Backend.Passes.AssignmentSubtractionPass.Controls.bases
abbrev a := Backend.Passes.AssignmentSubtractionPass.Controls.a
abbrev yul := InterfaceV1.Controls.StoreBoundary.producer
abbrev statement := InterfaceV1.Controls.StoreBoundary.statement
abbrev block := InterfaceV1.Controls.StoreBoundary.block
abbrev code := InterfaceV1.Controls.StoreBoundary.code

def stored : PrimTy.uint.Denote := ⟨5,rfl⟩
def program : Solidity.Prog C Γ Γ :=
  .cons (.assignLocal a (.simple (.lit 5 rfl))) .nil
def compilation : Evm.Compiler.Compilation 1 F program :=
  .core F (by first | rfl | decide | omega | simp only [])
def output (σ : State C Γ) : Solidity.Out C σ.H Γ :=
  ⟨σ.setLocal a stored,List.prefix_refl _⟩
def encode (σ : State C Γ) : Vector Scalar.Word 1 :=
  #v[BitVec.ofInt 256 (TEnv.get a σ.env).val]
def encodeOutput (σ : State C Γ) (out : Solidity.Out C σ.H Γ) : Vector Scalar.Word 1 :=
  encode out.st
def domain : State C Γ → Prop := fun _ => True

theorem public_selection : Evm.Compiler.compile 1 F program = some compilation := by
  first | rfl | decide | omega | simp only []
theorem source_run (σ : State C Γ) : program.run σ = .ok (output σ) := by
  first | rfl | decide | omega | simp only []
theorem output_encoding (σ : State C Γ) : encode (output σ).st = #v[5] := by
  first | rfl | decide | omega | simp only []
theorem updated_encoding (σ : State C Γ) :
    yul.update (encode σ) = encode (output σ).st := by
  first | rfl | decide | omega | simp only []
theorem block_run (σ : State C Γ) :
    Scalar.run code (encode σ).toList = some (encode (output σ).st).toList := by
  first | rfl | decide | omega | simp only []

theorem joint_input : compilation.Input 1 64 bases target machine :=
  ⟨Backend.Passes.AssignmentSubtractionPass.Controls.initial.core,by decide⟩

def producerAt (k : Nat) : ProducerStatements.Compiled (k+2) statement :=
  ProducerStatements.assignTargets (fun _ : Fin 1 => .local 0)
    (ProducerExpressions.literal k InterfaceV1.Controls.StoreBoundary.value.toFin)

theorem updated_at (k : Nat) (σ : State C Γ) :
    (producerAt k).update (encode σ) = encode (output σ).st := by
  first | rfl | decide | omega | simp only []

theorem yul_run (k : Nat) (σ : State C Γ) :
    evalStmt (k+2) .nil True.intro statement yul.profile (sourceLocals (encode σ)) =
      some ⟨sourceLocals (encode (output σ).st),.normal⟩ := by
  simpa only [updated_at] using (producerAt k).source (encode σ)

theorem source_forward (σ : State C Γ) (_ : domain σ)
    (out : Solidity.Out C σ.H Γ) (ran : program.run σ = .ok out) :
    ∃ fuel, evalStmt fuel .nil True.intro statement yul.profile (sourceLocals (encode σ)) =
      some ⟨sourceLocals (encodeOutput σ out),.normal⟩ := by
  have same : out = output σ := Except.ok.inj (ran.symm.trans (source_run σ))
  subst out
  exact ⟨2,yul_run 0 σ⟩

theorem source_backward (σ : State C Γ) (_ : domain σ) (fuel : Nat)
    (final : Vector Scalar.Word 1)
    (ran : evalStmt fuel .nil True.intro statement yul.profile (sourceLocals (encode σ)) =
      some ⟨sourceLocals final,.normal⟩) :
    ∃ out : Solidity.Out C σ.H Γ, program.run σ = .ok out ∧ encodeOutput σ out = final := by
  cases fuel with
  | zero => cases ran
  | succ fuel =>
    cases fuel with
    | zero => cases ran
    | succ k =>
      have same := Option.some.inj ((yul_run k σ).symm.trans ran)
      have locals := congrArg Outcome.vars same
      have point := congrFun locals (0 : Fin 1)
      have words : (encode (output σ).st)[0] = final[0] :=
        BitVec.eq_of_toNat_eq (congrArg Fin.val point)
      have vectors : encode (output σ).st = final := by
        apply Vector.ext
        intro i hi
        have zero : i = 0 := by omega
        subst i
        exact words
      exact ⟨output σ,source_run σ,vectors⟩

theorem source_block (σ : State C Γ) (_ : domain σ) (final : Vector Scalar.Word 1) :
    StructuredExec block (encode σ).toList final.toList ↔
      ∃ out : Solidity.Out C σ.H Γ, program.run σ = .ok out ∧ encodeOutput σ out = final := by
  constructor
  · intro trace
    cases trace with
    | code ran =>
      have same : encode (output σ).st = final :=
        Vector.toList_inj.mp (Option.some.inj ((block_run σ).symm.trans ran))
      exact ⟨output σ,source_run σ,same⟩
  · intro execution
    obtain ⟨out,ran,encoding⟩ := execution
    have same : out = output σ := Except.ok.inj (ran.symm.trans (source_run σ))
    subst out
    rw [←encoding]
    exact .code (block_run σ)

def producer : PendingG24 compilation statement yul.profile block domain encode encodeOutput where
  lowering := CheckedLowering.of_source compilation statement yul.profile block domain encode encodeOutput source_block
  required_success := ⟨target,output target,2,True.intro,source_run target,yul_run 0 target⟩
  source_forward := source_forward
  source_backward := source_backward
  required_input :=
    ⟨1,64,bases,target,machine,output target,2,True.intro,joint_input,rfl,source_run target,yul_run 0 target⟩

theorem joint_satisfiable : ∃ link : PendingG24 compilation statement yul.profile block domain encode encodeOutput,
    PendingRepresentedSuccess compilation statement yul.profile block domain encode encodeOutput link :=
  ⟨producer,PendingG24.represented compilation statement yul.profile block domain encode encodeOutput producer⟩

theorem nontrivial : encode target ≠ encode (output target).st := by
  first | decide | rfl | omega | simp only []


/-- The real selected target changes only the actual assigned local cell. -/
theorem actual_store (m : Evm.Machine) :
    Evm.run compilation.code m = .ok (Evm.Memory.writeMachine m 3 (.val (Evm.wmod 5))) 0 := by
  first | rfl | decide | omega | simp only []

theorem aligned_run : Evm.run compilation.code InterfaceV1.Controls.StoreBoundary.aligned =
    .ok InterfaceV1.Controls.StoreBoundary.aligned 0 := by
  change Evm.Out.ok {InterfaceV1.Controls.StoreBoundary.aligned with
    mem := Evm.upd InterfaceV1.Controls.StoreBoundary.aligned.mem 3 (.val (Evm.wmod 5))} 0 = _
  have memory : Evm.upd InterfaceV1.Controls.StoreBoundary.aligned.mem 3 (.val (Evm.wmod 5)) =
      InterfaceV1.Controls.StoreBoundary.aligned.mem := by
    funext address
    change (if address = 3 then Evm.Word.val (Evm.wmod 5) else Evm.Word.val (Evm.wmod 5)) = _
    simp only [ite_self]
    rfl
  rw [memory]

theorem changed :
    (Evm.Memory.writeMachine InterfaceV1.Controls.StoreBoundary.initial 3 (.val (Evm.wmod 5))).mem 3 ≠
      InterfaceV1.Controls.StoreBoundary.initial.mem 3 := by
  first | decide | rfl | omega | simp only []

/-- The V1 obstruction applies to this SAME publicly selected V2 program. -/
theorem no_v1_lowering (other : Backend.Block) :
    ¬ LoweringCertificate compilation.code other :=
  InterfaceV1.no_lowering_of_memory_sensitivity compilation.code other [0] [0]
    InterfaceV1.Controls.StoreBoundary.aligned InterfaceV1.Controls.StoreBoundary.initial
    (Evm.Memory.writeMachine InterfaceV1.Controls.StoreBoundary.initial 3 (.val (Evm.wmod 5)))
    3 rfl rfl aligned_run (actual_store _) changed

theorem no_v1_link :
    ¬ InterfaceV1.PendingG24 compilation statement yul.profile block domain encode encodeOutput := by
  intro link
  exact no_v1_lowering block link.lowering

def represented : PendingRepresentedSuccess compilation statement yul.profile block domain encode encodeOutput producer :=
  PendingG24.represented compilation statement yul.profile block domain encode encodeOutput producer

/-- Original source, stack and branch-specific G24 Rep observations together. -/
theorem complete_success : ∃ (out : Solidity.Out C target.H Γ) (final : Evm.Machine),
    program.run target = .ok out ∧ encodeOutput target out = encode (output target).st ∧
    Evm.run compilation.code machine = .ok final 0 ∧ final.stack = machine.stack ∧
    compilation.Rep (1 + Evm.Prog.pushes program) 64 bases target machine out.st final :=
  represented.success 1 64 bases target machine True.intro joint_input rfl 2
    (encode (output target).st) (yul_run 0 target)

theorem not_revert : Evm.run compilation.code machine ≠ .revert := by
  intro bad
  have incompatible := (actual_store machine).symm.trans bad
  cases incompatible

/-- info: 'Solidity.Yul.Compilation.P20.InterfaceV2.Controls.compilation' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms Solidity.Yul.Compilation.P20.InterfaceV2.Controls.compilation
/-- info: 'Solidity.Yul.Compilation.P20.InterfaceV2.Controls.public_selection' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms Solidity.Yul.Compilation.P20.InterfaceV2.Controls.public_selection
/-- info: 'Solidity.Yul.Compilation.P20.InterfaceV2.Controls.joint_input' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms Solidity.Yul.Compilation.P20.InterfaceV2.Controls.joint_input
/-- info: 'Solidity.Yul.Compilation.P20.InterfaceV2.Controls.source_forward' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms Solidity.Yul.Compilation.P20.InterfaceV2.Controls.source_forward
/-- info: 'Solidity.Yul.Compilation.P20.InterfaceV2.Controls.source_backward' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms Solidity.Yul.Compilation.P20.InterfaceV2.Controls.source_backward
/-- info: 'Solidity.Yul.Compilation.P20.InterfaceV2.Controls.source_block' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms Solidity.Yul.Compilation.P20.InterfaceV2.Controls.source_block
/-- info: 'Solidity.Yul.Compilation.P20.InterfaceV2.Controls.producer' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Solidity.Yul.Compilation.P20.InterfaceV2.Controls.producer
/-- info: 'Solidity.Yul.Compilation.P20.InterfaceV2.Controls.joint_satisfiable' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms Solidity.Yul.Compilation.P20.InterfaceV2.Controls.joint_satisfiable
/-- info: 'Solidity.Yul.Compilation.P20.InterfaceV2.Controls.nontrivial' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms Solidity.Yul.Compilation.P20.InterfaceV2.Controls.nontrivial
/-- info: 'Solidity.Yul.Compilation.P20.InterfaceV2.Controls.no_v1_lowering' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms Solidity.Yul.Compilation.P20.InterfaceV2.Controls.no_v1_lowering
/-- info: 'Solidity.Yul.Compilation.P20.InterfaceV2.Controls.no_v1_link' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms Solidity.Yul.Compilation.P20.InterfaceV2.Controls.no_v1_link
/-- info: 'Solidity.Yul.Compilation.P20.InterfaceV2.Controls.complete_success' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms Solidity.Yul.Compilation.P20.InterfaceV2.Controls.complete_success
/-- info: 'Solidity.Yul.Compilation.P20.InterfaceV2.Controls.not_revert' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms Solidity.Yul.Compilation.P20.InterfaceV2.Controls.not_revert
end Solidity.Yul.Compilation.P20.InterfaceV2.Controls

namespace Solidity.Yul.Compilation.P20.InterfaceV2.Controls
/-- Regression: the versioned consumer uses this actual memory-store producer,
not a supplied target trace or a substituted V1 stack-only certificate. -/
def consumerV2 : PendingRepresentedSuccess compilation statement yul.profile block
    domain encode encodeOutput producer :=
  Backend.Selection.p20RepresentedConsumerV2 compilation statement yul.profile block
    domain encode encodeOutput producer

/-- The consumer retains source execution, actual target execution, stack
preservation and full represented memory state for the existing bounded input. -/
theorem consumerV2_success :
    ∃ (out : Solidity.Out C target.H Γ) (final : Evm.Machine),
      program.run target = .ok out ∧
      encodeOutput target out = encodeOutput target (output target) ∧
      Evm.run compilation.code machine = .ok final 0 ∧ final.stack = machine.stack ∧
      compilation.Rep (1 + Evm.Prog.pushes program) 64 bases target machine out.st final :=
  consumerV2.success 1 64 bases target machine True.intro joint_input rfl 2
    (encodeOutput target (output target)) (yul_run 0 target)

/-- info: 'Solidity.Yul.Compilation.P20.InterfaceV2.Controls.consumerV2' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms consumerV2
/-- info: 'Solidity.Yul.Compilation.P20.InterfaceV2.Controls.consumerV2_success' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms consumerV2_success
end Solidity.Yul.Compilation.P20.InterfaceV2.Controls
