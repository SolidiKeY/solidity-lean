import Solidity.Source.Types
import Solidity.Lowering.V08.FixedBytesCallableArgumentControls

/-!
Isolated H62 backfill: width admission at the existing intrinsic Source.STy.
The width-admission section alone does not assert argument evaluation, state
transport, or ABI agreement. The later execution section consumes the existing
operational producers; ABI agreement remains unclaimed.
The two fixture rows retain the binary/maximal original width cases from
FixedBytesCallableArgumentControls; original execution theorems are read-only.
-/
namespace Solidity.H62.GenericV08
open Solidity.Source

/-- Widening composes at the existing type-indexed source admission relation. -/
theorem fixedBytes_widening (isBase : DeclName → DeclName → Bool)
    (n m k : Nat) (hn : 1 ≤ n ∧ n ≤ 32) (_hm : 1 ≤ m ∧ m ≤ 32)
    (hk : 1 ≤ k ∧ k ≤ 32) (nm : n ≤ m) (mk : m ≤ k) :
    STy.implicit isBase (.fixedBytes n hn) (.fixedBytes k hk) = true := by
  change decide (n ≤ k) = true
  exact decide_eq_true (Nat.le_trans nm mk)

/-- Every legal width admits identity conversion, without enumerating widths. -/
theorem fixedBytes_identity (isBase : DeclName → DeclName → Bool)
    (n : Nat) (hn : 1 ≤ n ∧ n ≤ 32) :
    STy.implicit isBase (.fixedBytes n hn) (.fixedBytes n hn) = true :=
  fixedBytes_widening isBase n n n hn hn hn (Nat.le_refl n) (Nat.le_refl n)

/-- Strict narrowing is refused by that same published admission relation. -/
theorem fixedBytes_narrowing (isBase : DeclName → DeclName → Bool)
    (n m : Nat) (hn : 1 ≤ n ∧ n ≤ 32) (_hm : 1 ≤ m ∧ m ≤ 32) (lt : m < n) :
    STy.implicit isBase (.fixedBytes n hn) (.fixedBytes m _hm) = false := by
  change decide (n ≤ m) = false
  exact decide_eq_false (Nat.not_le_of_gt lt)

/-- Width bounds live in the fixture, exactly as in the original source types. -/
structure WidthFixture where
  width : Nat
  bound : 1 ≤ width ∧ width ≤ 32
  old : List UInt8
  rhs : List UInt8

def WidthFixture.type (fixture : WidthFixture) : STy :=
  .fixedBytes fixture.width fixture.bound

/-- Exact binary and maximal input lists from the original declarations. -/
def widthFixtures : List WidthFixture :=
  [⟨2, by decide, [255,128], [0,1]⟩,
   ⟨32, by decide, [], List.replicate 32 255⟩]

/-- The fixture table consumes a general theorem; no decide table proves it. -/
theorem fixture_identity (isBase : DeclName → DeclName → Bool) (fixture : WidthFixture) :
    STy.implicit isBase fixture.type fixture.type = true :=
  fixedBytes_identity isBase fixture.width fixture.bound

/-- Every retained table row uses the same all-width admission proof. -/
theorem table_identity (isBase : DeclName → DeclName → Bool) :
    ∀ fixture ∈ widthFixtures, STy.implicit isBase fixture.type fixture.type = true := by
  intro fixture _member
  exact fixture_identity isBase fixture

#print axioms table_identity
#print axioms fixedBytes_widening
#print axioms fixedBytes_identity
#print axioms fixedBytes_narrowing
#print axioms fixture_identity
end Solidity.H62.GenericV08

/-! Guarded regression: width admission alone must not be reported as actual
argument execution or post-local transport. The following additive consumers
retain the published actual evaluator and joint Source/target producers.
Proof-term instance identities are separate from operational evidence. -/
namespace Solidity.H62.GenericV08.ExecutionTransport
open Solidity Source
open Solidity.Lowering.V07
open FixedBytesAssignmentControls
open Source.SemanticsExamples
open MixedAssignmentControls (globals)
open Solidity.Lowering.V08.FixedBytesCallableArgument

/-- Exact Source execution for every typed fixture and extra sufficient
horizon. Payload fitting is the existing producer, not a new length premise. -/
theorem source_execution (fixture : WidthFixture) (pipeline : Roadmap.Pipeline)
    (checked static : Bool) (extra : Nat) :
    (Source.evalConvArgs (globals pipeline) {F0 with checked := checked,static := static}
      (extra+4) (arguments (E := MixedAssignmentControls.E) fixture.width fixture.bound
        (.here : Source.Idx (SrcCtx fixture.width fixture.bound) _) (.there .here))).run
      (source fixture.width fixture.bound fixture.old fixture.rhs) =
    (.ok (.cons (.fixedBytes (FixedBytesAssignmentControls.payload fixture.width fixture.rhs)
        (Source.fitBytes_length fixture.width fixture.rhs)) .nil),
      ((source fixture.width fixture.bound fixture.old fixture.rhs).1.set .here
        (.fixedBytes (FixedBytesAssignmentControls.payload fixture.width fixture.rhs)
          (Source.fitBytes_length fixture.width fixture.rhs)),
        (source fixture.width fixture.bound fixture.old fixture.rhs).2)) := by
  first
  | exact argument_actual (globals pipeline) {F0 with checked := checked,static := static}
      extra (source fixture.width fixture.bound fixture.old fixture.rhs)
      fixture.width fixture.bound .here (.there .here)
      (FixedBytesAssignmentControls.payload fixture.width fixture.rhs)
      (Source.fitBytes_length fixture.width fixture.rhs) rfl
  | rfl

/-- Joint operational/result/post-local producer, not a decide table. It
retains both complete machines and their actual reached typed local relation. -/
def joint_execution (fixture : WidthFixture) (pipeline : Roadmap.Pipeline)
    (checked static : Bool) (extra : Nat) :=
  Controls.actual_client fixture.width fixture.bound pipeline checked static extra
    fixture.old fixture.rhs

/-- Exact original binary instance; no original theorem or input is rewritten. -/
theorem binary_instance (pipeline : Roadmap.Pipeline) (checked static : Bool) :
    joint_execution widthFixtures[0] pipeline checked static 0 =
      Controls.binary_client pipeline checked static := by rfl

/-- Exact original maximal-width instance under its original frame flags. -/
theorem maximal_instance (pipeline : Roadmap.Pipeline) :
    joint_execution widthFixtures[1] pipeline false false 0 =
      Controls.maximum_client pipeline := by rfl


/-- Original binary row inputs, separately from proof-irrelevant equalities. -/
theorem binary_fields :
    (widthFixtures[0]).width = 2 ∧ (widthFixtures[0]).old = [255,128] ∧
      (widthFixtures[0]).rhs = [0,1] := by first | decide | exact ⟨rfl,rfl,rfl⟩

/-- Original maximal row inputs; fitting remains the existing producer rule. -/
theorem maximal_fields :
    (widthFixtures[1]).width = 32 ∧ (widthFixtures[1]).old = [] ∧
      (widthFixtures[1]).rhs = List.replicate 32 255 := by first | decide | exact ⟨rfl,rfl,rfl⟩

end Solidity.H62.GenericV08.ExecutionTransport

#print axioms Solidity.H62.GenericV08.ExecutionTransport.source_execution

#print axioms Solidity.H62.GenericV08.ExecutionTransport.joint_execution

#print axioms Solidity.H62.GenericV08.ExecutionTransport.binary_instance

#print axioms Solidity.H62.GenericV08.ExecutionTransport.maximal_instance

#print axioms Solidity.H62.GenericV08.ExecutionTransport.binary_fields

#print axioms Solidity.H62.GenericV08.ExecutionTransport.maximal_fields
