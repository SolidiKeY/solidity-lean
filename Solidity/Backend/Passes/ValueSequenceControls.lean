import Solidity.Backend.Passes.ValueSequence
import Solidity.Backend.Passes.ExpressionControls
import Solidity.Backend.Passes.TripleControls

/-! Populated memory values, real binary-code prefix/order controls and
selected failures. These are value certificates, not Source tuple lowering. -/
namespace Solidity.Backend.Passes.ValueSequenceControls
open Solidity.Evm Solidity.Evm.Memory
open Solidity.Backend.Passes.Controls.Fixture

def first : Val C Γ .uint :=
  .readMem (.index .dyn (.var (.there .here) rfl) (.simple (.lit 0 rfl)))
def second : Val C Γ .uint :=
  .readMem (.index .dyn (.var (.there (.there (.there .here))) rfl) (.simple (.lit 0 rfl)))
def a : CompiledVal 0 (Frag.init Γ) first := (compileVal 0 (Frag.init Γ) first).get (by decide +kernel)
def d : CompiledVal 0 (Frag.init Γ) second := (compileVal 0 (Frag.init Γ) second).get (by decide +kernel)
def seven : PrimTy.uint.Denote := ⟨7, rfl⟩
def four : PrimTy.uint.Denote := ⟨4, rfl⟩
def three : PrimTy.uint.Denote := ⟨3, rfl⟩
theorem first_source : first.evalT σ = .ok seven := by with_unfolding_all rfl
theorem second_source : second.evalT σ = .ok four := by with_unfolding_all rfl

private theorem literal_word (n : Nat) (hn : n < W) {word : Word}
    (hr : ReprV .uint (indexValue ⟨n, hn⟩) word) : word = .val ⟨n, hn⟩ := by
  obtain ⟨z, hw, hv⟩ := hr
  have he : z = ⟨n, hn⟩ := Fin.ext (by
    change z.val = n
    change (n : Int) = (z.val : Int) at hv
    omega)
  exact hw.trans (congrArg Word.val he)

/-- Exact entire machine, not just a selected projection; arbitrary tails. -/
theorem ordered_tail (tail : List Word) :
    run (a.code ++ d.code) {machine with stack := tail} =
      .ok {machine with stack := w[4] :: w[7] :: tail} 0 := by
  obtain ⟨wa, wd, ha, hd, ht⟩ := value_pair_success_tail a d fixture_repr first_source second_source tail
  have ea : wa = w[7] := literal_word 7 (by decide) ha
  have ed : wd = w[4] := literal_word 4 (by decide) hd
  cases ea
  cases ed
  exact ht

/-- This exact pair is an actual emitted prefix of a checked binary value. -/
def difference : Val C Γ .uint := .binop .sub rfl rfl first second
def reversed : Val C Γ .uint := .binop .sub rfl rfl second first
def checkedDifference : CompiledVal 0 (Frag.init Γ) difference :=
  (compileVal 0 (Frag.init Γ) difference).get (by decide +kernel)
def checkedReversed : CompiledVal 0 (Frag.init Γ) reversed :=
  (compileVal 0 (Frag.init Γ) reversed).get (by decide +kernel)
theorem emitted_prefix : checkedDifference.code = (a.code ++ d.code) ++ binTail .uint .sub := rfl

theorem source_order : difference.evalT σ = .ok three ∧ reversed.evalT σ = .error .revert := by
  constructor <;> with_unfolding_all rfl

/-- The existing checked subtraction consumes the pair; selection/arithmetic
correctness is reused, not reimplemented. Reordering reaches underflow. -/
theorem consumer_order (tail : List Word) :
    run checkedDifference.code {machine with stack := tail} =
      .ok {machine with stack := w[3] :: tail} 0 ∧
    run checkedReversed.code {machine with stack := tail} = .revert := by
  constructor
  · obtain ⟨w, hw, ht⟩ := value_success_tail checkedDifference fixture_repr source_order.1 tail
    have he : w = w[3] := literal_word 3 (by decide) hw
    cases he
    exact ht
  · exact (value_revert_iff checkedReversed fixture_repr tail).mpr source_order.2

private def stackValues : Evm.Out → Option (List Nat)
  | .ok m _ => m.stack.mapM (fun w => match w with | .val n => some n.val | _ => none)
  | _ => none

theorem wrong_order : run (d.code ++ a.code) machine ≠ run (a.code ++ d.code) machine := by
  have hn : stackValues (run (d.code ++ a.code) machine) ≠
      stackValues (run (a.code ++ d.code) machine) := by decide +kernel
  exact fun he => hn (congrArg stackValues he)

theorem corruption : run (a.code ++ [Instr.pop] ++ d.code) machine ≠
    run (a.code ++ d.code) machine := by
  have hn : stackValues (run (a.code ++ [Instr.pop] ++ d.code) machine) ≠
      stackValues (run (a.code ++ d.code) machine) := by decide +kernel
  exact fun he => hn (congrArg stackValues he)

/-- A bool/uint pair demonstrates the genuinely heterogeneous stack law;
the failing unselected RHS of the short circuit remains unexecuted. -/
theorem heterogeneous (tail : List Word) :
    ∃ wb wu, ReprV .bool false wb ∧ ReprV .uint four wu ∧
      run ((ExpressionControls.checkedAnd false).code ++ d.code) {machine with stack := tail} =
        .ok (({machine with stack := tail}.push wb).push wu) 0 :=
  value_pair_success_tail (ExpressionControls.checkedAnd false) d fixture_repr rfl second_source tail

/-- Immediate failure needs no second source evaluation premise. -/
theorem immediate_failure (tail : List Word) :
    run ((ExpressionControls.checkedAnd true).code ++ d.code) {machine with stack := tail} = .revert :=
  (value_pair_revert_iff (ExpressionControls.checkedAnd true) d fixture_repr tail).mpr
    (.inl (by with_unfolding_all rfl))

def reached_failure (tail : List Word) :=
  value_pair_reached_revert a ExpressionControls.checkedBad fixture_repr first_source
    (by with_unfolding_all rfl) tail

private def cell (n : Nat) : Evm.Out → Option Nat
  | .ok m _ => match m.mem n with | .val w => some w.val | _ => none
  | _ => none

/-- Complete fixture vector: scalar, both aliases, independent reference,
both headers, both first-array elements and the independent element. All
non-stack fields are already preserved by ordered_tail. -/
theorem unchanged_memory : [3,2,1,0,16,17,18,20,21].mapM
    (fun n => cell n (run (a.code ++ d.code) machine)) =
      some [0,16,16,20,2,7,9,1,4] := by
  have ht := ordered_tail []
  change run (a.code ++ d.code) machine = _ at ht
  rw [ht]
  decide +kernel


open Solidity.Evm.Compiler
open Solidity.Backend.Passes.AllocatingControls
open Solidity.Backend.Passes.TripleControls

def freshA : CompiledVal 1 allocationStage.frag first :=
  (compileVal 1 allocationStage.frag first).get (by decide +kernel)
def freshD : CompiledVal 1 allocationStage.frag second :=
  (compileVal 1 allocationStage.frag second).get (by decide +kernel)

/-- Actual allocation establishes the full represented value input with
its selected map. Values preserve that reached machine below two words. -/
theorem after_allocation : ∃ (mid : Machine) (mb : Nat → Fin W) (wa wd : Word),
    run allocationStage.code initialMachine = .ok mid 0 ∧
    MappedOutput (.memory allocationStage) 1 7 initialBase (State.init C)
      initialMachine σ mid mb ∧
    ReprV .uint seven wa ∧ ReprV .uint four wd ∧
    run (allocationStage.code ++ (freshA.code ++ freshD.code)) initialMachine =
      .ok ((mid.push wa).push wd) 0 := by
  obtain ⟨mid, hm, _, hr⟩ := compilation_success (.memory allocationStage)
    prefix_input7 rfl ReachabilityControls.fresh_state_reaches_fixture
  obtain ⟨mb, ha⟩ := (mapped_output_iff (.memory allocationStage) _ _ _ _ _ _ _).mp hr
  have ma : MappedOutput (.memory allocationStage) 1 7 initialBase (State.init C)
      initialMachine σ mid mb := by
    simpa only [allocationStage.cert.pushes_zero, Nat.add_zero] using ha
  obtain ⟨wa, wd, hv, hu, ht⟩ := value_pair_success_tail freshA freshD ma.1
    first_source second_source mid.stack
  have em : {mid with stack := mid.stack} = mid := by cases mid; rfl
  rw [em] at ht
  have hm' : run allocationStage.code initialMachine = .ok mid 0 := hm
  exact ⟨mid, mb, wa, wd, hm', ma, hv, hu, by rw [run_append_ok hm']; exact ht⟩

end Solidity.Backend.Passes.ValueSequenceControls
