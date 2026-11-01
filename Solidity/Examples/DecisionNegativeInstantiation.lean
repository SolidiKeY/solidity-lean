import Solidity.Calculus.DecisionNegativeInstantiation
import Solidity.Examples.DecisionArrayGaps

/-!
# Negative-chain proof controls
An actual typed fixed-root client, preserved unknowns, positive quantifiers,
halted substitution guards, and a counterexample to exactness.
-/
namespace Solidity.Examples.DecisionNegativeInstantiation
open Solidity.Decide
open Solidity.Examples.DecisionArrayGaps (Probe)
set_option Elab.async false

private theorem fixedType : Probe.rootType "fixedArr" =
    some (.ref (.fixed (.prim .uint) 3)) := by decide +kernel

def fixedRead (i : LTm Probe (.val .uint)) : LTm Probe (.val .uint) :=
  .obsW (.index (.arr .fixed) (.app0 (.root "fixedArr" fixedType)) i)
def zero : LTm Probe (.val .uint) := .app0 (.lit (uintOfNat 0))
def one : LTm Probe (.val .uint) := .app0 (.lit (uintOfNat 1))
def fixedBody : LFml Probe := .imp
  (.eq (.app2 (.binop .lt rfl) (.var 0) (.app0 (.lit (uintOfNat 3)))) (.app0 (.lit true)))
  (.eq (fixedRead (.var 0)) zero)
def fixedChain : LFml Probe := .all 0 .uint fixedBody

theorem fixed_chain_shape : fixedChain.chainQF .uint = true := rfl

theorem fixed_guarded_instance_client : (LFml.imp fixedChain (fixedChain.inst [one])).Valid :=
  LFml.negativeChainInst_instance_client [one] 0 fixedBody fixed_chain_shape

/-- This client's actual finite sample holds at the unchanged initialized storage. -/
theorem fixed_instance_inhabited : (fixedChain.inst [one]).holds (State.init Probe) AEnv.dflt := by
  simp only [fixedChain, LFml.inst_all, List.map_cons, List.map_nil, LFml.conj]
  intro _
  rw [LFml.holds_subst1 (State.init Probe) AEnv.dflt 0 one (v := uintOfNat 1)
    (by rfl) _ (by rfl)]
  change true = true →
    (Storage.init Probe).obs.word (.ref ((SRef.ofRoot "fixedArr" fixedType).index (.arr .fixed) (uintOfNat 1))) = uintOfNat 0
  intro _
  rw [Storage.obs_word_ref, Storage.init, SFields.dflt_get]
  simp only [SRef.index, SRef.append, SRef.ofRoot, Path.index_fixed, Path.append_nil]
  rw [SVal.dflt_fixed, SVal.obs_word]
  simp only [SVal.findM, SVec.toList_replicate]
  rfl

theorem positive_chain_preserved : fixedChain.negativeChainInst [one] true = fixedChain := rfl

/-- An undefined sample retains its definedness guard rather than supplying a value. -/
theorem halted_sample_shape :
    fixedChain.inst [.err (s := .val .uint)] =
      .imp (.eq (.err (s := .val .uint)) (.err (s := .val .uint)))
        (fixedBody.subst1 0 (.err (s := .val .uint))) := rfl

theorem halted_sample_holds (g : State Probe []) (ν : AEnv) :
    (fixedChain.inst [.err (s := .val .uint)]).holds g ν := by
  intro h
  cases h

def falseTerm : LTm Probe (.val .bool) := .app0 (.lit false)
def trueTerm : LTm Probe (.val .bool) := .app0 (.lit true)
def impossibleChain : LFml Probe := .all 0 .bool (.eq (.var 0) falseTerm)
def converseTrap : LFml Probe := .imp impossibleChain (.eq falseTerm trueTerm)

theorem original_valid : converseTrap.Valid := by
  intro g ν h
  have bad : true = false := h true
  cases bad

/-- A valid original can have an invalid finite instance: the converse is false. -/
theorem finite_instance_invalid :
    ¬ (converseTrap.negativeChainInst [falseTerm] true).holds (State.init Probe) AEnv.dflt := by
  change ¬ ((false = false → false = false) → false = true)
  intro h
  have bad : false = true := h (fun _ => rfl)
  cases bad

theorem no_equivalence : ¬ ((converseTrap.negativeChainInst [falseTerm] true).Valid ↔ converseTrap.Valid) := by
  intro h
  exact finite_instance_invalid ((h.mpr original_valid) (State.init Probe) AEnv.dflt)

/-- The existing global fixed-block classification is unchanged by this proof-only component. -/
theorem original_gap_preserved :
    decideGoal Solidity.Examples.DecisionArrayGaps.fixedBlock = .unknown :=
  Solidity.Examples.DecisionArrayGaps.fixedBlock_unknown

end Solidity.Examples.DecisionNegativeInstantiation
