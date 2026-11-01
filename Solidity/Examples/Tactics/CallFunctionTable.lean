import Solidity.Calculus.CallFunctionGraph
import Solidity.Calculus.CallResultCapture

/-! # Typed call-function table controls
The functions below evaluate actual intrinsic checked terms. Existential
ledgers are used through proved interfaces, never materialized. These
controls are not yet source-call correspondence or compressed Fml leaves.
-/
namespace Solidity.Examples.Tactics.CallFunctionTable
open Solidity.CallFunctionTable
private abbrev C := StandardExample
private abbrev Γ : Ctx := [.val .uint]
private def lit (n : Nat) (h : PrimTy.uint.inRange (Int.ofNat n) = true) : Val C Γ .uint :=
  .simple (.lit n h)
private def affineTerm : Tm C Γ (.val .uint) :=
  (Val.binop .add rfl rfl
    (.binop .mul rfl rfl (.simple (.local .here)) (lit 3 rfl)) (lit 1 rfl)).lower
private def halfTerm : Tm C Γ (.val .uint) :=
  (Val.binop .div rfl rfl (.simple (.local .here)) (lit 2 rfl)).lower
private def partialTerm : Tm C Γ (.val .uint) :=
  (Val.binop .div rfl rfl (lit 1 rfl)
    (.binop .sub rfl rfl (.simple (.local .here)) (lit 1 rfl))).lower
private def f (x : Key) : Option Key :=
  affineTerm.eval ((State.init C).push (t := .val .uint) x)
private def g (x : Key) : Option Key :=
  halfTerm.eval ((State.init C).push (t := .val .uint) x)
private def conditionalDiv (x : Key) : Option Key :=
  partialTerm.eval ((State.init C).push (t := .val .uint) x)

/-- Two distinct inputs of the actual checked non-offset term. -/
theorem returning : f (uintOfNat 2) = some (uintOfNat 7) ∧
    f (uintOfNat 3) = some (uintOfNat 10) := ⟨rfl, rfl⟩

/-- Checked multiplication at the word maximum fails before a second call. -/
theorem firstFailure : (f (uintOfNat (2^256-1))).bind g = none := rfl

/-- A returning first call can feed a genuinely failing second division. -/
theorem secondFailure : (f (uintOfNat 0)).bind conditionalDiv = none := rfl

/-- A successful zero from the same second term is retained as a return. -/
theorem returnsZero : (f (uintOfNat 1)).bind conditionalDiv = some (uintOfNat 0) := rfl

/-- Noncommuting checked terms discriminate evaluation order. -/
theorem orderMatters : (f (uintOfNat 2)).bind g = some (uintOfNat 3) ∧
    (g (uintOfNat 2)).bind f = some (uintOfNat 4) := ⟨rfl, rfl⟩

/-- Failure is distinct from a successful zero at the graph boundary. -/
theorem zeroNotFailure : encode (some (uintOfNat 0)) ≠ encode none := by decide +kernel

/-- The actual partial function has an inhabited full-domain representation,
including distinct returning and overflowing inputs. -/
theorem inhabitedPartial : ∃ L : Ledger, Represents L f ∧
    L.at (uintOfNat 2) = 7 ∧ L.at (uintOfNat (2^256-1)) = -1 := by
  obtain ⟨L, hL⟩ := exists_represents f
  refine ⟨L, hL, ?_, ?_⟩
  · exact (returns_iff hL (uintOfNat 2) (uintOfNat 7)).mpr rfl
  · exact (failure_iff hL (uintOfNat (2^256-1))).mpr rfl

/-- A consistent composition graph witnesses the observable value three. -/
theorem inhabitedComposition : ∃ F G H : Ledger,
    Represents F f ∧ Represents G g ∧ Composes F G H ∧ H.at (uintOfNat 2) = 3 := by
  obtain ⟨F, hF⟩ := exists_represents f
  obtain ⟨G, hG⟩ := exists_represents g
  obtain ⟨H, hH⟩ := exists_represents (fun x => (f x).bind g)
  refine ⟨F, G, H, hF, hG, (composes_iff hF hG).mpr hH, ?_⟩
  exact (returns_iff hH (uintOfNat 2) (uintOfNat 3)).mpr rfl

/-- The false observable cannot be certified by a represented composition. -/
theorem wrongComposition (F G H : Ledger) (hF : Represents F f)
    (hG : Represents G g) (hH : Composes F G H) : H.at (uintOfNat 2) ≠ 4 := by
  have hr : Represents H (fun x => (f x).bind g) := (composes_iff hF hG).mp hH
  have hv : H.at (uintOfNat 2) = (3 : Int) :=
    (returns_iff hr (uintOfNat 2) (uintOfNat 3)).mpr rfl
  rw [hv]
  decide +kernel

/-- A default-zero ledger does not silently turn every failed call into zero. -/
theorem emptyNotFailure : ¬ Represents [] (fun _ => none) := by
  intro h
  have bad : (0 : Int) = -1 := h (uintOfNat 0)
  omega

/-- Composition clauses alone cannot certify an arbitrary malformed predecessor;
this inhabited countermodel makes the representation invariant essential. -/
theorem representationEssential : ∃ F : Ledger,
    Composes F [] [] ∧ ¬ Represents [] (fun _ => none) := by
  obtain ⟨F, hF⟩ := realize (fun _ : Key => (-2 : Int))
  refine ⟨F, ?_, emptyNotFailure⟩
  intro x
  constructor
  · intro h
    have bad : (-2 : Int) = -1 := (hF x).symm.trans h
    omega
  · intro r h
    have bad : (-2 : Int) = r.val := (hF x).symm.trans h
    have hr : 0 ≤ r.val := by
      have hRange : PrimTy.inRange .uint r.val = true := r.property
      simp only [PrimTy.inRange, decide_eq_true_eq] at hRange
      exact hRange.1
    omega

private abbrev Caller : Ctx := [.val .uint, .val .uint]
private abbrev Tables : Ctx := [.oldNet, .oldNet, .oldNet] ++ Caller
private def original : State C Caller :=
  ((({ State.init C with selfBalance := uintOfNat 5, net := [(uintOfNat 5, 19)] }).push (t := .val .uint) (uintOfNat 2)).push
    (t := .val .uint) (uintOfNat 99))
private def graphState (F G H : Ledger) : State C Tables :=
  (((original.push (t := .oldNet) F).push (t := .oldNet) G).push (t := .oldNet) H)
private def graph : Fml C Tables :=
  CallFunctionGraph.compose (.fresh "same" 0) (.fresh "same" 0)
    (.there (.there .here)) (.there .here) .here
private def wrongGraph : Fml C Tables :=
  CallFunctionGraph.equalZ (.netOf .here (.app0 (.lit (uintOfNat 2)))) (.app0 (.zlit 4))

/-- Actual intrinsic graph clauses have inhabited noncommuting models;
a wrong observation is false in that same typed model. -/
theorem intrinsicWitness : ∃ F G H : Ledger,
    Represents F f ∧ Represents G g ∧ holds (graphState F G H) graph ∧
    ¬ holds (graphState F G H) wrongGraph := by
  obtain ⟨F, hF⟩ := exists_represents f
  obtain ⟨G, hG⟩ := exists_represents g
  obtain ⟨H, hH⟩ := exists_represents (fun x => (f x).bind g)
  have hc : Composes F G H := (composes_iff hF hG).mpr hH
  refine ⟨F, G, H, hF, hG, ?_, ?_⟩
  · exact (CallFunctionGraph.holds_compose (.fresh "same" 0) (.fresh "same" 0)
      (.there (.there .here)) (.there .here) .here (graphState F G H)).mpr hc
  · have hv : H.at (uintOfNat 2) = (3 : Int) :=
      (returns_iff hH (uintOfNat 2) (uintOfNat 3)).mpr rfl
    change ¬ ((some (decide (H.at (uintOfNat 2) = 4)) : Option Bool) = some true)
    rw [hv]
    decide +kernel

/-- Logical function locals leave actual caller values and globals intact. -/
theorem callerFrame (F G H : Ledger) :
    (graphState F G H).drop (.push (.push (.push .refl))) = original ∧
    (graphState F G H).selfBalance = uintOfNat 5 ∧
    (graphState F G H).net.at (uintOfNat 5) = 19 := ⟨rfl, rfl, rfl⟩

/-- Both quantifiers and every lookup are included in the emitted clause size. -/
theorem intrinsicSize : graph.tmSize = 31 :=
  CallFunctionGraph.compose_size (.fresh "same" 0) (.fresh "same" 0)
    (.there (.there .here)) (.there .here) .here

end Solidity.Examples.Tactics.CallFunctionTable
