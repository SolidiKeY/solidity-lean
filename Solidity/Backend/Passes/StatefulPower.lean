import Solidity.Backend.Passes.StatefulValues
import Solidity.Backend.Scalar.SignedPower

/-! Apply the published heterogeneous checked signed-power contracts. The
owner's source theorem is only an Option/Int observation. Successful typed
results are recovered by subtype extensionality; failure classification below
additionally uses an ACTUAL accepted whole-value certificate and full input.
Numeric multistage code and symbolic whole code remain distinct interfaces. -/
namespace Solidity.Backend.Passes.StatefulPower
variable {C : Contract} {Γ : Ctx} {σ : State C Γ} {b L frame : Nat}
  {F : Evm.Frag Γ} {base : Nat → Fin Evm.W} {m : Evm.Machine}

/-- Separate successful operand loads; no equation with the actual legacy
whole-helper code schedule is asserted. -/
theorem operands {av : Val C Γ .int} {nv : Val C Γ .uint}
    (ac : Evm.Memory.CompiledVal b F av) (nc : Evm.Memory.CompiledVal b F nv)
    (input : Evm.Memory.StateRepr L b frame F σ base m)
    {a : PrimTy.int.Denote} {n : PrimTy.uint.Denote}
    (ha : av.evalT σ = .ok a) (hn : nv.evalT σ = .ok n) (tail : List Evm.Word) :
    ∃ wa wn : Fin Evm.W, Evm.ReprV .int a (.val wa) ∧ Evm.ReprV .uint n (.val wn) ∧
      Backend.Scalar.encodeValue .int a = BitVec.ofNat 256 wa.val ∧
      Backend.Scalar.encodeValue .uint n = BitVec.ofNat 256 wn.val ∧
      Evm.run (nc.code ++ ac.code) {m with stack := tail} =
        .ok (({m with stack := tail}.push (.val wn)).push (.val wa)) 0 := by
  obtain ⟨wordN,wordA,hnw,haw,ht⟩ := value_pair_success_tail nc ac input hn ha tail
  obtain ⟨wn,en,hen⟩ := ClosedValues.represented_word hnw
  obtain ⟨wa,ea,hea⟩ := ClosedValues.represented_word haw
  subst wordN; subst wordA
  exact ⟨wa,wn,haw,hnw,hea,hen,ht⟩

theorem source_success {av : Val C Γ .int} {nv : Val C Γ .uint}
    {a : PrimTy.int.Denote} {n : PrimTy.uint.Denote}
    (ha : av.evalT σ = .ok a) (hn : nv.evalT σ = .ok n)
    {v : PrimTy.int.Denote} (result : Backend.Scalar.powerSourceResult a n = some v) :
    (Val.checkedSignedPower av nv).evalT σ = .ok v := by
  have obs := Backend.Scalar.signedPower_source σ av nv a n ha hn
  rw [result] at obs
  cases hs : (Val.checkedSignedPower av nv).evalT σ with
  | error err => simp only [hs,Except.toOption,Option.map_none,Option.map_some,reduceCtorEq] at obs
  | ok value =>
    simp only [hs,Except.toOption,Option.map_some] at obs
    have same : value = v := by
      apply Subtype.ext
      exact Option.some.inj obs
    cases same
    rfl

/-- Full original whole-value input and ALL five independently executed
component capacities are retained. No concatenation of the two targets. -/
theorem application {av : Val C Γ .int} {nv : Val C Γ .uint}
    (whole : Evm.Memory.CompiledVal b F (Val.checkedSignedPower av nv))
    (input : Evm.Memory.StateRepr L b frame F σ base m)
    {a : PrimTy.int.Denote} {n : PrimTy.uint.Denote}
    (ha : av.evalT σ = .ok a) (hn : nv.evalT σ = .ok n)
    (tail : List Evm.Word) (saved : Backend.Scalar.Stack)
    (invocation : Backend.Scalar.SignedPowerInvocation a n saved) :
    ((Val.checkedSignedPower av nv).evalT σ).toOption.map (·.val) =
      (Backend.Scalar.powerSourceResult a n).map (·.val) ∧
    Evm.ValOutT .int ((Val.checkedSignedPower av nv).evalT σ)
      (Evm.run whole.code {m with stack := tail}) {m with stack := tail} ∧
    Backend.Scalar.signedPowerExecute (Backend.Scalar.encodeValue .int a ::
      Backend.Scalar.encodeValue .uint n :: saved) =
      some (Backend.Scalar.checkedOutcome .int (Backend.Scalar.powerSourceResult a n) saved) ∧
    Backend.Scalar.stackBound Backend.Scalar.powerPrepare ((saved.length+2:Nat):Int) = true ∧
    Backend.Scalar.stackBound Backend.Scalar.checkedUintPow.test ((saved.length+3:Nat):Int) = true ∧
    Backend.Scalar.stackBound Backend.Scalar.checkedUintPow.body ((saved.length+3:Nat):Int) = true ∧
    Backend.Scalar.stackBound Backend.Scalar.powerPostTest ((saved.length+2:Nat):Int) = true ∧
    Backend.Scalar.stackBound Backend.Scalar.powerSignBody ((saved.length+2:Nat):Int) = true :=
  ⟨Backend.Scalar.signedPower_source σ av nv a n ha hn,
    whole.cert.correct (input.stack tail),invocation.correct,
    invocation.prepareCapacity,invocation.powerTestCapacity,invocation.powerBodyCapacity,
    invocation.resultTestCapacity,invocation.resultBodyCapacity⟩

theorem success {av : Val C Γ .int} {nv : Val C Γ .uint}
    (whole : Evm.Memory.CompiledVal b F (Val.checkedSignedPower av nv))
    (input : Evm.Memory.StateRepr L b frame F σ base m)
    {a : PrimTy.int.Denote} {n : PrimTy.uint.Denote}
    (ha : av.evalT σ = .ok a) (hn : nv.evalT σ = .ok n)
    {v : PrimTy.int.Denote} (result : Backend.Scalar.powerSourceResult a n = some v)
    (tail : List Evm.Word) :
    (Val.checkedSignedPower av nv).evalT σ = .ok v ∧
      ∃ w : Fin Evm.W, Evm.ReprV .int v (.val w) ∧
      Backend.Scalar.encodeValue .int v = BitVec.ofNat 256 w.val ∧
      Evm.run whole.code {m with stack := tail} =
        .ok ({m with stack := tail}.push (.val w)) 0 := by
  have hs := source_success ha hn result
  obtain ⟨word,hw,ht⟩ := value_success_tail whole input hs tail
  obtain ⟨w,ew,he⟩ := ClosedValues.represented_word hw
  subst word
  exact ⟨hs,w,hw,he,ht⟩

/-- The owner Option observation alone cannot distinguish source error tags.
The real accepted ValFrag supplies that classification; no premise asserts it. -/
theorem failure {av : Val C Γ .int} {nv : Val C Γ .uint}
    (whole : Evm.Memory.CompiledVal b F (Val.checkedSignedPower av nv))
    (input : Evm.Memory.StateRepr L b frame F σ base m)
    {a : PrimTy.int.Denote} {n : PrimTy.uint.Denote}
    (ha : av.evalT σ = .ok a) (hn : nv.evalT σ = .ok n)
    (result : Backend.Scalar.powerSourceResult a n = none) (tail : List Evm.Word) :
    (Val.checkedSignedPower av nv).evalT σ = .error .revert ∧
      Evm.run whole.code {m with stack := tail} = .revert := by
  have obs := Backend.Scalar.signedPower_source σ av nv a n ha hn
  rw [result] at obs
  rcases whole.cert.correct (input.stack tail) with ⟨v,w,hs,_,_⟩ | ⟨hs,ht⟩
  · rw [hs] at obs
    cases obs
  · exact ⟨hs,ht⟩

end Solidity.Backend.Passes.StatefulPower
