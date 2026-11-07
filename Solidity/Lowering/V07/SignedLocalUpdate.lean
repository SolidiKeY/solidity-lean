import Solidity.Lowering.V07.SignedNarrowAddition
import Solidity.Lowering.V07.SignedNarrowSubtraction
import Solidity.Lowering.V07.UnsignedLocalUpdate

/-! Unchecked signed local increment/decrement with actual Source locations
and intrinsic captures. Prefix/postfix selects the returned value, while both
forms write the updated caller local. No frontend/admission claim is made. -/
namespace Solidity.Lowering.V07.SignedLocalUpdate
open SignedWidthCasts (ty)
open UnsignedLocalUpdate (changed)

def updateValue {C : Contract} {Γ : Ctx} (bits : Nat) (inc : Bool)
    (v : Val C Γ .int) : Val C Γ .int :=
  if inc then SignedNarrowAddition.addValue bits v (.simple (.lit 1 (by decide)))
  else SignedNarrowSubtraction.subValue bits v (.simple (.lit 1 (by decide)))

theorem source_value (bits : Nat) (valid : bits % 8 = 0 ∧ 8 ≤ bits ∧ bits ≤ 256)
    {D : Source.Layout} (inc : Bool) (x : Int)
    (hx : (ty bits valid).lo ≤ x ∧ x ≤ (ty bits valid).hi) :
    Source.incDecVal false inc (.int x hx : Source.Val D (.int (ty bits valid))) =
      .ok (Source.intWrap (ty bits valid) (changed inc x)) := by
  change Source.intRes (ty bits valid) false (changed inc x) = _
  unfold Source.intRes
  split
  · rename_i h
    have hw := SignedNarrowing.wrap_of_range bits valid _ h
    simp only [Source.intWrap,hw]
    rfl
  · rfl

theorem source_run (bits : Nat) (valid : bits % 8 = 0 ∧ 8 ≤ bits ∧ bits ≤ 256)
    {E : Source.Env} {Γ : Source.RCtx} (G : Source.Glob E) (F : Source.Fr) (fuel : Nat)
    (source : Source.EMState E Γ) (inc pre : Bool)
    (i : Source.Idx Γ (.int (ty bits valid))) (x : Int)
    (hx : (ty bits valid).lo ≤ x ∧ x ≤ (ty bits valid).hi)
    (read : source.1.get i = .int x hx) :
    (Source.evalE G {F with checked := false} (fuel+2) (.incDec inc pre (.local i))).run source =
      (.ok (.val (if pre then Source.intWrap (ty bits valid) (changed inc x) else .int x hx)),
        (source.1.set i (Source.intWrap (ty bits valid) (changed inc x)),source.2)) := by
  have location : (Source.evalLoc G {F with checked := false} (fuel+1) (.local i)).run source =
      (.ok (.local i),source) := rfl
  have old : (Source.readLoc {F with checked := false} (.local i)).run source =
      (.ok (source.1.get i),source) := rfl
  rw [Source.evalE,Source.Hoare.run_bind,location]
  dsimp only
  rw [Source.Hoare.run_bind,old]
  dsimp only
  rw [read,source_value]
  rfl

theorem value_run (bits : Nat) (valid : bits % 8 = 0 ∧ 8 ≤ bits ∧ bits ≤ 256)
    {C : Contract} {Γ : Ctx} (target : State C Γ) (inc : Bool) (v : Val C Γ .int)
    (x : Int) (hx : (ty bits valid).lo ≤ x ∧ x ≤ (ty bits valid).hi)
    (read : v.evalT target = .ok (integerValue (ty bits valid) x hx)) :
    (updateValue bits inc v).evalT target =
      .ok (integerValue (ty bits valid) ((ty bits valid).wrap (changed inc x))
        ((ty bits valid).wrap_mem (changed inc x))) := by
  have one : (ty bits valid).lo ≤ 1 ∧ 1 ≤ (ty bits valid).hi := by
    have hp : 2 ≤ 2^(bits-1) := Source.two_pow_le (by have := valid.2.1; omega : 1 ≤ bits-1)
    change -((2^(bits-1) : Nat) : Int) ≤ (1 : Int) ∧ 1 ≤ ((2^(bits-1)-1 : Nat) : Int)
    omega
  cases inc
  · exact SignedNarrowSubtraction.sub_value_run bits valid target v (.simple (.lit 1 (by decide)))
      x 1 hx one read rfl
  · exact SignedNarrowAddition.add_value_run bits valid target v (.simple (.lit 1 (by decide)))
      x 1 hx one read rfl

/-- The old value is captured before the write; a second binder captures the
selected expression result before Operand.run drops either temporary. -/
def code {C : Contract} {Γ : Ctx} (bits : Nat) (inc pre : Bool) (i : Idx Γ (.val .int)) :
    Prog C Γ (.val .int :: .val .int :: Γ) :=
  .cons (.declLocal .int (.user "v07_old") (some (.simple (.local i))))
    (.cons (.assignLocal (.there i) (updateValue bits inc (.simple (.local .here))))
      (.cons (.declLocal .int (.user "v07_updated_result")
        (some (.simple (.local (if pre then .there i else .here))))) .nil))

def operand {C : Contract} {Γ : Ctx} (bits : Nat) (inc pre : Bool)
    (i : Idx Γ (.val .int)) : DeferredSource.Operand C Γ (.prim .int) :=
  ⟨_,code bits inc pre i,.val (.simple (.local .here))⟩

theorem code_run (bits : Nat) (valid : bits % 8 = 0 ∧ 8 ≤ bits ∧ bits ≤ 256)
    {C : Contract} {Γ : Ctx} (target : State C Γ) (inc pre : Bool) (i : Idx Γ (.val .int))
    (x : Int) (hx : (ty bits valid).lo ≤ x ∧ x ≤ (ty bits valid).hi)
    (read : TEnv.get i target.env = integerValue (ty bits valid) x hx) :
    (code bits inc pre i).run target =
      .ok (⟨((target.setLocal i (integerValue (ty bits valid) ((ty bits valid).wrap (changed inc x))
        ((ty bits valid).wrap_mem (changed inc x)))).push (integerValue (ty bits valid) x hx)).push
        (if pre then integerValue (ty bits valid) ((ty bits valid).wrap (changed inc x))
          ((ty bits valid).wrap_mem (changed inc x)) else integerValue (ty bits valid) x hx),
        List.prefix_refl _⟩ : Out C target.H (.val .int :: .val .int :: Γ)) := by
  have update := value_run bits valid (target.push (integerValue (ty bits valid) x hx))
    inc (.simple (.local .here)) x hx rfl
  let old := integerValue (ty bits valid) x hx
  let new := integerValue (ty bits valid) ((ty bits valid).wrap (changed inc x))
    ((ty bits valid).wrap_mem (changed inc x))
  have captured : (Stmt.declLocal .int (.user "v07_old")
      (some (.simple (.local i)))).run target =
      .ok (⟨target.push old,List.prefix_refl _⟩) := by
    change Except.ok (⟨target.push (TEnv.get i target.env),List.prefix_refl _⟩ :
      Out C target.H (.val .int :: Γ)) = _
    rw [read]
  have written : (Stmt.assignLocal (.there i) (updateValue bits inc (.simple (.local .here)))).run
      (target.push old) = .ok (⟨(target.setLocal i new).push old,List.prefix_refl _⟩) := by
    change (do
      let v ← (updateValue bits inc (.simple (.local .here))).evalT (target.push old)
      pure (⟨(target.push old).setLocal (.there i) v,List.prefix_refl _⟩ :
        Out C target.H (.val .int :: Γ))) = _
    rw [update]
    rfl
  have selected : (Stmt.declLocal .int (.user "v07_updated_result")
      (some (.simple (.local (if pre then .there i else .here))))).run
      ((target.setLocal i new).push old) =
      .ok (⟨((target.setLocal i new).push old).push (if pre then new else old),List.prefix_refl _⟩) := by
    cases pre
    · rfl
    · change Except.ok (⟨((target.setLocal i new).push old).push
        (TEnv.get i (TEnv.set i new target.env)),List.prefix_refl _⟩ :
          Out C target.H (.val .int :: .val .int :: Γ)) = _
      rw [TEnv.get_set]
      rfl
  unfold code
  rw [Prog.run_cons_ok captured,Prog.run_cons_ok written,Prog.run_cons_ok selected,Prog.run_nil]
  rfl


theorem operand_run (bits : Nat) (valid : bits % 8 = 0 ∧ 8 ≤ bits ∧ bits ≤ 256)
    {C : Contract} {Γ : Ctx} (target : State C Γ) (inc pre : Bool) (i : Idx Γ (.val .int))
    (x : Int) (hx : (ty bits valid).lo ≤ x ∧ x ≤ (ty bits valid).hi)
    (read : TEnv.get i target.env = integerValue (ty bits valid) x hx) :
    (operand bits inc pre i).run target =
      .ok (⟨target.setLocal i (integerValue (ty bits valid) ((ty bits valid).wrap (changed inc x))
        ((ty bits valid).wrap_mem (changed inc x))),List.prefix_refl _⟩,
        .prim (if pre then integerValue (ty bits valid) ((ty bits valid).wrap (changed inc x))
          ((ty bits valid).wrap_mem (changed inc x)) else integerValue (ty bits valid) x hx)) := by
  unfold operand DeferredSource.Operand.run
  rw [code_run bits valid target inc pre i x hx read]
  rfl

/-- Initial alignment determines both runs, every updated alias, every selected
untouched local and the result captured before dropping the two fresh binders. -/
theorem transport (bits : Nat) (valid : bits % 8 = 0 ∧ 8 ≤ bits ∧ bits ≤ 256)
    {E : Source.Env} {srcΓ : Source.RCtx} {C : Contract} {Γ : Ctx} {ι : Type}
    (G : Source.Glob E) (F : Source.Fr) (fuel : Nat)
    (source : Source.EMState E srcΓ) (target : State C Γ) (inc pre : Bool)
    (si : ι → Source.Idx srcΓ (.int (ty bits valid))) (ti : ι → Idx Γ (.val .int))
    (family : IntegerLocalFamily (ty bits valid) si ti source.1 target.env)
    (i : ι) (x : Int) (hx : (ty bits valid).lo ≤ x ∧ x ≤ (ty bits valid).hi)
    (read : source.1.get (si i) = .int x hx) :
    (Source.evalE G {F with checked := false} (fuel+2) (.incDec inc pre (.local (si i)))).run source =
      (.ok (.val (if pre then Source.intWrap (ty bits valid) (changed inc x) else .int x hx)),
        (source.1.set (si i) (Source.intWrap (ty bits valid) (changed inc x)),source.2)) ∧
    (operand bits inc pre (ti i)).run target =
      .ok (⟨target.setLocal (ti i) (integerValue (ty bits valid) ((ty bits valid).wrap (changed inc x))
        ((ty bits valid).wrap_mem (changed inc x))),List.prefix_refl _⟩,
        .prim (if pre then integerValue (ty bits valid) ((ty bits valid).wrap (changed inc x))
          ((ty bits valid).wrap_mem (changed inc x)) else integerValue (ty bits valid) x hx)) ∧
    IntValueRel (ty bits valid)
      ((if pre then Source.intWrap (ty bits valid) (changed inc x) else .int x hx) : Source.Val E.layout (.int (ty bits valid)))
      (if pre then integerValue (ty bits valid) ((ty bits valid).wrap (changed inc x))
        ((ty bits valid).wrap_mem (changed inc x)) else integerValue (ty bits valid) x hx) ∧
    IntegerLocalFamily (ty bits valid) si ti
      (source.1.set (si i) (Source.intWrap (ty bits valid) (changed inc x)))
      (TEnv.set (ti i) (integerValue (ty bits valid) ((ty bits valid).wrap (changed inc x))
        ((ty bits valid).wrap_mem (changed inc x))) target.env) := by
  refine ⟨source_run bits valid G F fuel source inc pre (si i) x hx read,
    operand_run bits valid target inc pre (ti i) x hx (family.read i x hx read),?_,⟨?_,family.aliases⟩⟩
  · cases pre <;> exact integer_related _ _ _
  · intro k
    by_cases same : (si i).toNat = (si k).toNat
    · have hs := source_idx_injective _ _ same
      have ht := Idx.toNat_inj _ _ ((family.aliases i k).mp same)
      rw [←hs,←ht,source_locals_get_set,TEnv.get_set]
      exact integer_related _ _ _
    · have ht : (ti i).toNat ≠ (ti k).toNat := fun e => same ((family.aliases i k).mpr e)
      rw [source_locals_get_set_ne source.1 _ _ _ same,TEnv.get_set_ne _ _ _ target.env ht]
      exact family.values k

end Solidity.Lowering.V07.SignedLocalUpdate

/-- info: 'Solidity.Lowering.V07.SignedLocalUpdate.source_value' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Solidity.Lowering.V07.SignedLocalUpdate.source_value

/-- info: 'Solidity.Lowering.V07.SignedLocalUpdate.source_run' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Solidity.Lowering.V07.SignedLocalUpdate.source_run

/-- info: 'Solidity.Lowering.V07.SignedLocalUpdate.value_run' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Solidity.Lowering.V07.SignedLocalUpdate.value_run

/-- info: 'Solidity.Lowering.V07.SignedLocalUpdate.code_run' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Solidity.Lowering.V07.SignedLocalUpdate.code_run

/-- info: 'Solidity.Lowering.V07.SignedLocalUpdate.operand_run' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Solidity.Lowering.V07.SignedLocalUpdate.operand_run

/-- info: 'Solidity.Lowering.V07.SignedLocalUpdate.transport' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Solidity.Lowering.V07.SignedLocalUpdate.transport
