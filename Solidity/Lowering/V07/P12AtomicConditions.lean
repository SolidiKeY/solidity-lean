import Solidity.Lowering.V07.P12NextInterface

/-! Actual Boolean literal/local clauses for the frozen P12 condition contract.
These producers preserve both complete states; they do not choose a compiler
for arbitrary source syntax or establish admission/resource adequacy. -/
namespace Solidity.Lowering.V07.P12AtomicConditions
open P12NextInterface
variable {E : Source.Env} {C : Contract} {srcΓ : Source.RCtx} {Γ : Ctx}

theorem literal_source_run (G : Source.Glob E) (F : Source.Fr) (n : Nat)
    (s : Source.EMState E srcΓ) (b : Bool) :
    (Source.evalE G F (n+1) (.bool b)).run s = (.ok (.val (.bool b)),s) := by
  rfl

theorem literal_source_success (G : Source.Glob E) (F : Source.Fr) (n : Nat)
    (s a : Source.EMState E srcΓ) (b c : Bool)
    (run : (Source.evalE G F n (.bool b)).run s = (.ok (.val (.bool c)),a)) : c=b ∧ a=s := by
  cases n with
  | zero => cases run
  | succ n =>
    rw [literal_source_run] at run
    have value : some b = some c := congrArg
      (fun out : Source.R (Source.RVal E.layout .bool) =>
        match out with | .ok (.val (.bool x)) => some x | _ => none) (congrArg Prod.fst run)
    exact ⟨(Option.some.inj value).symm,(congrArg Prod.snd run).symm⟩

theorem literal_source_not_revert (G : Source.Glob E) (F : Source.Fr) (n : Nat)
    (s a : Source.EMState E srcΓ) (b : Bool) (data : Roadmap.Bytes) :
    (Source.evalE G F n (.bool b)).run s ≠ (.error (.revert data),a) := by
  cases n <;> intro run <;> cases run

def literalOperand (b : Bool) : DeferredSource.Operand C Γ (.prim .bool) :=
  .ofSrc (.val (.simple (.bool b)))
theorem literal_native_run (t : State C Γ) (b : Bool) :
    (literalOperand b).run t = .ok (⟨t,List.prefix_refl _⟩,.prim b) := by
  rfl

/-- Initial alignment is an inhabited input relation, not a desired result.
No relationship between the constant and unrelated caller slots is required. -/
def literal (G : Source.Glob E) (F : Source.Fr) (m : ContextMap srcΓ Γ)
    (values : ValueRelation E C) (worlds : WorldRelation E C) (b : Bool)
    (inhabited : ∃ s t, Aligned m values worlds s t) : Condition G F m values worlds (.bool b) where
  operand := literalOperand b
  initial_nonempty := inhabited
  success := by
    intro n s a t c old run
    obtain ⟨rfl,rfl⟩ := literal_source_success G F n s a b c run
    exact ⟨⟨t,List.prefix_refl _⟩,literal_native_run t _,old⟩
  revert := by
    intro n s a t data _ run
    exact False.elim (literal_source_not_revert G F n s a b data run)

theorem local_source_success (G : Source.Glob E) (F : Source.Fr) (n : Nat)
    (s a : Source.EMState E srcΓ) (i : Source.Idx srcΓ .bool) (b c : Bool)
    (read : s.1.get i = .bool b)
    (run : (Source.evalE G F n (.local i)).run s = (.ok (.val (.bool c)),a)) : c=b ∧ a=s := by
  cases n with
  | zero => cases run
  | succ n =>
    rw [source_local_value_run G F n s i (.bool b) read] at run
    have value : some b = some c := congrArg
      (fun out : Source.R (Source.RVal E.layout .bool) =>
        match out with | .ok (.val (.bool x)) => some x | _ => none) (congrArg Prod.fst run)
    exact ⟨(Option.some.inj value).symm,(congrArg Prod.snd run).symm⟩

theorem local_source_not_revert (G : Source.Glob E) (F : Source.Fr) (n : Nat)
    (s a : Source.EMState E srcΓ) (i : Source.Idx srcΓ .bool) (data : Roadmap.Bytes) :
    (Source.evalE G F n (.local i)).run s ≠ (.error (.revert data),a) := by
  cases n <;> intro run <;> cases run

def localOperand (j : Idx Γ (.val .bool)) : DeferredSource.Operand C Γ (.prim .bool) :=
  .ofSrc (.val (.simple (.local j)))
theorem local_native_run (t : State C Γ) (j : Idx Γ (.val .bool)) :
    (localOperand j).run t = .ok (⟨t,List.prefix_refl _⟩,.prim (TEnv.get j t.env)) := by
  rfl

/-- A local clause follows the actual mapped binding at each initial state.
Boolean reflection relates source/native contents; no post-state/run is assumed. -/
def readLocal (G : Source.Glob E) (F : Source.Fr) (m : ContextMap srcΓ Γ)
    (values : ValueRelation E C) (worlds : WorldRelation E C)
    (reflectBool : ∀ s t v b, values s t .bool (.val .bool) v b → v = .bool b)
    (inhabited : ∃ s t, Aligned m values worlds s t)
    (i : Source.Idx srcΓ .bool) (j : Idx Γ (.val .bool)) (slot : m.slot i = ⟨.val .bool,j⟩) :
    Condition G F m values worlds (.local i) where
  operand := localOperand j
  initial_nonempty := inhabited
  success := by
    intro n s a t c old run
    have linked := old.2 i
    rw [slot] at linked
    have read := reflectBool s.2 t.glob (s.1.get i) (TEnv.get j t.env) linked
    obtain ⟨rfl,rfl⟩ := local_source_success G F n s a i (TEnv.get j t.env) c read run
    exact ⟨⟨t,List.prefix_refl _⟩,local_native_run t j,old⟩
  revert := by
    intro n s a t data _ run
    exact False.elim (local_source_not_revert G F n s a i data run)

/-- info: 'Solidity.Lowering.V07.P12AtomicConditions.literal_source_run' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms Solidity.Lowering.V07.P12AtomicConditions.literal_source_run

/-- info: 'Solidity.Lowering.V07.P12AtomicConditions.literal_source_success' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms Solidity.Lowering.V07.P12AtomicConditions.literal_source_success

/-- info: 'Solidity.Lowering.V07.P12AtomicConditions.literal_source_not_revert' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms Solidity.Lowering.V07.P12AtomicConditions.literal_source_not_revert

/-- info: 'Solidity.Lowering.V07.P12AtomicConditions.literal_native_run' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms Solidity.Lowering.V07.P12AtomicConditions.literal_native_run

/-- info: 'Solidity.Lowering.V07.P12AtomicConditions.local_source_success' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms Solidity.Lowering.V07.P12AtomicConditions.local_source_success

/-- info: 'Solidity.Lowering.V07.P12AtomicConditions.local_source_not_revert' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms Solidity.Lowering.V07.P12AtomicConditions.local_source_not_revert

/-- info: 'Solidity.Lowering.V07.P12AtomicConditions.local_native_run' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Solidity.Lowering.V07.P12AtomicConditions.local_native_run

/-- info: 'Solidity.Lowering.V07.P12AtomicConditions.literal' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Solidity.Lowering.V07.P12AtomicConditions.literal

/-- info: 'Solidity.Lowering.V07.P12AtomicConditions.readLocal' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Solidity.Lowering.V07.P12AtomicConditions.readLocal

end Solidity.Lowering.V07.P12AtomicConditions
