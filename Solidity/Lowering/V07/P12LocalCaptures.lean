import Solidity.Lowering.V07.P12NextInterface

/-!
# Generic P12 reference captures of Source locals

`P12StorageCaptureControls.producer` and `P12MemoryCaptureControls.producer`
build the published `StorageCapture`/`MemoryCapture` records for one fixture.
This module builds them for ANY context map, Source local `i`, native slot
`j` (`m.slot i = ⟨.alias R, j⟩` or `⟨.mem R, j⟩`) and ANY value/world relations,
given two explicit relation properties:

- `StorageNonnull`/`MemoryNonnull`: a related reference binding is `some`;
- `StorageFaithful`/`MemoryFaithful`: two related references are equal iff
  their Source paths (addresses) are equal. Memory compares `HRef.id` across
  native reference types, as the interface does.

Both are required only at worlds related by `worlds`. They are properties
of the relations alone (no run, no postrelation, no
desired preservation result); the fixtures' relations satisfy them
(`P12LocalCaptureControls`). The producers do the rest: Source local
execution is inverted at every horizon (horizon zero times out, outside the
contract), the native code is the published alias capture, and alias
reflection follows from faithfulness at the reached caller.

Not supplied: selection of the local from admitted syntax, effectful
reference expressions (index/member paths), allocation, copies, deletion or
lifetimes, and physical store/heap correspondence.
-/
namespace Solidity.Lowering.V07.P12LocalCaptures
open P12NextInterface

variable {E : Source.Env} {C : Contract}

/-- Related storage-reference bindings are present. -/
def StorageNonnull (values : ValueRelation E C) (worlds : WorldRelation E C) (R : RefTy) : Prop :=
  ∀ (s : Source.St E) (g : State C []), worlds s g → ∀ (σ : Source.STy) (loc : σ.loc? = some .storage)
    (p : Source.SPath) (v : Option (SRef C (.ref R))),
    values s g σ (.alias R) (.storRef loc p) v → ∃ r, v = some r

/-- Related storage references are equal iff their Source paths are. -/
def StorageFaithful (values : ValueRelation E C) (worlds : WorldRelation E C) (R : RefTy) : Prop :=
  ∀ (s : Source.St E) (g : State C []), worlds s g → ∀ (σ σ' : Source.STy)
    (loc : σ.loc? = some .storage) (loc' : σ'.loc? = some .storage)
    (p p' : Source.SPath) (r r' : SRef C (.ref R)),
    values s g σ (.alias R) (.storRef loc p) (some r) →
    values s g σ' (.alias R) (.storRef loc' p') (some r') → (p = p' ↔ r = r')

/-- Related memory-reference bindings are present. -/
def MemoryNonnull (values : ValueRelation E C) (worlds : WorldRelation E C) (R : RefTy) : Prop :=
  ∀ (s : Source.St E) (g : State C []), worlds s g → ∀ (σ : Source.STy) (loc : σ.loc? = some .memory)
    (a : Nat) (v : Option (HRef g.H R)),
    values s g σ (.mem R) (.memRef loc a) v → ∃ r, v = some r

/-- Related memory references have equal identities iff their Source
addresses are equal, across native reference types. -/
def MemoryFaithful (values : ValueRelation E C) (worlds : WorldRelation E C) (R : RefTy) : Prop :=
  ∀ (s : Source.St E) (g : State C []), worlds s g → ∀ (σ σ' : Source.STy) (R' : RefTy)
    (loc : σ.loc? = some .memory) (loc' : σ'.loc? = some .memory)
    (a a' : Nat) (r : HRef g.H R) (r' : HRef g.H R'),
    values s g σ (.mem R) (.memRef loc a) (some r) →
    values s g σ' (.mem R') (.memRef loc' a') (some r') → (a = a' ↔ r.id = r'.id)

/-- Source local reads succeed with the stored value and the same state, at
every positive horizon, and never revert. -/
theorem local_success {srcΓ : Source.RCtx} {τ : Source.STy} (G : Source.Glob E) (F : Source.Fr)
    (fuel : Nat) (i : Source.Idx srcΓ τ) (s after : Source.EMState E srcΓ)
    (v : Source.Val E.layout τ)
    (run : (Source.evalE G F fuel (.local i)).run s = (.ok (.val v),after)) :
    s.1.get i = v ∧ after = s := by
  cases fuel with
  | zero => cases run
  | succ n =>
    have h : (Source.evalE G F (n+1) (.local i)).run s = (.ok (.val (s.1.get i)),s) := rfl
    rw [h] at run
    have hv : some (s.1.get i) = some v := congrArg
      (fun x : Source.R (Source.RVal E.layout τ) => match x with | .ok (.val w) => some w | _ => none)
      (congrArg Prod.fst run)
    exact ⟨Option.some.inj hv, (congrArg Prod.snd run).symm⟩

theorem local_not_revert {srcΓ : Source.RCtx} {τ : Source.STy} (G : Source.Glob E) (F : Source.Fr)
    (fuel : Nat) (i : Source.Idx srcΓ τ) (s after : Source.EMState E srcΓ) (data : Roadmap.Bytes) :
    (Source.evalE G F fuel (.local i)).run s ≠ (.error (.revert data),after) := by
  cases fuel <;> intro run <;> cases run

/-- The relation at a mapped slot, with the slot's sigma unfolded. -/
theorem slot_related {srcΓ : Source.RCtx} {Γ : Ctx} {τ : Source.STy} {u : LTy}
    (m : ContextMap srcΓ Γ) (values : ValueRelation E C) (worlds : WorldRelation E C)
    (s : Source.EMState E srcΓ) (t : State C Γ) (aligned : Aligned m values worlds s t)
    (i : Source.Idx srcΓ τ) (j : Idx Γ u) (slot : m.slot i = ⟨u, j⟩) :
    values s.2 t.glob τ u (s.1.get i) (TEnv.get j t.env) := by
  have h := aligned.2 i
  rw [slot] at h
  exact h

/-- **Generic storage-reference capture** of a Source local. -/
def storageLocal {srcΓ : Source.RCtx} {Γ : Ctx} (G : Source.Glob E) (F : Source.Fr)
    (m : ContextMap srcΓ Γ) (values : ValueRelation E C) (worlds : WorldRelation E C)
    (τ : Source.STy) (location : τ.loc? = some .storage) (R : RefTy)
    (i : Source.Idx srcΓ τ) (j : Idx Γ (.alias R)) (slot : m.slot i = ⟨.alias R, j⟩)
    (inhabited : ∃ s t, Aligned m values worlds s t)
    (nonnull : StorageNonnull values worlds R) (faithful : StorageFaithful values worlds R) :
    StorageCapture G F m values worlds τ location R (.local i) where
  code := storageCapture j
  initial_nonempty := inhabited
  success := by
    intro n s after t path aligned run
    obtain ⟨read, same⟩ := local_success G F n i s after _ run
    subst after
    have rel := slot_related m values worlds s t aligned i j slot
    rw [read] at rel
    obtain ⟨r, hr⟩ := nonnull _ _ aligned.1 τ location path _ rel
    rw [hr] at rel
    refine ⟨⟨t.push (t := .alias R) (some r), List.prefix_refl _⟩, r,
      storage_capture_run t j r hr, rfl, rfl, ?_, aligned.1, ?_⟩
    · exact ContextMap.related_cons m _ s.1 t.env aligned.2 τ (.alias R) _ (some r) rel
    · intro σ oldLocation i' j' oldPath oldRef slot' read' target'
      have rel' := slot_related m values worlds s t aligned i' j' slot'
      rw [read'] at rel'
      have target'' : TEnv.get j' t.env = some oldRef := target'
      rw [target''] at rel'
      exact faithful _ _ aligned.1 τ σ location oldLocation path oldPath r oldRef rel rel'
  revert := by
    intro n s after t data _ run
    exact False.elim (local_not_revert G F n i s after data run)

/-- **Generic memory-reference capture** of a Source local (no allocation). -/
def memoryLocal {srcΓ : Source.RCtx} {Γ : Ctx} (G : Source.Glob E) (F : Source.Fr)
    (m : ContextMap srcΓ Γ) (values : ValueRelation E C) (worlds : WorldRelation E C)
    (τ : Source.STy) (location : τ.loc? = some .memory) (R : RefTy)
    (mapFree : (Ty.ref R).mapFree = true)
    (i : Source.Idx srcΓ τ) (j : Idx Γ (.mem R)) (slot : m.slot i = ⟨.mem R, j⟩)
    (inhabited : ∃ s t, Aligned m values worlds s t)
    (nonnull : MemoryNonnull values worlds R) (faithful : MemoryFaithful values worlds R) :
    MemoryCapture G F m values worlds τ location R mapFree (.local i) where
  code := memoryCapture j mapFree
  initial_nonempty := inhabited
  success := by
    intro n s after t address aligned run
    obtain ⟨read, same⟩ := local_success G F n i s after _ run
    subst after
    have rel := slot_related m values worlds s t aligned i j slot
    rw [read] at rel
    obtain ⟨r, hr⟩ := nonnull _ _ aligned.1 τ location address _ rel
    rw [hr] at rel
    refine ⟨⟨t.push (t := .mem R) (some r), List.prefix_refl _⟩, r,
      memory_capture_run t j mapFree r hr, rfl, rfl, ?_, aligned.1, ?_⟩
    · exact ContextMap.related_cons m _ s.1 t.env aligned.2 τ (.mem R) _ (some r) rel
    · intro σ oldLocation i' oldR j' oldAddress oldRef slot' read' target'
      have rel' := slot_related m values worlds s t aligned i' j' slot'
      rw [read'] at rel'
      have target'' : TEnv.get j' t.env = some oldRef := target'
      rw [target''] at rel'
      exact faithful _ _ aligned.1 τ σ oldR location oldLocation address oldAddress r oldRef rel rel'
  revert := by
    intro n s after t data _ run
    exact False.elim (local_not_revert G F n i s after data run)

/-- info: 'Solidity.Lowering.V07.P12LocalCaptures.local_success' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms local_success
/-- info: 'Solidity.Lowering.V07.P12LocalCaptures.local_not_revert' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms local_not_revert
/-- info: 'Solidity.Lowering.V07.P12LocalCaptures.slot_related' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms slot_related
/-- info: 'Solidity.Lowering.V07.P12LocalCaptures.storageLocal' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms storageLocal
/-- info: 'Solidity.Lowering.V07.P12LocalCaptures.memoryLocal' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms memoryLocal

end Solidity.Lowering.V07.P12LocalCaptures
