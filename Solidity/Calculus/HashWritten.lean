import Solidity.Calculus.Decision

/-!
# Written memory inside hash input reasoning (M7)

These Lean-only helpers compose the existing hash-input congruence and
memory cut, without changing the hash functions or the decision dispatcher.
The converse uses only the formula's existing finite `HashFree` premise.
A successful heap write observes a list update of normalized bytes; equality
of those inputs is equal lengths and a bounded pointwise comparison.

`HashInputReduction` deliberately requires a proof of the intrinsic input
formula, including every binder's own premise. Its memory cut is exact under
the original premise. Refutation additionally requires that premise at the
returned prestate. The negative quantified-array reduction/realization needed
to produce this certificate for `gapWrittenMemory` is not implemented here.
-/

namespace Solidity.Decide.WrittenMemory

variable {C : Contract} {Γ Δ : Ctx}

/-- The byte observed by each builtin, including `ecrecover`. -/
def byte (b : Int) : Nat := b.toNat % 256

/-- `s` and `t` have equal byte inputs exactly when their lengths and every
in-range byte agree. Comparing full `uint` elements would be too strong. -/
theorem bytes_eq_iff (xs ys : List Int) :
    xs.map byte = ys.map byte ↔ xs.length = ys.length ∧
      ∀ i, i < xs.length → xs[i]?.map byte = ys[i]?.map byte := by
  constructor
  · intro h
    have hl : (xs.map byte).length = (ys.map byte).length := congrArg List.length h
    refine ⟨by simpa only [List.length_map] using hl, ?_⟩
    intro i _
    simpa only [List.getElem?_map] using congrArg (fun zs : List Nat => zs[i]?) h
  · intro ⟨hl, he⟩
    apply List.ext_getElem?
    intro i
    simp only [List.getElem?_map]
    by_cases hi : i < xs.length
    · exact he i hi
    · have hx : xs[i]? = none := List.getElem?_eq_none (Nat.le_of_not_lt hi)
      have hy : ys[i]? = none := List.getElem?_eq_none (by omega)
      simp only [hx, hy, Option.map_none]

/-- After `s[j] = v`, input equality compares the written byte at `j` and
all untouched bytes elsewhere. The bound is essential for a successful write. -/
theorem written_bytes_eq_iff (xs ys : List Int) (j : Nat) (v : Int) (hj : j < xs.length) :
    (xs.set j v).map byte = ys.map byte ↔ xs.length = ys.length ∧
      ∀ i, i < xs.length →
        (if j = i then some (byte v) else xs[i]?.map byte) = ys[i]?.map byte := by
  rw [bytes_eq_iff]
  simp only [List.length_set]
  apply and_congr_right
  intro _
  apply forall_congr'
  intro i
  apply imp_congr_right
  intro _
  by_cases hji : j = i
  · subst i
    simp only [List.getElem?_set, hj, ↓reduceIte, Option.map_some]
  · simp only [List.getElem?_set, hji, ↓reduceIte]

/-- `s[j] = v` changes exactly that byte in the array object's input. -/
theorem words_setElem_bytes {H : HTy} (o : MObj H (.array (.prim .uint)))
    (j : Nat) (v : PrimTy.uint.Denote) :
    (MObj.words (.array (.prim .uint)) (MObj.setElem .dyn o j v)).map byte =
      ((MObj.words (.array (.prim .uint)) o).map byte).set j (byte v.1) := by
  simp only [MObj.setElem_dyn, MObj.words, List.map_set]

/-- The observation of an actual successful `s[j] = v`, rather than an
out-of-bounds `List.set` (which alone would silently do nothing). -/
theorem words_write_index {H : HTy} {hp hp' : Heap H}
    {r : HRef H (.array (.prim .uint))} {j v : PrimTy.uint.Denote}
    (hw : hp.writeAddr (.index r .dyn j) v = some hp') :
    (MObj.words (.array (.prim .uint)) (hp'.get r)).map byte =
      ((MObj.words (.array (.prim .uint)) (hp.get r)).map byte).set j.1.toNat (byte v.1) := by
  simp only [Heap.writeAddr, Heap.setIndex] at hw
  split at hw
  · simp only [Option.some.injEq] at hw
    subst hp'
    simpa only [Heap.get_set_same] using words_setElem_bytes (hp.get r) j.1.toNat v
  · cases hw

/-- A typed object's hash input is its normalized byte observation. -/
theorem hashInput_ref {H : HTy} (μ : Grown H (fun _ => Unit)) {R : RefTy} (r : HRef μ.H' R) :
    μ.hashInput R r.id = some ((MObj.words R (μ.heap.get r)).map byte) := by
  simp only [Grown.hashInput, HRef.ofId?_self, Option.map_some]
  rfl

/-- The hash input after a successful `s[j] = v`, on the actual updated
heap. This retains the unchanged tail and the original heap extension. -/
theorem hashInput_write_index {H : HTy} (μ : Grown H (fun _ => Unit))
    {hp' : Heap μ.H'} {r : HRef μ.H' (.array (.prim .uint))}
    {j v : PrimTy.uint.Denote} (hw : μ.heap.writeAddr (.index r .dyn j) v = some hp') :
    (⟨μ.ext, hp', ()⟩ : Grown H (fun _ => Unit)).hashInput (.array (.prim .uint)) r.id =
      some (((MObj.words (.array (.prim .uint)) (μ.heap.get r)).map byte).set
        j.1.toNat (byte v.1)) := by
  rw [hashInput_ref]
  exact congrArg some (words_write_index hw)

/-- An update's existing finite premise includes every hash at every
actual landing, including `s[0] = 1`'s written memory. -/
theorem hashFree_lands {m : Modality} {U : Upd C Γ Δ} {φ : Fml C Δ} {σ : State C Γ}
    (hf : (Fml.upd m U φ).HashFree σ) {g : GlobT C σ.H} {τ : State C Δ}
    (hl : U.Lands σ g τ) : φ.HashFree τ := by
  intro k hk x y out hx hy
  exact hf k hk x y out (.inr ⟨g, τ, hl.1, hl, hx⟩) (.inr ⟨g, τ, hl.1, hl, hy⟩)

/-- `hash(s) == hash(t)` reduces to input equality under its own finite
premise. Both locals must be set; this never assumes global injectivity. -/
theorem hashEq_iff_input (σ : State C Γ) (k : HashKind) (hk : k ≠ .ecrecover)
    {R S : RefTy} (i : Idx Γ (.mem R)) (j : Idx Γ (.mem S)) {a b : Nat}
    (hi : σ.getV i = some a) (hj : σ.getV j = some b)
    (hf : (Fml.eq (hnode k i) (hnode k j)).HashFree σ) :
    holds σ (.eq (hnode k i) (hnode k j)) ↔
      σ.glob.memT.hashInput R a = σ.glob.memT.hashInput S b := by
  change (hnode k i).denote σ = (hnode k j).denote σ ↔ _
  rw [hnode_denote σ k i hi, hnode_denote σ k j hj, Option.some.injEq]
  constructor
  · intro he
    have hb : (hnode k j).HashIn σ k (σ.glob.memT.hashInput S b)
        (σ.glob.memT.hashId k R a) := by
      rw [he]
      exact hnode_hashIn_of σ k j hj
    exact hf k hk _ _ _ (.inl (hnode_hashIn_of σ k i hi)) (.inr hb)
  · exact Grown.hashId_of_input σ.glob.memT k

/-- The same reduction through `[s[0] = 1]` or its diamond. The failed or
exhausted update branch is identical; the premise is used only at landings. -/
theorem hashEq_afterT_iff {m : Modality} (U : Upd C Γ Δ) (σ : State C Γ)
    (k : HashKind) (hk : k ≠ .ecrecover) {R S : RefTy}
    (i : Idx Δ (.mem R)) (j : Idx Δ (.mem S)) (a b : State C Δ → Nat)
    (hi : ∀ g τ, U.Lands σ g τ → τ.getV i = some (a τ))
    (hj : ∀ g τ, U.Lands σ g τ → τ.getV j = some (b τ))
    (hf : (Fml.upd m U (.eq (hnode k i) (hnode k j))).HashFree σ) :
    Fml.holdsS σ (.upd m U (.eq (hnode k i) (hnode k j))) ↔
      U.afterT m σ (fun τ => τ.glob.memT.hashInput R (a τ) = τ.glob.memT.hashInput S (b τ)) := by
  change U.afterT m σ (fun τ => holds τ (.eq (hnode k i) (hnode k j))) ↔ _
  cases hg : U.globT σ with
  | none => simp only [Upd.afterT, hg]
  | some g =>
    simp only [Upd.afterT, hg]
    have he : ∀ τ, U.Lands σ g τ →
        (holds τ (.eq (hnode k i) (hnode k j)) ↔
          τ.glob.memT.hashInput R (a τ) = τ.glob.memT.hashInput S (b τ)) :=
      fun τ hl => hashEq_iff_input τ k hk i j (hi g τ hl) (hj g τ hl) (hashFree_lands hf hl)
    exact ⟨fun h τ hl => (he τ hl).1 (h τ hl), fun h τ hl => (he τ hl).2 (h τ hl)⟩

/-- An intrinsic input formula with its scope-correct proof, under the
original formula's premise. This is not a coverage or extraction predicate. -/
structure HashInputReduction (φ : Fml C []) where
  formula : Fml C []
  correct : ∀ σ : State C [], φ.HashFree σ → (Fml.holdsS σ φ ↔ holds σ formula)

namespace HashInputReduction

/-- Composing input reduction with exactly `decideMem`'s existing hoist and
cut. The original finite premise is retained, including binder-local meaning. -/
def cut {φ : Fml C []} (r : HashInputReduction φ) {ψ : Fml C []}
    (hc : (r.formula.hoist 1024).mxTop = some ψ) : HashInputReduction φ :=
  ⟨ψ, fun σ hf => (r.correct σ hf).trans
    ((Fml.hoist_holds 1024 r.formula σ).symm.trans (Fml.mxTop_holds hc σ))⟩

/-- Run the existing memory cut only after a proof-backed input reduction. -/
def cut? {φ : Fml C []} (r : HashInputReduction φ) : Option (HashInputReduction φ) :=
  match hc : (r.formula.hoist 1024).mxTop with
  | none => none
  | some _ψ => some (r.cut hc)

/-- A proof of the cut input leaf proves the original hash formula. -/
theorem sound {φ : Fml C []} (r : HashInputReduction φ) (h : Fml.Valid r.formula) : Fml.ValidH φ :=
  fun σ hf => (r.correct σ hf).2 (h σ)

/-- A false cut leaf refutes the original only with its actual finite
premise; at a collision `holdsH` could instead be vacuously true. -/
theorem refutes {φ : Fml C []} (r : HashInputReduction φ) (σ : State C [])
    (hf : φ.HashFree σ) (hn : ¬ holds σ r.formula) : ¬ Fml.holdsH σ φ :=
  fun h => hn ((r.correct σ hf).1 (h hf))

/-- The existing memory decision can prove a certified hash-input formula. -/
theorem valid_of_decideMem {φ : Fml C []} (r : HashInputReduction φ)
    (h : decideMem r.formula = .proved) : Fml.ValidH φ := r.sound (decideMem_sound h)

/-- Refutation preserves the same prestate and explicitly requires its
original hash premise, rather than assuming collision freedom. -/
theorem refutes_of_decideMem {φ : Fml C []} (r : HashInputReduction φ) {σ : State C []}
    (hf : φ.HashFree σ) (h : decideMem r.formula = .refuted σ) : ¬ Fml.holdsH σ φ :=
  r.refutes σ hf (decideMem_refutes h)

end HashInputReduction

/-- info: 'Solidity.Decide.WrittenMemory.hashInput_write_index' depends on axioms: [propext] -/
#guard_msgs in #print axioms hashInput_write_index
/-- info: 'Solidity.Decide.WrittenMemory.hashEq_afterT_iff' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms hashEq_afterT_iff
/-- info: 'Solidity.Decide.WrittenMemory.HashInputReduction.cut?' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms HashInputReduction.cut?
/-- info: 'Solidity.Decide.WrittenMemory.HashInputReduction.valid_of_decideMem' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in #print axioms HashInputReduction.valid_of_decideMem
/-- info: 'Solidity.Decide.WrittenMemory.HashInputReduction.refutes_of_decideMem' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in #print axioms HashInputReduction.refutes_of_decideMem

end Solidity.Decide.WrittenMemory
