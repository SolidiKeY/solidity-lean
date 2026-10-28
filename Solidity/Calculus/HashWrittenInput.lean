import Solidity.Calculus.HashMove

/-!
# Written memory inside hash input reasoning (M7)
Normalized byte equality and actual write/update observations compose without
changing any hash function. Converse congruence uses only the existing finite
formula-local premise and excludes recovery. Allocation counterexamples retain
every binder's own premise. `HashWrittenRealize` consumes these helpers for
its exact syntax schema; `HashWritten` supplies the general memory-cut adapter.
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

/-- Construct the update's finite premise from its unique actual landing.
The updater itself must contain no hash nodes. -/
theorem hashFree_update_of_landing {m : Modality} {U : Upd C Γ Δ}
    {φ : Fml C Δ} {σ : State C Γ} {g : GlobT C σ.H} {τ : State C Δ}
    (hu : ∀ k inp out, ¬ U.HashIn σ k inp out)
    (hl : U.Lands σ g τ) (hf : φ.HashFree τ) :
    (Fml.upd m U φ).HashFree σ := by
  intro k hk x y out hx hy
  rcases hx with hx | ⟨gx, tx, _, lx, hx⟩
  · exact (hu k x out hx).elim
  rcases hy with hy | ⟨gy, ty, _, ly, hy⟩
  · exact (hu k y out hy).elim
  have ex : tx = τ := Upd.Lands.eq lx hl
  have ey : ty = τ := Upd.Lands.eq ly hl
  subst tx
  subst ty
  exact hf k hk x y out hx hy

/-- Realized unequal inputs at an actual landing refute both modalities.
A failed write cannot supply this certificate. -/
theorem refutes_update_input {m : Modality} {U : Upd C Γ Δ}
    {σ : State C Γ} {g : GlobT C σ.H} {τ : State C Δ}
    (k : HashKind) (hk : k ≠ .ecrecover) {R S : RefTy}
    (i : Idx Δ (.mem R)) (j : Idx Δ (.mem S)) {a b : Nat}
    (hu : ∀ kind inp out, ¬ U.HashIn σ kind inp out)
    (hl : U.Lands σ g τ)
    (hf : (Fml.eq (hnode k i) (hnode k j)).HashFree τ)
    (hi : τ.getV i = some a) (hj : τ.getV j = some b)
    (hne : τ.glob.memT.hashInput R a ≠ τ.glob.memT.hashInput S b) :
    ¬ Fml.holdsH σ (.upd m U (.eq (hnode k i) (hnode k j))) := by
  intro h
  have hp := h (hashFree_update_of_landing hu hl hf)
  have he := hp.of_lands hl
  exact hne ((hashEq_iff_input τ k hk i j hi hj hf).1 he)

/-- Minimal scoped realization interface: an actual typed object and a
body counterexample under that body's own finite premise. -/
structure AllocCounterexample (σ : State C Γ) (R : RefTy)
    (φ : Fml C (.mem R :: Γ)) where
  object : MObj σ.H R
  refutes : ¬ Fml.holdsH ((σ.alloc object).1.push (t := .mem R) (some (σ.alloc object).2)) φ

/-- Nested applications preserve the distinct premise at every binder. -/
theorem AllocCounterexample.refutes_alloc {σ : State C Γ} {R : RefTy}
    {φ : Fml C (.mem R :: Γ)} (r : AllocCounterexample σ R φ) (x : Var) :
    ¬ Fml.holdsH σ (.allocAll x R φ) := by
  intro h
  apply r.refutes
  exact h (fun _ _ _ _ _ h => h.elim) r.object

/-- info: 'Solidity.Decide.WrittenMemory.hashInput_write_index' depends on axioms: [propext] -/
#guard_msgs in #print axioms hashInput_write_index
/-- info: 'Solidity.Decide.WrittenMemory.hashEq_afterT_iff' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms hashEq_afterT_iff
/-- info: 'Solidity.Decide.WrittenMemory.hashFree_update_of_landing' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms hashFree_update_of_landing
/-- info: 'Solidity.Decide.WrittenMemory.refutes_update_input' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms refutes_update_input
/-- info: 'Solidity.Decide.WrittenMemory.AllocCounterexample.refutes_alloc' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in #print axioms AllocCounterexample.refutes_alloc
end Solidity.Decide.WrittenMemory
