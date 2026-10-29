import Solidity.Calculus.MemObserve

/-!
# Exact enclosing negative-block preparation before the memory cut

A fresh uint length atom precedes its array. All finite-instance indices
are value terms in that outer scope; the actual length is constrained in
the array body. The supported negative range block and exterior observations
are recognized with equality proofs. Reconstruction preserves the real fresh
heap identity and every optional exterior observation.
-/

namespace Solidity.Decide

variable {C : Contract} {Γ : Ctx} {q : PrimTy}

def mxLengthAtom : MxPoint C (.mem (.array (.prim q)) :: .val .uint :: Γ) :=
  MxPoint.ix .length (.pvV (.there .here)) rfl

def mxLiteralPoint (k : PrimTy.uint.Denote) : MxPoint C (.mem (.array (.prim q)) :: .val .uint :: Γ) :=
  MxPoint.ix .read (.app0 (.lit k)) rfl

/-- Zero, the scoped length atom, exterior read indices, and checked
successors. A successor at uint's top remains a failed guarded point. -/
def mxLengthPoints (ks : List PrimTy.uint.Denote) :
    List (MxPoint C (.mem (.array (.prim q)) :: .val .uint :: Γ)) :=
  [mxLiteralPoint (uintOfNat 0), mxLengthAtom] ++
    ks.map mxLiteralPoint ++ [mxLengthAtom.succ] ++ ks.map (fun k => (mxLiteralPoint k).succ)

def mxLengthPrep (x : Var) (v : q.Denote) (ks : List PrimTy.uint.Denote) :
    MxInstPrep C (.mem (.array (.prim q)) :: .val .uint :: Γ) x (mxRangeBody .here v) :=
  ⟨mxLengthPoints ks, mxRangeInstances .here v (mxLengthPoints ks),
    mxRangeInstances_checked x .here v (mxLengthPoints ks)⟩

theorem mxLengthPrep_zero (σ : State C Γ) (n : PrimTy.uint.Denote)
    (o : MObj σ.H (.array (.prim q))) (x : Var) (v : q.Denote) (ks : List PrimTy.uint.Denote) :
    ∃ pt ∈ (mxLengthPrep (C := C) (Γ := Γ) x v ks).points,
      pt.tm.eval ((σ.push (t := .val .uint) n).allocPush o) = some (uintOfNat 0) := by
  refine ⟨mxLiteralPoint (uintOfNat 0), ?_, rfl⟩
  exact List.mem_append_left _ List.mem_cons_self

theorem mxLengthPrep_read (x : Var) (v : q.Denote) (ks : List PrimTy.uint.Denote)
    {k : PrimTy.uint.Denote} (hk : k ∈ ks) :
    mxLiteralPoint (C := C) (Γ := Γ) (q := q) k ∈ (mxLengthPrep x v ks).points := by
  apply List.mem_append_left
  apply List.mem_append_left
  apply List.mem_append_right
  exact List.mem_map.2 ⟨k, hk, rfl⟩

theorem mxLengthPrep_read_break (σ : State C Γ) (n : PrimTy.uint.Denote)
    (o : MObj σ.H (.array (.prim q))) (x : Var) (v : q.Denote) (ks : List PrimTy.uint.Denote)
    {k : PrimTy.uint.Denote} (hk : k ∈ ks) :
    k.1 ∈ mxRangeBreaks (σ.push (t := .val .uint) n) o (mxLengthPrep x v ks).points := by
  apply List.mem_cons_of_mem
  apply List.mem_cons_of_mem
  apply List.mem_filterMap.2
  refine ⟨mxLiteralPoint k, mxLengthPrep_read x v ks hk, ?_⟩
  rfl

def mxLengthEq : Fml C (.mem (.array (.prim q)) :: .val .uint :: Γ) :=
  .eq (MxOrig.len .here).tm (.pvV (.there .here))

theorem mxLengthEq_holds (σ : State C Γ) (n : PrimTy.uint.Denote)
    (o : MObj σ.H (.array (.prim q))) :
    holds ((σ.push (t := .val .uint) n).allocPush o) (mxLengthEq (q := q)) ↔
      mxFillN .dyn o = n := by
  change (MxOrig.len .here).tm.denote ((σ.push (t := .val .uint) n).allocPush o) = some n ↔ _
  have hl : (MxOrig.len .here).tm.denote ((σ.push (t := .val .uint) n).allocPush o) =
      some (mxFillN .dyn o) := by
    simpa only [MxObs.tm, MxObs.obs] using
      (MxObs.denote_alloc (σ.push (t := .val .uint) n) o (MxObs.len (q := q)))
  rw [hl]
  exact ⟨Option.some.inj, congrArg some⟩

def mxNegativeSource (s x : Var) (v : q.Denote) (a : MxExterior q) : Fml C Γ :=
  .allocAll s (.array (.prim q)) (.imp (.all x .uint (mxRangeBody .here v)) a.fml)

def mxNegativeBody (k : Nat) (s x : Var) (v : q.Denote) (a : MxExterior q) : Fml C Γ :=
  .all (.fresh "se" k) .uint (.allocAll s (.array (.prim q))
    (.imp mxLengthEq (.imp (mxLengthPrep x v a.reads).body a.fml)))

/-- Exactness is at every parent state, not just validity. The fresh
object remains in the same extended heap typing throughout reconstruction. -/
theorem mxNegativeBody_holds (k : Nat) (s x : Var) (v : q.Denote) (a : MxExterior q) (σ : State C Γ) :
    holds σ (mxNegativeBody k s x v a) ↔ holds σ (mxNegativeSource s x v a) := by
  change (∀ n : PrimTy.uint.Denote, ∀ o : MObj σ.H (.array (.prim q)),
      holds ((σ.push (t := .val .uint) n).allocPush o) mxLengthEq →
      holds ((σ.push (t := .val .uint) n).allocPush o) (mxLengthPrep x v a.reads).body →
      holds ((σ.push (t := .val .uint) n).allocPush o) a.fml) ↔
    (∀ o : MObj σ.H (.array (.prim q)),
      holds (σ.allocPush o) (.all x .uint (mxRangeBody .here v)) → holds (σ.allocPush o) a.fml)
  constructor
  · intro h o hb
    let n := mxFillN .dyn o
    have hb' : holds ((σ.push (t := .val .uint) n).allocPush o)
        (.all x .uint (mxRangeBody .here v)) :=
      (mxRangeBlock_holds (σ.push (t := .val .uint) n) o x v).2 ((mxRangeBlock_holds σ o x v).1 hb)
    have hp : holds ((σ.push (t := .val .uint) n).allocPush o) (mxLengthPrep x v a.reads).body :=
      (mxLengthPrep x v a.reads).sound ((σ.push (t := .val .uint) n).allocPush o) hb'
    have hg : holds ((σ.push (t := .val .uint) n).allocPush o) a.fml :=
      h n o ((mxLengthEq_holds σ n o).2 rfl) hp
    exact (a.holds_alloc σ o).2 ((a.holds_alloc (σ.push (t := .val .uint) n) o).1 hg)
  · intro h n o _ hp
    let p := mxLengthPrep (C := C) (Γ := Γ) x v a.reads
    let B := mxRangeBreaks (σ.push (t := .val .uint) n) o p.points
    let o' := mxFloorRebuild .dyn (by trivial) o B
    have hb' : holds ((σ.push (t := .val .uint) n).allocPush o')
        (.all x .uint (mxRangeBody .here v)) :=
      p.range_reconstruct_points (σ.push (t := .val .uint) n) o x v
        (mxLengthPrep_zero σ n o x v a.reads) hp
    have hb : holds (σ.allocPush o') (.all x .uint (mxRangeBody .here v)) :=
      (mxRangeBlock_holds σ o' x v).2 ((mxRangeBlock_holds (σ.push (t := .val .uint) n) o' x v).1 hb')
    have hg : holds (σ.allocPush o') a.fml := h o' hb
    apply (a.holds_alloc (σ.push (t := .val .uint) n) o).2
    apply (a.rebuild o B List.mem_cons_self
      (fun k hk => mxLengthPrep_read_break σ n o x v a.reads hk)).1
    exact (a.holds_alloc σ o').1 hg

/-- A whole-leaf proof-carrying result; unsupported syntax is unchanged. -/
structure MxNegativePrep (C : Contract) (Γ : Ctx) (φ : Fml C Γ) where
  body : Fml C Γ
  changed : Bool
  exact : ∀ σ : State C Γ, holds σ body ↔ holds σ φ

def MxNegativePrep.id (φ : Fml C Γ) : MxNegativePrep C Γ φ := ⟨φ, false, fun _ => Iff.rfl⟩

/-- A value-binder view retains its original intrinsic syntax equality. -/
structure MxAllView (φ : Fml C Γ) where
  x : Var
  p : PrimTy
  body : Fml C (.val p :: Γ)
  eq : φ = .all x p body

def mxAllView (φ : Fml C Γ) : Option (MxAllView φ) := by
  apply @Fml.casesOn C (fun Γ φ => Option (MxAllView φ)) Γ φ
  case all => exact fun x p b => some ⟨x, p, b, rfl⟩
  all_goals intros; exact none

private def mxNegativeAlloc (k : Nat) (s : Var) (R : RefTy) :
    (b : Fml C (.mem R :: Γ)) → MxNegativePrep C Γ (.allocAll s R b) :=
  match R with
  | .array (.prim q) => fun b =>
    let result : Option (MxNegativePrep C Γ (.allocAll s (.array (.prim q)) b)) := do
      let ⟨left, right, himp⟩ ← mxImpView b
      let ⟨x, p, body, hall⟩ ← mxAllView left
      if hp : p = .uint then
        let ⟨rq, array, value, hrange⟩ ← mxRangeBody? (hp ▸ body)
        if hq : rq = q then
          if hi : hq ▸ array = .here then
            let ⟨a, hg⟩ ← MxExterior.ofFml? right
            let v : q.Denote := hq ▸ value
            pure ⟨mxNegativeBody k s x v a, true, fun σ => by
              have hr : (hp ▸ body) = mxRangeBody array value := hrange
              cases hp
              cases hq
              simp only [hi] at hr
              rw [himp, hall, hr, hg]
              exact mxNegativeBody_holds k s x v a σ⟩
          else none
        else none
      else none
    result.getD (MxNegativePrep.id _)
  | _ => fun _ => MxNegativePrep.id _

/-- Only the supported fresh primitive range block is rewritten. The
literal-index exterior recognizer supplies the exact stable read footprint.
Positive prefix value binders are preserved capture-safely. -/
def mxNegativePrepareAt (k : Nat) {Γ : Ctx} (φ : Fml C Γ) : MxNegativePrep C Γ φ :=
  @Fml.casesOn C (fun Γ φ => MxNegativePrep C Γ φ) Γ φ
    (MxNegativePrep.id _) (fun _ _ => MxNegativePrep.id _) (fun _ => MxNegativePrep.id _)
    (fun _ => MxNegativePrep.id _) (fun _ _ => MxNegativePrep.id _)
    (fun _ _ => MxNegativePrep.id _) (fun _ _ _ => MxNegativePrep.id _)
    (fun _ _ _ _ => MxNegativePrep.id _) (fun _ => MxNegativePrep.id _)
    (fun x p b =>
      let r := mxNegativePrepareAt k b
      ⟨.all x p r.body, r.changed, fun σ => forall_congr' fun v => r.exact (σ.push (t := .val p) v)⟩)
    (fun _ _ _ _ => MxNegativePrep.id _) (fun _ _ => MxNegativePrep.id _)
    (fun s R b => mxNegativeAlloc k s R b) (fun _ => MxNegativePrep.id _)
  termination_by structural φ

/-- Explicit prefix equation; do not unfold the recursive recursor with `simp`. -/
theorem mxNegativePrepareAt_all (k : Nat) (x : Var) (p : PrimTy) (b : Fml C (.val p :: Γ)) :
    mxNegativePrepareAt k (.all x p b) =
      let r := mxNegativePrepareAt k b
      ⟨.all x p r.body, r.changed, fun σ => forall_congr' fun v => r.exact (σ.push (t := .val p) v)⟩ := rfl

theorem mxNegativePrepareAt_allocAll (k : Nat) (s : Var) (R : RefTy)
    (b : Fml C (.mem R :: Γ)) :
    mxNegativePrepareAt k (.allocAll s R b) = mxNegativeAlloc k s R b := rfl

/-- Reserve the length atom above every binder and named root of the whole
input before descending through its prefix. Existing intrinsic indices remain
capture-safe; the standard fresh supply also keeps printed binders distinct. -/
def mxNegativePrepare (φ : Fml C Γ) : MxNegativePrep C Γ φ :=
  mxNegativePrepareAt φ.fresh φ

#print axioms mxNegativeBody_holds
#print axioms mxNegativePrepare

end Solidity.Decide
