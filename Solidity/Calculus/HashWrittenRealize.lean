import Solidity.Calculus.HashWrittenInput

/-! # Realized certificates for written-memory hash equalities
The syntax certificate accepts two actual fresh uint arrays followed by
one write of byte 1 at index 0 and an equality of their hashes. Names,
modality and non-recovery hash kind are parameters. Other syntax is refused.
This adds no assumption about collisions and does not implement the general
negative-array lane.
-/
namespace Solidity.Decide.WrittenMemory.Realize
open Solidity.Decide.WrittenMemory
variable {C : Contract}
abbrev UA : RefTy := .array (.prim .uint)
abbrev Γst : Ctx := [.mem UA, .mem UA]
def num {Γ : Ctx} (n : Nat) : Tm C Γ (.val .uint) := .app0 (.lit (uintOfNat n))
def writeTerm : Tm C Γst .mem := .app3 .write (.app0 .memory)
  (.app2 (.mat .dyn) (.pvI (.there .here)) (num 0)) (.app1 .mval (num 1))
def writeFirst : Upd C Γst Γst := .snoc .nil (.memory writeTerm)
def schema (x y : Var) (k : HashKind) (m : Modality) : Fml C [] :=
  .allocAll x UA (.allocAll y UA (.upd m writeFirst
    (.eq (hnode k (.there .here)) (hnode k .here))))
/-- Actual fresh states used to realize the original pin, not sampled reads. -/
private def originalS : State C [.mem UA] :=
  let σ := State.init C
  let a := σ.alloc (famObj σ.H 1)
  a.1.push (t := .mem UA) (some a.2)
private def originalST : State C Γst :=
  let a := originalS.alloc (famObj originalS.H 2)
  a.1.push (t := .mem UA) (some a.2)

/-- Writing the existing byte is a genuine successful landing. -/
private theorem original_landing : writeFirst.Lands (originalST (C := C)) originalST.globG originalST := by
  refine ⟨?_, rfl, ?_⟩
  · simp only [writeFirst, writeTerm, num, Upd.globT_eq_globTM, Upd.globTM, Option.bind_some,
      UpdElem.globT_eq_globTM, UpdElem.globTM, Tm.eval_eq_evalM, Tm.evalM,
      Op0.eval, Op1.eval, Op2.eval, Op3.eval]
    change ((Grown.writeT originalST.glob.memT (.index 0 .dyn (uintOfNat 0) : MAddrT (.prim .uint))
      (uintOfNat 1)).bind fun μ => some (originalST.globG.withMem μ)) = some originalST.globG
    dsimp [Grown.writeT, MAddrT.resolve, HRef.ofId?, MvT.toMVal, Heap.writeAddr, Heap.setIndex]
    simp only [show originalST.glob.memT.H'[0]? = some UA from rfl, ↓reduceDIte,
      Option.map_some, Option.bind_some, MObj.elems_dyn, MObj.setElem_dyn]
    simp only [show (uintOfNat 0).val.toNat = 0 from by decide +kernel,
      show (originalST.glob.memT.heap.get (⟨0, rfl⟩ : HRef originalST.H UA)).val.length = 1 from rfl,
      Nat.zero_lt_succ, ↓reduceIte, Option.bind_some]
    rfl
  · intro t i
    rfl

/-- Both freshly allocated objects belong to the existing checked family. -/
private theorem original_family : FamHeap famBound (originalST (C := C)).glob := by
  have hs : FamHeap famBound originalS.glob :=
    FamHeap.alloc (σ := State.init C)
      (FamHeap.empty famBound (State.init C).glob rfl) (j := 1) (by decide)
  intro R r
  exact FamHeap.alloc (σ := originalS) hs (j := 2) (by decide) r

/-- Actual family hashes establish the landing's finite premise for each kind. -/
private theorem original_pair_free (k : HashKind) (hk : k ≠ .ecrecover) :
    (Fml.eq (hnode k (.there .here)) (hnode k .here)).HashFree (originalST (C := C)) :=
  Fml.hashFree_fam
    (show (Fml.eq (hnode k (.there .here)) (hnode k .here) : Fml C Γst).sw k =
      some (.eq (.pvV (.there .here)) (.pvV .here)) from by cases k <;> rfl)
    originalST original_family (famOK_bound k hk)

/-- A realized input counterexample for the entire written-equality schema. -/
private theorem original_body_refutes (k : HashKind) (hk : k ≠ .ecrecover) (m : Modality) :
    ¬ Fml.holdsH (originalST (C := C)) (.upd m writeFirst
      (.eq (hnode k (.there .here)) (hnode k .here))) := by
  apply refutes_update_input k hk (.there .here) .here (a := 0) (b := 1)
  · intro kind inp out h
    simp only [writeFirst, writeTerm, num, Upd.HashIn, UpdElem.HashIn, Tm.HashIn, Op2.HashIn, or_self] at h
  · exact original_landing
  · exact original_pair_free k hk
  · rfl
  · rfl
  · change some [1] ≠ some [2]
    decide +kernel

/-- The schema's counterexample supplies every binder's own finite premise. -/
theorem schema_refutes (x y : Var) (k : HashKind) (hk : k ≠ .ecrecover) (m : Modality) :
    ¬ Fml.holdsH (State.init C) (schema x y k m) := by
  let rt : AllocCounterexample (originalS (C := C)) UA
      (.upd m writeFirst (.eq (hnode k (.there .here)) (hnode k .here))) :=
    ⟨famObj originalS.H 2, original_body_refutes k hk m⟩
  let rs : AllocCounterexample (State.init C) UA
      (.allocAll y UA (.upd m writeFirst (.eq (hnode k (.there .here)) (hnode k .here)))) :=
    ⟨famObj [] 1, rt.refutes_alloc y⟩
  exact rs.refutes_alloc x

/-- Extract only an exactly checked written-equality body. Tactic `cases`
elaborates to intrinsic recursors; no indexed-family match or untyped syntax
is introduced. Term comparisons use the existing certified `Tm.beqR`. -/
def body? (k : HashKind) (φ : Fml C Γst) :
    Option {m : Modality // φ = .upd m writeFirst
      (.eq (hnode k (.there .here)) (hnode k .here))} := by
  cases φ with
  | upd m U ψ =>
    cases U with
    | snoc U e =>
      cases U with
      | nil =>
        cases e with
        | memory t =>
          by_cases ht : t.beqR (writeTerm (C := C)) = true
          · have et : t = writeTerm := Tm.eq_of_beqR ht
            subst t
            cases ψ with
            | @eq _ p a b =>
              by_cases ha : a.beqR (hnode k (.there .here)) = true
              · have ea : Srt.val p = Srt.val .uint ∧ HEq a (hnode k (.there .here)) :=
                  Sigma.mk.inj (Tm.sigma_eq_of_beqR ha)
                have ep : Srt.val p = Srt.val .uint := ea.1
                cases ep
                have ea' : a = hnode k (.there .here) := eq_of_heq ea.2
                subst a
                by_cases hb : b.beqR (hnode k .here) = true
                · have eb : b = hnode k .here := Tm.eq_of_beqR hb
                  subst b
                  exact some ⟨m, rfl⟩
                · exact none
              · exact none
            | _ => exact none
          · exact none
        | _ => exact none
      | _ => exact none
    | _ => exact none
  | _ => exact none

/-- Extract the two fresh-array scopes and their exact body certificate.
Binder names are retained; a mismatched type, update, term or scope is refused. -/
def extract? (k : HashKind) (φ : Fml C []) :
    Option {p : Var × Var × Modality // φ = schema p.1 p.2.1 k p.2.2} := by
  cases φ with
  | allocAll x R ψ =>
    by_cases hR : R = UA
    · subst R
      cases ψ with
      | allocAll y S θ =>
        by_cases hS : S = UA
        · subst S
          cases body? k θ with
          | none => exact none
          | some r => exact some ⟨(x, y, r.val), congrArg
              (fun b => Fml.allocAll x UA (.allocAll y UA b)) r.property⟩
        · exact none
      | _ => exact none
    · exact none
  | _ => exact none

/-- A syntax certificate produces a kernel-certified actual countermodel. -/
def refutationK? (k : HashKind) (hk : k ≠ .ecrecover) (φ : Fml C []) :
    Option (PLift (¬ Fml.holdsH (State.init C) φ)) :=
  (extract? k φ).map fun (r : {p : Var × Var × Modality // φ = schema p.1 p.2.1 k p.2.2}) =>
    ⟨by rw [r.property]; exact schema_refutes r.val.1 r.val.2.1 k hk r.val.2.2⟩

/-- Try exactly the three existing non-recovery kinds. -/
def refutation? (φ : Fml C []) : Option (PLift (¬ Fml.holdsH (State.init C) φ)) :=
  (refutationK? .keccak (by decide) φ).orElse fun _ =>
    (refutationK? .sha256 (by decide) φ).orElse fun _ =>
      refutationK? .ripemd160 (by decide) φ

/-- info: 'Solidity.Decide.WrittenMemory.Realize.schema_refutes' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms schema_refutes
/-- info: 'Solidity.Decide.WrittenMemory.Realize.refutation?' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms refutation?



end Solidity.Decide.WrittenMemory.Realize
