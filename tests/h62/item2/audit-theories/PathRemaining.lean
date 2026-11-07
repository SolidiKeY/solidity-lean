import tests.h62.item2.«audit-theories».PathWitnesses

/-!
Remaining joint inputs for every explicit theorem in Typed/Obs/Paths.
Storage packets use actual declared StandardExample roots. Observations are
abstract Obs inputs, not an assertion of storage realizability. The array
packet includes a successful write at a live slot, not only a length proof.
-/
namespace H62.AuditTheories
open Solidity
private abbrev PB : Ty := .prim .bool
private abbrev PU : Ty := .prim .uint

/-- Both field lookup premises hold for Person.age. -/
theorem path_lookup_joint_witness :
    ∃ (s f : Name) (T T' : Ty),
      Semantics.lookupBy f (Semantics.structDef s) = some T ∧
      Semantics.lookupBy f (Semantics.structDef s) = some T' :=
  ⟨"Person", "age", PU, PU, rfl, rfl⟩

/-- The global class and all nested-read data coexist. -/
theorem obs_find_find_joint_witness :
    ∃ (L : Ty → Type) (loc : ObsLoc L) (o : Obs L) (U V : Ty)
      (p : L U) (q : Path U V), letI : ObsLoc L := loc
      (o.find p).find q = o.find (ObsLoc.app p q) :=
  ⟨Path PB, inferInstance, auditObs _, PB, PB, .nil, .nil, Obs.find_find _ _ _⟩

/-- The identity read has a real location. -/
theorem obs_find_nil_joint_witness :
    ∃ (L : Ty → Type) (loc : ObsLoc L) (o : Obs L) (U : Ty) (p : L U),
      letI : ObsLoc L := loc
      (o.find p).find .nil = o.find p :=
  ⟨Path PB, inferInstance, auditObs _, PB, .nil, Obs.find_nil _ _⟩

/-- Saving a read has jointly inhabited global and local inputs. -/
theorem obs_save_find_joint_witness :
    ∃ (L : Ty → Type) (loc : ObsLoc L) (o : Obs L) (U : Ty) (p : L U),
      letI : ObsLoc L := loc
      o.save p (o.find p) = o :=
  ⟨Path PB, inferInstance, auditObs _, PB, .nil, Obs.save_find _ _⟩

/-- A primitive continuation and replacement coexist with the observation. -/
theorem obs_save_word_below_joint_witness :
    ∃ (L : Ty → Type) (loc : ObsLoc L) (o : Obs L) (U : Ty) (p : L U)
      (P : PrimTy) (r : Path U (.prim P)) (v : TVal U),
      letI : ObsLoc L := loc
      (o.save p v).word (ObsLoc.app p r) = v.word r :=
  ⟨Path PB, inferInstance, auditObs _, PB, .nil, .bool, .nil, auditObs _,
    Obs.save_word_below _ _ _ _⟩

/-- The primitive location is inhabited together with the replacement. -/
theorem obs_save_word_same_joint_witness :
    ∃ (L : Ty → Type) (loc : ObsLoc L) (o : Obs L) (P : PrimTy)
      (p : L (.prim P)) (v : TVal (.prim P)), letI : ObsLoc L := loc
      (o.save p v).word p = v.word .nil :=
  ⟨Path PB, inferInstance, auditObs _, .bool, .nil, auditObs _, Obs.save_word_same _ _ _⟩

/-- Read-below-write has all typed arguments, not an empty location family. -/
theorem obs_find_save_below_joint_witness :
    ∃ (L : Ty → Type) (loc : ObsLoc L) (o : Obs L) (U V : Ty)
      (q : L U) (r : Path U V) (v : TVal V), letI : ObsLoc L := loc
      (o.save (ObsLoc.app q r) v).find q = (o.find q).save r v :=
  ⟨Path PB, inferInstance, auditObs _, PB, PB, .nil, .nil, auditObs _,
    Obs.find_save_below _ _ _ _⟩

/-- A live uint storage root. -/
def auditTotal : SRef StandardExample PU := ⟨"total", rfl, .nil⟩
/-- A distinct live root for the root-separation premise. -/
def auditAge : SRef StandardExample PU := ⟨"age", rfl, .nil⟩

/-- Equal-root references and their type indices coexist. -/
theorem sref_ty_eq_joint_witness :
    ∃ (C : Contract) (U W : Ty) (r : SRef C U) (q : SRef C W), r.root = q.root :=
  ⟨StandardExample, PU, PU, auditTotal, auditTotal, rfl⟩

/-- A real root can be extended. -/
theorem sref_strip_append_joint_witness :
    ∃ (C : Contract) (U W : Ty) (r : SRef C U) (p : Path U W),
      r.strip? (r.append p) = some p :=
  ⟨StandardExample, PU, PU, auditTotal, .nil, SRef.strip?_append _ _⟩

/-- The strip equality is feasible together with both references. -/
theorem sref_eq_of_strip_joint_witness :
    ∃ (C : Contract) (U W : Ty) (r : SRef C U) (q : SRef C W) (p : Path U W),
      r.strip? q = some p := by
  refine ⟨StandardExample, PU, PU, auditTotal, auditTotal.append .nil, .nil, ?_⟩
  exact SRef.strip?_append _ _

/-- All composition inputs coexist at a declared root. -/
theorem sref_append_append_joint_witness :
    ∃ (C : Contract) (U V W : Ty) (r : SRef C U) (p : Path U V) (q : Path V W),
      (r.append p).append q = r.append (p.append q) :=
  ⟨StandardExample, PU, PU, PU, auditTotal, .nil, .nil, SRef.append_append _ _ _⟩

/-- The identity composition has an inhabited root. -/
theorem sref_append_nil_joint_witness :
    ∃ (C : Contract) (U : Ty) (r : SRef C U), r.append .nil = r :=
  ⟨StandardExample, PU, auditTotal, SRef.append_nil _⟩

/-- Both extended references share an actual compatible prefix. -/
theorem sref_strip_append_append_joint_witness :
    ∃ (C : Contract) (U V W : Ty) (r : SRef C U) (p : Path U V) (q : Path U W),
      (r.append p).strip? (r.append q) = Path.strip? p q :=
  ⟨StandardExample, PU, PU, PU, auditTotal, .nil, .nil, SRef.strip?_append_append _ _ _⟩

/-- The separation premise holds for two declared, distinct roots. -/
theorem sref_root_ne_joint_witness :
    ∃ (C : Contract) (U W : Ty) (r : SRef C U) (q : SRef C W),
      r.root ≠ q.root ∧ r.strip? q = none :=
  ⟨StandardExample, PU, PU, auditTotal, auditAge, by decide,
    SRef.strip?_root_ne _ _ (by decide)⟩

/-- A location from an actual root has the extension input. -/
theorem sloc_strip_app_joint_witness :
    ∃ (C : Contract) (U W : Ty) (p : SLoc C U) (r : Path U W),
      SLoc.strip? p (SLoc.app p r) = some r :=
  ⟨StandardExample, PU, PU, .ref auditTotal, .nil, SLoc.strip?_app _ _⟩

/-- Strip equality is jointly feasible for live locations. -/
theorem sloc_eq_of_strip_joint_witness :
    ∃ (C : Contract) (U W : Ty) (p : SLoc C U) (q : SLoc C W) (r : Path U W),
      SLoc.strip? p q = some r :=
  ⟨StandardExample, PU, PU, .ref auditTotal, SLoc.app (.ref auditTotal) .nil, .nil,
    SLoc.strip?_app _ _⟩

/-- Location composition has all intermediate types and paths. -/
theorem sloc_app_app_joint_witness :
    ∃ (C : Contract) (U V W : Ty) (p : SLoc C U) (q : Path U V) (r : Path V W),
      SLoc.app (SLoc.app p q) r = SLoc.app p (q.append r) :=
  ⟨StandardExample, PU, PU, PU, .ref auditTotal, .nil, .nil, SLoc.app_app _ _ _⟩

/-- The location identity input is live. -/
theorem sloc_app_nil_joint_witness :
    ∃ (C : Contract) (U : Ty) (p : SLoc C U), SLoc.app p .nil = p :=
  ⟨StandardExample, PU, .ref auditTotal, SLoc.app_nil _⟩

/-- Both extended locations coexist with a live prefix. -/
theorem sloc_strip_app_app_joint_witness :
    ∃ (C : Contract) (U V W : Ty) (p : SLoc C U) (q : Path U V) (r : Path U W),
      SLoc.strip? (SLoc.app p q) (SLoc.app p r) = Path.strip? q r :=
  ⟨StandardExample, PU, PU, PU, .ref auditTotal, .nil, .nil, SLoc.strip?_app_app _ _ _⟩

/-- The generic location instance applies to an actual reference. -/
theorem sloc_app_ref_joint_witness :
    ∃ (C : Contract) (U W : Ty) (r : SRef C U) (q : Path U W),
      (ObsLoc.app (SLoc.ref r) q : SLoc C W) = .ref (r.append q) :=
  ⟨StandardExample, PU, PU, auditTotal, .nil, SLoc.app_ref _ _⟩

/-- Value and composed-read paths coexist. -/
theorem sval_findM_append_joint_witness :
    ∃ (T U W : Ty) (x : SVal T) (p : Path T U) (r : Path U W),
      x.findM (p.append r) = (x.findM p).bind (·.findM r) :=
  ⟨PB, PB, PB, .prim false, .nil, .nil, SVal.findM_append _ _ _⟩

/-- Value, both save paths and replacement coexist. -/
theorem sval_saveM_append_eq_joint_witness :
    ∃ (T U W : Ty) (x : SVal T) (p : Path T U) (r : Path U W) (v : SVal W),
      x.saveM (p.append r) v =
        (x.findM p).bind fun y => (y.saveM r v).bind fun y' => x.saveM p y' :=
  ⟨PB, PB, PB, .prim false, .nil, .nil, .prim true, SVal.saveM_append_eq _ _ _ _⟩

/-- Successful find and a concrete replacement coexist; save also succeeds. -/
theorem sval_saveM_of_findM_joint_witness :
    ∃ (T U : Ty) (x : SVal T) (p : Path T U) (y v : SVal U),
      x.findM p = some y ∧ ∃ x', x.saveM p v = some x' :=
  ⟨PB, PB, .prim false, .nil, .prim false, .prim true, rfl, .prim true, rfl⟩

/-- The composed-save success premise holds with all correlated data. -/
theorem sval_saveM_append_joint_witness :
    ∃ (T U W : Ty) (x : SVal T) (p : Path T U) (r : Path U W)
      (v : SVal W) (x' : SVal T), x.saveM (p.append r) v = some x' := by
  refine ⟨PB, PB, PB, .prim false, .nil, .nil, .prim true, .prim true, ?_⟩
  rw [Path.append_nil]
  rfl

/-- A live one-element array admits the indexed save; all length-side inputs
    coexist with the actual successful update. -/
theorem sval_saveM_at_n_joint_witness :
    ∃ (E W : Ty) (y y' : SVal (.ref (.array E))) (i : PrimTy.uint.Denote)
      (r : Path E W) (v : SVal W), y.saveM (.at i r) v = some y' := by
  refine ⟨PB, PB, .array (.cons (.prim false) .nil) .nil (by decide),
    .array (.cons (.prim true) .nil) .nil (by decide), uintOfNat 0, .nil, .prim true, ?_⟩
  simp only [SVal.saveM, SVec.toList_cons, SVec.toList_nil, SList.toList_nil]
  rfl

#print axioms path_lookup_joint_witness
#print axioms obs_find_find_joint_witness
#print axioms obs_find_nil_joint_witness
#print axioms obs_save_find_joint_witness
#print axioms obs_save_word_below_joint_witness
#print axioms obs_save_word_same_joint_witness
#print axioms obs_find_save_below_joint_witness
#print axioms sref_ty_eq_joint_witness
#print axioms sref_strip_append_joint_witness
#print axioms sref_eq_of_strip_joint_witness
#print axioms sref_append_append_joint_witness
#print axioms sref_append_nil_joint_witness
#print axioms sref_strip_append_append_joint_witness
#print axioms sref_root_ne_joint_witness
#print axioms sloc_strip_app_joint_witness
#print axioms sloc_eq_of_strip_joint_witness
#print axioms sloc_app_app_joint_witness
#print axioms sloc_app_nil_joint_witness
#print axioms sloc_strip_app_app_joint_witness
#print axioms sloc_app_ref_joint_witness
#print axioms sval_findM_append_joint_witness
#print axioms sval_saveM_append_eq_joint_witness
#print axioms sval_saveM_of_findM_joint_witness
#print axioms sval_saveM_append_joint_witness
#print axioms sval_saveM_at_n_joint_witness
end H62.AuditTheories
