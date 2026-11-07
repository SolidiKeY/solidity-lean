import Solidity.Theory.Typed.Obs.Paths

/-!
Joint-input witnesses for the frozen typed-path and observation interfaces.
Every type/data/class input is packed together, including the quantified frame
premise. Concrete separated array indices demonstrate per-input feasibility;
an inhabited ObsLoc structure alone is not counted as that proof.
-/
namespace H62.AuditTheories
open Solidity

private abbrev B : Ty := .prim .bool

/-- All append_assoc inputs coexist at the bool identity path. -/
theorem path_append_assoc_joint_witness :
    ∃ (T U V W : Ty) (p : Path T U) (q : Path U V) (r : Path V W),
      (p.append q).append r = p.append (q.append r) :=
  ⟨B, B, B, B, .nil, .nil, .nil, Path.append_assoc .nil .nil .nil⟩

/-- All append_nil_right inputs coexist at an intrinsic bool path. -/
theorem path_append_nil_right_joint_witness :
    ∃ (T U : Ty) (p : Path T U), p.append .nil = p :=
  ⟨B, B, .nil, Path.append_nil_right .nil⟩

/-- All strip?_append inputs coexist, including the dependent continuation. -/
theorem path_strip_append_joint_witness :
    ∃ (T U W : Ty) (p : Path T U) (r : Path U W),
      Path.strip? p (p.append r) = some r :=
  ⟨B, B, B, .nil, .nil, Path.strip?_append .nil .nil⟩

/-- eq_of_strip? has a jointly satisfiable strip equation and typed inputs. -/
theorem path_eq_of_strip_joint_witness :
    ∃ (T U W : Ty) (p : Path T U) (q : Path T W) (r : Path U W),
      Path.strip? p q = some r ∧ q = p.append r :=
  ⟨B, B, B, .nil, .nil, .nil, rfl, Path.eq_of_strip? .nil .nil rfl⟩

/-- split_of_labels has matching labels and a real continuation at one input. -/
theorem path_split_of_labels_joint_witness :
    ∃ (T U W : Ty) (p : Path T U) (q : Path T W) (s : List Semantics.Selector),
      q.labels = p.labels ++ s ∧ ∃ r : Path U W, q = p.append r ∧ r.labels = s :=
  ⟨B, B, B, .nil, .nil, [], by simp only [Path.labels_nil, List.nil_append],
    .nil, (Path.append_nil .nil).symm, Path.labels_nil⟩

/-- strip?_none's premise holds for two distinct dynamic-array elements. -/
theorem path_strip_none_joint_witness :
    ∃ (T U W : Ty) (p : Path T U) (q : Path T W), Path.strip? p q = none :=
  ⟨.ref (.array B), B, B, .at (uintOfNat 0) .nil, .at (uintOfNat 1) .nil, rfl⟩

/-- All strip?_append_append inputs share compatible source/target types. -/
theorem path_strip_append_append_joint_witness :
    ∃ (T U V W : Ty) (p : Path T U) (q : Path U V) (r : Path U W),
      Path.strip? (p.append q) (p.append r) = Path.strip? q r :=
  ⟨B, B, B, B, .nil, .nil, .nil, Path.strip?_append_append .nil .nil .nil⟩

/-- app_path's typed path arguments coexist. -/
theorem obsloc_app_path_joint_witness :
    ∃ (T U W : Ty) (p : Path T U) (r : Path U W),
      (ObsLoc.app p r : Path T W) = p.append r :=
  ⟨B, B, B, .nil, .nil, rfl⟩

/-- strip?_path's typed path arguments coexist. -/
theorem obsloc_strip_path_joint_witness :
    ∃ (T U W : Ty) (p : Path T U) (q : Path T W),
      (ObsLoc.strip? p q : Option (Path U W)) = Path.strip? p q :=
  ⟨B, B, B, .nil, .nil, rfl⟩

/-- Total observations, used only after concrete input locations are chosen. -/
def auditObs (L : Ty → Type) : Obs L where
  word := fun {P} _ => PrimTy.dflt P
  len := fun _ => 0
  has := fun _ => true

/-- Obs.ext's three quantified hypotheses hold simultaneously for one pair. -/
theorem obs_ext_joint_witness :
    ∃ (L : Ty → Type) (o o' : Obs L),
      (∀ {P : PrimTy} (q : L (.prim P)), o.word q = o'.word q) ∧
      (∀ {E : Ty} (q : L (.ref (.array E))), o.len q = o'.len q) ∧
      (∀ {U : Ty} (q : L U), o.has q = o'.has q) :=
  ⟨Path B, auditObs _, auditObs _, (fun _ => rfl), (fun _ => rfl), (fun _ => rfl)⟩

/-- find_word includes its global location instance and actual primitive path. -/
theorem obs_find_word_joint_witness :
    ∃ (L : Ty → Type) (loc : ObsLoc L) (o : Obs L) (U : Ty) (p : L U)
      (P : PrimTy) (r : Path U (.prim P)),
      letI : ObsLoc L := loc
      (o.find p).word r = o.word (ObsLoc.app p r) :=
  ⟨Path B, inferInstance, auditObs _, B, .nil, .bool, .nil, rfl⟩

/-- find_len includes an actual dynamic-array location and its class instance. -/
theorem obs_find_len_joint_witness :
    ∃ (L : Ty → Type) (loc : ObsLoc L) (o : Obs L) (U : Ty) (p : L U)
      (E : Ty) (r : Path U (.ref (.array E))),
      letI : ObsLoc L := loc
      (o.find p).len r = o.len (ObsLoc.app p r) :=
  ⟨Path (.ref (.array B)), inferInstance, auditObs _, .ref (.array B), .nil, B, .nil, rfl⟩

/-- find_save_same jointly has a location, observation and replacement value. -/
theorem obs_find_save_same_joint_witness :
    ∃ (L : Ty → Type) (loc : ObsLoc L) (o : Obs L) (U : Ty) (p : L U) (v : TVal U),
      letI : ObsLoc L := loc
      (o.save p v).find p = v :=
  ⟨Path B, inferInstance, auditObs _, B, .nil, auditObs _, rfl⟩

/-- find_save_frame's entire quantified frame holds at separated array indices. -/
theorem obs_find_save_frame_joint_witness :
    ∃ (L : Ty → Type) (loc : ObsLoc L) (o : Obs L) (U W : Ty)
      (p : L U) (q : L W) (v : TVal U),
      letI : ObsLoc L := loc
      (∀ {V : Ty} (r : Path W V), ObsLoc.strip? p (ObsLoc.app q r) = none) ∧
      (o.save p v).find q = o.find q := by
  refine ⟨Path (.ref (.array B)), inferInstance, auditObs _, B, B,
    .at (uintOfNat 0) .nil, .at (uintOfNat 1) .nil, auditObs _, ?_, ?_⟩
  · intro V r
    change Path.strip? (Path.at (uintOfNat 0) (Path.nil (T := B)))
      ((Path.at (uintOfNat 1) (Path.nil (T := B))).append r) = none
    rw [Path.append_at, Path.append_nil]
    rfl
  · apply Obs.find_save_frame
    intro V r
    change Path.strip? (Path.at (uintOfNat 0) (Path.nil (T := B)))
      ((Path.at (uintOfNat 1) (Path.nil (T := B))).append r) = none
    rw [Path.append_at, Path.append_nil]
    rfl

/-- save_word_frame's class/data inputs and strip premise hold together. -/
theorem obs_save_word_frame_joint_witness :
    ∃ (L : Ty → Type) (loc : ObsLoc L) (o : Obs L) (U : Ty) (p : L U)
      (P : PrimTy) (q : L (.prim P)) (v : TVal U),
      letI : ObsLoc L := loc
      ObsLoc.strip? p q = none ∧ (o.save p v).word q = o.word q :=
  ⟨Path (.ref (.array B)), inferInstance, auditObs _, B, .at (uintOfNat 0) .nil,
    .bool, .at (uintOfNat 1) .nil, auditObs _, rfl, rfl⟩

/-- save_len_frame's length location and replacement value coexist with its frame. -/
theorem obs_save_len_frame_joint_witness :
    ∃ (L : Ty → Type) (loc : ObsLoc L) (o : Obs L) (U : Ty) (p : L U)
      (E : Ty) (q : L (.ref (.array E))) (v : TVal U),
      letI : ObsLoc L := loc
      ObsLoc.strip? p q = none ∧ (o.save p v).len q = o.len q :=
  ⟨Path (.ref (.array (.ref (.array B)))), inferInstance, auditObs _, .ref (.array B),
    .at (uintOfNat 0) .nil, B, .at (uintOfNat 1) .nil, auditObs _, rfl, rfl⟩

#print axioms path_append_assoc_joint_witness
#print axioms path_append_nil_right_joint_witness
#print axioms path_strip_append_joint_witness
#print axioms path_eq_of_strip_joint_witness
#print axioms path_split_of_labels_joint_witness
#print axioms path_strip_none_joint_witness
#print axioms path_strip_append_append_joint_witness
#print axioms obsloc_app_path_joint_witness
#print axioms obsloc_strip_path_joint_witness
#print axioms obs_ext_joint_witness
#print axioms obs_find_word_joint_witness
#print axioms obs_find_len_joint_witness
#print axioms obs_find_save_same_joint_witness
#print axioms obs_find_save_frame_joint_witness
#print axioms obs_save_word_frame_joint_witness
#print axioms obs_save_len_frame_joint_witness
end H62.AuditTheories
