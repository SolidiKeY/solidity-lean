import Solidity.Calculus.ReadQuery

/-!
# Occurrence-indexed values for dependent read queries

An arithmetic solver assigns values to finitely many read occurrences.
Those values determine later mapping keys, so their actual locations are
known only after replay. Replay retains every selected location/value pair;
its alias consistency is exactly the condition for actual storage to
realize the trace. No mapping keys or primitive domains are enumerated.
-/

namespace Solidity.ReadRealization

variable {C : Contract} {α : Type}

/-- Each read occurrence is numbered, and its value retains its type. -/
abbrev ReadValues := Nat → (p : PrimTy) → p.Denote

/-- Decode a finite list at each occurrence's actual type. Missing or
mismatched entries choose a typed default, never an untyped runtime value. -/
def ReadValues.ofList (xs : List Semantics.CallValue) : ReadValues :=
  fun i p => (xs[i]?.bind (Semantics.CallValue.as? p)).getD (PrimTy.dflt p)

/-- A finite typed assignment supplies occurrence values. A mismatched
type or an index outside the finite prefix uses that type's default. -/
def Assignment.values : Assignment C → ReadValues
  | [], _, p => PrimTy.dflt p
  | ⟨r, v⟩ :: _, 0, p => if h : r.prim = p then h ▸ v else PrimTy.dflt p
  | _ :: a, i + 1, p => Assignment.values a i p

namespace Query

/-- Replay a typed value for each selected read, recording the actual
locations selected by earlier values. The starting index permits composition. -/
def replay (values : ReadValues) : Nat → Query C α → α × Assignment C
  | _, .pure x => (x, [])
  | i, .read r k =>
    let v := values i r.prim
    let tail := replay values (i + 1) (k v)
    (tail.1, ⟨r, v⟩ :: tail.2)

/-- Record an actual valuation's occurrence trace, including repeated
locations. This does not merge aliases or change later location selection. -/
def record (rd : (r : Ref C) → r.Value) : Query C α → α × Assignment C
  | .pure x => (x, [])
  | .read r k => let tail := record rd (k (rd r)); (tail.1, ⟨r, rd r⟩ :: tail.2)

/-- Composed queries share one occurrence stream. The continuation starts
after exactly the reads actually selected by its argument query. -/
theorem replay_bind {β : Type} (q : Query C α) (f : α → Query C β)
    (values : ReadValues) (start : Nat) :
    replay values start (q.bind f) =
      let first := replay values start q
      let next := replay values (start + first.2.length) (f first.1)
      (next.1, first.2 ++ next.2) := by
  induction q generalizing start with
  | pure x => simp only [bind, replay, List.length_nil, Nat.add_zero, List.nil_append]
  | read r k ih =>
    simp only [bind, replay, ih, List.length_cons, List.cons_append]
    rw [Nat.add_right_comm start 1, Nat.add_assoc]

/-- A source-derived bound on selected occurrences, for every value choice. -/
def Within (q : Query C α) (n : Nat) : Prop :=
  ∀ values start, (replay values start q).2.length ≤ n

theorem within_pure (x : α) (n : Nat) : Within (.pure (C := C) x) n :=
  fun _ _ => Nat.zero_le n

theorem within_mono {q : Query C α} {n m : Nat} (h : q.Within n) (hn : n ≤ m) : q.Within m :=
  fun values start => Nat.le_trans (h values start) hn

theorem within_read (r : Ref C) (k : r.Value → Query C α) (n : Nat)
    (h : ∀ v, (k v).Within n) : Within (.read r k) (n + 1) :=
  fun values start => Nat.succ_le_succ (h (values start r.prim) values (start + 1))

theorem within_bind {β : Type} (q : Query C α) (f : α → Query C β) {n m : Nat}
    (hq : q.Within n) (hf : ∀ x, (f x).Within m) : (q.bind f).Within (n + m) := by
  intro values start
  rw [replay_bind]
  simp only [List.length_append]
  exact Nat.add_le_add (hq values start) (hf (replay values start q).1 values _)

/-- Index offsets can be moved into the occurrence-value stream. -/
theorem replay_shift (q : Query C α) (values : ReadValues) (offset start : Nat) :
    replay (fun i p => values (offset + i) p) start q = replay values (offset + start) q := by
  induction q generalizing start with
  | pure x => rfl
  | read r k ih =>
    simp only [replay, ih, Nat.add_assoc]

/-- Dropping an occurrence is the same as advancing its stream index. -/
theorem replay_cons_values (q : Query C α) (entry : (r : Ref C) × r.Value)
    (a : Assignment C) (start : Nat) :
    replay (Assignment.values (entry :: a)) (start + 1) q = replay a.values start q := by
  induction q generalizing start with
  | pure x => rfl
  | read r k ih =>
    simp only [replay, Assignment.values, ih]

/-- Reading back an actual occurrence list selects the same values and
locations, even when later locations depend on earlier reads. -/
theorem replay_record (q : Query C α) (rd : (r : Ref C) → r.Value) :
    replay (record rd q).2.values 0 q = record rd q := by
  induction q with
  | pure x => rfl
  | read r k ih =>
    simp only [record, replay, Assignment.values, ↓reduceDIte, replay_cons_values, ih]

/-- Recording does not change the query result. -/
theorem record_value (q : Query C α) (rd : (r : Ref C) → r.Value) :
    (record rd q).1 = q.run rd := by
  induction q with
  | pure x => rfl
  | read r k ih => exact ih (rd r)

/-- Every recorded occurrence receives the actual valuation's value. -/
theorem record_read (q : Query C α) (rd : (r : Ref C) → r.Value) :
    ∀ entry ∈ (record rd q).2, rd entry.1 = entry.2 := by
  induction q with
  | pure x => intro entry h; cases h
  | read r k ih =>
    intro entry h
    rcases List.mem_cons.mp h with he | ht
    · cases he; rfl
    · exact ih (rd r) entry ht

/-- Actual valuations always yield alias-consistent occurrence traces. -/
theorem record_consistent (q : Query C α) (rd : (r : Ref C) → r.Value) :
    (record rd q).2.Consistent :=
  fun r v w hv hw => (q.record_read rd ⟨r, v⟩ hv).symm.trans (q.record_read rd ⟨r, w⟩ hw)

/-- Agreement with every selected occurrence preserves the whole query. -/
theorem replay_correct (q : Query C α) (values : ReadValues) (start : Nat) (st : Storage C)
    (h : ∀ (r : Ref C) (v : r.Value), ⟨r, v⟩ ∈ (replay values start q).2 → r.read st = v) :
    q.runStorage st = (replay values start q).1 := by
  induction q generalizing start with
  | pure x => rfl
  | read r k ih =>
    change (k (r.read st)).runStorage st = (replay values (start + 1) (k (values start r.prim))).1
    rw [h r (values start r.prim) List.mem_cons_self]
    exact ih (values start r.prim) (start + 1) (fun q v hm => h q v (List.mem_cons_of_mem _ hm))

/-- A materialized consistent assignment recovers every occurrence value. -/
theorem _root_.Solidity.ReadRealization.Assignment.read_realize {a : Assignment C}
    (hc : a.Consistent) {r : Ref C} {v : r.Value} (hm : ⟨r, v⟩ ∈ a) :
    r.read a.realize = v :=
  (ReadRealization.realize_read (Assignment.lookup a) (a.map Sigma.fst) r
    (List.mem_map.mpr ⟨⟨r, v⟩, hm, rfl⟩)).trans (Assignment.lookup_of_mem hc hm)

/-- Replay's alias gate is sufficient even when a selected value determines
a later location. The materialized storage follows exactly the same trace. -/
theorem replay_realize (q : Query C α) (values : ReadValues) (start : Nat)
    (hc : (replay values start q).2.Consistent) :
    q.runStorage (replay values start q).2.realize = (replay values start q).1 :=
  q.replay_correct values start _ (fun _ _ hm => Assignment.read_realize hc hm)

/-- Consistency is also necessary: actual storage cannot assign conflicting
values to two occurrences that select the same typed location. -/
theorem replay_realizable_iff (q : Query C α) (values : ReadValues) (start : Nat) :
    (replay values start q).2.Consistent ↔ ∃ st : Storage C,
      q.runStorage st = (replay values start q).1 ∧
      ∀ (r : Ref C) (v : r.Value), ⟨r, v⟩ ∈ (replay values start q).2 → r.read st = v := by
  constructor
  · intro hc
    exact ⟨_, q.replay_realize values start hc, fun _ _ hm => Assignment.read_realize hc hm⟩
  · rintro ⟨st, _, h⟩ r v w hv hw
    exact (h r v hv).symm.trans (h r w hw)

/-- Every actual execution has a finite, consistent occurrence assignment
that replay follows exactly. No concrete counterexample is lost. -/
theorem replay_storage_exists (q : Query C α) (st : Storage C) :
    ∃ a : Assignment C, (replay a.values 0 q).1 = q.runStorage st ∧
      (replay a.values 0 q).2.Consistent := by
  let rd : (r : Ref C) → r.Value := fun r => r.read st
  have hr := q.replay_record rd
  exact ⟨(record rd q).2, (congrArg Prod.fst hr).trans (q.record_value rd),
    by rw [hr]; exact q.record_consistent rd⟩

/-- The finite witness fits a proved source bound as well as preserving
every selected location and the result. -/
theorem replay_storage_exists_bounded (q : Query C α) (st : Storage C) {n : Nat}
    (hq : q.Within n) : ∃ a : Assignment C, a.length ≤ n ∧
      (replay a.values 0 q).1 = q.runStorage st ∧ (replay a.values 0 q).2.Consistent := by
  let rd : (r : Ref C) → r.Value := fun r => r.read st
  have hr := q.replay_record rd
  refine ⟨(record rd q).2, ?_, (congrArg Prod.fst hr).trans (q.record_value rd), ?_⟩
  · simpa only [hr] using hq (record rd q).2.values 0
  · rw [hr]
    exact q.record_consistent rd

/-- Exact validity over occurrence values with the alias gate retained. -/
theorem all_storage_iff_traces (q : Query C Bool) :
    (∀ st : Storage C, q.runStorage st = true) ↔
      ∀ values : ReadValues, (replay values 0 q).2.Consistent → (replay values 0 q).1 = true := by
  constructor
  · intro h values hc
    exact (q.replay_realize values 0 hc).symm.trans (h _)
  · intro h st
    obtain ⟨a, ha, hc⟩ := q.replay_storage_exists st
    exact ha.symm.trans (h a.values hc)

/-- Materialize a false occurrence trace only after its aliases agree. -/
def countermodelFromTrace? (q : Query C Bool) (values : ReadValues) (start : Nat := 0) :
    Option { st : Storage C // q.runStorage st = false } :=
  let trace := replay values start q
  if hc : trace.2.consistentB = true then
    if hf : trace.1 = false then
      some ⟨trace.2.realize,
        (q.replay_realize values start ((Assignment.consistentB_iff _).mp hc)).trans hf⟩
    else none
  else none

end Query

end Solidity.ReadRealization
