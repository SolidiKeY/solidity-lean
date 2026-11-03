import Solidity.Backend.StorageOps.CopyReadCapture

/-! One-word projection of an existing generated query write trace. This is
not a source evaluator, value/state layer or replacement operation algorithm.
The numeric correspondence retains explicit finite symbolic alias separation;
independent recursive output correspondence is a further obligation. -/
namespace Solidity.Backend.StorageOps.CopyReadback
open TypeGraph Solidity.Storage Solidity.Storage.Representation Solidity.Storage.Representation.Graph

/-- Read one query's last write, or its old word if the trace never writes it.
Only a scalar projection of the EXISTING annotated write list is accumulated. -/
noncomputable def traceWord {n : Nat} {G : Schema n} {T : TypeGraph.Ty n}
    (q : Query G T) (log : List (Query G T × Semantics.Word))
    (initial : Semantics.Word) : Semantics.Word := by
  classical
  exact log.foldl (fun word op => if op.1 = q then op.2 else word) initial

theorem traceWord_append {n : Nat} {G : Schema n} {T : TypeGraph.Ty n}
    (q : Query G T) (first second : List (Query G T × Semantics.Word)) (initial : Semantics.Word) :
    traceWord q (first ++ second) initial = traceWord q second (traceWord q first initial) := by
  classical
  exact List.foldl_append

theorem traceWord_outside {n : Nat} {G : Schema n} {T : TypeGraph.Ty n}
    (q : Query G T) (log : List (Query G T × Semantics.Word)) (initial : Semantics.Word)
    (outside : ∀ op ∈ log, op.1 ≠ q) : traceWord q log initial = initial := by
  classical
  induction log generalizing initial with
  | nil => rfl
  | cons op rest ih =>
    simp only [traceWord,List.foldl_cons,if_neg (outside op List.mem_cons_self)]
    exact ih initial (fun later member => outside later (List.mem_cons_of_mem _ member))

/-- Scalar readback of actual numeric fold-write execution. The match premise
is about finite addresses/query identities, never desired output preservation. -/
theorem numeric_trace {n N : Nat} {G : Schema n} {T : TypeGraph.Ty n}
    (q : Query G T) (log : List (Query G T × Semantics.Word))
    (dst : Solidity.Storage.Loc) (hash : Solidity.Storage.Pre → Nat) (initial : WordStore)
    (addressMatch : ∀ op ∈ log,
      (op.1.location dst).word N hash = (q.location dst).word N hash ↔ op.1 = q) :
    ((log.map (fun op => (op.1.location dst,op.2))).foldl
      (fun w op => writeWord w (op.1.word N hash) op.2) initial)
      ((q.location dst).word N hash) = traceWord q log (initial ((q.location dst).word N hash)) := by
  classical
  induction log generalizing initial with
  | nil => rfl
  | cons op rest ih =>
    simp only [List.map_cons,List.foldl_cons]
    rw [ih _ (fun later member => addressMatch later (List.mem_cons_of_mem _ member))]
    change traceWord q rest (writeWord initial ((op.1.location dst).word N hash) op.2
      ((q.location dst).word N hash)) =
      traceWord q rest (if op.1 = q then op.2 else initial ((q.location dst).word N hash))
    apply congrArg (traceWord q rest)
    by_cases same : op.1 = q
    · simp only [same,writeWord,ite_true]
    · have different : (q.location dst).word N hash ≠ (op.1.location dst).word N hash := by
        intro equal
        exact same ((addressMatch op List.mem_cons_self).mp equal.symm)
      simp only [writeWord,if_neg different,if_neg same]

/-- The actual recursive numeric copy admits this exact trace readback under
its GENERATED demand coverage and finite symbolic query separation. No global
hash injectivity or full graph representation is silently assumed. -/
theorem copy_trace {n N L R : Nat} {G : Schema n} {T : TypeGraph.Ty n}
    (old src : Value G T) (q : Query G T) (dst source : Solidity.Storage.Loc)
    (initial : WordStore) {hash : Solidity.Storage.Pre → Nat} {P : List Solidity.Storage.Pre}
    {locations : List Solidity.Storage.Loc} (run : FiniteRun N L R hash P locations)
    (queryCovered : q.location dst ∈ locations)
    (writesCovered : ∀ d ∈ CopyDemands.demands old src, d.location dst ∈ locations)
    (separate : ∀ d ∈ CopyDemands.demands old src, d.location dst = q.location dst → d = q) :
    CopyWrites.numericCopy (N := N) old src dst source hash initial ((q.location dst).word N hash) =
      traceWord q (CopyWrites.queryWrites old src (fun d => initial ((d.location source).word N hash)))
        (initial ((q.location dst).word N hash)) := by
  apply numeric_trace
  intro op inside
  have generated : op.1 ∈ CopyDemands.demands old src := by
    rw [← CopyWrites.query_sequence old src (fun d => initial ((d.location source).word N hash))]
    exact List.mem_map.mpr ⟨op,inside,rfl⟩
  constructor
  · intro equal
    exact separate op.1 generated (run.word_inj (writesCovered _ generated) queryCovered equal)
  · intro equal
    rw [equal]

private theorem zeros_preserve {n : Nat} {G : Schema n} {T : TypeGraph.Ty n}
    (q : Query G T) (queries : List (Query G T)) :
    traceWord q (CopyWrites.zeros queries) ClearDemands.zero = ClearDemands.zero := by
  classical
  induction queries with
  | nil => rfl
  | cons first rest ih =>
    change traceWord q (CopyWrites.zeros rest)
      (if first = q then ClearDemands.zero else ClearDemands.zero) = _
    rw [ite_self]
    exact ih

/-- Every generated zero observation is actually zero after the full trace,
including duplicates and later zero writes to the same query. -/
theorem zero_member {n : Nat} {G : Schema n} {T : TypeGraph.Ty n}
    (q : Query G T) (queries : List (Query G T)) (initial : Semantics.Word)
    (member : q ∈ queries) : traceWord q (CopyWrites.zeros queries) initial = ClearDemands.zero := by
  classical
  induction queries generalizing initial with
  | nil => cases member
  | cons first rest ih =>
    change traceWord q (CopyWrites.zeros rest)
      (if first = q then ClearDemands.zero else initial) = _
    rcases List.mem_cons.mp member with same | later
    · subst first
      rw [if_pos rfl]
      exact zeros_preserve q rest
    · exact ih _ later

/-- Fresh initialization realizes every successful independent DEFAULT read,
regardless of the former numeric garbage. Completeness is from the checked
original copy permit, not a post-preservation premise. -/
theorem default_readback {n : Nat} {G : Schema n} {T : TypeGraph.Ty n}
    (permit : CopyPermit G T) (q : Query G T) (initial word : Semantics.Word)
    (observed : q.read (Value.dflt T) = some word) :
    traceWord q (CopyWrites.zeros (CopyDefaults.demands G T)) initial = word := by
  have member := CopyDefaults.complete G T permit q word observed
  have zero := CopyDefaults.listed_zero G T q member
  have same : ClearDemands.zero = word := Option.some.inj (zero.symm.trans observed)
  rw [← same]
  exact zero_member q _ initial member

/-- The ACTUAL fresh-present slot trace initializes defaults BEFORE copy.
For every successful default observation, the former cell word is irrelevant;
the remaining proof is independent present-value copy readback. -/
theorem fresh_slot {n : Nat} {G : Schema n} {T : TypeGraph.Ty n}
    (src : Value G T) (permit : CopyPermit G T) (q : Query G T)
    (reader : Query G T → Semantics.Word) (initial word : Semantics.Word)
    (observed : q.read (Value.dflt T) = some word) :
    traceWord q (CopyWrites.slotWrites .absent (.present src) reader) initial =
      traceWord q (CopyWrites.queryWrites (Value.dflt T) src reader) word := by
  change traceWord q (CopyWrites.zeros (CopyDefaults.demands G T) ++
    CopyWrites.queryWrites (Value.dflt T) src reader) initial = _
  rw [traceWord_append,default_readback permit q initial word observed]

/-- PUBLIC SOURCE representation and OLD numeric transport supply independent
source INPUT words for the actual trace readback. This still does not assert
that this scalar trace equals the independent copied OUTPUT observation. -/
theorem represented_copy_trace {n N L R : Nat} {G : Schema n} {T : TypeGraph.Ty n}
    (old src : Value G T) (q : Query G T) (dst source : Solidity.Storage.Loc)
    (store : Store) (initial : WordStore)
    {hash : Solidity.Storage.Pre → Nat} {P : List Solidity.Storage.Pre}
    {locations : List Solidity.Storage.Loc} (run : FiniteRun N L R hash P locations)
    (beforeSrc : Represented src (ClearDemands.demands src) source store)
    (before : Transport N hash locations store initial)
    (sourceCovered : ∀ d ∈ ClearDemands.demands src, d.location source ∈ locations)
    (queryCovered : q.location dst ∈ locations)
    (writesCovered : ∀ d ∈ CopyDemands.demands old src, d.location dst ∈ locations)
    (separate : ∀ d ∈ CopyDemands.demands old src, d.location dst = q.location dst → d = q) :
    CopyWrites.numericCopy (N := N) old src dst source hash initial ((q.location dst).word N hash) =
      traceWord q (CopyWrites.queryWrites old src (fun d => (d.read src).getD ClearDemands.zero))
        (initial ((q.location dst).word N hash)) := by
  rw [copy_trace old src q dst source initial run queryCovered writesCovered separate]
  rw [CopyReadCapture.reader_congr old src _ _
    (CopyReadCapture.represented_reads src source store initial hash locations beforeSrc before sourceCovered)]

/-- Existing typed query prefixing is injective, at arbitrary finite depth.
This is a syntactic typed operation law, not numeric layout injectivity. -/
theorem prefix_injective {n : Nat} {G : Schema n} {A B : TypeGraph.Ty n}
    (path : TypeGraph.Path G A B) (a b : Query G B)
    (same : a.prefix path = b.prefix path) : a = b := by
  induction path with
  | nil => cases a <;> cases b <;> exact same
  | cons step rest ih =>
    apply ih
    cases a with
    | word ap =>
      cases b with
      | word bp =>
        change Query.word (.cons step (rest.append ap)) = Query.word (.cons step (rest.append bp)) at same
        injection same with hp hpath
        subst hp
        have eqpath := eq_of_heq hpath
        injection eqpath with hA hB hC hstep hrest
        exact congrArg Query.word hrest
      | length bp => cases same
    | length ap =>
      cases b with
      | word bp => cases same
      | length bp =>
        change Query.length (.cons step (rest.append ap)) = Query.length (.cons step (rest.append bp)) at same
        injection same with hE hpath
        subst hE
        have eqpath := eq_of_heq hpath
        injection eqpath with hA hB hC hstep hrest
        exact congrArg Query.length hrest

/-- Readback factors through any finite typed common prefix using actual
prefixWrites, with no numeric/layout injectivity assumption. -/
theorem prefix_trace {n : Nat} {G : Schema n} {A B : TypeGraph.Ty n}
    (path : TypeGraph.Path G A B) (q : Query G B)
    (log : List (Query G B × Semantics.Word)) (initial : Semantics.Word) :
    traceWord (q.prefix path) (CopyWrites.prefixWrites path log) initial = traceWord q log initial := by
  classical
  induction log generalizing initial with
  | nil => rfl
  | cons op rest ih =>
    change traceWord (q.prefix path) (CopyWrites.prefixWrites path rest)
      (if op.1.prefix path = q.prefix path then op.2 else initial) =
      traceWord q rest (if op.1 = q then op.2 else initial)
    rw [ih]
    have same : op.1.prefix path = q.prefix path ↔ op.1 = q :=
      ⟨prefix_injective path op.1 q,congrArg (Query.prefix path)⟩
    simp only [same]

private noncomputable def stepNumber {n : Nat} {G : Schema n} {A B : TypeGraph.Ty n}
    (step : Step G A B) : Nat :=
  @Step.rec n G (fun _ _ _ => Nat)
    (fun position => position.toNat) (fun index => index.val)
    (fun index => index.val) (fun _ => 0) A B step
private noncomputable def pathFirst {n : Nat} {G : Schema n} {A B : TypeGraph.Ty n}
    (path : TypeGraph.Path G A B) : Option Nat :=
  @TypeGraph.Path.rec n G (fun _ _ _ => Option Nat) (fun {_} => none)
    (fun step _ _ => some (stepNumber step)) A B path
private noncomputable def queryFirst {n : Nat} {G : Schema n} {A : TypeGraph.Ty n} : Query G A → Option Nat
  | .word path => pathFirst path
  | .length path => pathFirst path
private theorem first_prefix {n : Nat} {G : Schema n} {A B : TypeGraph.Ty n}
    (step : Step G A B) (q : Query G B) :
    queryFirst (q.prefix (.cons step .nil)) = some (stepNumber step) := by
  cases q <;> rfl

/-- Distinct field positions or array/fixed indices give distinct prefixed
queries, even when endpoint types differ. This is typed syntax only. -/
private theorem distinct_steps {n : Nat} {G : Schema n} {A B C : TypeGraph.Ty n}
    (left : Step G A B) (right : Step G A C)
    (different : stepNumber left ≠ stepNumber right) (a : Query G B) (b : Query G C) :
    a.prefix (.cons left .nil) ≠ b.prefix (.cons right .nil) := by
  intro same
  have first := congrArg queryFirst same
  rw [first_prefix,first_prefix] at first
  exact different (Option.some.inj first)

/-- All actual writes below a numerically different typed selector leave this
query's scalar trace projection untouched. No address disjointness is inferred. -/
private theorem sibling_trace {n : Nat} {G : Schema n} {A B C : TypeGraph.Ty n}
    (left : Step G A B) (right : Step G A C)
    (different : stepNumber left ≠ stepNumber right)
    (q : Query G B) (log : List (Query G C × Semantics.Word)) (initial : Semantics.Word) :
    traceWord (q.prefix (.cons left .nil))
      (CopyWrites.prefixWrites (.cons right .nil) log) initial = initial := by
  apply traceWord_outside
  intro op member
  obtain ⟨child,inside,same⟩ := List.mem_map.mp member
  subst op
  exact distinct_steps right left different.symm child.1 q

theorem fields_trace {n : Nat} {G : Schema n} {i : Fin n} {B C : TypeGraph.Ty n}
    (left : Field (G.fields i) B) (right : Field (G.fields i) C)
    (different : left.toNat ≠ right.toNat)
    (q : Query G B) (log : List (Query G C × Semantics.Word)) (initial : Semantics.Word) :
    traceWord (q.prefix (.cons (.field left) .nil))
      (CopyWrites.prefixWrites (.cons (.field right) .nil) log) initial = initial :=
  sibling_trace (.field left) (.field right) different q log initial

theorem indices_trace {n : Nat} {G : Schema n} {E : TypeGraph.Ty n}
    (left right : Index) (different : left.val ≠ right.val)
    (q : Query G E) (log : List (Query G E × Semantics.Word)) (initial : Semantics.Word) :
    traceWord (q.prefix (.cons (.index left) .nil))
      (CopyWrites.prefixWrites (.cons (.index right) .nil) log) initial = initial :=
  sibling_trace (.index left) (.index right) different q log initial

theorem fixed_trace {n : Nat} {G : Schema n} {E : TypeGraph.Ty n} {m : FixedSize}
    (left right : Index) (different : left.val ≠ right.val)
    (q : Query G E) (log : List (Query G E × Semantics.Word)) (initial : Semantics.Word) :
    traceWord (q.prefix (.cons (.fixed (m := m) left) .nil))
      (CopyWrites.prefixWrites (.cons (.fixed right) .nil) log) initial = initial :=
  sibling_trace (.fixed left) (.fixed right) different q log initial

/-- info: 'Solidity.Backend.StorageOps.CopyReadback.traceWord' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms traceWord
/-- info: 'Solidity.Backend.StorageOps.CopyReadback.traceWord_append' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms traceWord_append
/-- info: 'Solidity.Backend.StorageOps.CopyReadback.traceWord_outside' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms traceWord_outside
/-- info: 'Solidity.Backend.StorageOps.CopyReadback.numeric_trace' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms numeric_trace
/-- info: 'Solidity.Backend.StorageOps.CopyReadback.copy_trace' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms copy_trace
/-- info: 'Solidity.Backend.StorageOps.CopyReadback.zero_member' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms zero_member
/-- info: 'Solidity.Backend.StorageOps.CopyReadback.default_readback' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms default_readback
/-- info: 'Solidity.Backend.StorageOps.CopyReadback.fresh_slot' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms fresh_slot
/-- info: 'Solidity.Backend.StorageOps.CopyReadback.represented_copy_trace' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in #print axioms represented_copy_trace
/-- info: 'Solidity.Backend.StorageOps.CopyReadback.prefix_injective' does not depend on any axioms -/
#guard_msgs in #print axioms prefix_injective
/-- info: 'Solidity.Backend.StorageOps.CopyReadback.prefix_trace' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms prefix_trace
/-- info: 'Solidity.Backend.StorageOps.CopyReadback.fields_trace' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms fields_trace
/-- info: 'Solidity.Backend.StorageOps.CopyReadback.indices_trace' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms indices_trace
/-- info: 'Solidity.Backend.StorageOps.CopyReadback.fixed_trace' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms fixed_trace

end Solidity.Backend.StorageOps.CopyReadback
