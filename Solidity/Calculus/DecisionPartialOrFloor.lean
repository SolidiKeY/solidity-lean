import Solidity.Calculus.DecisionHaltingOrCertificate
import Solidity.Calculus.MemStructCut
import Solidity.Calculus.DecisionSourceDiscovery

/-!
# Deciding the nested partial-OR floor family

`PartialOrBlockAt sp value key result` is the claim
`(∀ uint i; ∀ uint j; ((i ≤ j && i < s - 1) || i ≤ i) == true → m[i] == value)
→ m[key] == result`, with `s` a uint root and `m` a `uint ⇒ uint` mapping root.
The checked subtraction halts exactly when `s = 0`, and `||` evaluates its left
operand first, so the guard is `true` exactly when `j < i` or `1 ≤ s`. The
antecedent therefore says `m[i] = value` for every `i ≥ 1`, and `m[0] = value`
only when `1 ≤ s`. Hence the claim is valid exactly when `0 < key` and
`result = value` (`PartialOrBlockAt.valid_positive`), and otherwise refuted at
one symbolic state: `s = 0`, `m` reads `value` at every key but zero, and a
word different from `result` at zero (`counterState`). The mapping is stored
as one entry over a default, so the countermodel is a region, not a list of
`2^256` keys.

The family is recognized from the formula alone: the roots range over the
contract's declared uint and `uint ⇒ uint` mapping roots, the literals over
the uint literals on the source skeleton (`sourceUIntChainLiterals`). No
coverage or verdict function is consulted. The general APF guard-floor
reconstruction for partial guards is not claimed.
-/
namespace Solidity.Decide.ResidueReason
open Semantics (lookupBy)

namespace PartialOrRoots
variable {C : Contract}

/-- The countermodel's mapping: `value` everywhere but key zero. -/
def counterMap (value result : PrimTy.uint.Denote) :
    SVal (.ref (.mapping .uint (.prim .uint))) :=
  .map (.cons (uintOfNat 0) (.prim (MemoryWitness.different .uint result)) .nil) (.prim value)

/-- The initial storage with the mapping root replaced; the scalar stays `0`. -/
def counterStorage (sp : PartialOrRoots C) (value result : PrimTy.uint.Denote) : Storage C :=
  SFields.set (Storage.init C) sp.mappingType (counterMap value result)

/-- The symbolic countermodel state. -/
def counterState (sp : PartialOrRoots C) (value result : PrimTy.uint.Denote) : State C [] :=
  (State.init C).withStorage (sp.counterStorage value result)

theorem roots_ne (sp : PartialOrRoots C) : sp.scalar ≠ sp.mapping := by
  intro h
  have h' := sp.scalarType
  rw [h, sp.mappingType] at h'
  cases h'

/-- The scalar root reads zero in the countermodel, in every context. -/
theorem scalarRead_counter (sp : PartialOrRoots C) {Γ : Ctx} (σ : State C Γ)
    (value result : PrimTy.uint.Denote) (hs : σ.storage = sp.counterStorage value result) :
    (sp.scalarRead (Γ := Γ)).eval σ = some (uintOfNat 0) := by
  simp only [scalarRead, Tm.eval_app2, Tm.eval_app0, Op0.eval_eq_evalM, Op0.evalM,
    Op2.eval_eq_evalM, Op2.evalM, Option.bind_eq_bind, Option.bind_some]
  change (σ.storage.find (SRef.ofRoot sp.scalar sp.scalarType)).bind (fun v => some v.view) = _
  rw [hs]
  simp only [Storage.find, SRef.ofRoot, counterStorage,
    SFields.get_set_ne _ sp.mappingType sp.scalarType (Ne.symm sp.roots_ne), Storage.init,
    SFields.dflt_get, SVal.find_eq_findM, SVal.findM]
  rfl

/-- The mapping root reads its region value in the countermodel. -/
theorem mapRead_counter (sp : PartialOrRoots C) {Γ : Ctx} (σ : State C Γ)
    (value result : PrimTy.uint.Denote) (hs : σ.storage = sp.counterStorage value result)
    (key : Tm C Γ (.val .uint)) (u : PrimTy.uint.Denote) (hk : key.eval σ = some u) :
    (sp.mapRead key).eval σ =
      some (if u = uintOfNat 0 then MemoryWitness.different .uint result else value) := by
  simp only [mapRead, Tm.eval_app2, Tm.eval_app0, Op0.eval_eq_evalM, Op0.evalM,
    Op2.eval_eq_evalM, Op2.evalM, hk, Option.bind_eq_bind, Option.bind_some,
    Storage.atT, CloseS.checkIndex_map_root]
  change (σ.storage.find ((SRef.ofRoot sp.mapping sp.mappingType :
    SRef C (.ref (.mapping .uint (.prim .uint)))).index .map u)).bind
      (fun v => some v.view) = _
  rw [hs]
  simp only [Storage.find, SRef.index, SRef.append, SRef.ofRoot, counterStorage,
    SFields.get_set_same, Path.index_map, counterMap, SVal.find_eq_findM]
  rw [Path.append_nil]
  simp only [SVal.findM, SMap.toList_cons, SMap.toList_nil]
  by_cases h : u = uintOfNat 0
  · simp only [lookupBy, h, if_true]
    rfl
  · simp only [lookupBy, h, if_false]
    rfl

/-- With a zero scalar, the guard is never `true` at first index zero. -/
theorem sourceGuard_zero (sp : PartialOrRoots C) (σ : State C [])
    (value result : PrimTy.uint.Denote) (hs : σ.storage = sp.counterStorage value result)
    (j : PrimTy.uint.Denote) :
    ¬ holds ((σ.push (t := .val .uint) (uintOfNat 0)).push (t := .val .uint) j)
      (.eq sp.sourceGuard (.app0 (.lit true))) := by
  intro h
  have hs0 : (sp.scalarRead (Γ := [.val .uint, .val .uint])).denote
      ((σ.push (t := .val .uint) (uintOfNat 0)).push (t := .val .uint) j) = some (uintOfNat 0) :=
    Tm.denote_eval _ _ _ (sp.scalarRead_counter _ value result hs)
  change ((some (decide ((uintOfNat 0).1 ≤ j.1))).bind (fun x => binopT (p := .bool) .and rfl x
      ((some (uintOfNat 0)).bind fun a => binopT (p := .uint) .lt rfl a
        ((sp.scalarRead.denote ((σ.push (t := .val .uint) (uintOfNat 0)).push (t := .val .uint) j)).bind
          fun b => binopT (p := .uint) .sub rfl b (some (uintOfNat 1)))))).bind
    (fun x => binopT (p := .bool) .or rfl x
      (some (decide ((uintOfNat 0).1 ≤ (uintOfNat 0).1)))) = some true at h
  rw [hs0] at h
  have hj : decide ((uintOfNat 0).val ≤ j.val) = true :=
    decide_eq_true (PrimTy.uint_nonneg j)
  rw [hj] at h
  exact absurd h (by decide)

/-- The countermodel satisfies the antecedent. -/
theorem sourceBlock_counter (sp : PartialOrRoots C) (first second : Var)
    (value result : PrimTy.uint.Denote) :
    holds (sp.counterState value result) (sp.sourceBlock first second value) := by
  intro i j hg
  by_cases hi : i = uintOfNat 0
  · subst hi
    exact absurd hg (sp.sourceGuard_zero _ value result rfl j)
  · apply (holds_eq_of_eval (x := value) (y := value) ?_ rfl).mpr rfl
    rw [sp.mapRead_counter _ value result rfl _ i rfl, if_neg hi]

/-- Outside the valid case, the countermodel refutes the claim. -/
theorem sourceClaim_counter_refutes (sp : PartialOrRoots C) (first second : Var)
    (value key result : PrimTy.uint.Denote) (h : ¬ (0 < key.1 ∧ result = value)) :
    ¬ holds (sp.counterState value result) (sp.sourceClaim first second value key result) := by
  intro hc
  have hb := hc (sp.sourceBlock_counter first second value result)
  have he := (holds_eq_of_eval (sp.mapRead_counter _ value result rfl _ key rfl) rfl).mp hb
  by_cases hk : key = uintOfNat 0
  · rw [if_pos hk] at he
    exact MemoryWitness.different_ne _ _ he
  · rw [if_neg hk] at he
    apply h
    refine ⟨?_, he.symm⟩
    have hn : 0 ≤ key.1 := PrimTy.uint_nonneg key
    have hne : key.1 ≠ 0 := fun h0 => hk (Subtype.ext h0)
    omega

end PartialOrRoots

variable {C : Contract}

/-- A recognized member, with its roots and literals. -/
structure PartialOrFloor (φ : Fml C []) where
  sp : PartialOrRoots C
  value : PrimTy.uint.Denote
  key : PrimTy.uint.Denote
  result : PrimTy.uint.Denote
  block : PartialOrBlockAt sp value key result φ

/-- The declared roots of one type, with their typing proofs. -/
def rootsOfType (C : Contract) (T : Ty) : List {n : Name // C.rootType n = some T} :=
  C.vars.filterMap fun fT => if h : C.rootType fT.1 = some T then some ⟨fT.1, h⟩ else none

/-- The candidate root pairs, from the contract's declarations. -/
def partialOrRootsOf (C : Contract) : List (PartialOrRoots C) :=
  (rootsOfType C (.prim .uint)).flatMap fun s =>
    (rootsOfType C (.ref (.mapping .uint (.prim .uint)))).map fun m => ⟨s.1, m.1, s.2, m.2⟩

/-- Constant-work constructor checks before any candidate enumeration:
`(∀ uint; ∀ uint; _ → _) → _`. -/
def partialOrShape (φ : Fml C []) : Bool :=
  match sourceImpView? φ with
  | none => false
  | some outer => match sourceUIntAllView? outer.lhs with
    | none => false
    | some first => match sourceUIntAllView? first.body with
      | none => false
      | some second => (sourceImpView? second.body).isSome

/-- Search the declared roots and the skeleton's uint literals. -/
def partialOrFloor? (φ : Fml C []) : Option (PartialOrFloor φ) :=
  if !partialOrShape φ then none else
  let lits := sourceUIntChainLiterals φ
  (partialOrRootsOf C).findSome? fun sp =>
    lits.findSome? fun value => lits.findSome? fun key => lits.findSome? fun result =>
      (partialOrBlockAt? sp value key result φ).map fun w => ⟨sp, value, key, result, w⟩

/-- Decidable source classification, independent of target, coverage and verdict. -/
def _root_.Solidity.Fml.partialOrFloor (φ : Fml C []) : Bool := (partialOrFloor? φ).isSome

/-- The exact answer: proved on the valid literals, else the symbolic countermodel. -/
def PartialOrFloor.answer {φ : Fml C []} (w : PartialOrFloor φ) : MemoryWitness.Answer φ :=
  if h : 0 < w.key.1 ∧ w.result = w.value then
    .proved (by
      have b : PartialOrBlockAt w.sp w.value w.key w.value φ := h.2 ▸ w.block
      exact b.valid_positive h.1)
  else
    .refuted (fun _ => w.sp.counterState w.value w.result) (fun _ hh =>
      w.sp.sourceClaim_counter_refutes _ _ _ _ _ h (Eq.mp (congrArg (fun ψ => holds (w.sp.counterState w.value w.result) ψ)
        w.block.equation) hh))

/-- The answer for a recognized member. -/
def partialOrFloorAnswer? (φ : Fml C []) : Option (MemoryWitness.Answer φ) :=
  (partialOrFloor? φ).map PartialOrFloor.answer

theorem rootsOfType_mem {T : Ty} {n : Name} (h : C.rootType n = some T) :
    (⟨n, h⟩ : {n : Name // C.rootType n = some T}) ∈ rootsOfType C T := by
  unfold rootsOfType
  apply List.mem_filterMap.mpr
  exact ⟨(n, T), Semantics.lookupBy_eq_some_mem h, by simp only [dif_pos h]⟩

theorem partialOrRootsOf_mem (sp : PartialOrRoots C) : sp ∈ partialOrRootsOf C := by
  unfold partialOrRootsOf
  apply List.mem_flatMap.mpr
  refine ⟨⟨sp.scalar, sp.scalarType⟩, rootsOfType_mem sp.scalarType, ?_⟩
  apply List.mem_map.mpr
  exact ⟨⟨sp.mapping, sp.mappingType⟩, rootsOfType_mem sp.mappingType, rfl⟩

theorem sourceClaim_literals (sp : PartialOrRoots C) (i j : Var)
    (value key result : PrimTy.uint.Denote) :
    value ∈ sourceUIntChainLiterals (sp.sourceClaim i j value key result) ∧
    key ∈ sourceUIntChainLiterals (sp.sourceClaim i j value key result) ∧
    result ∈ sourceUIntChainLiterals (sp.sourceClaim i j value key result) := by
  refine ⟨?_, ?_, ?_⟩
  · change value ∈ (_ ++ (_ ++ [value])) ++ _
    exact List.mem_append_left _ (List.mem_append_right _ (List.mem_append_right _
      (List.mem_singleton_self value)))
  · change key ∈ _ ++ ((_ ++ (_ ++ [key])) ++ _)
    exact List.mem_append_right _ (List.mem_append_left _ (List.mem_append_right _
      (List.mem_append_right _ (List.mem_singleton_self key))))
  · change result ∈ _ ++ (_ ++ [result])
    exact List.mem_append_right _ (List.mem_append_right _ (List.mem_singleton_self result))

/-- **Completeness of recognition**: every member of the family is found. -/
theorem partialOrFloor_complete {sp : PartialOrRoots C} {value key result : PrimTy.uint.Denote}
    {φ : Fml C []} (w : PartialOrBlockAt sp value key result φ) : φ.partialOrFloor = true := by
  have hl := sourceClaim_literals sp w.first w.second value key result
  rw [← w.equation] at hl
  have hs : partialOrShape φ = true := by
    rw [w.equation]
    rfl
  unfold Fml.partialOrFloor partialOrFloor?
  simp only [hs, Bool.not_true, Bool.false_eq_true, if_false, List.findSome?_isSome_iff,
    Option.isSome_map]
  exact ⟨sp, partialOrRootsOf_mem sp, value, hl.1, key, hl.2.1, result, hl.2.2,
    partialOrBlockAt_complete w⟩

/-- Every recognition carries an actual member witness. -/
theorem partialOrFloor_witness {φ : Fml C []} (h : φ.partialOrFloor = true) :
    Nonempty (PartialOrFloor φ) := by
  unfold Fml.partialOrFloor at h
  cases he : partialOrFloor? φ with
  | none => rw [he] at h; cases h
  | some w => exact ⟨w⟩

/-- Exact classification of the family. -/
theorem partialOrFloor_iff {φ : Fml C []} :
    φ.partialOrFloor = true ↔ Nonempty (PartialOrFloor φ) :=
  ⟨partialOrFloor_witness, fun ⟨w⟩ => partialOrFloor_complete w.block⟩

/-- The exact semantic verdict of every member. -/
theorem PartialOrFloor.valid_iff {φ : Fml C []} (w : PartialOrFloor φ) :
    Fml.Valid φ ↔ (0 < w.key.1 ∧ w.result = w.value) := by
  constructor
  · intro hv
    by_cases h : 0 < w.key.1 ∧ w.result = w.value
    · exact h
    · exact absurd (Eq.mp (congrArg (fun ψ => holds (w.sp.counterState w.value w.result) ψ)
        w.block.equation) (hv _))
        (w.sp.sourceClaim_counter_refutes w.block.first w.block.second _ _ _ h)
  · intro h
    have b : PartialOrBlockAt w.sp w.value w.key w.value φ := h.2 ▸ w.block
    exact b.valid_positive h.1

theorem partialOrFloorAnswer_isSome {φ : Fml C []} (h : φ.partialOrFloor = true) :
    (partialOrFloorAnswer? φ).isSome = true := by
  unfold partialOrFloorAnswer?
  simpa only [Option.isSome_map] using h

end Solidity.Decide.ResidueReason
