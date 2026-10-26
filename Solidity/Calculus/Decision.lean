import Solidity.Calculus.AutoComplete
import Solidity.Calculus.QuantTotality
import Solidity.Calculus.LedgerReduction
import Solidity.Calculus.LedgerBlock
import Solidity.Calculus.HashKinds
import Solidity.Calculus.ArrayReduction
import Solidity.Calculus.MemSwap

/-!
# The closer's decision, stated (M7)

The theorem the closer is held to (`docs/automation.md`, M7): on a scoped
leaf `Fml C []` it terminates with a proof (`LeafVerdict.proved`) or a
certified counterexample (`LeafVerdict.refuted σ`, a typed state that
refutes the leaf), and it may answer `unknown` only where the user allowed
it (`docs/automation.md`, M6, decisions c, c′, d and their extensions):

* a product of two non-literal terms (KeY `int` or a 256-bit type), `x ** e`
  at a literal `e ≥ 2` and `mulmod` of two symbolic factors among them;
* `/`, `%`, `**`, `<<`, `>>`, `&`, `|`, `^` with two symbolic operands, a
  symbolic divisor (`c / x`), exponent or shift amount counted as such
  (`Waivers`: each class a field, all waived by the user's answer);
* a quantified formula over array or mapping contents outside the array
  property fragment (Bradley, Manna and Sipma), negative-position
  `havoc`/`anon`/`allocAll`/`grow` and storage binders among them;
* a verdict that turns on an `ecrecover` value (an `opaque` function) or
  on a hash preimage (e3′, 2026-10-25).

Hashes are read as e3′ has it: each goal under the premise that its own
hash terms are free of collisions (`Fml.HashFree`, `Fml.holdsH`,
`Fml.ValidH`), no axiom and no global assumption; the premise is taken
per scope, each binder's instance under its own.  In the fragment a hash
term stands where that premise settles it: against a hash of its kind
(`==`, `!=`), or as the key of a mapping at a root whose keys are all
hashes (`Fml.inTarget`); `ecrecover` stands nowhere, and neither does a
hash under a hidden memory binder or an anonymising update (an unset
reference hashes to nothing, a key of nothing reads the default key `0`:
a preimage question) or a hash key of anything but a memory local in the
starting memory.

A leaf with hashes (`decideHash`, plan step 7) is decided where its memory
locals are fresh byte strings read only by hashes of one kind: read with
each string the word its hash returns (`Fml.swPrefix`,
`Calculus/HashSwap.lean`), valid whatever the hash where the body's value
binders are positive (`Fml.swPrefix_validH`, `Fml.posAll`); refuted by
choosing the strings, a class of equal strings at a time, from a family
whose hashes are distinct (`Fml.swInst`, `Fml.swInst_refutes`,
`Calculus/HashReduction.lean`; `famN` strings, the kernel's theorem up to
`famBound`, computed past it, `famCheck`), which meets the premise.  A
string hashed by two kinds stands for one word per kind (`decideHash2`,
`Calculus/HashKinds.lean`): the second kind's words binders of their own,
linked to the first's by the premise, the result read by the one-kind
swap.  `decideHash` answers on `Fml.hashCovered`
(`decideGoal_complete_hash`, through `Fml.swPrefix_complete` and
`Fml.tk_complete`, the relabeling of `Calculus/HashRelabel.lean`); for one
kind the reduction is moreover exact on its fragment (`Fml.swPrefix_exact`,
`Calculus/HashComplete.lean`: keyed roots `mapping(uint => uint)`, the
swapped leaf in `Fml.rl`, the prefix's string levels the words', at most
`N` strings with the family of `N` checked, positive binders).

The fragment is `Fml.inTarget`, the statement `DecisionTheorem`, both
about the one decision function `decideGoal` (`decideLeaf` on a leaf
without a hash, `decideHash` on one with).  The statement is the goal of the rounds to come, not true
today: `Examples/Decision.lean` pins a leaf of the fragment answered
`unknown` for each shape left (`gapArrayBlock` … `gapHashNegForall`,
`docs/automation.md`, M7).  A statement of the form "some decider is complete" would
be vacuous: a classical function deciding validity by `Classical.choice`
exists, so the statement is about this computable function, which later
rounds extend.

What is proved: `decideLeaf` is sound (`decideLeaf_sound`), its refutations
are refutations (`decideLeaf_refutes`), and it answers on `Fml.Covered`
(`decideLeaf_complete`), the fragment M4 proves total
(`dependentReduction?_isSome`) as extended since, or the leaves every
quantifier of which past the prefix is Presburger once the body is
prepared (`Fml.quantCovered`, `quantReduction?_isSome`, decided by
`QFml.decide_iff`): `bool` quantifiers expanded and positive ones dropped
to fresh atoms (`expandPrep_valid_iff`), negative array-property blocks
over roots, keyed by `uint` or `int`, instantiated at the index set (`apfPrep`, sound by
`LFml.apfInst_sound` and exact by `ApfFml.apfInst_refute` wherever it
instantiates; `apfPrep_valid_iff` is `Prep.valid_iff`, which every
preparation has), reads at no bound variable hoisted out
(`hoistPrep_valid_iff`); or the leaves that read the starting ledger
(`Fml.ledgerCovered`), with blocks over it instantiated likewise
(`Fml.ledgerBlockCovered`, `ledgerBlockReduction?_isSome`), or storage arrays at symbolic indices
(`Fml.arrayCovered`, `arrayReduction?_isSome`); `decideGoal` likewise
under the hash premise (`decideGoal_sound`, `decideGoal_refutes`,
`decideGoal_complete` on covered leaves without a hash,
`decideGoal_complete_hash` on `Fml.hashCovered`).  `Fml.Covered`
also holds of formulas with programs, which `Fml.inTarget` (on leaves)
excludes; on program-free leaves the inclusion `Fml.Covered ⊆
Fml.inTarget` is not proved (`Fml.Covered` is read on the eliminated leaf,
`Fml.inTarget` on the source).

The array-property check is syntactic and conservative: an update or a
program under a quantifier counts as reading at its variable, the body of a
negative-position block must be quantifier-free, and an index guard is an
`&&`/`||` of comparisons (never `!=`, never a strict one of two bound
variables) of index terms, a bound variable or a term mentioning none; a
path indexes at most one bound variable (no `m[i][j]` with both bound, as
Bradley, Manna and Sipma state their result for one dimension); a hash
stored by an update, a hash key of a nested mapping or of anything but a
memory local in the starting memory, a hash under a hidden memory binder
or an anonymising update,
and an `ecrecover` term are outside.  So
`Fml.inTarget` is a subset of the fragment the user named, with one known
exception: a hash under a negative-position value quantifier whose hash
pairs the scope above does not read (`gapHashNegForall`), where the leaf
can be false only at a collision, which no refutation can exhibit;
excluding it narrows `Fml.inTarget`, which needs the user's approval.
-/

namespace Solidity.Decide

open Linear

variable {C : Contract}

/-! ## Verdicts and the decision -/

/-- What the closer answers on a leaf. -/
inductive LeafVerdict (C : Contract) where
  /-- The leaf is valid. -/
  | proved
  /-- The typed state refutes the leaf. -/
  | refuted (σ : State C [])
  /-- Neither: allowed only outside the fragment. -/
  | unknown

/-- **The pipelines**: the automatic pipeline (`dependentReduction?`), its
arithmetic decided by the verified procedure (`AFml.decide_iff`), a `false`
answer turned into a typed countermodel (`DependentReduction.verify`); on a
leaf it refuses, the quantified pipeline (`quantReduction?`), decided by
the verified projection procedure (`QFml.decide_iff`, `QuantReduction.verify`);
on a leaf both refuse, the pipeline with storage array reads
(`arrayReduction?`, `ArrayReduction.verify`); then the one with ledger reads
(`ledgerReduction?`, `LedgerReduction.verify`); then the one with blocks
over the ledger (`ledgerBlockReduction?`, `LedgerBlockReduction.verify`). -/
def decideLeafA (φ : Fml C []) : LeafVerdict C :=
  match dependentReduction? φ with
  | some r =>
    match r.verify with
    | .inl _ => .proved
    | .inr cm => .refuted cm.state
  | none =>
    match quantReduction? φ with
    | some q =>
      match q.verify with
      | .inl _ => .proved
      | .inr cm => .refuted cm.1
    | none =>
      match arrayReduction? φ with
      | some q =>
        match q.verify with
        | .inl _ => .proved
        | .inr cm => .refuted cm.state
      | none =>
        match ledgerReduction? φ with
        | some q =>
          match q.verify with
          | .inl _ => .proved
          | .inr cm => .refuted cm.state
        | none =>
          match ledgerBlockReduction? φ with
          | some q =>
            match q.verify with
            | .inl _ => .proved
            | .inr cm => .refuted cm.1
          | none => .unknown

/-- **Soundness.** -/
theorem decideLeafA_sound {φ : Fml C []} (h : decideLeafA φ = .proved) : Fml.Valid φ := by
  unfold decideLeafA at h
  split at h
  · split at h
    · rename_i hv _
      exact hv.down
    · cases h
  · split at h
    · split at h
      · rename_i hv _
        exact hv.down
      · cases h
    · split at h
      · split at h
        · rename_i hv _
          exact hv.down
        · cases h
      · split at h
        · split at h
          · rename_i hv _
            exact hv.down
          · cases h
        · split at h
          · split at h
            · rename_i hv _
              exact hv.down
            · cases h
          · cases h

/-- **Refutations are certified**: the state returned refutes the leaf. -/
theorem decideLeafA_refutes {φ : Fml C []} {σ : State C []} (h : decideLeafA φ = .refuted σ) :
    ¬ holds σ φ := by
  unfold decideLeafA at h
  split at h
  · split at h
    · cases h
    · rename_i cm _
      cases h
      exact cm.refutes
  · split at h
    · split at h
      · cases h
      · rename_i cm _
        cases h
        exact cm.2
    · split at h
      · split at h
        · cases h
        · rename_i cm _
          cases h
          exact cm.refutes
      · split at h
        · split at h
          · cases h
          · rename_i cm _
            cases h
            exact cm.refutes
        · split at h
          · split at h
            · cases h
            · rename_i cm _
              cases h
              exact cm.2
          · cases h

/-- **The fragment of the pipelines**: M4's, on the eliminated leaf, and the
quantified one (`Fml.quantCovered`, M7 step 4), the one with ledger
reads (`Fml.ledgerCovered`, M7 step 3), the one with storage array reads
(`Fml.arrayCovered`, M7 step 6), and the one with blocks over the ledger
(`Fml.ledgerBlockCovered`, feature 21). -/
def _root_.Solidity.Fml.CoveredA (φ : Fml C []) : Bool :=
  φ.inExact && φ.exactBounded || φ.quantCovered || φ.arrayCovered || φ.ledgerCovered ||
    φ.ledgerBlockCovered

/-- **Completeness on `Fml.CoveredA`.** -/
theorem decideLeafA_complete {φ : Fml C []} (h : φ.CoveredA = true) : decideLeafA φ ≠ .unknown := by
  simp only [Fml.CoveredA, Bool.or_eq_true, Bool.and_eq_true] at h
  unfold decideLeafA
  cases hd : dependentReduction? φ with
  | some r =>
    dsimp only
    split <;> exact fun h => nomatch h
  | none =>
    rcases h with (((h | h) | h) | h) | h
    · have := dependentReduction?_isSome φ h.1 h.2
      rw [hd] at this
      cases this
    · obtain ⟨q, hq⟩ := Option.isSome_iff_exists.mp (quantReduction?_isSome φ h)
      dsimp only
      rw [hq]
      dsimp only
      split <;> exact fun h => nomatch h
    · obtain ⟨q, hq⟩ := Option.isSome_iff_exists.mp (arrayReduction?_isSome φ h)
      dsimp only
      split
      · split <;> exact fun h => nomatch h
      · rw [hq]
        dsimp only
        split <;> exact fun h => nomatch h
    · obtain ⟨q, hq⟩ := Option.isSome_iff_exists.mp (ledgerReduction?_isSome φ h)
      dsimp only
      split
      · split <;> exact fun h => nomatch h
      · split
        · split <;> exact fun h => nomatch h
        · rw [hq]
          dsimp only
          split <;> exact fun h => nomatch h
    · obtain ⟨q, hq⟩ := Option.isSome_iff_exists.mp (ledgerBlockReduction?_isSome φ h)
      dsimp only
      split
      · split <;> exact fun h => nomatch h
      · split
        · split <;> exact fun h => nomatch h
        · split
          · split <;> exact fun h => nomatch h
          · rw [hq]
            dsimp only
            split <;> exact fun h => nomatch h


/-! ### Fresh memory arrays (M7, plan step 6)

A leaf the pipelines above refuse and that binds fresh arrays of
primitives (`Fml.allocAll`) is read with its reads of them cut into atoms
(`Fml.mxTop`, `Calculus/MemSwap.lean`), exactly at every state
(`Fml.mxTop_holds`), and the cut leaf decided by `decideLeafA`. -/

/-- The formula binds a fresh memory object. -/
def _root_.Solidity.Fml.hasAllocAll {Γ : Ctx} : Fml C Γ → Bool
  | .allocAll .. => true
  | .not φ => φ.hasAllocAll
  | .and φ ψ | .imp φ ψ => φ.hasAllocAll || ψ.hasAllocAll
  | .all _ _ φ => φ.hasAllocAll
  | _ => false

/-- The leaf's fresh arrays cut, the cut leaf decided. -/
def decideMem (φ : Fml C []) : LeafVerdict C :=
  if φ.hasAllocAll then
    match φ.mxTop with
    | some ψ => decideLeafA ψ
    | none => .unknown
  else .unknown

theorem decideMem_sound {φ : Fml C []} (h : decideMem φ = .proved) : Fml.Valid φ := by
  unfold decideMem at h
  split at h
  · split at h
    · rename_i ψ hψ
      exact (Fml.mxTop_valid hψ).2 (decideLeafA_sound h)
    · cases h
  · cases h

theorem decideMem_refutes {φ : Fml C []} {σ : State C []} (h : decideMem φ = .refuted σ) :
    ¬ holds σ φ := by
  unfold decideMem at h
  split at h
  · split at h
    · rename_i ψ hψ
      exact fun hφ => decideLeafA_refutes h ((Fml.mxTop_holds hψ σ).1 hφ)
    · cases h
  · cases h

/-- **The decision**: `decideLeafA`, then on a leaf it answers `unknown` on,
the one with its fresh arrays cut (`decideMem`). -/
def decideLeaf (φ : Fml C []) : LeafVerdict C :=
  match decideLeafA φ with
  | .unknown => decideMem φ
  | v => v

/-- **Soundness.** -/
theorem decideLeaf_sound {φ : Fml C []} (h : decideLeaf φ = .proved) : Fml.Valid φ := by
  unfold decideLeaf at h
  split at h
  · exact decideMem_sound h
  · exact decideLeafA_sound h

/-- **Refutations are certified**: the state returned refutes the leaf. -/
theorem decideLeaf_refutes {φ : Fml C []} {σ : State C []} (h : decideLeaf φ = .refuted σ) :
    ¬ holds σ φ := by
  unfold decideLeaf at h
  split at h
  · exact decideMem_refutes h
  · exact decideLeafA_refutes h

theorem decideLeaf_not_valid {φ : Fml C []} {σ : State C []} (h : decideLeaf φ = .refuted σ) :
    ¬ Fml.Valid φ :=
  fun hv => decideLeaf_refutes h (hv σ)

/-- **The fragment with fresh arrays**: the leaf binds one, its cut is
defined and in `Fml.CoveredA`. -/
def _root_.Solidity.Fml.memCovered (φ : Fml C []) : Bool :=
  φ.hasAllocAll && match φ.mxTop with
    | some ψ => ψ.CoveredA
    | none => false

/-- **The fragment proved complete**: `Fml.CoveredA`, or a leaf with fresh
arrays whose cut is in it (`Fml.memCovered`, M7 step 6). -/
def _root_.Solidity.Fml.Covered (φ : Fml C []) : Bool := φ.CoveredA || φ.memCovered

theorem decideMem_complete {φ : Fml C []} (h : φ.memCovered = true) : decideMem φ ≠ .unknown := by
  unfold Fml.memCovered at h
  simp only [Bool.and_eq_true] at h
  obtain ⟨ha, h⟩ := h
  unfold decideMem
  rw [if_pos ha]
  split at h
  · exact decideLeafA_complete h
  · cases h

/-- **Completeness on `Fml.Covered`.** -/
theorem decideLeaf_complete {φ : Fml C []} (h : φ.Covered = true) : decideLeaf φ ≠ .unknown := by
  unfold decideLeaf
  split
  · rename_i hv
    simp only [Fml.Covered, Bool.or_eq_true] at h
    rcases h with h | h
    · exact absurd hv (decideLeafA_complete h)
    · exact decideMem_complete h
  · assumption

/-- On the fragment the verdict is exact. -/
theorem decideLeaf_proved_iff {φ : Fml C []} (h : φ.Covered = true) :
    decideLeaf φ = .proved ↔ Fml.Valid φ := by
  refine ⟨decideLeaf_sound, fun hv => ?_⟩
  cases hd : decideLeaf φ with
  | proved => rfl
  | refuted σ => exact absurd hv (decideLeaf_not_valid hd)
  | unknown => exact absurd hd (decideLeaf_complete h)

/-! ### Leaves with hashes (M7, plan step 7)

A leaf whose memory locals are fresh byte strings read only by hashes of
one kind (`Fml.swPrefix`, `Calculus/HashSwap.lean`): its swapped reading,
each string a word, decided by `decideLeaf`; a proof proves the leaf
(`Fml.swPrefix_validH`).  Otherwise the strings are chosen, a class of
equal strings at a time (`rgs`: the restricted growth strings, one class
per string), each class one of a family of strings with distinct hashes
(`Fml.swInst`, `Calculus/HashReduction.lean`), and the first instance
`decideLeaf` refutes gives a state, which meets the leaf's premise and
refutes it (`Fml.swInst_refutes`). -/

/-- A refutation under the goal's own premise. -/
structure HashRefutation (φ : Fml C []) where
  state : State C []
  refutes : ¬ Fml.holdsH state φ

/-- The instance of the leaf at the classes `cs`, refuted by `decideLeaf`:
a refutation of the leaf. -/
def refuteAt (k : HashKind) {N : Nat} (hok : famOK k N = true) (φ : Fml C []) (cs : List Nat) :
    Option (HashRefutation φ) :=
  if hcs : ∀ j ∈ cs, j < N then
    match he : φ.swInst k cs with
    | none => none
    | some φf =>
      match hd : decideLeaf φf with
      | .refuted σ => some ⟨σ.noHeap, Fml.swInst_refutes hok he hcs (decideLeaf_refutes hd)⟩
      | _ => none
  else none

/-- **A leaf with hashes of kind `k`**: proved by its swapped reading, or
refuted at the first class of strings whose instance is refuted. -/
def decideHashK (k : HashKind) (hk : k ≠ .ecrecover) (φ : Fml C []) : LeafVerdict C :=
  match φ.swPrefix k with
  | none => .unknown
  | some φ' =>
    match decideLeaf φ' with
    | .proved => if φ.posAll = true then .proved else .unknown
    | _ =>
      match famCheck φ.allocCount with
      | isFalse _ => .unknown
      | isTrue hok =>
        match (rgs φ.allocCount).findSome? (refuteAt k (famOKAll_ok hok hk) φ) with
        | some r => .refuted r.state
        | none => .unknown

theorem decideHashK_sound {k : HashKind} {hk : k ≠ .ecrecover} {φ : Fml C []}
    (h : decideHashK k hk φ = .proved) : Fml.ValidH φ := by
  unfold decideHashK at h
  split at h
  · cases h
  · rename_i φ' he
    split at h
    · rename_i hd
      split at h
      · rename_i hp
        exact Fml.swPrefix_validH he hp (decideLeaf_sound hd)
      · cases h
    · split at h
      · cases h
      · split at h <;> cases h

theorem decideHashK_refutes {k : HashKind} {hk : k ≠ .ecrecover} {φ : Fml C []} {σ : State C []}
    (h : decideHashK k hk φ = .refuted σ) : ¬ Fml.holdsH σ φ := by
  unfold decideHashK at h
  split at h
  · cases h
  · split at h
    · split at h <;> cases h
    · split at h
      · cases h
      · split at h
        · rename_i r _
          cases h
          exact r.refutes
        · cases h

/-! ### Completeness on leaves with hashes -/

/-- **The covered leaves with hashes of kind `k`**: the swapped leaf and each
instance at classes of its strings covered (`Fml.Covered`), the family of
`famN` strings checked (`famCovered`: by the kernel's theorem up to
`famBound`, computed past it), the swapped leaf in the relabeling fragment
over its keyed roots, which map words to words. -/
def _root_.Solidity.Fml.coveredK (k : HashKind) (φ : Fml C []) : Bool :=
  match φ.swPrefix k with
  | none => false
  | some φ' =>
    let V := φ.allocLevels
    let K := φ'.vRoots V
    φ'.Covered && famCovered φ.allocCount &&
      (rgs φ.allocCount).all (fun cs => (φ.swInst k cs).any Fml.Covered) &&
      φ.swRL k V K && φ.prefixOK V && kTypedB C K && φ.posAll

theorem findSome?_ne_none {α β : Type} {f : α → Option β} {a : α} :
    {l : List α} → a ∈ l → f a ≠ none → l.findSome? f ≠ none
  | [], h, _ => absurd h List.not_mem_nil
  | b :: l, h, hf => by
    rw [List.findSome?_cons]
    cases hb : f b with
    | some _ => exact fun h => nomatch h
    | none =>
      rcases List.mem_cons.1 h with rfl | h
      · exact absurd hb hf
      · exact findSome?_ne_none h hf

/-- **Completeness for one kind.** -/
theorem decideHashK_complete {k : HashKind} (hk : k ≠ .ecrecover) {φ : Fml C []}
    (h : φ.coveredK k = true) : decideHashK k hk φ ≠ .unknown := by
  unfold Fml.coveredK at h
  split at h
  · cases h
  · rename_i φ' e
    simp only [Bool.and_eq_true, List.all_eq_true] at h
    obtain ⟨⟨⟨⟨⟨⟨hcov, hn⟩, hall⟩, hrl⟩, hpre⟩, hK⟩, hpos⟩ := h
    obtain ⟨hokA, hck⟩ := famCheck_isTrue (famOKAll_famN hn)
    unfold decideHashK
    rw [e]
    simp only
    cases hd : decideLeaf φ' with
    | proved => simp only [hpos, ↓reduceIte]; exact fun h => nomatch h
    | unknown => exact absurd hd (decideLeaf_complete hcov)
    | refuted σ =>
      simp only
      rw [hck]
      simp only
      have hnv := decideLeaf_not_valid hd
      obtain ⟨cs, hcs, φf, hf, hnf⟩ := Fml.swPrefix_complete (famOKAll_ok hokA hk) e (kTyped_of hK) hrl hpre
        (le_famN _) hnv
      have hcovf : φf.Covered = true := by
        have := hall cs hcs
        rw [hf] at this
        exact this
      have href : refuteAt k (famOKAll_ok hokA hk) φ cs ≠ none := by
        unfold refuteAt
        have hb : ∀ j ∈ cs, j < famN φ.allocCount := fun j hj => by
          have := rgsFrom_bound φ.allocCount 0 cs hcs j hj
          have := le_famN φ.allocCount
          omega
        rw [dif_pos hb]
        split
        · rename_i he; rw [hf] at he; cases he
        · rename_i φf' he
          rw [hf] at he
          cases he
          split
          · exact fun h => nomatch h
          · rename_i hne
            exfalso
            cases hv : decideLeaf φf with
            | proved => exact hnf (decideLeaf_sound hv)
            | unknown => exact decideLeaf_complete hcovf hv
            | refuted σ => exact hne σ hv
      have := findSome?_ne_none hcs href
      cases hs : (rgs φ.allocCount).findSome? (refuteAt k (famOKAll_ok hokA hk) φ) with
      | none => exact absurd hs this
      | some r => exact fun h => nomatch h

/-- A refutation of the leaf with two kinds at the classes `cs`: the
instance with the second kind's words fixed (`Fml.tk`), refuted by
`decideLeaf`. -/
def refuteAt2 (k₁ k₂ : HashKind) (hk₁ : k₁ ≠ .ecrecover) (hk₂ : k₂ ≠ .ecrecover) {N : Nat}
    (hokA : famOKAll N = true) (φ φF : Fml C []) (he : φ.tk k₁ k₂ N true = some φF) (cs : List Nat) :
    Option (HashRefutation φ) :=
  if hcs : ∀ j ∈ cs, j < N then
    match hi : φF.swInst k₁ cs with
    | none => none
    | some inst =>
      match hd : decideLeaf inst with
      | .refuted σ => some ⟨σ.noHeap, Fml.tk_refutes hk₁ hk₂ hokA he hi hcs (decideLeaf_refutes hd)⟩
      | _ => none
  else none

/-- **A leaf with strings hashed by two kinds** (`k₁`, `k₂`): the second
kind's words as binders of their own (`Fml.tk`), the result read by the
one-kind swap; proved by it, or refuted at the first class of strings whose
instance, the second kind's words fixed, is refuted. -/
def decideHash2 (k₁ k₂ : HashKind) (hk₁ : k₁ ≠ .ecrecover) (hk₂ : k₂ ≠ .ecrecover) (φ : Fml C []) :
    LeafVerdict C :=
  match φ.tk k₁ k₂ (famN φ.allocCount) false with
  | none => .unknown
  | some φ₂ =>
    match φ₂.swPrefix k₁ with
    | none => .unknown
    | some φ₂' =>
      match decideLeaf φ₂' with
      | .proved => if φ₂.posAll = true then .proved else .unknown
      | _ =>
        match famCheck φ.allocCount with
        | isFalse _ => .unknown
        | isTrue hokA =>
          match he : φ.tk k₁ k₂ (famN φ.allocCount) true with
          | none => .unknown
          | some φF =>
            match (rgs φ₂.allocCount).findSome? (refuteAt2 k₁ k₂ hk₁ hk₂ hokA φ φF he) with
            | some r => .refuted r.state
            | none => .unknown

theorem decideHash2_sound {k₁ k₂ : HashKind} {hk₁ : k₁ ≠ .ecrecover} {hk₂ : k₂ ≠ .ecrecover}
    {φ : Fml C []} (h : decideHash2 k₁ k₂ hk₁ hk₂ φ = .proved) : Fml.ValidH φ := by
  unfold decideHash2 at h
  split at h
  · cases h
  · rename_i φ₂ e₂
    split at h
    · cases h
    · rename_i φ₂' e'
      split at h
      · rename_i hd
        split at h
        · rename_i hp
          exact Fml.tk_validH hk₁ hk₂ e₂ (Fml.swPrefix_validH e' hp (decideLeaf_sound hd))
        · cases h
      · split at h
        · cases h
        · split at h
          · cases h
          · split at h <;> cases h

theorem decideHash2_refutes {k₁ k₂ : HashKind} {hk₁ : k₁ ≠ .ecrecover} {hk₂ : k₂ ≠ .ecrecover}
    {φ : Fml C []} {σ : State C []} (h : decideHash2 k₁ k₂ hk₁ hk₂ φ = .refuted σ) :
    ¬ Fml.holdsH σ φ := by
  unfold decideHash2 at h
  split at h
  · cases h
  · split at h
    · cases h
    · split at h
      · split at h <;> cases h
      · split at h
        · cases h
        · split at h
          · cases h
          · split at h
            · rename_i r _
              cases h
              exact r.refutes
            · cases h

/-- One way of deciding a leaf with hashes, with its fragment. -/
structure HashTry (C : Contract) where
  run : Fml C [] → LeafVerdict C
  covers : Fml C [] → Bool
  sound : ∀ {φ}, run φ = .proved → Fml.ValidH φ
  refutes : ∀ {φ σ}, run φ = .refuted σ → ¬ Fml.holdsH σ φ
  complete : ∀ {φ}, covers φ = true → run φ ≠ .unknown

/-- The first answer of a list of decisions. -/
def firstKnown : List (Fml C [] → LeafVerdict C) → Fml C [] → LeafVerdict C
  | [], _ => .unknown
  | t :: ts, φ =>
    match t φ with
    | .unknown => firstKnown ts φ
    | v => v

theorem firstKnown_mem {φ : Fml C []} {v : LeafVerdict C} (hv : v ≠ .unknown) :
    (ts : List (Fml C [] → LeafVerdict C)) → firstKnown ts φ = v → ∃ t ∈ ts, t φ = v
  | [], h => absurd h.symm hv
  | t :: ts, h => by
    unfold firstKnown at h
    split at h
    · obtain ⟨t', ht', e⟩ := firstKnown_mem hv ts h
      exact ⟨t', List.mem_cons_of_mem _ ht', e⟩
    · rename_i hne
      exact ⟨t, List.mem_cons_self, by rw [← h]⟩

theorem firstKnown_ne {φ : Fml C []} :
    (ts : List (Fml C [] → LeafVerdict C)) → (∃ t ∈ ts, t φ ≠ .unknown) → firstKnown ts φ ≠ .unknown
  | [], ⟨_, h, _⟩ => nomatch h
  | t :: ts, ⟨t', ht', hne⟩ => by
    unfold firstKnown
    split
    · rename_i hu
      rcases List.mem_cons.1 ht' with rfl | ht'
      · exact absurd hu hne
      · exact firstKnown_ne ts ⟨t', ht', hne⟩
    · rename_i v hv
      exact hv


/-- **The covered leaves with hashes of two kinds** (`k₁`, `k₂`): the
reading with the second kind's words in the one-kind fragment of `k₁`
(`Fml.coveredK`'s conditions on it), each instance with the second kind's
words fixed covered, and the second kind's words in the relabeling
fragment (`Fml.tkRL`). -/
def _root_.Solidity.Fml.coveredK2 (k₁ k₂ : HashKind) (φ : Fml C []) : Bool :=
  match φ.tk k₁ k₂ (famN φ.allocCount) false with
  | none => false
  | some φ₂ =>
    match φ₂.swPrefix k₁ with
    | none => false
    | some φ₂' =>
      match φ.tk k₁ k₂ (famN φ.allocCount) true with
      | none => false
      | some φF =>
        let V := φ₂.allocLevels
        let K := φ₂'.vRoots V
        φ₂'.Covered && famCovered φ.allocCount &&
          (rgs φ₂.allocCount).all (fun cs => (φF.swInst k₁ cs).any Fml.Covered) &&
          φ₂.swRL k₁ V K && φ₂.prefixOK V && kTypedB C K && φ.tkRL k₁ k₂ && φ₂.posAll

/-- **Completeness for two kinds.** -/
theorem decideHash2_complete {k₁ k₂ : HashKind} (hk₁ : k₁ ≠ .ecrecover) (hk₂ : k₂ ≠ .ecrecover)
    {φ : Fml C []} (h : φ.coveredK2 k₁ k₂ = true) : decideHash2 k₁ k₂ hk₁ hk₂ φ ≠ .unknown := by
  unfold Fml.coveredK2 at h
  split at h
  · cases h
  · rename_i φ₂ e₂
    split at h
    · cases h
    · rename_i φ₂' e'
      split at h
      · cases h
      · rename_i φF hF
        simp only [Bool.and_eq_true, List.all_eq_true] at h
        obtain ⟨⟨⟨⟨⟨⟨⟨hcov, hn⟩, hall⟩, hrl⟩, hpre⟩, hK⟩, hrl₂⟩, hpos⟩ := h
        obtain ⟨hokA, hck⟩ := famCheck_isTrue (famOKAll_famN hn)
        have hlen : φ₂.allocCount ≤ famN φ.allocCount := by
          rw [Fml.tk_allocCount φ e₂]; exact le_famN _
        unfold decideHash2
        rw [e₂]
        simp only
        rw [e']
        simp only
        cases hd : decideLeaf φ₂' with
        | proved => simp only [hpos, ↓reduceIte]; exact fun h => nomatch h
        | unknown => exact absurd hd (decideLeaf_complete hcov)
        | refuted σ =>
          simp only
          rw [hck]
          simp only
          have hinst : ∀ cs ∈ rgs φ₂.allocCount, ∃ φF instF,
              φ.tk k₁ k₂ (famN φ.allocCount) true = some φF ∧ φF.swInst k₁ cs = some instF := by
            intro cs hcs
            have := hall cs hcs
            cases hi : φF.swInst k₁ cs with
            | none => rw [hi] at this; cases this
            | some instF => exact ⟨φF, instF, hF, hi⟩
          obtain ⟨cs, hcs, φF', instF, hF', hi, hnf⟩ := Fml.tk_complete hk₁ hk₂ hokA e₂ e' (kTyped_of hK)
            hrl hpre hlen hrl₂ hinst (decideLeaf_not_valid hd)
          rw [hF] at hF'
          cases hF'
          have hcovf : instF.Covered = true := by
            have := hall cs hcs
            rw [hi] at this
            exact this
          have href : refuteAt2 k₁ k₂ hk₁ hk₂ hokA φ φF hF cs ≠ none := by
            unfold refuteAt2
            have hb : ∀ j ∈ cs, j < famN φ.allocCount := fun j hj => by
              have := rgsFrom_bound φ₂.allocCount 0 cs hcs j hj
              omega
            rw [dif_pos hb]
            split
            · rename_i he; rw [hi] at he; cases he
            · rename_i inst' he
              rw [hi] at he
              cases he
              split
              · exact fun h => nomatch h
              · rename_i hne
                exfalso
                cases hv : decideLeaf instF with
                | proved => exact hnf (decideLeaf_sound hv)
                | unknown => exact decideLeaf_complete hcovf hv
                | refuted σ => exact hne σ hv
          have := findSome?_ne_none hcs href
          split
          · rename_i he; rw [hF] at he; cases he
          · rename_i φF'' he
            rw [hF] at he
            cases he
            cases hs : (rgs φ₂.allocCount).findSome? (refuteAt2 k₁ k₂ hk₁ hk₂ hokA φ φF hF) with
            | none => exact absurd hs this
            | some r => exact fun h => nomatch h

/-- A leaf with hashes of one kind. -/
def tryK (k : HashKind) (hk : k ≠ .ecrecover) : HashTry C :=
  ⟨decideHashK k hk, Fml.coveredK k, decideHashK_sound, decideHashK_refutes, decideHashK_complete hk⟩

/-- A leaf with hashes of two kinds. -/
def tryK2 (k₁ k₂ : HashKind) (hk₁ : k₁ ≠ .ecrecover) (hk₂ : k₂ ≠ .ecrecover) : HashTry C :=
  ⟨decideHash2 k₁ k₂ hk₁ hk₂, Fml.coveredK2 k₁ k₂, decideHash2_sound, decideHash2_refutes,
    decideHash2_complete hk₁ hk₂⟩

/-- **The ways of deciding a leaf with hashes**: of one kind, each kind in
turn; of two, each ordered pair. -/
def hashTries : List (HashTry C) :=
  [tryK .keccak (by decide), tryK .sha256 (by decide), tryK .ripemd160 (by decide),
    tryK2 .keccak .sha256 (by decide) (by decide), tryK2 .sha256 .keccak (by decide) (by decide),
    tryK2 .keccak .ripemd160 (by decide) (by decide), tryK2 .ripemd160 .keccak (by decide) (by decide),
    tryK2 .sha256 .ripemd160 (by decide) (by decide), tryK2 .ripemd160 .sha256 (by decide) (by decide)]

/-- **A leaf with hashes**: the first way that answers. -/
def decideHash (φ : Fml C []) : LeafVerdict C := firstKnown (hashTries.map (·.run)) φ

theorem decideHash_sound {φ : Fml C []} (h : decideHash φ = .proved) : Fml.ValidH φ := by
  obtain ⟨t, ht, e⟩ := firstKnown_mem (φ := φ) (v := .proved) (fun h => nomatch h) _ h
  obtain ⟨T, -, rfl⟩ := List.mem_map.1 ht
  exact T.sound e

theorem decideHash_refutes {φ : Fml C []} {σ : State C []} (h : decideHash φ = .refuted σ) :
    ¬ Fml.holdsH σ φ := by
  obtain ⟨t, ht, e⟩ := firstKnown_mem (φ := φ) (v := .refuted σ) (fun h => nomatch h) _ h
  obtain ⟨T, -, rfl⟩ := List.mem_map.1 ht
  exact T.refutes e

/-- **The covered leaves with hashes**: of some way of deciding them. -/
def _root_.Solidity.Fml.hashCovered (φ : Fml C []) : Bool :=
  φ.hasHash && (hashTries (C := C)).any (·.covers φ)

theorem decideHash_complete {φ : Fml C []} (h : (hashTries (C := C)).any (·.covers φ) = true) :
    decideHash φ ≠ .unknown := by
  obtain ⟨T, hT, hc⟩ := List.any_eq_true.1 h
  exact firstKnown_ne _ ⟨T.run, List.mem_map_of_mem hT, T.complete hc⟩

/-! ### The decision, read so -/

/-- **The decision the theorem is about**: `decideLeaf` on a leaf without
a hash, `decideHash` on one with a hash. -/
def decideGoal (φ : Fml C []) : LeafVerdict C :=
  if φ.hasHash then decideHash φ else decideLeaf φ

/-- **Soundness**, under the goal's premise. -/
theorem decideGoal_sound {φ : Fml C []} (h : decideGoal φ = .proved) : Fml.ValidH φ := by
  unfold decideGoal at h
  cases hh : φ.hasHash
  · rw [hh, if_neg Bool.false_ne_true] at h
    exact (Fml.validH_iff hh).mpr (decideLeaf_sound h)
  · rw [hh, if_pos rfl] at h
    exact decideHash_sound h

/-- **Refutations are certified**: the state's instance meets the premise
and refutes the leaf. -/
theorem decideGoal_refutes {φ : Fml C []} {σ : State C []} (h : decideGoal φ = .refuted σ) :
    ¬ Fml.holdsH σ φ := by
  unfold decideGoal at h
  cases hh : φ.hasHash
  · rw [hh, if_neg Bool.false_ne_true] at h
    exact fun hv => decideLeaf_refutes h ((Fml.holdsH_iff σ φ hh).mp hv)
  · rw [hh, if_pos rfl] at h
    exact decideHash_refutes h

/-- **Completeness on the covered leaves without a hash.** -/
theorem decideGoal_complete {φ : Fml C []} (h : φ.Covered = true) (hh : φ.hasHash = false) :
    decideGoal φ ≠ .unknown := by
  unfold decideGoal
  rw [hh]
  exact decideLeaf_complete h

/-- **Completeness on the covered leaves with hashes** (`Fml.hashCovered`). -/
theorem decideGoal_complete_hash {φ : Fml C []} (h : φ.hashCovered = true) :
    decideGoal φ ≠ .unknown := by
  simp only [Fml.hashCovered, Bool.and_eq_true] at h
  unfold decideGoal
  rw [if_pos h.1]
  exact decideHash_complete h.2

/-! ## The fragment the user named -/

/-- **The classes the closer may leave `unknown` with two symbolic
operands** (`true`: waived; the user's answer of 2026-10-25 waives all
four). -/
structure Waivers where
  /-- `/`, `%`, a modulus of `addmod`/`mulmod`: a symbolic divisor. -/
  division : Bool := true
  /-- `**`: a symbolic exponent. -/
  power : Bool := true
  /-- `<<`, `>>`: a symbolic shift amount. -/
  shift : Bool := true
  /-- `&`, `|`, `^`: two symbolic operands. -/
  bitwise : Bool := true


/-- A literal's integer. -/
def _root_.Solidity.Op0.litValue? {s : Srt} : Op0 C s → Option Int
  | .lit (p := .bool) v => some (cond (show Bool from v) 1 0)
  | .lit (p := .uint) v => some v.val
  | .lit (p := .int) v => some v.val
  | .zlit n => some n
  | _ => none

def _root_.Solidity.Tm.litValue? {Γ : Ctx} {s : Srt} : Tm C Γ s → Option Int
  | .app0 o => o.litValue?
  | _ => none

def _root_.Solidity.Tm.isLitV {Γ : Ctx} {s : Srt} (t : Tm C Γ s) : Bool := t.litValue?.isSome

/-- Whether an operator applied to operands (literal or not, the second's
literal value) is in the fragment. -/
def _root_.Solidity.BinOp.admits (w : Waivers) (op : BinOp) (xl yl : Bool) (y? : Option Int) : Bool :=
  match op with
  | .mul | .mulW => xl || yl
  | .div | .mod => yl || !w.division
  | .pow | .powW =>
    match y? with
    | some n => decide (n ≤ 1)
    | none => !w.power
  | .shl | .shr => yl || !w.shift
  | .band | .bor | .bxor => xl || yl || !w.bitwise
  | _ => true

def _root_.Solidity.Op2.admits (w : Waivers) {a b s : Srt} (o : Op2 C a b s) (xl yl : Bool)
    (y? : Option Int) : Bool :=
  match o with
  | .binop op _ => op.admits w xl yl y?
  | .zbin op _ => op != .mul || xl || yl
  | .hash _ => false
  | _ => true

def _root_.Solidity.Op3.admits (w : Waivers) {a b c s : Srt} (o : Op3 C a b c s) (xl yl zl : Bool) :
    Bool :=
  match o with
  | .modular .mulmod => (xl || yl) && (zl || !w.division)
  | .modular .addmod => zl || !w.division
  | _ => true

def _root_.Solidity.Op2.hashKind? {a b s : Srt} : Op2 C a b s → Option HashKind
  | .hash k => some k
  | _ => none

/-- `==`, `!=`. -/
def _root_.Solidity.Op2.isEqNe {a b s : Srt} : Op2 C a b s → Bool
  | .binop .eqB _ | .binop .neB _ => true
  | _ => false

/-- A mapping's key: `m[k]`. -/
def _root_.Solidity.Op2.isMapAt {a b s : Srt} : Op2 C a b s → Bool
  | .at .map => true
  | _ => false

def _root_.Solidity.Op0.rootNameD? {s : Srt} : Op0 C s → Option Name
  | .root r _ => some r
  | _ => none

/-- A root of the storage. -/
def _root_.Solidity.Tm.rootNameD? {Γ : Ctx} {s : Srt} : Tm C Γ s → Option Name
  | .app0 o => o.rootNameD?
  | _ => none

/-- A hash term whose verdicts the goal's premise settles: of a kind other
than `ecrecover`, whose value is `opaque`. -/
def _root_.Solidity.Tm.hashable? {Γ : Ctx} {s : Srt} : Tm C Γ s → Option HashKind
  | .app2 o _ _ =>
    match o.hashKind? with
    | some .ecrecover => none
    | k => k
  | _ => none

/-- A memory local. -/
def _root_.Solidity.Tm.isPvI {Γ : Ctx} {s : Srt} : Tm C Γ s → Bool
  | .pvI _ => true
  | _ => false

/-- The starting memory. -/
def _root_.Solidity.Tm.isMemory {Γ : Ctx} {s : Srt} : Tm C Γ s → Bool
  | .app0 .memory => true
  | _ => false

/-- A hash of a memory local in the starting memory: a key it reads is a
hash's, never the default a key with no value reads (a memory written past
a string's end has none). -/
def _root_.Solidity.Tm.hashOfLocal {Γ : Ctx} {s : Srt} : Tm C Γ s → Bool
  | .app2 o x y => o.isHash && x.isMemory && y.isPvI
  | _ => false

/-- Two hash terms of one kind: their equation is their inputs' under the
goal's premise. -/
def _root_.Solidity.Tm.hashPair {Γ : Ctx} {s s' : Srt} (x : Tm C Γ s) (y : Tm C Γ s') : Bool :=
  match x.hashable?, y.hashable? with
  | some k, some k' => k == k'
  | _, _ => false

/-- **A term of the fragment**: every operator admitted.  A hash term is
admitted only where the goal's premise settles it (`hashOK`): an operand
of `==`/`!=` against a hash of its kind, or a key of a mapping at a root
(whose other keys must then be hashes too, `Fml.inTarget`).  Anywhere
else its verdicts may turn on a preimage, and the closer may leave them. -/
def _root_.Solidity.Tm.inTarget {Γ : Ctx} (w : Waivers) (hashOK : Bool) : {s : Srt} → Tm C Γ s → Bool
  | _, .netOf _ a => a.inTarget w false
  | _, .app1 _ x => x.inTarget w false
  | _, .app2 o x y =>
    let eqH := o.isEqNe && x.hashPair y
    let keyH := o.isMapAt && x.rootNameD?.isSome && y.hashable?.isSome && y.hashOfLocal
    x.inTarget w eqH && y.inTarget w (eqH || keyH) &&
      (if o.isHash then hashOK else o.admits w x.isLitV y.isLitV y.litValue?)
  | _, .app3 o x y z => x.inTarget w false && y.inTarget w false && z.inTarget w false &&
      o.admits w x.isLitV y.isLitV z.isLitV
  | _, _ => true

def _root_.Solidity.Rhs.inTarget {Γ : Ctx} (w : Waivers) {t : LTy} : Rhs C Γ t → Bool
  | .val a | .zint a => a.inTarget w false
  | .path q => q.inTarget w false
  | .mref i => i.inTarget w false
  | .store s => s.inTarget w false
  | .unset | .saveNet | .saveNetMt => true

def _root_.Solidity.UpdElem.inTarget {Γ Δ : Ctx} (w : Waivers) : UpdElem C Γ Δ → Bool
  | .local _ r => r.inTarget w
  | .storage s => s.inTarget w false
  | .memory m => m.inTarget w false
  | .selfBalance _ a | .setBalance a => a.inTarget w false
  | .net r _ a | .pay r a | .netMt r a => r.inTarget w false && a.inTarget w false

def _root_.Solidity.Upd.inTarget {Γ : Ctx} (w : Waivers) : {Δ : Ctx} → Upd C Γ Δ → Bool
  | _, .nil => true
  | _, .snoc U e => U.inTarget w && e.inTarget w
  | _, .decl U _ r => U.inTarget w && r.inTarget w
  | _, .pop U _ | _, .drop U _ => U.inTarget w

/-! ### Reads and the array property fragment -/

/-- The symbols that read contents: storage, memory, a hash, the ledger. -/
def _root_.Solidity.Op2.isRead {a b s : Srt} : Op2 C a b s → Bool
  | .find | .len | .read | .mlen | .sfind | .copyMem | .iread | .findIn | .sfindIn | .hash _ => true
  | _ => false

/-- The symbols that write. -/
def _root_.Solidity.Op2.isWrite {a b s : Srt} : Op2 C a b s → Bool
  | .delAt | .pushSlot | .pop | .shrink | .extend | .copySt _ | .delAtIn | .copy _ => true
  | _ => false

def _root_.Solidity.Op1.isWrite {a s : Srt} : Op1 C a s → Bool
  | .alloc .. | .addM .. => true
  | _ => false

/-- The symbols that index: the second operand is the index. -/
def _root_.Solidity.Op2.isIndex {a b s : Srt} : Op2 C a b s → Bool
  | .at _ | .mat _ => true
  | _ => false

/-- A bound variable, by its level. -/
def _root_.Solidity.Tm.isBound {Γ : Ctx} (qs : List Nat) {s : Srt} : Tm C Γ s → Bool
  | .pvV i | .pvZ i => qs.contains i.level
  | _ => false

/-- The term mentions a bound variable. -/
def _root_.Solidity.Tm.mentions {Γ : Ctx} (qs : List Nat) : {s : Srt} → Tm C Γ s → Bool
  | _, .pvV i | _, .pvZ i => qs.contains i.level
  | _, .netOf _ a | _, .app1 _ a => a.mentions qs
  | _, .app2 _ x y => x.mentions qs || y.mentions qs
  | _, .app3 _ x y z => x.mentions qs || y.mentions qs || z.mentions qs
  | _, _ => false

/-- The term reads contents at a bound variable. -/
def _root_.Solidity.Tm.readsAt {Γ : Ctx} (qs : List Nat) : {s : Srt} → Tm C Γ s → Bool
  | _, .netOf _ a => a.mentions qs || a.readsAt qs
  | _, .app1 o x => (match o with | .net | .wt | .cleanTail => x.mentions qs | _ => false) ||
      x.readsAt qs
  | _, .app2 o x y => (o.isRead && (x.mentions qs || y.mentions qs)) || x.readsAt qs || y.readsAt qs
  | _, .app3 _ x y z => x.readsAt qs || y.readsAt qs || z.readsAt qs
  | _, _ => false

/-- The term reads contents at all. -/
def _root_.Solidity.Tm.readsAny {Γ : Ctx} : {s : Srt} → Tm C Γ s → Bool
  | _, .netOf _ _ => true
  | _, .app1 o x => (match o with | .net | .wt | .cleanTail => true | _ => false) || x.readsAny
  | _, .app2 o x y => o.isRead || x.readsAny || y.readsAny
  | _, .app3 _ x y z => x.readsAny || y.readsAny || z.readsAny
  | _, _ => false

/-- **A value term of the array property fragment**: a bound variable
occurs only as an index (`a[i]`, `m[k]`, a memory element, a ledger
entry), never under arithmetic, never in a nested index (`a[a[i]]`), at
most once along a path (`m[i][j]` with `i`, `j` both bound is outside:
Bradley, Manna and Sipma state their result for arrays of one dimension),
and nothing is written at a path that mentions it. -/
def _root_.Solidity.Tm.apfV {Γ : Ctx} (qs : List Nat) : {s : Srt} → Tm C Γ s → Bool
  | _, .pvV i | _, .pvZ i => !qs.contains i.level
  | _, .netOf _ a => a.isBound qs || !a.mentions qs
  | _, .app1 o x =>
    match o with
    | .net => x.isBound qs || !x.mentions qs
    | o => if o.isWrite then !x.mentions qs else x.apfV qs
  | _, .app2 o x y =>
    if o.isIndex then x.apfV qs && (y.isBound qs || !y.mentions qs) && !(y.isBound qs && x.mentions qs)
    else if o.isWrite then !(x.mentions qs || y.mentions qs)
    else x.apfV qs && y.apfV qs
  | _, .app3 o x y z =>
    match o with
    | .atIn _ => !x.mentions qs && y.apfV qs && (z.isBound qs || !z.mentions qs) &&
        !(z.isBound qs && y.mentions qs)
    | .ite => x.apfV qs && y.apfV qs && z.apfV qs
    | .modular _ => x.apfV qs && y.apfV qs && z.apfV qs
    | _ => !(x.mentions qs || y.mentions qs || z.mentions qs)
  | _, _ => true

/-- An index term (Bradley, Manna and Sipma): a bound variable, or a term
mentioning none. -/
def _root_.Solidity.Tm.indexTerm {Γ : Ctx} (qs : List Nat) {s : Srt} (t : Tm C Γ s) : Bool :=
  t.isBound qs || !t.mentions qs

/-- A guard comparison: `<`, `>`, `<=`, `>=`, `==`, never `!=`. -/
def _root_.Solidity.Op2.isGuardCmp {a b s : Srt} : Op2 C a b s → Bool
  | .binop .lt _ | .binop .gt _ | .binop .le _ | .binop .ge _ | .binop .eqB _ => true
  | .zcmp .lt _ | .zcmp .gt _ | .zcmp .le _ | .zcmp .ge _ | .zcmp .eqB _ => true
  | _ => false

/-- A strict comparison: `<`, `>`.  Between two bound variables it is
outside the fragment (`i < j` is `i + 1 ≤ j`, arithmetic on the bound
variables, outside Bradley, Manna and Sipma's fragment as they state it;
`BinOp.isStrict` is the decision's counterpart). -/
def _root_.Solidity.Op2.isStrictCmp {a b s : Srt} : Op2 C a b s → Bool
  | .binop .lt _ | .binop .gt _ | .zcmp .lt _ | .zcmp .gt _ => true
  | _ => false

def _root_.Solidity.Op2.isAndOr {a b s : Srt} : Op2 C a b s → Bool
  | .binop .and _ | .binop .or _ => true
  | _ => false

/-- **An index-guard term**: `&&`/`||` of comparisons of index terms, or a
term mentioning no bound variable. -/
def _root_.Solidity.Tm.apfG {Γ : Ctx} (qs : List Nat) : {s : Srt} → Tm C Γ s → Bool
  | _, .app2 o x y =>
    if o.isAndOr then x.apfG qs && y.apfG qs
    else if o.isGuardCmp then
      x.indexTerm qs && y.indexTerm qs && !(o.isStrictCmp && x.isBound qs && y.isBound qs)
    else !(x.mentions qs || y.mentions qs)
  | _, t => !t.mentions qs

/-- The literal `true`. -/
def _root_.Solidity.Tm.isTrueLit {Γ : Ctx} {p : PrimTy} : Tm C Γ (.val p) → Bool
  | .app0 o => match o with | .lit (p := .bool) v => v | _ => false
  | _ => false

/-- A quantifier-free formula not mentioning a bound variable. -/
def _root_.Solidity.Fml.groundQF {Γ : Ctx} (qs : List Nat) : Fml C Γ → Bool
  | .tt => true
  | .eq a b => !(a.mentions qs || b.mentions qs)
  | .wellFormed s => !s.mentions qs
  | .not φ => φ.groundQF qs
  | .and φ ψ | .imp φ ψ => φ.groundQF qs && ψ.groundQF qs
  | _ => false

/-- **An index guard**: conjunctions of guard atoms, an atom an equation of
guard terms (a Boolean one against `true`), or ground. -/
def _root_.Solidity.Fml.apfGuard {Γ : Ctx} (qs : List Nat) : Fml C Γ → Bool
  | .tt => true
  | .and φ ψ => φ.apfGuard qs && ψ.apfGuard qs
  | φ@(@Fml.eq _ _ p a b) =>
    φ.groundQF qs ||
      (match p with
        | .bool => (a.apfG qs && b.isTrueLit) || (a.isTrueLit && b.apfG qs)
        | _ => a.indexTerm qs && b.indexTerm qs)
  | φ => φ.groundQF qs

/-- A quantifier-free value formula over `Tm.apfV` terms. -/
def _root_.Solidity.Fml.apfValue {Γ : Ctx} (qs : List Nat) : Fml C Γ → Bool
  | .tt => true
  | .eq a b => a.apfV qs && b.apfV qs
  | .wellFormed s => s.apfV qs
  | .not φ => φ.apfValue qs
  | .and φ ψ | .imp φ ψ => φ.apfValue qs && ψ.apfValue qs
  | _ => false

/-- **The body of a universal block**: `guard → value`, conjunctions of
them. -/
def _root_.Solidity.Fml.apfBody {Γ : Ctx} (qs : List Nat) : Fml C Γ → Bool
  | .imp G V => (G.apfGuard qs && V.apfBody qs) || (Fml.imp G V).apfValue qs
  | .and φ ψ => φ.apfBody qs && ψ.apfBody qs
  | φ => φ.apfValue qs

/-- The formula reads contents at a bound variable; an update or a program
counts as one (conservative). -/
def _root_.Solidity.Fml.readsAt (qs : List Nat) : {Γ : Ctx} → Fml C Γ → Bool
  | _, .tt => false
  | _, .eq a b => a.readsAt qs || b.readsAt qs
  | _, .wellFormed s => s.mentions qs || s.readsAt qs
  | _, .not φ | _, .havoc φ | _, .anon _ φ | _, .grow φ | _, .all _ _ φ | _, .bind _ _ _ φ
  | _, .allocAll _ _ φ => φ.readsAt qs
  | _, .and φ ψ | _, .imp φ ψ => φ.readsAt qs || ψ.readsAt qs
  | _, .upd .. | _, .modal .. => true

/-- The formula reads contents at all. -/
def _root_.Solidity.Fml.readsAny : {Γ : Ctx} → Fml C Γ → Bool
  | _, .tt => false
  | _, .eq a b => a.readsAny || b.readsAny
  | _, .wellFormed _ => true
  | _, .not φ | _, .havoc φ | _, .anon _ φ | _, .grow φ | _, .all _ _ φ | _, .bind _ _ _ φ
  | _, .allocAll _ _ φ => φ.readsAny
  | _, .and φ ψ | _, .imp φ ψ => φ.readsAny || ψ.readsAny
  | _, .upd .. | _, .modal .. => true

/-- The quantifier-free formulas whose terms are in the fragment. -/
def _root_.Solidity.Fml.qfTarget {Γ : Ctx} (w : Waivers) : Fml C Γ → Bool
  | .tt => true
  | .eq a b => a.inTarget w (a.hashPair b) && b.inTarget w (a.hashPair b)
  | .wellFormed s => s.inTarget w false
  | .not φ => φ.qfTarget w
  | .and φ ψ | .imp φ ψ => φ.qfTarget w && ψ.qfTarget w
  | _ => false

/-- **A universal block of the array property fragment**, the levels of its
variables collected. -/
def _root_.Solidity.Fml.apfBlock (w : Waivers) : {Γ : Ctx} → List Nat → Fml C Γ → Bool
  | Γ, qs, .all _ _ φ => φ.apfBlock w (Γ.length :: qs)
  | _, qs, φ => φ.apfBody qs && φ.qfTarget w

/-- **The fragment, at a polarity** (`pol`: positive, the formula's own
`∀` a `∃` of its negation; `pres`: under a negative-position quantifier,
past which only Presburger quantifiers, reading nothing at their variable,
keep the negation in `∃*∀*`). -/
def _root_.Solidity.Fml.target (w : Waivers) : {Γ : Ctx} → Bool → Bool → Fml C Γ → Bool
  | _, _, _, .tt => true
  | _, _, _, .eq a b => a.inTarget w (a.hashPair b) && b.inTarget w (a.hashPair b)
  | _, _, _, .wellFormed s => s.inTarget w false
  | _, pol, n, .not φ => φ.target w (!pol) n
  | _, pol, n, .and φ ψ => φ.target w pol n && ψ.target w pol n
  | _, pol, n, .imp φ ψ => φ.target w (!pol) n && ψ.target w pol n
  | _, pol, n, .upd _ U φ => U.inTarget w && φ.target w pol n
  | _, _, _, .modal .. => false
  | Γ, pol, n, .all _ _ φ =>
    if !φ.readsAt [Γ.length] then φ.target w pol (n || !pol)
    else if n then false
    else if pol then φ.target w pol n
    else φ.apfBlock w [Γ.length]
  | Γ, pol, n, .bind _ _ t φ =>
    match t with
    | .val _ | .kint =>
      if !φ.readsAt [Γ.length] then φ.target w pol (n || !pol)
      else if n then false
      else if pol then φ.target w pol n
      else φ.apfBlock w [Γ.length]
    | .mem _ =>
      !φ.hasHash && if pol && !n then φ.target w pol n else !φ.readsAny && φ.target w pol true
    | _ => if pol && !n then φ.target w pol n else !φ.readsAny && φ.target w pol true
  | _, pol, n, .anon _ φ =>
    !φ.hasHash && if pol && !n then φ.target w pol n else !φ.readsAny && φ.target w pol true
  | _, pol, n, .havoc φ | _, pol, n, .grow φ | _, pol, n, .allocAll _ _ φ =>
    if pol && !n then φ.target w pol n else !φ.readsAny && φ.target w pol true

/-! ### Hashes as mapping keys

A mapping keyed by hashes (`mapping(string => V)`) compares its keys: two
hash keys compare as their inputs under the premise, a hash key and any
other key as a preimage question.  So a root with a hash key must have hash
keys only. -/

/-- The keys at the mappings at roots: the root and the key's hash kind,
where the premise settles it. -/
def _root_.Solidity.Tm.mapKeys {Γ : Ctx} : {s : Srt} → Tm C Γ s → List (Name × Option HashKind)
  | _, .netOf _ a | _, .app1 _ a => a.mapKeys
  | _, .app2 o x y =>
    (if o.isMapAt then (match x.rootNameD? with
      | some r => [(r, y.hashable?)]
      | none => [])
    else []) ++ x.mapKeys ++ y.mapKeys
  | _, .app3 _ x y z => x.mapKeys ++ y.mapKeys ++ z.mapKeys
  | _, _ => []

def _root_.Solidity.Rhs.mapKeys {Γ : Ctx} {t : LTy} : Rhs C Γ t → List (Name × Option HashKind)
  | .val a | .zint a => a.mapKeys
  | .path q => q.mapKeys
  | .mref i => i.mapKeys
  | .store s => s.mapKeys
  | .unset | .saveNet | .saveNetMt => []

def _root_.Solidity.UpdElem.mapKeys {Γ Δ : Ctx} : UpdElem C Γ Δ → List (Name × Option HashKind)
  | .local _ r => r.mapKeys
  | .storage s | .memory s => s.mapKeys
  | .selfBalance _ a | .setBalance a => a.mapKeys
  | .net r _ a | .pay r a | .netMt r a => r.mapKeys ++ a.mapKeys

def _root_.Solidity.Upd.mapKeys {Γ : Ctx} : {Δ : Ctx} → Upd C Γ Δ → List (Name × Option HashKind)
  | _, .nil => []
  | _, .snoc U e => U.mapKeys ++ e.mapKeys
  | _, .decl U _ r => U.mapKeys ++ r.mapKeys
  | _, .pop U _ | _, .drop U _ => U.mapKeys

def _root_.Solidity.Fml.mapKeys : {Γ : Ctx} → Fml C Γ → List (Name × Option HashKind)
  | _, .tt | _, .modal .. => []
  | _, .eq a b => a.mapKeys ++ b.mapKeys
  | _, .wellFormed s => s.mapKeys
  | _, .not φ | _, .havoc φ | _, .all _ _ φ | _, .bind _ _ _ φ | _, .anon _ φ | _, .allocAll _ _ φ
  | _, .grow φ => φ.mapKeys
  | _, .and φ ψ | _, .imp φ ψ => φ.mapKeys ++ ψ.mapKeys
  | _, .upd _ U φ => U.mapKeys ++ φ.mapKeys

/-- A root with a hash key has hash keys of that kind only. -/
def keysAgree (ks : List (Name × Option HashKind)) : Bool :=
  ks.all fun (r, h) => ks.all fun (r', h') => r' != r || h == h'

/-- **The fragment the user named**, on a scoped leaf: no program, every
operator admitted (`Waivers`), every quantifier over contents in the array
property fragment, every hash where the goal's premise settles it. -/
def _root_.Solidity.Fml.inTarget (w : Waivers) (φ : Fml C []) : Bool :=
  φ.target w true false && keysAgree φ.mapKeys

/-- **The open theorem**: on the fragment, `decideGoal` answers; its
verdicts are read under the goal's hash premise (`decideGoal_sound`,
`decideGoal_refutes`). -/
def DecisionTheorem (w : Waivers := {}) : Prop :=
  ∀ (C : Contract) (φ : Fml C []), φ.inTarget w = true → decideGoal φ ≠ .unknown

/-- info: 'Solidity.Decide.decideLeaf_sound' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms decideLeaf_sound

/-- info: 'Solidity.Decide.decideLeaf_refutes' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms decideLeaf_refutes

/-- info: 'Solidity.Decide.decideLeaf_complete' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms decideLeaf_complete

/-- info: 'Solidity.Decide.decideGoal_sound' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms decideGoal_sound

/-- info: 'Solidity.Decide.decideGoal_refutes' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms decideGoal_refutes

/-- info: 'Solidity.Decide.decideGoal_complete' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms decideGoal_complete

/-- info: 'Solidity.Decide.decideGoal_complete_hash' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms decideGoal_complete_hash

/-- info: 'Solidity.Decide.decideHash2_sound' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms decideHash2_sound

/-- info: 'Solidity.Decide.decideHash2_refutes' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms decideHash2_refutes

/-- info: 'Solidity.Decide.decideHash2_complete' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms decideHash2_complete

/-- info: 'Solidity.Fml.swPrefix_validH' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Fml.swPrefix_validH

/-- info: 'Solidity.Fml.swInst_refutes' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Fml.swInst_refutes

/-- info: 'Solidity.Fml.swPrefix_complete' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Fml.swPrefix_complete

/-- info: 'Solidity.Fml.swPrefix_exact' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Fml.swPrefix_exact

end Solidity.Decide
