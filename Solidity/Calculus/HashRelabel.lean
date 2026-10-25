import Solidity.Calculus.HashReduction

/-!
# Hash words relabeled (M7, plan step 7: completeness)

The swapped leaf (`Fml.swPrefix`, `Calculus/HashSwap.lean`) reads each fresh
string as a free word; its refutations (`Fml.swInst`,
`Calculus/HashReduction.lean`) fix the words to the hashes of a family of
strings.  Both read the words only as they compare: against each other
(`v == w`) and as keys of the roots their mappings are keyed by (`ids[v]`).
So a state refuting the free reading is relabeled into one refuting the
fixed one: the words moved to the family's, the keyed roots' entries moved
with them (`RelRL`), every other part of the state kept.

`ρ` maps each fixed word to the free word of its class, the free words
outside the fixed ones to a word `z` none of them is, and is the identity
elsewhere; so the only fixed key it sends to a free one is that free word's
own.  `Tm.rl` is the fragment: the words compared or as keys of the roots
`K`, the storage read only at a path (`find(storage, p)`) and written only
by a one-element update; `Fml.rl` adds the connectives, equations, `∀` and
the one-element updates.
-/

namespace Solidity.Decide

variable {C : Contract}

/-! ## The fragment -/

/-- Constants read alike in a relabeled state: no storage, no root keyed by
words. -/
def _root_.Solidity.Op0.rlOK (K : List Name) {s : Srt} : Op0 C s → Bool
  | .lit _ | .env _ | .zlit _ => true
  | .root r _ => !K.contains r
  | _ => false

/-- Unary symbols that read no storage. -/
def _root_.Solidity.Op1.rlOK {a s : Srt} : Op1 C a s → Bool
  | .unop .. | .net | .delValue | .field _ | .toInt => true
  | _ => false

/-- Binary symbols that read no storage but a path's index check. -/
def _root_.Solidity.Op2.rlOK {a b s : Srt} : Op2 C a b s → Bool
  | .binop .. | .at _ | .zbin .. | .zcmp .. => true
  | _ => false

def _root_.Solidity.Op3.rlOK {a b c s : Srt} : Op3 C a b c s → Bool
  | .ite | .modular _ => true
  | _ => false

/-- The storage itself. -/
def _root_.Solidity.Tm.isSt {Γ : Ctx} : {s : Srt} → Tm C Γ s → Bool
  | _, .app0 .storage => true
  | _, _ => false

/-- A root of `K`. -/
def _root_.Solidity.Tm.isKRoot (K : List Name) {Γ : Ctx} : {s : Srt} → Tm C Γ s → Bool
  | _, .app0 (.root r _) => K.contains r
  | _, _ => false

/-- A word local at a level of `V`. -/
def _root_.Solidity.Tm.isVVar (V : List Nat) {Γ : Ctx} : {s : Srt} → Tm C Γ s → Bool
  | _, .pvV i => V.contains i.level
  | _, _ => false

/-- An index into a root. -/
def _root_.Solidity.Op2.isAt {a b s : Srt} : Op2 C a b s → Bool
  | .at _ => true
  | _ => false

/-- **A key of a keyed root**: `r[v]`, `r` a root of `K`, `v` a word local
at a level of `V`. -/
def _root_.Solidity.Tm.kKey (V : List Nat) (K : List Name) {Γ : Ctx} : {s : Srt} → Tm C Γ s → Bool
  | _, .app2 o x y => o.isAt && x.isKRoot K && y.isVVar V
  | _, _ => false

/-- **The fragment's terms**: no word local of `V` but in a key of `K`, the
storage read only at a path, no root of `K` but in a key. -/
def _root_.Solidity.Tm.rl (V : List Nat) (K : List Name) {Γ : Ctx} : {s : Srt} → Tm C Γ s → Bool
  | _, .pvV i => !V.contains i.level
  | _, .netOf _ a => a.rl V K
  | _, .pvZ _ => true
  | _, .app0 o => o.rlOK K
  | _, .app1 o x => o.rlOK && x.rl V K
  | _, .app2 o x y =>
    match o with
    | .find => x.isSt && (y.kKey V K || y.rl V K)
    | _ => o.rlOK && x.rl V K && y.rl V K
  | _, .app3 o x y z => o.rlOK && x.rl V K && y.rl V K && z.rl V K
  | _, _ => false

/-- The roots of `K` map words to words. -/
def KTyped (C : Contract) (K : List Name) : Prop :=
  ∀ r ∈ K, C.rootType r = some (.ref (.mapping .uint (.prim .uint)))

theorem _root_.Solidity.Tm.kKey_view {V : List Nat} {K : List Name} (hK : KTyped C K) {Γ : Ctx}
    {p : PrimTy} (y : Tm C Γ (.path (.prim p))) (h : y.kKey V K = true) :
    ∃ (hp : p = .uint) (r : Name) (hr : C.rootType r = some (.ref (.mapping .uint (.prim .uint))))
      (i : Idx Γ (.val .uint)), hp ▸ y = .app2 (.at .map) (.app0 (.root r hr)) (.pvV i) ∧
      K.contains r = true ∧ V.contains i.level = true := by
  cases y with
  | app2 o x z =>
    simp only [Tm.kKey, Bool.and_eq_true] at h
    obtain ⟨⟨ho, hx⟩, hz⟩ := h
    cases o with
    | «at» it =>
      cases x with
      | app0 o' =>
        cases o' with
        | root r hr =>
          simp only [Tm.isKRoot] at hx
          have hr' := hK r (List.contains_iff_mem.1 hx)
          rw [hr'] at hr
          cases hr
          cases it with
          | map =>
            cases z with
            | pvV i =>
              simp only [Tm.isVVar] at hz
              exact ⟨rfl, r, hr', i, rfl, hx, hz⟩
            | _ => simp only [Tm.isVVar, Bool.false_eq_true] at hz
          | arr a => cases a
        | _ => simp only [Tm.isKRoot, Bool.false_eq_true] at hx
      | _ => simp only [Tm.isKRoot, Bool.false_eq_true] at hx
    | _ => simp only [Op2.isAt, Bool.false_eq_true] at ho
  | _ => simp only [Tm.kKey, Bool.false_eq_true] at h

/-! ## States relabeled -/

/-- Two global parts alike but for the storage and the heap. -/
structure GAgree0 (g g' : State C []) : Prop where
  net : g'.net = g.net
  bal : g'.selfBalance = g.selfBalance
  tx : g'.tx = g.tx

theorem GAgree0.envVal {g g' : State C []} (h : GAgree0 g g') (k : EnvKey) :
    g'.envVal k = g.envVal k := by
  cases k <;> simp only [State.envVal, h.tx, h.bal]

/-- **A state relabeled** (`τ''`, its words fixed) **and the state it came
from** (`τ'`, its words free): each key `x` of a root of `K` read at
`ρ x`, every other root alike, each word local of `V` sent by `ρ` to its
free word and the only fixed word sent there, every other local alike. -/
structure RelRL (ρ : PrimTy.uint.Denote → PrimTy.uint.Denote) (V : List Nat) (K : List Name)
    {Γ : Ctx} (τ'' τ' : State C Γ) : Prop where
  glob : GAgree0 τ'.glob τ''.glob
  stK : ∀ r ∈ K, ∀ (hr : C.rootType r = some (.ref (.mapping .uint (.prim .uint))))
    (x : PrimTy.uint.Denote),
    τ''.storage.find ⟨r, hr, .key x .nil⟩ = τ'.storage.find ⟨r, hr, .key (ρ x) .nil⟩
  stO : ∀ (r : Name) {T : Ty} (hr : C.rootType r = some T), r ∉ K →
    τ''.storage.get hr = τ'.storage.get hr
  locT : ∀ {t : LTy} (i : Idx Γ t), V.contains i.level = true → t = .val .uint
  locV : ∀ (i : Idx Γ (.val .uint)), V.contains i.level = true →
    ρ (τ''.getV i) = τ'.getV i ∧ ∀ x, ρ x = τ'.getV i → x = τ''.getV i
  locO : ∀ {t : LTy} (i : Idx Γ t), V.contains i.level = false → τ''.getV i = τ'.getV i

section Ops

variable {g g' : State C []}

theorem _root_.Solidity.Op0.eval_rl {K : List Name} {s : Srt} (o : Op0 C s) (ho : o.rlOK K = true)
    (h : GAgree0 g g') : o.eval g' = Srt.trO s (o.eval g) := by
  cases o with
  | env k => show some _ = some _; rw [h.envVal]
  | lit | zlit | root => rfl
  | _ => simp only [Op0.rlOK, Bool.false_eq_true] at ho

theorem _root_.Solidity.Op0.denote_rl {K : List Name} {s : Srt} (o : Op0 C s)
    (ho : o.rlOK K = true) (h : GAgree0 g g') : o.denote g' = o.denote g := by
  cases o with
  | env k => show some _ = some _; rw [h.envVal]
  | lit | zlit | root => rfl
  | _ => simp only [Op0.rlOK, Bool.false_eq_true] at ho

theorem _root_.Solidity.Op1.eval_rl {a s : Srt} (o : Op1 C a s) (ho : o.rlOK = true)
    (h : GAgree0 g g') (x : Option (a.Den C g.H)) :
    o.eval g' (Srt.trO a x) = Srt.trO s (o.eval g x) := by
  cases o with
  | net => simp only [Op1.eval_eq_evalM, Op1.evalM, Srt.trO, h.net]
  | unop | delValue | field | toInt => rfl
  | _ => simp only [Op1.rlOK, Bool.false_eq_true] at ho

theorem _root_.Solidity.Op1.denote_rl {a s : Srt} (o : Op1 C a s) (ho : o.rlOK = true)
    (h : GAgree0 g g') (d : a.TDen C) : o.denote g' d = o.denote g d := by
  cases o with
  | net => simp only [Op1.denote, h.net]
  | unop | delValue | field | toInt => rfl
  | _ => simp only [Op1.rlOK, Bool.false_eq_true] at ho

end Ops

/-- Paths and locations off the roots of `K`. -/
def NotK (K : List Name) {H : HTy} : (s : Srt) → Option (s.Den C H) → s.TDen C → Prop
  | .path _, x, d => (∀ p, x = some p → p.root ∉ K) ∧ (∀ p, d = SLoc.ref p → p.root ∉ K)
  | _, _, _ => True

/-! ## Reads at a key -/

section Keys

variable {Γ : Ctx}

theorem _root_.Solidity.Tm.isSt_eq {x : Tm C Γ .st} (h : x.isSt = true) : x = .app0 .storage := by
  cases x with
  | app0 o =>
    cases o with
    | storage => rfl
    | _ => simp only [Tm.isSt, Bool.false_eq_true] at h
  | _ => simp only [Tm.isSt, Bool.false_eq_true] at h

/-- A key of a root reads as the reference at the key. -/
theorem keyPath_eval (σ : State C Γ) (r : Name)
    (hr : C.rootType r = some (.ref (.mapping .uint (.prim .uint)))) (i : Idx Γ (.val .uint)) :
    (Tm.app2 (.at .map) (.app0 (.root r hr)) (.pvV i)).eval σ =
      some (⟨r, hr, .key (TEnv.get i σ.env) .nil⟩ : SRef C (.prim .uint)) := by
  show Op2.eval σ.glob (.at .map) (some (SRef.ofRoot r hr)) (some (TEnv.get i σ.env)) = _
  rw [Op2.eval_eq_evalM]
  simp only [Op2.evalM, Storage.atT, Storage.checkIndex, Storage.find, Option.bind_eq_bind,
    Option.bind_some, SRef.ofRoot]
  rw [SVal.find_eq_findM, SVal.findM_nil']
  simp only [Option.bind_some]
  with_unfolding_all rfl

theorem keyPath_denote (σ : State C Γ) (r : Name)
    (hr : C.rootType r = some (.ref (.mapping .uint (.prim .uint)))) (i : Idx Γ (.val .uint)) :
    (Tm.app2 (.at .map) (.app0 (.root r hr)) (.pvV i)).denote σ =
      SLoc.ref (⟨r, hr, .key (TEnv.get i σ.env) .nil⟩ : SRef C (.prim .uint)) := by
  simp only [Tm.denote, Op2.denote, Op0.denote]
  with_unfolding_all rfl

theorem find_eval (σ : State C Γ) {P : PrimTy} (y : Tm C Γ (.path (.prim P))) :
    (Tm.app2 .find (.app0 .storage) y).eval σ =
      (y.eval σ).bind fun p => (σ.storage.find p).map SVal.view := by
  show Op2.eval σ.glob .find (some σ.storage) (y.eval σ) = _
  rw [Op2.eval_eq_evalM]
  cases y.eval σ with
  | none => rfl
  | some p =>
    simp only [Op2.evalM, Option.bind_eq_bind, Option.bind_some]
    cases σ.storage.find p <;> rfl

theorem find_denote (σ : State C Γ) {P : PrimTy} (y : Tm C Γ (.path (.prim P))) :
    (Tm.app2 .find (.app0 .storage) y).denote σ = some (σ.storage.obs.word (y.denote σ)) := rfl

theorem obs_word_key (st : Storage C) {P : PrimTy} (r : Name)
    (hr : C.rootType r = some (.ref (.mapping .uint (.prim P)))) (x : PrimTy.uint.Denote) :
    st.obs.word (.ref ⟨r, hr, .key x .nil⟩) = SVal.wordOf (st.find ⟨r, hr, .key x .nil⟩) := by
  show SVal.wordOf ((st.get hr).findM _) = SVal.wordOf ((st.get hr).find _)
  rw [SVal.find_eq_findM]

end Keys

/-! ## Writes -/

section Writes

/-- A write is a function of the root it writes. -/
def writeF {T U : Ty} (fv : SVal T) (path : Path T U) (new : SVal U) : Option (SVal T) :=
  if new.isPrim then fv.save path new else (fv.find path).bind fun c => fv.save path (c.overlay new)

theorem Storage.write_eq (st : Storage C) {U : Ty} (p : SRef C U) (v : SVal U) :
    st.write p v = (writeF (st.get p.hroot) p.path v).map (st.set p.hroot) := by
  unfold Storage.write writeF Storage.save Storage.find
  split
  · simp only [Option.bind_eq_bind]
    cases (st.get p.hroot).save p.path v <;> rfl
  · simp only [Option.bind_eq_bind]
    cases (st.get p.hroot).find p.path with
    | none => rfl
    | some c =>
      simp only [Option.bind_some]
      cases (st.get p.hroot).save p.path (c.overlay v) <;> rfl

/-- **A word written at a key of a root**: there, and nowhere else. -/
theorem Storage.write_key (st : Storage C) (r : Name)
    (hr : C.rootType r = some (.ref (.mapping .uint (.prim .uint)))) (x w : PrimTy.uint.Denote) :
    ∃ st₁, st.write ⟨r, hr, .key x .nil⟩ (.prim w) = some st₁ ∧
      (∀ y, st₁.find ⟨r, hr, .key y .nil⟩ =
        if y = x then some (.prim w) else st.find ⟨r, hr, .key y .nil⟩) ∧
      (∀ (r₂ : Name) {T : Ty} (h₂ : C.rootType r₂ = some T), r ≠ r₂ → st₁.get h₂ = st.get h₂) := by
  have hs : ∃ fv, (st.get hr).save (.key x .nil) (.prim w) = some fv := by
    rw [SVal.save_eq_saveM]
    generalize st.get hr = m
    cases m with
    | map es d =>
      simp only [SVal.saveM]
      split <;> exact ⟨_, rfl⟩
  obtain ⟨fv, hfv⟩ := hs
  refine ⟨st.set hr fv, ?_, ?_, ?_⟩
  · rw [Storage.write_eq]
    show (writeF (st.get hr) (.key x .nil) (.prim w)).map (st.set hr) = _
    unfold writeF
    rw [if_pos (show (SVal.prim w).isPrim = true from rfl), hfv]
    rfl
  · intro y
    show ((st.set hr fv).get hr).find (.key y .nil) = _
    rw [SFields.get_set_same]
    by_cases hy : y = x
    · subst hy
      rw [if_pos rfl]
      exact SVal.find_save_same _ _ _ hfv
    · rw [if_neg hy]
      rw [SVal.save_eq_saveM] at hfv
      rw [SVal.find_eq_findM, SVal.findM_saveM_diverges (Path.Diverges.key .nil .nil (Ne.symm hy))
        _ _ hfv]
      show _ = (st.get hr).find _
      rw [SVal.find_eq_findM]
  · intro r₂ T h₂ hne
    exact SFields.get_set_ne st hr h₂ hne fv

end Writes

section Terms

variable {ρ : PrimTy.uint.Denote → PrimTy.uint.Denote} {V : List Nat} {K : List Name} {Γ : Ctx}
  {τ'' τ' : State C Γ}

theorem RelRL.find_notK (h : RelRL ρ V K τ'' τ') {U : Ty} (p : SRef C U) (hp : p.root ∉ K) :
    τ''.storage.find p = τ'.storage.find p := by
  show (τ''.storage.get p.hroot).find p.path = (τ'.storage.get p.hroot).find p.path
  rw [h.stO p.root p.hroot hp]

theorem RelRL.word_notK (h : RelRL ρ V K τ'' τ') {P : PrimTy} (d : SLoc C (.prim P))
    (hd : ∀ p, d = SLoc.ref p → p.root ∉ K) : τ''.storage.obs.word d = τ'.storage.obs.word d := by
  cases d with
  | ref p =>
    show (τ''.storage.get p.hroot).obs.word p.path = (τ'.storage.get p.hroot).obs.word p.path
    rw [h.stO p.root p.hroot (hd p rfl)]
  | dangling => rfl

/-- **A term of the fragment reads alike in a relabeled state.** -/
theorem _root_.Solidity.Tm.rl_reads (hK : KTyped C K) (h : RelRL ρ V K τ'' τ') {s : Srt}
    (t : Tm C Γ s)
    (ht : t.rl V K = true) :
    t.eval τ'' = Srt.trO s (t.eval τ') ∧ t.denote τ'' = t.denote τ' ∧
      NotK K s (t.eval τ') (t.denote τ') := by
  induction t with
  | pvV i =>
    simp only [Tm.rl, Bool.not_eq_true'] at ht
    have e := h.locO i ht
    exact ⟨congrArg some e, congrArg some e, trivial⟩
  | pvZ i =>
    have hl : V.contains i.level = false := by
      cases hv : V.contains i.level
      · rfl
      · cases h.locT i hv
    have e := h.locO i hl
    exact ⟨congrArg some e, congrArg some e, trivial⟩
  | netOf i a iha =>
    simp only [Tm.rl] at ht
    have hl : V.contains i.level = false := by
      cases hv : V.contains i.level
      · rfl
      · cases h.locT i hv
    have e : TEnv.get i τ''.env = TEnv.get i τ'.env := h.locO i hl
    obtain ⟨ha1, ha2, -⟩ := iha ht
    refine ⟨?_, ?_, trivial⟩
    · show (a.eval τ'').bind _ = (a.eval τ').bind _
      rw [ha1, e]
      rfl
    · show (a.denote τ'').map _ = (a.denote τ').map _
      rw [ha2, e]
  | app0 o =>
    simp only [Tm.rl] at ht
    refine ⟨Op0.eval_rl o ht h.glob, Op0.denote_rl o ht h.glob, ?_⟩
    cases o with
    | root r hr =>
      simp only [Op0.rlOK, Bool.not_eq_true'] at ht
      have hn : r ∉ K := fun hm => by rw [List.contains_iff_mem.2 hm] at ht; cases ht
      exact ⟨fun p e => by cases e; exact hn, fun p e => by cases e; exact hn⟩
    | _ => trivial
  | app1 o x ihx =>
    simp only [Tm.rl, Bool.and_eq_true] at ht
    obtain ⟨hx1, hx2, hx3⟩ := ihx ht.2
    refine ⟨?_, ?_, ?_⟩
    · show o.eval τ''.glob (x.eval τ'') = _
      rw [hx1]
      exact Op1.eval_rl o ht.1 h.glob _
    · show o.denote τ''.glob (x.denote τ'') = o.denote τ'.glob (x.denote τ')
      rw [hx2]
      exact Op1.denote_rl o ht.1 h.glob _
    · cases o with
      | field hf =>
        refine ⟨fun p e => ?_, fun p e => ?_⟩
        · show p.root ∉ K
          change Option.map (·.field hf) (x.eval τ') = some p at e
          obtain ⟨q, hq, rfl⟩ := Option.map_eq_some_iff.1 e
          exact hx3.1 q hq
        · change ObsLoc.app (x.denote τ') (.field hf .nil) = SLoc.ref p at e
          revert e
          cases hd : x.denote τ' with
          | ref q => intro e; cases e; exact hx3.2 q hd
          | dangling => intro e; cases e
      | _ => first | trivial | simp only [Op1.rlOK, Bool.false_eq_true, false_and] at ht
  | app2 o x y ihx ihy =>
    cases o with
    | find =>
      simp only [Tm.rl, Bool.and_eq_true, Bool.or_eq_true] at ht
      obtain ⟨hx, hy⟩ := ht
      have hx' := Tm.isSt_eq hx
      subst hx'
      refine ⟨?_, ?_, trivial⟩
      · rcases hy with hy | hy
        · obtain ⟨rfl, r, hr, i, rfl, hrK, hi⟩ := Tm.kKey_view hK y hy
          rw [find_eval, find_eval, keyPath_eval, keyPath_eval]
          simp only [Option.bind_some]
          have e := h.stK r (List.contains_iff_mem.1 hrK) hr (TEnv.get i τ''.env)
          rw [e, show ρ (TEnv.get i τ''.env) = TEnv.get i τ'.env from (h.locV i hi).1]
          rfl
        · obtain ⟨hy1, -, hy3⟩ := ihy hy
          rw [find_eval, find_eval, hy1]
          show ((y.eval τ').bind _) = (y.eval τ').bind _
          cases he : y.eval τ' with
          | none => rfl
          | some p =>
            simp only [Option.bind_some]
            rw [h.find_notK p (hy3.1 p he)]
      · rw [find_denote, find_denote]
        rcases hy with hy | hy
        · obtain ⟨rfl, r, hr, i, rfl, hrK, hi⟩ := Tm.kKey_view hK y hy
          rw [keyPath_denote, keyPath_denote, obs_word_key, obs_word_key]
          have e := h.stK r (List.contains_iff_mem.1 hrK) hr (TEnv.get i τ''.env)
          rw [e, show ρ (TEnv.get i τ''.env) = TEnv.get i τ'.env from (h.locV i hi).1]
        · obtain ⟨-, hy2, hy3⟩ := ihy hy
          rw [hy2, h.word_notK _ hy3.2]
    | «at» it =>
      simp only [Tm.rl, Op2.rlOK, Bool.true_and, Bool.and_eq_true] at ht
      obtain ⟨hx1, hx2, hx3⟩ := ihx ht.1
      obtain ⟨hy1, hy2, -⟩ := ihy ht.2
      refine ⟨?_, ?_, ?_⟩
      · show Op2.eval τ''.glob (.at it) (x.eval τ'') (y.eval τ'') = _
        rw [hx1, hy1, Op2.eval_eq_evalM]
        show _ = Op2.evalM τ'.glob (.at it) (x.eval τ') (y.eval τ')
        cases hp : x.eval τ' with
        | none => rfl
        | some p =>
          cases y.eval τ' with
          | none => rfl
          | some k =>
            simp only [Op2.evalM, Srt.trO, Option.bind_eq_bind, Option.bind_some, Storage.atT,
              Storage.checkIndex]
            rw [show τ''.glob.storage.find p = τ'.glob.storage.find p from h.find_notK p (hx3.1 p hp)]
      · show Op2.denote τ''.glob (.at it) _ _ (x.denote τ'') (y.denote τ'') =
          Op2.denote τ'.glob (.at it) _ _ (x.denote τ') (y.denote τ')
        rw [hx2, hy2]
        rfl
      · refine ⟨fun q e => ?_, fun q e => ?_⟩
        · rw [Tm.eval_app2, Op2.eval_eq_evalM] at e
          revert e
          cases hp : x.eval τ' with
          | none => intro e; cases e
          | some p =>
            cases y.eval τ' with
            | none => intro e; cases e
            | some k =>
              simp only [Op2.evalM, Option.bind_eq_bind, Option.bind_some, Storage.atT]
              intro e
              obtain ⟨_, -, e⟩ := Option.bind_eq_some_iff.1 e
              cases e
              exact hx3.1 p hp
        · change ObsLoc.app (x.denote τ') _ = SLoc.ref q at e
          revert e
          cases hd : x.denote τ' with
          | ref p => intro e; cases e; exact hx3.2 p hd
          | dangling => intro e; cases e
    | binop op hop =>
      simp only [Tm.rl, Op2.rlOK, Bool.true_and, Bool.and_eq_true] at ht
      obtain ⟨hx1, hx2, -⟩ := ihx ht.1
      obtain ⟨hy1, hy2, -⟩ := ihy ht.2
      refine ⟨?_, ?_, trivial⟩
      · show Op2.eval τ''.glob (.binop op hop) (x.eval τ'') (y.eval τ'') = _
        rw [hx1, hy1]; rfl
      · show Op2.denote τ''.glob (.binop op hop) _ _ (x.denote τ'') (y.denote τ'') = _
        rw [hx2, hy2]; rfl
    | zbin op hop =>
      simp only [Tm.rl, Op2.rlOK, Bool.true_and, Bool.and_eq_true] at ht
      obtain ⟨hx1, hx2, -⟩ := ihx ht.1
      obtain ⟨hy1, hy2, -⟩ := ihy ht.2
      refine ⟨?_, ?_, trivial⟩
      · show Op2.eval τ''.glob (.zbin op hop) (x.eval τ'') (y.eval τ'') = _
        rw [hx1, hy1]; rfl
      · show Op2.denote τ''.glob (.zbin op hop) _ _ (x.denote τ'') (y.denote τ'') = _
        rw [hx2, hy2]; rfl
    | zcmp op hop =>
      simp only [Tm.rl, Op2.rlOK, Bool.true_and, Bool.and_eq_true] at ht
      obtain ⟨hx1, hx2, -⟩ := ihx ht.1
      obtain ⟨hy1, hy2, -⟩ := ihy ht.2
      refine ⟨?_, ?_, trivial⟩
      · show Op2.eval τ''.glob (.zcmp op hop) (x.eval τ'') (y.eval τ'') = _
        rw [hx1, hy1]; rfl
      · show Op2.denote τ''.glob (.zcmp op hop) _ _ (x.denote τ'') (y.denote τ'') = _
        rw [hx2, hy2]; rfl
    | _ => simp only [Tm.rl, Op2.rlOK, Bool.false_eq_true, Bool.false_and] at ht
  | app3 o x y z ihx ihy ihz =>
    simp only [Tm.rl, Bool.and_eq_true] at ht
    obtain ⟨⟨⟨ho, hx⟩, hy⟩, hz⟩ := ht
    obtain ⟨hx1, hx2, -⟩ := ihx hx
    obtain ⟨hy1, hy2, -⟩ := ihy hy
    obtain ⟨hz1, hz2, -⟩ := ihz hz
    cases o with
    | ite =>
      refine ⟨?_, ?_, trivial⟩
      · show Op3.eval τ''.glob .ite (x.eval τ'') (y.eval τ'') (z.eval τ'') = _
        rw [hx1, hy1, hz1]; rfl
      · show Op3.denote .ite (x.denote τ'') (y.denote τ'') (z.denote τ'') = _
        rw [hx2, hy2, hz2]; rfl
    | modular op =>
      refine ⟨?_, ?_, trivial⟩
      · show Op3.eval τ''.glob (.modular op) (x.eval τ'') (y.eval τ'') (z.eval τ'') = _
        rw [hx1, hy1, hz1]; rfl
      · show Op3.denote (.modular op) (x.denote τ'') (y.denote τ'') (z.denote τ'') = _
        rw [hx2, hy2, hz2]; rfl
    | _ => simp only [Op3.rlOK, Bool.false_eq_true] at ho
  | pvP | pvS | pvI => simp only [Tm.rl, Bool.false_eq_true] at ht

end Terms

/-! ## Formulas -/

def _root_.Solidity.Op3.isSave {a b c s : Srt} : Op3 C a b c s → Bool
  | .save => true
  | _ => false

def _root_.Solidity.Op1.isSval {a s : Srt} : Op1 C a s → Bool
  | .sval => true
  | _ => false

/-- A word stored: `sval(w)`. -/
def _root_.Solidity.Tm.rlSv (V : List Nat) (K : List Name) {Γ : Ctx} : {s : Srt} → Tm C Γ s → Bool
  | _, .app1 o w => o.isSval && w.rl V K
  | _, _ => false

/-- **A storage write of the fragment**: `save(storage, p, sval(w))`. -/
def _root_.Solidity.Tm.rlSave (V : List Nat) (K : List Name) {Γ : Ctx} :
    {s : Srt} → Tm C Γ s → Bool
  | _, .app3 o x y z => o.isSave && x.isSt && (y.kKey V K || y.rl V K) && z.rlSv V K
  | _, _ => false

def _root_.Solidity.Rhs.rlV (V : List Nat) (K : List Name) {Γ : Ctx} {t : LTy} : Rhs C Γ t → Bool
  | .val t => t.rl V K
  | _ => false

def _root_.Solidity.UpdElem.rl1 (V : List Nat) (K : List Name) {Γ : Ctx} : UpdElem C Γ Γ → Bool
  | .storage s => s.rlSave V K
  | .local i r => !V.contains i.level && r.rlV V K
  | _ => false

/-- A one-element update of the fragment. -/
def _root_.Solidity.Upd.rl1 (V : List Nat) (K : List Name) {Γ : Ctx} :
    {Δ : Ctx} → Upd C Γ Δ → Bool
  | _, .snoc .nil e => e.rl1 V K
  | _, .decl .nil _ r => r.rlV V K
  | _, _ => false

/-- **The fragment's formulas**: equations of its terms or of two word
locals of `V`, the connectives, `∀`, and one-element updates with no push. -/
def _root_.Solidity.Fml.rl (V : List Nat) (K : List Name) : {Γ : Ctx} → Fml C Γ → Bool
  | _, .tt => true
  | _, .eq a b => (a.rl V K && b.rl V K) || (a.isVVar V && b.isVVar V)
  | _, .not φ => Fml.rl V K φ
  | _, .and φ ψ => Fml.rl V K φ && Fml.rl V K ψ
  | _, .imp φ ψ => Fml.rl V K φ && Fml.rl V K ψ
  | _, .all _ _ φ => Fml.rl V K φ
  | _, .upd _ U φ => U.pushFree && U.rl1 V K && Fml.rl V K φ
  | _, _ => false

section Formulas

variable {ρ : PrimTy.uint.Denote → PrimTy.uint.Denote} {V : List Nat} {K : List Name}

theorem _root_.Solidity.Idx.level_here {Γ : Ctx} {t : LTy} :
    (Idx.here : Idx (t :: Γ) t).level = Γ.length := by
  simp only [Idx.level, Idx.toNat, List.length_cons]
  omega

theorem _root_.Solidity.Idx.level_there {Γ : Ctx} {t u : LTy} (j : Idx Γ t) :
    (Idx.there j : Idx (u :: Γ) t).level = j.level := by
  have := j.toNat_lt
  simp only [Idx.level, Idx.toNat, List.length_cons]
  omega

theorem _root_.Solidity.Tm.isVVar_view {Γ : Ctx} {p : PrimTy} {t : Tm C Γ (.val p)}
    (h : t.isVVar V = true) : ∃ i : Idx Γ (.val p), t = .pvV i ∧ V.contains i.level = true := by
  cases t with
  | pvV i => exact ⟨i, rfl, h⟩
  | _ => simp only [Tm.isVVar, Bool.false_eq_true] at h

variable {Γ : Ctx} {τ'' τ' : State C Γ}

theorem RelRL.push (h : RelRL ρ V K τ'' τ') (hV : ∀ l ∈ V, l < Γ.length) {p : PrimTy}
    (v : p.Denote) : RelRL ρ V K (τ''.push (t := .val p) v) (τ'.push (t := .val p) v) := by
  have hn : V.contains Γ.length = false := by
    cases hc : V.contains Γ.length
    · rfl
    · exact absurd (hV _ (List.contains_iff_mem.1 hc)) (Nat.lt_irrefl _)
  refine ⟨h.glob, h.stK, h.stO, fun {t} i hi => ?_, fun i hi => ?_, fun {t} i hi => ?_⟩
  · cases i with
    | here => rw [Idx.level_here, hn] at hi; cases hi
    | there j => rw [Idx.level_there] at hi; exact h.locT j hi
  · cases i with
    | here => rw [Idx.level_here, hn] at hi; cases hi
    | there j => rw [Idx.level_there] at hi; exact h.locV j hi
  · cases i with
    | here => rfl
    | there j => rw [Idx.level_there] at hi; exact h.locO j hi

theorem RelRL.setLocal (h : RelRL ρ V K τ'' τ') {p : PrimTy} (i : Idx Γ (.val p))
    (hi : V.contains i.level = false) (v : p.Denote) :
    RelRL ρ V K (τ''.setLocal i v) (τ'.setLocal i v) := by
  refine ⟨h.glob, h.stK, h.stO, fun {t} j hj => h.locT j hj, fun j hj => ?_, fun {t} j hj => ?_⟩
  · have hij : i.toNat ≠ j.toNat := by
      intro e
      have ht := Idx.ty_eq_of_toNat e
      cases ht
      obtain rfl := Idx.toNat_inj i j e
      rw [hi] at hj; cases hj
    rw [State.getV_setLocal_ne _ _ _ hij, State.getV_setLocal_ne _ _ _ hij]
    exact h.locV j hj
  · by_cases hij : i.toNat = j.toNat
    · obtain rfl := Idx.ty_eq_of_toNat hij
      obtain rfl := Idx.toNat_inj i j hij
      rw [State.getV_setLocal_same, State.getV_setLocal_same]
      rfl
    · rw [State.getV_setLocal_ne _ _ _ hij, State.getV_setLocal_ne _ _ _ hij]
      exact h.locO j hj

theorem save_eval (σ : State C Γ) {P : PrimTy} (y : Tm C Γ (.path (.prim P)))
    (w : Tm C Γ (.val P)) :
    (Tm.app3 .save (.app0 .storage) y (.app1 .sval w)).eval σ =
      (y.eval σ).bind fun p => (w.eval σ).bind fun v => σ.storage.write p (.prim v) := by
  show Op3.eval σ.glob .save (some σ.storage) (y.eval σ) ((w.eval σ).map SVal.prim) = _
  rw [Op3.eval_eq_evalM]
  cases y.eval σ with
  | none => rfl
  | some p =>
    cases w.eval σ with
    | none => rfl
    | some v => rfl

/-- A write at a key of a keyed root, relabeled. -/
theorem RelRL.writeKey (h : RelRL ρ V K τ'' τ') (r : Name) (hrK : r ∈ K)
    (hr : C.rootType r = some (.ref (.mapping .uint (.prim .uint)))) (i : Idx Γ (.val .uint))
    (hi : V.contains i.level = true) (w : PrimTy.uint.Denote) :
    ∃ st₁ st₂, τ''.storage.write ⟨r, hr, .key (TEnv.get i τ''.env) .nil⟩ (.prim w) = some st₁ ∧
      τ'.storage.write ⟨r, hr, .key (TEnv.get i τ'.env) .nil⟩ (.prim w) = some st₂ ∧
      RelRL ρ V K (τ''.withStorage st₁) (τ'.withStorage st₂) := by
  obtain ⟨st₁, h₁, hf₁, hg₁⟩ := Storage.write_key τ''.storage r hr (TEnv.get i τ''.env) w
  obtain ⟨st₂, h₂, hf₂, hg₂⟩ := Storage.write_key τ'.storage r hr (TEnv.get i τ'.env) w
  refine ⟨st₁, st₂, h₁, h₂, ⟨⟨h.glob.net, h.glob.bal, h.glob.tx⟩, ?_, ?_, h.locT, h.locV, h.locO⟩⟩
  · intro r' hr'K hr' x
    by_cases e : r' = r
    · subst e
      show st₁.find _ = st₂.find _
      rw [hf₁, hf₂]
      have hv := h.locV i hi
      have hx : (x = TEnv.get i τ''.env) ↔ (ρ x = TEnv.get i τ'.env) := by
        constructor
        · intro e; rw [e]; exact hv.1
        · exact hv.2 x
      by_cases ex : x = TEnv.get i τ''.env
      · rw [if_pos ex, if_pos (hx.1 ex)]
      · rw [if_neg ex, if_neg (fun e => ex (hx.2 e))]
        exact h.stK r' hr'K hr' x
    · show (st₁.get hr').find _ = (st₂.get hr').find _
      rw [hg₁ r' hr' (Ne.symm e), hg₂ r' hr' (Ne.symm e)]
      exact h.stK r' hr'K hr' x
  · intro r₂ T h₂' hn
    have hne : r ≠ r₂ := fun e => hn (e ▸ hrK)
    show st₁.get h₂' = st₂.get h₂'
    rw [hg₁ r₂ h₂' hne, hg₂ r₂ h₂' hne]
    exact h.stO r₂ h₂' hn

/-- A write off the keyed roots, relabeled. -/
theorem RelRL.writeOff (h : RelRL ρ V K τ'' τ') {U : Ty} (p : SRef C U) (hp : p.root ∉ K)
    (v : SVal U) :
    (τ''.storage.write p v).isSome = (τ'.storage.write p v).isSome ∧
      ∀ st₁ st₂, τ''.storage.write p v = some st₁ → τ'.storage.write p v = some st₂ →
        RelRL ρ V K (τ''.withStorage st₁) (τ'.withStorage st₂) := by
  rw [Storage.write_eq, Storage.write_eq, h.stO p.root p.hroot hp]
  refine ⟨by cases writeF (τ'.storage.get p.hroot) p.path v <;> rfl, fun st₁ st₂ e₁ e₂ => ?_⟩
  cases hw : writeF (τ'.storage.get p.hroot) p.path v with
  | none => rw [hw] at e₁; cases e₁
  | some fv =>
    rw [hw] at e₁ e₂
    cases e₁
    cases e₂
    refine ⟨⟨h.glob.net, h.glob.bal, h.glob.tx⟩, ?_, ?_, h.locT, h.locV, h.locO⟩
    · intro r' hr'K hr' x
      have hne : p.root ≠ r' := fun e => hp (e ▸ hr'K)
      show ((τ''.storage.set p.hroot fv).get hr').find _ = ((τ'.storage.set p.hroot fv).get hr').find _
      rw [SFields.get_set_ne _ _ _ hne, SFields.get_set_ne _ _ _ hne]
      exact h.stK r' hr'K hr' x
    · intro r₂ T h₂' hn
      show (τ''.storage.set p.hroot fv).get h₂' = (τ'.storage.set p.hroot fv).get h₂'
      by_cases e : p.root = r₂
      · rcases p with ⟨r₀, hr₀, path⟩
        simp only at e
        subst e
        obtain rfl : _ = T := Option.some.inj (hr₀.symm.trans h₂')
        rw [SFields.get_set_same, SFields.get_set_same]
      · rw [SFields.get_set_ne _ _ _ e, SFields.get_set_ne _ _ _ e]
        exact h.stO r₂ h₂' hn

theorem _root_.Solidity.Tm.rlSave_view {V : List Nat} {K : List Name} {Γ : Ctx} {s : Tm C Γ .st}
    (h : s.rlSave V K = true) :
    ∃ (P : PrimTy) (y : Tm C Γ (.path (.prim P))) (w : Tm C Γ (.val P)),
      s = .app3 .save (.app0 .storage) y (.app1 .sval w) ∧ (y.kKey V K = true ∨ y.rl V K = true) ∧
        w.rl V K = true := by
  cases s with
  | app3 o x y z =>
    simp only [Tm.rlSave, Bool.and_eq_true, Bool.or_eq_true] at h
    obtain ⟨⟨⟨ho, hx⟩, hy⟩, hz⟩ := h
    cases o with
    | save =>
      have hx' := Tm.isSt_eq hx
      subst hx'
      cases z with
      | app1 o' w =>
        simp only [Tm.rlSv, Bool.and_eq_true] at hz
        cases o' with
        | sval => exact ⟨_, y, w, rfl, hy, hz.2⟩
        | _ => simp only [Op1.isSval, Bool.false_eq_true, false_and] at hz
      | _ => simp only [Tm.rlSv, Bool.false_eq_true] at hz
    | _ => simp only [Op3.isSave, Bool.false_eq_true] at ho
  | _ => simp only [Tm.rlSave, Bool.false_eq_true] at h

/-- **A formula of the fragment holds alike in a relabeled state.** -/
theorem _root_.Solidity.Fml.rl_holds {ρ : PrimTy.uint.Denote → PrimTy.uint.Denote} {V : List Nat}
    {K : List Name} (hK : KTyped C K) {Γ : Ctx} (φ : Fml C Γ) (hφ : φ.rl V K = true) :
    ∀ (τ'' τ' : State C Γ), (∀ l ∈ V, l < Γ.length) → RelRL ρ V K τ'' τ' →
      (holds τ'' φ ↔ holds τ' φ) := by
  induction φ with
  | tt => intro _ _ _ _; exact Iff.rfl
  | eq a b =>
    intro τ'' τ' hV h
    simp only [Fml.rl, Bool.or_eq_true, Bool.and_eq_true] at hφ
    rcases hφ with ⟨ha, hb⟩ | ⟨ha, hb⟩
    · rw [holds_eq, holds_eq, (Tm.rl_reads hK h a ha).2.1, (Tm.rl_reads hK h b hb).2.1]
    · obtain ⟨i, rfl, hi⟩ := Tm.isVVar_view ha
      obtain ⟨j, rfl, hj⟩ := Tm.isVVar_view hb
      have ht := h.locT i hi
      cases ht
      rw [holds_eq, holds_eq]
      have hvi := h.locV i hi
      have hvj := h.locV j hj
      show some (TEnv.get i τ''.env) = some (TEnv.get j τ''.env) ↔
        some (TEnv.get i τ'.env) = some (TEnv.get j τ'.env)
      have ei : ρ (TEnv.get i τ''.env) = TEnv.get i τ'.env := hvi.1
      have ej : ρ (TEnv.get j τ''.env) = TEnv.get j τ'.env := hvj.1
      constructor
      · intro e
        rw [← ei, ← ej, Option.some.inj e]
      · intro e
        exact congrArg some (hvj.2 _ (ei.trans (Option.some.inj e)))
  | wellFormed => intro _ _ _ _; simp only [Fml.rl, Bool.false_eq_true] at hφ
  | not φ ih =>
    intro τ'' τ' hV h
    exact not_congr (ih hφ τ'' τ' hV h)
  | and φ ψ ihφ ihψ =>
    intro τ'' τ' hV h
    simp only [Fml.rl, Bool.and_eq_true] at hφ
    exact and_congr (ihφ hφ.1 τ'' τ' hV h) (ihψ hφ.2 τ'' τ' hV h)
  | imp φ ψ ihφ ihψ =>
    intro τ'' τ' hV h
    simp only [Fml.rl, Bool.and_eq_true] at hφ
    exact imp_congr (ihφ hφ.1 τ'' τ' hV h) (ihψ hφ.2 τ'' τ' hV h)
  | all x p φ ih =>
    intro τ'' τ' hV h
    exact forall_congr' fun v => ih hφ _ _ (fun l hl => Nat.lt_succ_of_lt (hV l hl)) (h.push hV v)
  | upd m U φ ih =>
    intro τ'' τ' hV h
    simp only [Fml.rl, Bool.and_eq_true] at hφ
    obtain ⟨⟨hpf, hU⟩, hφ⟩ := hφ
    show U.afterT m τ'' (holds · φ) ↔ U.afterT m τ' (holds · φ)
    cases U with
    | snoc U₀ e₀ =>
      cases U₀ with
      | nil =>
        cases e₀ with
        | storage s =>
          have hs : s.rlSave V K = true := hU
          rw [Upd.afterT_storage1 m τ'' s hpf, Upd.afterT_storage1 m τ' s hpf]
          obtain ⟨P, y, w, rfl, hy, hw⟩ := Tm.rlSave_view hs
          rw [save_eval, save_eval]
          have hw' : w.eval τ'' = w.eval τ' := (Tm.rl_reads hK h w hw).1
          rcases hy with hy | hy
          · obtain ⟨rfl, r, hr, i, rfl, hrK, hi⟩ := Tm.kKey_view hK y hy
            rw [keyPath_eval, keyPath_eval, hw']
            simp only [Option.bind_some]
            cases w.eval τ' with
            | none => exact Iff.rfl
            | some v =>
              simp only [Option.bind_some]
              obtain ⟨st₁, st₂, h₁, h₂, hrel⟩ := h.writeKey r (List.contains_iff_mem.1 hrK) hr i hi v
              rw [h₁, h₂]
              exact ih hφ _ _ hV hrel
          · obtain ⟨hy1, -, hy3⟩ := Tm.rl_reads hK h y hy
            rw [hy1, hw']
            simp only [Srt.trO]
            cases hp : y.eval τ' with
            | none => exact Iff.rfl
            | some p =>
              cases w.eval τ' with
              | none => exact Iff.rfl
              | some v =>
                simp only [Option.bind_some]
                obtain ⟨hsome, hrel⟩ := h.writeOff p (hy3.1 p hp) (.prim v)
                cases h₂ : τ'.storage.write p (.prim v) with
                | none =>
                  rw [h₂] at hsome
                  cases h₁ : τ''.storage.write p (.prim v) with
                  | none => exact Iff.rfl
                  | some _ => rw [h₁] at hsome; cases hsome
                | some st₂ =>
                  rw [h₂] at hsome
                  cases h₁ : τ''.storage.write p (.prim v) with
                  | none => rw [h₁] at hsome; cases hsome
                  | some st₁ => exact ih hφ _ _ hV (hrel st₁ st₂ h₁ h₂)
        | «local» i r =>
          cases r with
          | val t =>
            have hU' : (!V.contains i.level && t.rl V K) = true := hU
            simp only [Bool.and_eq_true, Bool.not_eq_true'] at hU'
            rw [Upd.afterT_local1 m τ'' i t hpf, Upd.afterT_local1 m τ' i t hpf,
              (Tm.rl_reads hK h t hU'.2).1]
            cases t.eval τ' with
            | none => exact Iff.rfl
            | some v => exact ih hφ _ _ hV (h.setLocal i hU'.1 v)
          | _ => simp only [Upd.rl1, UpdElem.rl1, Rhs.rlV, Bool.false_eq_true, Bool.and_false] at hU
        | _ => simp only [Upd.rl1, UpdElem.rl1, Bool.false_eq_true] at hU
      | _ => simp only [Upd.rl1, Bool.false_eq_true] at hU
    | decl U₀ x r =>
      cases U₀ with
      | nil =>
        cases r with
        | val t =>
          have hU' : t.rl V K = true := hU
          rw [Upd.afterT_decl1 m τ'' x t hpf, Upd.afterT_decl1 m τ' x t hpf,
            (Tm.rl_reads hK h t hU').1]
          cases t.eval τ' with
          | none => exact Iff.rfl
          | some v => exact ih hφ _ _ (fun l hl => Nat.lt_succ_of_lt (hV l hl)) (h.push hV v)
        | _ => simp only [Upd.rl1, Rhs.rlV, Bool.false_eq_true] at hU
      | _ => simp only [Upd.rl1, Bool.false_eq_true] at hU
    | _ => simp only [Upd.rl1, Bool.false_eq_true] at hU
  | modal | havoc | bind | anon | allocAll | grow =>
    intro _ _ _ _; simp only [Fml.rl, Bool.false_eq_true] at hφ

end Formulas

end Solidity.Decide
