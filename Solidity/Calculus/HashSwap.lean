import Solidity.Calculus.HashPremise
import Solidity.Theory.Typed.Mem

/-!
# Hashes of fresh byte strings read as words (M7, plan step 7)

A leaf `∀ fresh s t. ψ` whose memory locals are byte strings
(`Fml.allocAll` at `uint[]`, any contents) read only by hashes of one kind
(`hash(memory, s)`, not `ecrecover`) is read with each such local replaced
by the word its hash returns: `Fml.sw` replaces the binder by `∀ uint`
and each hash node by the local (`Tm.sw`), on a body of equations, the
connectives and one-element updates (a storage write, a value local declared
or set).  The rest of the leaf reads no memory.

`SwRel` relates a state of the leaf to one of its swapped reading: one
storage, ledger, balance and transaction, the heaps free (the swapped
reading reads none), every local read alike but a memory local, whose word
is its object's hash.  Over it every term reads alike (`Tm.sw_eval`,
`Tm.sw_denote`) and so does every formula (`Fml.sw_holds`).

Here the leaf's hashes are free variables: a valid swapped reading makes
the leaf valid, whatever the hash function (`Fml.swPrefix_validH`).  The
converse, a refutation that meets the goal's own hash premise, is in
`Calculus/HashReduction.lean`.
-/

namespace Solidity.Decide

variable {C : Contract}

/-! ## Contexts with memory locals read as words -/

/-- A memory local read as the word its hash returns. -/
def _root_.Solidity.LTy.sw : LTy → LTy
  | .val p => .val p
  | .alias R => .alias R
  | .mem _ => .val .uint
  | .old => .old
  | .oldNet => .oldNet
  | .kint => .kint

/-- The context with each memory local a word. -/
abbrev _root_.Solidity.Ctx.sw (Γ : Ctx) : Ctx := Γ.map LTy.sw

/-- A position, in the swapped context. -/
def _root_.Solidity.Idx.sw : {Γ : Ctx} → {t : LTy} → Idx Γ t → Idx (Ctx.sw Γ) t.sw
  | _, _, .here => .here
  | _, _, .there i => .there i.sw

theorem _root_.Solidity.Idx.toNat_sw : {Γ : Ctx} → {t : LTy} → (i : Idx Γ t) →
    i.sw.toNat = i.toNat
  | _, _, .here => rfl
  | _, _, .there i => congrArg (· + 1) (Idx.toNat_sw i)

/-! ## Sorts that read no heap -/

/-- The memory sort: the only one whose values are typed by the heap. -/
def _root_.Solidity.Srt.isMem : Srt → Bool
  | .mem => true
  | _ => false

/-- A reading carried to another heap typing: the value itself, at every
sort but the memory's. -/
def _root_.Solidity.Srt.trO {H H' : HTy} : (s : Srt) → Option (s.Den C H) → Option (s.Den C H')
  | .val _, x => x
  | .path _, x => x
  | .st, x => x
  | .sv _, x => x
  | .ident _, x => x
  | .addr _, x => x
  | .mem, _ => none
  | .mv _, x => x
  | .sts _, x => x
  | .spath _ _, x => x
  | .kint, x => x

/-- Two global parts alike but for the heap. -/
structure GAgree (g g' : State C []) : Prop where
  storage : g'.storage = g.storage
  net : g'.net = g.net
  bal : g'.selfBalance = g.selfBalance
  tx : g'.tx = g.tx

theorem GAgree.envVal {g g' : State C []} (h : GAgree g g') (k : EnvKey) :
    g'.envVal k = g.envVal k := by
  cases k <;> simp only [State.envVal, h.tx, h.bal]

section Ops

variable {g g' : State C []}

theorem _root_.Solidity.Op0.eval_trO {s : Srt} (o : Op0 C s) (hs : s.isMem = false)
    (h : GAgree g g') : o.eval g' = Srt.trO s (o.eval g) := by
  cases o with
  | env k => show some _ = some _; rw [h.envVal]
  | storage => show some _ = some _; rw [h.storage]
  | memory => cases hs
  | _ => rfl

theorem _root_.Solidity.Op0.denote_agree {s : Srt} (o : Op0 C s) (h : GAgree g g') :
    o.denote g' = o.denote g := by
  cases o with
  | env k => show some _ = some _; rw [h.envVal]
  | storage => show Storage.obs _ = Storage.obs _; rw [h.storage]
  | _ => rfl

theorem _root_.Solidity.Op1.eval_trO {a s : Srt} (o : Op1 C a s) (ha : a.isMem = false)
    (hs : s.isMem = false) (h : GAgree g g') (x : Option (a.Den C g.H)) :
    o.eval g' (Srt.trO a x) = Srt.trO s (o.eval g x) := by
  cases o with
  | net => simp only [Op1.eval_eq_evalM, Op1.evalM, Srt.trO, h.net]
  | next => simp only [Op1.eval_eq_evalM, Op1.evalM, Srt.trO, h.storage]
  | alloc => cases ha
  | addM => cases ha
  | _ => rfl

theorem _root_.Solidity.Op1.denote_agree {a s : Srt} (o : Op1 C a s) (h : GAgree g g')
    (d : a.TDen C) : o.denote g' d = o.denote g d := by
  cases o with
  | net => simp only [Op1.denote, h.net]
  | next => simp only [Op1.denote, h.storage]
  | _ => rfl

theorem _root_.Solidity.Op2.eval_trO {a b s : Srt} (o : Op2 C a b s) (ha : a.isMem = false)
    (hb : b.isMem = false) (h : GAgree g g') (x : Option (a.Den C g.H)) (y : Option (b.Den C g.H)) :
    o.eval g' (Srt.trO a x) (Srt.trO b y) = Srt.trO s (o.eval g x y) := by
  cases o with
  | «at» it => simp only [Op2.eval_eq_evalM, Op2.evalM, Srt.trO, h.storage]
  | read | mlen | copyMem | iread | copy | copySt | hash => cases ha
  | _ => rfl

theorem _root_.Solidity.Op2.denote_agree {a b s : Srt} (o : Op2 C a b s) (ha : a.isMem = false) (x : Option (a.Den C g.H)) (y : Option (b.Den C g.H))
    (x' : Option (a.Den C g'.H)) (y' : Option (b.Den C g'.H)) (da : a.TDen C) (db : b.TDen C) :
    o.denote g' x' y' da db = o.denote g x y da db := by
  cases o with
  | read | mlen | copyMem | iread | copy | copySt | hash => cases ha
  | _ => rfl

theorem _root_.Solidity.Op3.eval_trO {a b c s : Srt} (o : Op3 C a b c s) (ha : a.isMem = false) (x : Option (a.Den C g.H)) (y : Option (b.Den C g.H))
    (z : Option (c.Den C g.H)) :
    o.eval g' (Srt.trO a x) (Srt.trO b y) (Srt.trO c z) = Srt.trO s (o.eval g x y z) := by
  cases o with
  | write => cases ha
  | _ => rfl

end Ops

/-! ## The swapped reading -/

/-- A hash node of kind `k` of a memory local, in the starting memory: the
local, read as a word. -/
def _root_.Solidity.Op2.hashSw? (k : HashKind) {Γ : Ctx} {a b s : Srt} :
    Op2 C a b s → Tm C Γ a → Tm C Γ b → Option (Tm C (Ctx.sw Γ) s)
  | .hash k', .app0 .memory, .pvI i => if k' = k then some (.pvV i.sw) else none
  | _, _, _ => none

/-- **A term, swapped**: every hash node of kind `k` of a memory local a word
local, every other symbol kept; `none` on any other read of the memory. -/
def _root_.Solidity.Tm.sw (k : HashKind) {Γ : Ctx} : {s : Srt} → Tm C Γ s → Option (Tm C (Ctx.sw Γ) s)
  | _, .pvV i => some (.pvV i.sw)
  | _, .pvP i => some (.pvP i.sw)
  | _, .pvS i => some (.pvS i.sw)
  | _, .pvI _ => none
  | _, .netOf i a => (a.sw k).map (.netOf i.sw)
  | s, .app0 o => if s.isMem then none else some (.app0 o)
  | s, .app1 (a := a) o x => if a.isMem || s.isMem then none else (x.sw k).map (.app1 o)
  | s, .app2 (a := a) (b := b) o x y =>
    match o.hashSw? k x y with
    | some t => some t
    | none => if a.isMem || b.isMem || s.isMem then none else
        (x.sw k).bind fun x' => (y.sw k).map fun y' => .app2 o x' y'
  | s, .app3 (a := a) (b := b) (c := c) o x y z =>
    if a.isMem || b.isMem || c.isMem || s.isMem then none else
      (x.sw k).bind fun x' => (y.sw k).bind fun y' => (z.sw k).map fun z' => .app3 o x' y' z'
  | _, .pvZ i => some (.pvZ i.sw)

/-! ## States read alike -/

/-- A local of the leaf and of its swapped reading held alike: a memory
local's word is the hash of the object it names (by identity, in the memory
`g`), any other local the same value. -/
def LocRel (k : HashKind) (g : State C []) : (t : LTy) → t.VDen C → t.sw.VDen C → Prop
  | .mem R, v, w => ∃ id, v = some id ∧ w = g.memT.hashId k R id
  | .val _, v, w => v = w
  | .alias _, v, w => v = w
  | .old, v, w => v = w
  | .oldNet, v, w => v = w
  | .kint, v, w => v = w

/-- **A state of the leaf and one of its swapped reading**: their global
parts alike but for the heap, their locals held alike (`LocRel`). -/
structure SwRel (k : HashKind) {Γ : Ctx} (τ : State C Γ) (τ' : State C (Ctx.sw Γ)) : Prop where
  glob : GAgree τ.glob τ'.glob
  loc : ∀ {t : LTy} (i : Idx Γ t), LocRel k τ.glob t (τ.getV i) (τ'.getV i.sw)

section Terms

variable {k : HashKind} {Γ : Ctx} {τ : State C Γ} {τ' : State C (Ctx.sw Γ)}

theorem SwRel.get_val (h : SwRel k τ τ') {p : PrimTy} (i : Idx Γ (.val p)) :
    TEnv.get i.sw τ'.env = TEnv.get i τ.env := (h.loc i).symm

theorem SwRel.get_alias (h : SwRel k τ τ') {R : RefTy} (i : Idx Γ (.alias R)) :
    TEnv.get i.sw τ'.env = TEnv.get i τ.env := (h.loc i).symm

theorem SwRel.get_old (h : SwRel k τ τ') (i : Idx Γ .old) :
    TEnv.get i.sw τ'.env = TEnv.get i τ.env := (h.loc i).symm

theorem SwRel.get_oldNet (h : SwRel k τ τ') (i : Idx Γ .oldNet) :
    TEnv.get i.sw τ'.env = TEnv.get i τ.env := (h.loc i).symm

theorem SwRel.get_kint (h : SwRel k τ τ') (i : Idx Γ .kint) :
    TEnv.get i.sw τ'.env = TEnv.get i τ.env := (h.loc i).symm

/-- A hash node's swapped reading reads its hash. -/
theorem _root_.Solidity.Op2.hashSw?_reads (h : SwRel k τ τ') {a b s : Srt} (o : Op2 C a b s)
    (x : Tm C Γ a) (y : Tm C Γ b) {t' : Tm C (Ctx.sw Γ) s} (ht : o.hashSw? k x y = some t') :
    t'.eval τ' = Srt.trO s ((Tm.app2 o x y).eval τ) ∧ t'.denote τ' = (Tm.app2 o x y).denote τ := by
  unfold Op2.hashSw? at ht
  split at ht
  · rename_i R k' i
    by_cases hk : k' = k
    · subst hk
      simp only [if_true, Option.some.injEq] at ht
      subst ht
      obtain ⟨id, hid, hw⟩ := h.loc i
      have hv : (TEnv.get i τ.env).map (·.id) = some id := hid
      have hw' : TEnv.get i.sw τ'.env = τ.glob.memT.hashId k' R id := hw
      have he : (Tm.app2 (Op2.hash (R := R) k') (Tm.app0 Op0.memory) (Tm.pvI i)).eval τ =
          some (τ.glob.memT.hashId k' R id) := by
        show Op2.eval τ.glob (.hash k') (Op0.eval τ.glob .memory) ((TEnv.get i τ.env).map (·.id)) = _
        rw [hv, Op2.eval_eq_evalM]
        rfl
      refine ⟨?_, ?_⟩
      · rw [he]
        show some (TEnv.get i.sw τ'.env) = some _
        rw [hw']
      · show some (TEnv.get i.sw τ'.env) = Op2.eval τ.glob (.hash k') _ _
        rw [show Op2.eval τ.glob (.hash k') ((Tm.app0 (Γ := Γ) Op0.memory).eval τ)
          ((Tm.pvI i).eval τ) = some (τ.glob.memT.hashId k' R id) from he, hw']
    · simp only [hk, if_false, reduceCtorEq] at ht
  · cases ht

/-- **A swapped term reads as the term.** -/
theorem _root_.Solidity.Tm.sw_eval (h : SwRel k τ τ') : {s : Srt} → (t : Tm C Γ s) →
    {t' : Tm C (Ctx.sw Γ) s} → t.sw k = some t' → t'.eval τ' = Srt.trO s (t.eval τ)
  | _, .pvV i, _, e => by
    cases e
    show some _ = some _
    rw [h.get_val]
  | _, .pvP i, _, e => by
    cases e
    show TEnv.get i.sw τ'.env = TEnv.get i τ.env
    rw [h.get_alias]
  | _, .pvS i, _, e => by
    cases e
    show some _ = some _
    rw [h.get_old]
  | _, .pvI _, _, e => by cases e
  | _, .netOf i a, _, e => by
    obtain ⟨a', ha, rfl⟩ := Option.map_eq_some_iff.1 e
    show (a'.eval τ').bind _ = (a.eval τ).bind _
    rw [Tm.sw_eval h a ha, h.get_oldNet]
    rfl
  | s, .app0 o, _, e => by
    simp only [Tm.sw] at e
    split at e
    · cases e
    · rename_i hs
      cases e
      exact Op0.eval_trO o (Bool.eq_false_iff.2 hs) h.glob
  | s, .app1 (a := a) o x, _, e => by
    simp only [Tm.sw] at e
    split at e
    · cases e
    · rename_i hm
      simp only [Bool.or_eq_true, not_or, Bool.not_eq_true] at hm
      obtain ⟨x', hx, rfl⟩ := Option.map_eq_some_iff.1 e
      show o.eval τ'.glob (x'.eval τ') = _
      rw [Tm.sw_eval h x hx]
      exact Op1.eval_trO o hm.1 hm.2 h.glob _
  | s, .app2 (a := a) (b := b) o x y, _, e => by
    simp only [Tm.sw] at e
    split at e
    · rename_i t₀ hh
      cases e
      exact (o.hashSw?_reads h x y hh).1
    · split at e
      · cases e
      · rename_i hm
        simp only [Bool.or_eq_true, not_or, Bool.not_eq_true] at hm
        obtain ⟨x', hx, e⟩ := Option.bind_eq_some_iff.1 e
        obtain ⟨y', hy, rfl⟩ := Option.map_eq_some_iff.1 e
        show o.eval τ'.glob (x'.eval τ') (y'.eval τ') = _
        rw [Tm.sw_eval h x hx, Tm.sw_eval h y hy]
        exact Op2.eval_trO o hm.1.1 hm.1.2 h.glob _ _
  | s, .app3 (a := a) (b := b) (c := c) o x y z, _, e => by
    simp only [Tm.sw] at e
    split at e
    · cases e
    · rename_i hm
      simp only [Bool.or_eq_true, not_or, Bool.not_eq_true] at hm
      obtain ⟨x', hx, e⟩ := Option.bind_eq_some_iff.1 e
      obtain ⟨y', hy, e⟩ := Option.bind_eq_some_iff.1 e
      obtain ⟨z', hz, rfl⟩ := Option.map_eq_some_iff.1 e
      show o.eval τ'.glob (x'.eval τ') (y'.eval τ') (z'.eval τ') = _
      rw [Tm.sw_eval h x hx, Tm.sw_eval h y hy, Tm.sw_eval h z hz]
      exact Op3.eval_trO (g := τ.glob) o hm.1.1.1 _ _ _
  | _, .pvZ i, _, e => by
    cases e
    show some _ = some _
    rw [h.get_kint]

/-- **A swapped term denotes as the term.** -/
theorem _root_.Solidity.Tm.sw_denote (h : SwRel k τ τ') : {s : Srt} → (t : Tm C Γ s) →
    {t' : Tm C (Ctx.sw Γ) s} → t.sw k = some t' → t'.denote τ' = t.denote τ
  | _, .pvV i, _, e => by
    cases e
    show some _ = some _
    rw [h.get_val]
  | _, .pvP i, _, e => by
    cases e
    have e := h.get_alias i
    simp only [Tm.denote]
    revert e
    generalize TEnv.get i.sw τ'.env = a
    generalize TEnv.get i τ.env = b
    intro e
    subst e
    cases a <;> rfl
  | _, .pvS i, _, e => by
    cases e
    show Storage.obs _ = Storage.obs _
    rw [h.get_old]
  | _, .pvI _, _, e => by cases e
  | _, .netOf i a, _, e => by
    obtain ⟨a', ha, rfl⟩ := Option.map_eq_some_iff.1 e
    show (a'.denote τ').map _ = (a.denote τ).map _
    rw [Tm.sw_denote h a ha, h.get_oldNet]
  | s, .app0 o, _, e => by
    simp only [Tm.sw] at e
    split at e
    · cases e
    · cases e
      exact Op0.denote_agree o h.glob
  | s, .app1 (a := a) o x, _, e => by
    simp only [Tm.sw] at e
    split at e
    · cases e
    · obtain ⟨x', hx, rfl⟩ := Option.map_eq_some_iff.1 e
      show o.denote τ'.glob (x'.denote τ') = o.denote τ.glob (x.denote τ)
      rw [Tm.sw_denote h x hx]
      exact Op1.denote_agree o h.glob _
  | s, .app2 (a := a) (b := b) o x y, _, e => by
    simp only [Tm.sw] at e
    split at e
    · rename_i t₀ hh
      cases e
      exact (o.hashSw?_reads h x y hh).2
    · split at e
      · cases e
      · rename_i hm
        simp only [Bool.or_eq_true, not_or, Bool.not_eq_true] at hm
        obtain ⟨x', hx, e⟩ := Option.bind_eq_some_iff.1 e
        obtain ⟨y', hy, rfl⟩ := Option.map_eq_some_iff.1 e
        show o.denote τ'.glob (x'.eval τ') (y'.eval τ') (x'.denote τ') (y'.denote τ') =
          o.denote τ.glob (x.eval τ) (y.eval τ) (x.denote τ) (y.denote τ)
        rw [Tm.sw_denote h x hx, Tm.sw_denote h y hy]
        exact Op2.denote_agree o hm.1.1 _ _ _ _ _ _
  | s, .app3 (a := a) (b := b) (c := c) o x y z, _, e => by
    simp only [Tm.sw] at e
    split at e
    · cases e
    · obtain ⟨x', hx, e⟩ := Option.bind_eq_some_iff.1 e
      obtain ⟨y', hy, e⟩ := Option.bind_eq_some_iff.1 e
      obtain ⟨z', hz, rfl⟩ := Option.map_eq_some_iff.1 e
      show o.denote (x'.denote τ') (y'.denote τ') (z'.denote τ') =
        o.denote (x.denote τ) (y.denote τ) (z.denote τ)
      rw [Tm.sw_denote h x hx, Tm.sw_denote h y hy, Tm.sw_denote h z hz]
  | _, .pvZ i, _, e => by
    cases e
    show some _ = some _
    rw [h.get_kint]

end Terms

/-! ## One-element updates -/

section Updates

variable {Γ : Ctx}

/-- A storage write lands on the state with the storage it computes. -/
theorem Upd.afterT_storage1 (m : Modality) (τ : State C Γ) (s : Tm C Γ .st)
    (hp : (Upd.snoc .nil (.storage s) : Upd C Γ Γ).pushFree = true) (P : State C Γ → Prop) :
    (Upd.snoc .nil (.storage s) : Upd C Γ Γ).afterT m τ P ↔
      (match s.eval τ with
        | none => m.onHalt
        | some st => P (τ.withStorage st)) := by
  have hg : (Upd.snoc .nil (.storage s) : Upd C Γ Γ).globT τ =
      (s.eval τ).bind fun st => some (τ.globG.withStorage st) := rfl
  unfold Upd.afterT
  rw [hg]
  cases hs : s.eval τ with
  | none =>
    simp only [Option.bind_none, Upd.exh_of_pushFree (σ₀ := τ) hp, Bool.false_eq_true, or_false]
  | some st =>
    simp only [Option.bind_some]
    have hL : (Upd.snoc .nil (.storage s) : Upd C Γ Γ).Lands τ (τ.globG.withStorage st)
        (τ.withStorage st) := ⟨by rw [hg, hs]; rfl, rfl, fun _ => rfl⟩
    exact ⟨fun h => h _ hL, fun h σ' hl => (Upd.Lands.eq hL hl) ▸ h⟩

/-- A declared value lands on the state with it pushed. -/
theorem Upd.afterT_decl1 (m : Modality) (τ : State C Γ) (x : Var) {p : PrimTy}
    (t : Tm C Γ (.val p)) (hp : (Upd.decl .nil x (.val t) : Upd C Γ (.val p :: Γ)).pushFree = true)
    (P : State C (.val p :: Γ) → Prop) :
    (Upd.decl .nil x (.val t) : Upd C Γ (.val p :: Γ)).afterT m τ P ↔
      (match t.eval τ with
        | none => m.onHalt
        | some v => P (τ.push (t := .val p) v)) := by
  have hg : (Upd.decl .nil x (.val t) : Upd C Γ (.val p :: Γ)).globT τ =
      (t.eval τ).bind fun _ => some τ.globG := rfl
  unfold Upd.afterT
  rw [hg]
  cases hs : t.eval τ with
  | none =>
    simp only [Option.bind_none, Upd.exh_of_pushFree (σ₀ := τ) hp, Bool.false_eq_true, or_false]
  | some v =>
    simp only [Option.bind_some]
    have hL := Upd.lands_decl (Upd.lands_nil τ) x (r := .val t) (v := (v : p.Denote)) hs
    exact ⟨fun h => h _ hL, fun h σ' hl => (Upd.Lands.eq hL hl) ▸ h⟩

/-- A value local set lands on the state with it set. -/
theorem Upd.afterT_local1 (m : Modality) (τ : State C Γ) {p : PrimTy} (i : Idx Γ (.val p))
    (t : Tm C Γ (.val p)) (hp : (Upd.snoc .nil (.local i (.val t)) : Upd C Γ Γ).pushFree = true)
    (P : State C Γ → Prop) :
    (Upd.snoc .nil (.local i (.val t)) : Upd C Γ Γ).afterT m τ P ↔
      (match t.eval τ with
        | none => m.onHalt
        | some v => P (τ.setLocal i v)) := by
  have hg : (Upd.snoc .nil (.local i (.val t)) : Upd C Γ Γ).globT τ =
      (t.eval τ).bind fun _ => some τ.globG := rfl
  unfold Upd.afterT
  rw [hg]
  cases hs : t.eval τ with
  | none =>
    simp only [Option.bind_none, Upd.exh_of_pushFree (σ₀ := τ) hp, Bool.false_eq_true, or_false]
  | some v =>
    simp only [Option.bind_some]
    have hL := Upd.lands_snoc_local (Upd.lands_nil τ) i (r := .val t) (v := (v : p.Denote)) hs
    exact ⟨fun h => h _ hL, fun h σ' hl => (Upd.Lands.eq hL hl) ▸ h⟩

end Updates

section Preserve

variable {k : HashKind} {Γ : Ctx} {τ : State C Γ} {τ' : State C (Ctx.sw Γ)}

theorem SwRel.withStorage (h : SwRel k τ τ') (st : Storage C) :
    SwRel k (τ.withStorage st) (τ'.withStorage st) :=
  ⟨⟨rfl, h.glob.net, h.glob.bal, h.glob.tx⟩, fun i => h.loc i⟩

theorem SwRel.push (h : SwRel k τ τ') {p : PrimTy} (v : p.Denote) :
    SwRel k (τ.push (t := .val p) v) (τ'.push (t := .val p) v) :=
  ⟨h.glob, fun i => by
    cases i with
    | here => rfl
    | there j => exact h.loc j⟩

theorem SwRel.setLocal (h : SwRel k τ τ') {p : PrimTy} (i : Idx Γ (.val p)) (v : p.Denote) :
    SwRel k (τ.setLocal i v) (τ'.setLocal (t := .val p) i.sw v) :=
  ⟨h.glob, fun {u} j => by
    by_cases hij : i.toNat = j.toNat
    · obtain rfl := Idx.ty_eq_of_toNat hij
      obtain rfl := Idx.toNat_inj i j hij
      show LocRel k τ.glob (.val p) ((τ.setLocal i v).getV i) ((τ'.setLocal (t := .val p) i.sw v).getV i.sw)
      rw [State.getV_setLocal_same, State.getV_setLocal_same]
      rfl
    · have hij' : i.sw.toNat ≠ j.sw.toNat := by rw [Idx.toNat_sw, Idx.toNat_sw]; exact hij
      rw [State.getV_setLocal_ne _ _ _ hij, State.getV_setLocal_ne _ _ _ hij']
      exact h.loc j⟩

end Preserve

/-! ## Formulas -/

/-- A local's right-hand side, swapped: a value. -/
def _root_.Solidity.Rhs.sw (k : HashKind) {Γ : Ctx} : {t : LTy} → Rhs C Γ t →
    Option (Rhs C (Ctx.sw Γ) t.sw)
  | _, .val t => (t.sw k).map .val
  | _, _ => none

/-- An element of a one-element update, swapped: a storage write, a value
local set. -/
def _root_.Solidity.UpdElem.sw1? (k : HashKind) {Γ : Ctx} :
    UpdElem C Γ Γ → Option (UpdElem C (Ctx.sw Γ) (Ctx.sw Γ))
  | .storage s => (s.sw k).map .storage
  | .local i r => (r.sw k).map (.local i.sw)
  | _ => none

/-- A one-element update, swapped: a storage write, a value local declared
or set. -/
def _root_.Solidity.Upd.sw1? (k : HashKind) {Γ : Ctx} :
    {Δ : Ctx} → Upd C Γ Δ → Option (Upd C (Ctx.sw Γ) (Ctx.sw Δ))
  | _, .snoc .nil e => (e.sw1? k).map (.snoc .nil)
  | _, .decl .nil x r => (r.sw k).map (.decl .nil x)
  | _, _ => none

/-- **A formula, swapped**: equations, `wt`, the connectives and one-element
updates with no push, its terms swapped (`Tm.sw`); `none` on any binder or
program. -/
def _root_.Solidity.Fml.sw (k : HashKind) : {Γ : Ctx} → Fml C Γ → Option (Fml C (Ctx.sw Γ))
  | _, .tt => some .tt
  | _, .eq a b => (a.sw k).bind fun a' => (b.sw k).map fun b' => .eq a' b'
  | _, .wellFormed s => (s.sw k).map .wellFormed
  | _, .not φ => (Fml.sw k φ).map .not
  | _, .and φ ψ => (Fml.sw k φ).bind fun φ' => (Fml.sw k ψ).map fun ψ' => .and φ' ψ'
  | _, .imp φ ψ => (Fml.sw k φ).bind fun φ' => (Fml.sw k ψ).map fun ψ' => .imp φ' ψ'
  | _, .upd m U φ => (U.sw1? k).bind fun U' =>
      if U.pushFree && U'.pushFree then (Fml.sw k φ).map (.upd m U') else none
  | _, _ => none

/-- **A swapped formula holds as the formula.** -/
theorem _root_.Solidity.Fml.sw_holds {k : HashKind} {Γ : Ctx} (φ : Fml C Γ) :
    ∀ {φ' : Fml C (Ctx.sw Γ)}, φ.sw k = some φ' → ∀ (τ : State C Γ) (τ' : State C (Ctx.sw Γ)),
      SwRel k τ τ' → (holds τ' φ' ↔ holds τ φ) := by
  induction φ with
  | tt => intro _ e _ _ _; cases e; exact Iff.rfl
  | eq a b =>
    intro _ e τ τ' h
    obtain ⟨a', ha, e⟩ := Option.bind_eq_some_iff.1 e
    obtain ⟨b', hb, rfl⟩ := Option.map_eq_some_iff.1 e
    rw [holds_eq, holds_eq, Tm.sw_denote h a ha, Tm.sw_denote h b hb]
  | wellFormed s =>
    intro _ e τ τ' h
    obtain ⟨s', hs, rfl⟩ := Option.map_eq_some_iff.1 e
    rw [holds_wellFormed, holds_wellFormed, Tm.sw_eval h s hs]
    rfl
  | not φ ih =>
    intro _ e τ τ' h
    obtain ⟨φ', hφ, rfl⟩ := Option.map_eq_some_iff.1 e
    exact not_congr (ih hφ τ τ' h)
  | and φ ψ ihφ ihψ =>
    intro _ e τ τ' h
    obtain ⟨φ', hφ, e⟩ := Option.bind_eq_some_iff.1 e
    obtain ⟨ψ', hψ, rfl⟩ := Option.map_eq_some_iff.1 e
    exact and_congr (ihφ hφ τ τ' h) (ihψ hψ τ τ' h)
  | imp φ ψ ihφ ihψ =>
    intro _ e τ τ' h
    obtain ⟨φ', hφ, e⟩ := Option.bind_eq_some_iff.1 e
    obtain ⟨ψ', hψ, rfl⟩ := Option.map_eq_some_iff.1 e
    exact imp_congr (ihφ hφ τ τ' h) (ihψ hψ τ τ' h)
  | upd m U φ ih =>
    intro _ e τ τ' h
    obtain ⟨U', hU, e⟩ := Option.bind_eq_some_iff.1 e
    split at e
    · rename_i hpf
      simp only [Bool.and_eq_true] at hpf
      obtain ⟨φ', hφ, rfl⟩ := Option.map_eq_some_iff.1 e
      show U'.afterT m τ' (holds · φ') ↔ U.afterT m τ (holds · φ)
      cases U with
      | snoc U₀ e₀ =>
        cases U₀ with
        | nil =>
          have hU' : (e₀.sw1? k).map (.snoc .nil) = some U' := hU
          obtain ⟨e', he, rfl⟩ := Option.map_eq_some_iff.1 hU'
          cases e₀ with
          | storage s =>
            have he' : (s.sw k).map UpdElem.storage = some e' := he
            obtain ⟨s', hs, rfl⟩ := Option.map_eq_some_iff.1 he'
            rw [Upd.afterT_storage1 m τ' s' hpf.2, Upd.afterT_storage1 m τ s hpf.1,
              Tm.sw_eval h s hs]
            cases s.eval τ with
            | none => exact Iff.rfl
            | some st => exact ih hφ _ _ (h.withStorage st)
          | «local» i r =>
            have he' : (r.sw k).map (UpdElem.local i.sw) = some e' := he
            obtain ⟨r', hr, rfl⟩ := Option.map_eq_some_iff.1 he'
            cases r with
            | val t =>
              have hr' : (t.sw k).map Rhs.val = some r' := hr
              obtain ⟨t', ht, rfl⟩ := Option.map_eq_some_iff.1 hr'
              rw [Upd.afterT_local1 m τ' i.sw t' hpf.2, Upd.afterT_local1 m τ i t hpf.1,
                Tm.sw_eval h t ht]
              cases t.eval τ with
              | none => exact Iff.rfl
              | some v => exact ih hφ _ _ (h.setLocal i v)
            | _ => cases hr
          | _ => cases he
        | _ => cases hU
      | decl U₀ x r =>
        cases U₀ with
        | nil =>
          have hU' : (r.sw k).map (.decl .nil x) = some U' := hU
          obtain ⟨r', hr, rfl⟩ := Option.map_eq_some_iff.1 hU'
          cases r with
          | val t =>
            have hr' : (t.sw k).map Rhs.val = some r' := hr
            obtain ⟨t', ht, rfl⟩ := Option.map_eq_some_iff.1 hr'
            rw [Upd.afterT_decl1 m τ' x t' hpf.2, Upd.afterT_decl1 m τ x t hpf.1,
              Tm.sw_eval h t ht]
            cases t.eval τ with
            | none => exact Iff.rfl
            | some v => exact ih hφ _ _ (h.push v)
          | _ => cases hr
        | _ => cases hU
      | _ => cases hU
    · cases e
  | modal | havoc | all | bind | anon | allocAll | grow => intro _ e; cases e

/-! ## Fresh objects and their hashes -/

section Alloc

theorem _root_.Solidity.MObj.words_wk {H H' : HTy} (e : H <+: H') : (R : RefTy) → (o : MObj H R) →
    MObj.words R (MObj.wk e R o) = MObj.words R o
  | .struct _, _ => rfl
  | .array (.prim .uint), o => by
    show ((o.1.map (MVal.wk e (.prim .uint))).map fun v => (v : PrimTy.uint.Denote).1) =
      o.1.map fun v => (v : PrimTy.uint.Denote).1
    rw [List.map_map]
    rfl
  | .array (.prim .int), _ | .array (.prim .bool), _ => rfl
  | .array (.ref _), _ => rfl
  | .fixed _ _, _ => rfl
  | .mapping _ _, o => (o : Empty).elim

variable {Γ : Ctx}

theorem _root_.Solidity.State.getV_alloc (σ : State C Γ) {R : RefTy} (o : MObj σ.H R) {t : LTy}
    (i : Idx Γ t) : (σ.alloc o).1.getV i = σ.getV i := by
  show LTy.VDen.ofT t (TEnv.get i (TEnv.wk _ Γ σ.env)) = LTy.VDen.ofT t (TEnv.get i σ.env)
  rw [TEnv.get_wk]
  cases t with
  | mem _ =>
    show Option.map _ (Option.map _ _) = _
    rw [Option.map_map]
    rfl
  | _ => rfl

/-- **An allocation keeps every older object's hash.** -/
theorem _root_.Solidity.State.alloc_hashId (σ : State C Γ) {R : RefTy} (o : MObj σ.H R)
    (k : HashKind) {R' : RefTy} (r : HRef σ.H R') :
    (σ.alloc o).1.glob.memT.hashId k R' r.id = σ.glob.memT.hashId k R' r.id := by
  have hid : r.id < σ.H.length := (List.getElem?_eq_some_iff.1 r.get?).1
  show (((HRef.ofId? (σ.H ++ [R]) R' r.id).map ((σ.heap.alloc o).1.hash k)).getD _) =
    ((HRef.ofId? σ.H R' r.id).map (σ.heap.hash k)).getD _
  rw [HRef.ofId?_wk (List.prefix_append σ.H [R]) R' hid, HRef.ofId?_self]
  show k.apply (MObj.words R' ((σ.heap.alloc o).1.get (r.wk _))) = k.apply (MObj.words R' (σ.heap.get r))
  rw [Heap.keeps_alloc σ.heap o r, MObj.words_wk]

/-- **A fresh object hashes its own bytes.** -/
theorem _root_.Solidity.State.alloc_hashId_self (σ : State C Γ) {R : RefTy} (o : MObj σ.H R)
    (k : HashKind) :
    (σ.alloc o).1.glob.memT.hashId k R (σ.alloc o).2.id = k.apply (MObj.words R o) := by
  show (((HRef.ofId? (σ.H ++ [R]) R (σ.heap.alloc o).2.id).map ((σ.heap.alloc o).1.hash k)).getD _) = _
  rw [HRef.ofId?_self]
  show k.apply (MObj.words R ((σ.heap.alloc o).1.get (σ.heap.alloc o).2)) = _
  rw [Heap.get_alloc, MObj.words_wk]

end Alloc

section PreserveAlloc

variable {k : HashKind} {Γ : Ctx} {τ : State C Γ} {τ' : State C (Ctx.sw Γ)}

theorem SwRel.alloc (h : SwRel k τ τ') {R : RefTy} (o : MObj τ.H R) :
    SwRel k (τ.alloc o).1 τ' :=
  ⟨⟨h.glob.storage, h.glob.net, h.glob.bal, h.glob.tx⟩, fun {t} i => by
    rw [State.getV_alloc]
    have hl := h.loc i
    cases t with
    | mem R' =>
      obtain ⟨id, hid, hw⟩ := hl
      refine ⟨id, hid, ?_⟩
      have hv : (TEnv.get i τ.env).map (·.id) = some id := hid
      obtain ⟨r, hr, rfl⟩ := Option.map_eq_some_iff.1 hv
      rw [hw, State.alloc_hashId]
    | _ => exact hl⟩

theorem SwRel.pushMem (h : SwRel k τ τ') {R : RefTy} (r : HRef τ.H R) :
    SwRel k (τ.push (t := .mem R) (some r)) (τ'.push (t := .val .uint) (τ.glob.memT.hashId k R r.id)) :=
  ⟨h.glob, fun i => by
    cases i with
    | here => exact ⟨r.id, rfl, rfl⟩
    | there j => exact h.loc j⟩

end PreserveAlloc

/-! ## The leaf's prefix -/

/-- **A leaf, swapped**: a prefix of `∀ p` and of fresh byte strings
(`allocAll` at `uint[]`), the latter read as `∀ uint` (the word each hashes
to), then a body `Fml.sw` takes. -/
def _root_.Solidity.Fml.swPrefix (k : HashKind) : {Γ : Ctx} → Fml C Γ → Option (Fml C (Ctx.sw Γ))
  | _, .all x p φ => (Fml.swPrefix k φ).map (.all x p)
  | _, .allocAll x R φ =>
    if R = .array (.prim .uint) then (Fml.swPrefix k φ).map (.all x .uint) else none
  | _, .tt => Fml.sw k .tt
  | _, .eq a b => Fml.sw k (.eq a b)
  | _, .wellFormed s => Fml.sw k (.wellFormed s)
  | _, .not φ => Fml.sw k (.not φ)
  | _, .and φ ψ => Fml.sw k (.and φ ψ)
  | _, .imp φ ψ => Fml.sw k (.imp φ ψ)
  | _, .upd m U φ => Fml.sw k (.upd m U φ)
  | _, .modal .. | _, .havoc _ | _, .bind .. | _, .anon .. | _, .grow _ => none

/-- On a formula `Fml.sw` takes the premise is read nowhere: it has no binder. -/
theorem _root_.Solidity.Fml.holdsS_of_sw {k : HashKind} {Γ : Ctx} (φ : Fml C Γ) :
    ∀ {φ' : Fml C (Ctx.sw Γ)}, φ.sw k = some φ' → ∀ τ : State C Γ, (Fml.holdsS τ φ ↔ holds τ φ) := by
  induction φ with
  | tt | eq | wellFormed => intro _ _ _; exact Iff.rfl
  | not φ ih =>
    intro _ e τ
    obtain ⟨φ', hφ, rfl⟩ := Option.map_eq_some_iff.1 e
    exact not_congr (ih hφ τ)
  | and φ ψ ihφ ihψ =>
    intro _ e τ
    obtain ⟨φ', hφ, e⟩ := Option.bind_eq_some_iff.1 e
    obtain ⟨ψ', hψ, rfl⟩ := Option.map_eq_some_iff.1 e
    exact and_congr (ihφ hφ τ) (ihψ hψ τ)
  | imp φ ψ ihφ ihψ =>
    intro _ e τ
    obtain ⟨φ', hφ, e⟩ := Option.bind_eq_some_iff.1 e
    obtain ⟨ψ', hψ, rfl⟩ := Option.map_eq_some_iff.1 e
    exact imp_congr (ihφ hφ τ) (ihψ hψ τ)
  | upd m U φ ih =>
    intro _ e τ
    obtain ⟨U', _, e⟩ := Option.bind_eq_some_iff.1 e
    split at e
    · obtain ⟨φ', hφ, rfl⟩ := Option.map_eq_some_iff.1 e
      exact ⟨fun h => Upd.afterT_imp h fun σ' => (ih hφ σ').1,
        fun h => Upd.afterT_imp h fun σ' => (ih hφ σ').2⟩
    · cases e
  | modal | havoc | all | bind | anon | allocAll | grow => intro _ e; cases e

/-- **The swapped leaf's validity is the leaf's**, at related states: what
the swapped reading says, the leaf says under its premise. -/
theorem _root_.Solidity.Fml.swPrefix_sound {k : HashKind} {Γ : Ctx} (φ : Fml C Γ) :
    ∀ {φ' : Fml C (Ctx.sw Γ)}, φ.swPrefix k = some φ' → ∀ (τ : State C Γ) (τ' : State C (Ctx.sw Γ)),
      SwRel k τ τ' → holds τ' φ' → Fml.holdsS τ φ := by
  induction φ with
  | all x p φ ih =>
    intro _ e τ τ' h hv
    obtain ⟨φ', hφ, rfl⟩ := Option.map_eq_some_iff.1 e
    exact fun v _ => ih hφ _ _ (h.push v) (hv v)
  | allocAll x R φ ih =>
    intro _ e τ τ' h hv
    simp only [Fml.swPrefix] at e
    split at e
    · obtain ⟨φ', hφ, rfl⟩ := Option.map_eq_some_iff.1 e
      intro o _
      exact ih hφ _ _ ((h.alloc o).pushMem _) (hv _)
    · cases e
  | tt | eq | wellFormed | not | and | imp | upd =>
    intro _ e τ τ' h hv
    exact (Fml.holdsS_of_sw _ e τ).2 ((Fml.sw_holds _ e τ τ' h).1 hv)
  | modal | havoc | bind | anon | grow => intro _ e; cases e

/-- **A valid swapped leaf is valid under the leaf's premise.** -/
theorem _root_.Solidity.Fml.swPrefix_validH {k : HashKind} {φ : Fml C []} {φ' : Fml C []}
    (e : φ.swPrefix k = some φ') (hv : Fml.Valid φ') : Fml.ValidH φ :=
  fun σ _ => Fml.swPrefix_sound φ e σ σ ⟨⟨rfl, rfl, rfl, rfl⟩, fun i => nomatch i⟩ (hv σ)

end Solidity.Decide
