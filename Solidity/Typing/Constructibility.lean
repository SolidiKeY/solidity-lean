import Solidity.Typing.Fits

/-!
# Which storages are reachable, exactly

`Typing/Reachability.lean` and `Typing/Tight.lean` prove reachable ⇒
canonical and tight.  The converse: everything canonical and tight is
reachable when its mapping keys and array slots are in range
(`SVal.Fits`: what a literal can write, `Simple.lit`), by one scoped program
(`Build.rootsProg`, over `Syntax/Scoped.lean`): a word is assigned; a struct
is filled member by member through an alias bound to it; a dynamic array is
pushed to its whole run of slots, then each slot past the end is bound to an
alias, popped, and filled through the alias (the only way to write past an
end), then the live elements are filled; a fixed-size array element by
element; a mapping entry by entry, each created by a `delete` so that an
entry holding the default is there too.  Each alias is declared in a block
of its own (`Build.bound`), so a fill leaves the context it starts in and
its caller's aliases, read by position, as they were.

The builder runs by the typed run (`TRuns`), each step read on `TRun.*`
(`run_push`, `run_pop`, …): no step loops or pushes onto `2^256 - 1`
elements, and none allocates, so a fill ends in its start state with only
the storage replaced.  The proof tracks the value at the path being filled
as a chain of saves at that path (`Wrote`), which is why every fill starts
from the default, at a path where saving the default changes nothing.
-/

namespace Solidity

open Semantics (structDef lookupBy setBy nodupKeysB lookupBy_eq_some_mem)

variable {C : Contract}

/-- A sequence followed by another. -/
def Prog.append {Γ Δ Ε : Ctx} : Prog C Γ Δ → Prog C Δ Ε → Prog C Γ Ε
  | .nil, Q => Q
  | .cons s P, Q => .cons s (P.append Q)

/-- One statement `n` times. -/
def Prog.rep {Γ : Ctx} (n : Nat) (s : Stmt C Γ Γ) : Prog C Γ Γ :=
  match n with
  | 0 => .nil
  | n + 1 => .cons s (Prog.rep n s)

namespace Build

/-! ## The builder -/

/-- The name of the alias a fill at depth `d` binds. -/
def slot (d : Nat) : Var := .fresh "slot" d

theorem inRange_of_lt {j : Nat} (h : j < 2 ^ 256) : PrimTy.uint.inRange (j : Int) = true := by
  simp only [PrimTy.inRange, decide_eq_true_eq]
  omega

/-- The literal `n` at the numeric type `p`, or `0` where `n` is out of its
range (an index the builder writes has none, `SVal.Fits`). -/
def numLit {Γ : Ctx} (p : PrimTy) (hp : p.isNumeric = true) (n : Int) : Simple C Γ p :=
  if h : p.inRange n = true then .lit n h
  else .lit 0 (by cases p <;> first | rfl | exact absurd hp (by decide))

theorem numLit_eq {Γ : Ctx} {p : PrimTy} {hp : p.isNumeric = true} {n : Int}
    (h : p.inRange n = true) : numLit (C := C) (Γ := Γ) p hp n = .lit n h := dif_pos h

/-- A word as a literal. -/
def litOf {Γ : Ctx} : (p : PrimTy) → p.Denote → Simple C Γ p
  | .bool, b => .bool b
  | .uint, v => .lit v.1 v.2
  | .int, v => .lit v.1 v.2

/-- An index below `2^256` as a `uint`. -/
def idxU (j : Nat) (hb : j < 2 ^ 256) : PrimTy.uint.Denote :=
  (⟨(j : Int), inRange_of_lt hb⟩ : {n : Int // PrimTy.uint.inRange n = true})

/-- `{ R storage slot d = q; body }`: the alias bound for the body, which
fills through it, and ended with the block. -/
def bound {Γ : Ctx} (d : Nat) (R : RefTy) (q : SPath C Γ (.ref R))
    (body : Prog C (.alias R :: Γ) (.alias R :: Γ)) : Prog C Γ Γ :=
  .cons (.block (.cons (.declStorage R (slot d) (some (.path q))) body)) .nil

mutual

/-- A program that turns the default at `q : T` into `v`.  A word is
assigned.  Anything else binds an alias to `q` in a block and fills through
it: a struct member by member; a dynamic array by pushing every slot it has,
popping those past its end one at a time (each bound to a deeper alias
before its `pop`, and filled through it after), then filling the live
elements; a fixed-size array element by element; a mapping entry by entry,
each created by a `delete` first. -/
def fill {Γ : Ctx} (d : Nat) : {T : Ty} → SPath C Γ T → SVal T → Prog C Γ Γ
  | .prim _, .loc l, .prim v => .cons (.assign l (.val (.simple (litOf _ v)))) .nil
  | .ref (.struct _), q, .struct fs =>
    bound d _ q (fillFields d .here (fun _ _ hm => lookupBy_of_nodup (structDef_nodup _) hm) fs)
  | .ref (.array E), q, @SVal.array _ n e sh _ =>
    bound d _ q
      (if hE : E.defaultOkS = true then
        (Prog.rep (n + sh.length)
            (.push (.alias .here : SPath C _ (.array E)) none (by simp only [Option.isSome_none,
                hE, Bool.or_true]))).append
          ((fillShadow d .here n sh).append (fillElems d (ArrTy.dyn (E := E)) .here 0 e))
      else .nil)
  | .ref (.fixed E n), q, .fixed e => bound d _ q (fillElems d (ArrTy.fixed (E := E) (n := n)) .here 0 e)
  | .ref (.mapping K _), q, .map m _ => bound d _ q (fillEntries d K .here m)

/-- The members of a struct bound to `a`, one after another. -/
def fillFields {Γ : Ctx} (d : Nat) {s : Name} (a : Idx Γ (.alias (.struct s))) :
    {fs : List (Name × Ty)} → (∀ f T, (f, T) ∈ fs → lookupBy f (structDef s) = some T) →
    SFields fs → Prog C Γ Γ
  | _, _, .nil => .nil
  | (f, T) :: _, hsub, .cons v rest =>
      (fill (d + 1) (.loc (.field (.alias a) f (hsub f T List.mem_cons_self))) v).append
        (fillFields d a (fun g U hm => hsub g U (List.mem_cons_of_mem _ hm)) rest)

/-- The slots past the end of the array bound to `a`, from the last: slot
`i` bound, popped, then filled through its alias.  A word slot is only
popped (it is cleared). -/
def fillShadow {Γ : Ctx} (d : Nat) {E : Ty} (a : Idx Γ (.alias (.array E))) (i : Nat) :
    SList E → Prog C Γ Γ
  | .nil => .nil
  | .cons w rest =>
      (fillShadow d a (i + 1) rest).append
        (match (generalizing := false) hE : E with
         | .prim _ => .cons (.pop (.alias a)) .nil
         | .ref R => bound (d + 1) R
             (hE ▸ .loc (.index (.arr .dyn) (.alias a) (.simple (numLit .uint rfl (i : Int)))))
             (.cons (.pop (.alias a.there)) (fill (d + 1) (hE ▸ .alias .here) w)))

/-- The live elements of the array bound to `a`, from index `j`. -/
def fillElems {Γ : Ctx} (d : Nat) {R : RefTy} {E : Ty} (ak : ArrTy R E) (a : Idx Γ (.alias R))
    (j : Nat) : {n : Nat} → SVec E n → Prog C Γ Γ
  | _, .nil => .nil
  | _, .cons w rest =>
      (fill (d + 1) (.loc (.index (.arr ak) (.alias a) (.simple (numLit .uint rfl (j : Int))))) w).append
        (fillElems d ak a (j + 1) rest)

/-- The entries of the mapping bound to `a`: each created by `delete`, then
filled. -/
def fillEntries {Γ : Ctx} (d : Nat) (k : PrimTy) {V : Ty}
    (a : Idx Γ (.alias (.mapping k V))) : SMap k V → Prog C Γ Γ
  | .nil => .nil
  | .cons key w rest =>
      .cons (.delete (.index .map (.alias a) (.simple (litOf k key)) : Loc C Γ V))
        ((fill (d + 1) (.loc (.index .map (.alias a) (.simple (litOf k key)))) w).append
          (fillEntries d k a rest))

end

/-! ## Saves at one path -/

section Wrote

variable {st₀ st st' : Storage C} {U : Ty} {r : SRef C U}

/-- A save, by its compiled form. -/
theorem Storage.save_eq {X : SVal U} :
    st.save r X = ((st.get r.hroot).saveM r.path X).map (st.set r.hroot) := by
  simp only [Storage.save, SVal.save_eq_saveM, Option.bind_eq_bind]
  cases (st.get r.hroot).saveM r.path X <;> rfl

/-- `st` is `st₀` with `X` saved at `r`. -/
def Wrote (st₀ st : Storage C) {U : Ty} (r : SRef C U) (X : SVal U) : Prop := st₀.save r X = some st

theorem Wrote.find {X : SVal U} (h : Wrote st₀ st r X) : st.find r = some X := by
  unfold Wrote at h
  rw [Storage.save_eq] at h
  cases hv : (st₀.get r.hroot).saveM r.path X with
  | none => rw [hv] at h; exact nomatch h
  | some v =>
    rw [hv] at h
    cases h
    show ((st₀.set r.hroot v).get r.hroot).find r.path = some X
    rw [SFields.get_set_same, SVal.find_eq_findM]
    exact SVal.findM_saveM _ _ _ hv

theorem Wrote.idem {X : SVal U} (h : Wrote st₀ st r X) : st.save r X = some st := by
  unfold Wrote at h
  rw [Storage.save_eq] at h ⊢
  cases hv : (st₀.get r.hroot).saveM r.path X with
  | none => rw [hv] at h; exact nomatch h
  | some v =>
    rw [hv] at h
    cases h
    rw [SFields.get_set_same, SVal.saveM_idem _ _ _ hv]
    simp only [Option.map_some, SFields.set_set]

theorem Wrote.trans {X Y : SVal U} (h : Wrote st₀ st r X) (h' : st.save r Y = some st') :
    Wrote st₀ st' r Y := by
  unfold Wrote at h ⊢
  rw [Storage.save_eq] at h h' ⊢
  cases hv : (st₀.get r.hroot).saveM r.path X with
  | none => rw [hv] at h; exact nomatch h
  | some v =>
    rw [hv] at h
    cases h
    rw [SFields.get_set_same] at h'
    cases hv' : v.saveM r.path Y with
    | none => rw [hv'] at h'; exact nomatch h'
    | some v' =>
      rw [hv'] at h'
      cases h'
      rw [SVal.saveM_saveM _ _ _ _ hv hv']
      simp only [Option.map_some, SFields.set_set]

/-- A child saved below a path written: the value written there changes. -/
theorem Wrote.child {N : SVal U} {W : Ty} {q : Path U W} {w : SVal W} (h : Wrote st₀ st r N)
    (h' : st.save (r.append q) w = some st') :
    ∃ N', N.saveM q w = some N' ∧ Wrote st₀ st' r N' := by
  have hf := h.find
  rw [Storage.save_eq] at h'
  cases hv : (st.get r.hroot).saveM (r.path.append q) w with
  | none =>
    change ((st.get r.hroot).saveM (r.path.append q) w).map _ = _ at h'
    rw [hv] at h'; exact nomatch h'
  | some v =>
    change ((st.get r.hroot).saveM (r.path.append q) w).map _ = _ at h'
    rw [hv] at h'
    cases h'
    obtain ⟨y, y', hy, hy', hv'⟩ := SVal.saveM_append _ _ _ _ hv
    have hN : y = N := by
      have : (st.get r.hroot).find r.path = some N := hf
      rw [SVal.find_eq_findM, hy] at this
      exact Option.some.inj this
    subst hN
    refine ⟨y', hy', h.trans ?_⟩
    rw [Storage.save_eq, hv']
    rfl

/-- Saving the value a child already holds, below a path written, changes
nothing. -/
theorem Wrote.childNoop {N : SVal U} {W : Ty} {q : Path U W} {D : SVal W} (h : Wrote st₀ st r N)
    (hq : N.saveM q D = some N) : st.save (r.append q) D = some st := by
  have hf := h.find
  have hi := h.idem
  rw [Storage.save_eq] at hi ⊢
  change ((st.get r.hroot).saveM (r.path.append q) D).map _ = _
  rw [SVal.saveM_append_eq]
  have hy : (st.get r.hroot).findM r.path = some N := by
    rw [← SVal.find_eq_findM]; exact hf
  rw [hy]
  simp only [Option.bind_some, hq]
  exact hi

end Wrote

/-! ## Runs -/

section Steps

variable {Γ : Ctx}

/-- `P` runs, by the typed run, from `σ` to `τ`. -/
def TRuns {Γ' : Ctx} (σ : State C Γ) (P : Prog C Γ Γ') (τ : State C Γ') : Prop :=
  ∃ o : Out C σ.H Γ', P.run σ = .ok o ∧ o.st = τ

/-- `s` runs, by the typed run, from `σ` to `τ`. -/
def SRuns {Γ' : Ctx} (σ : State C Γ) (s : Stmt C Γ Γ') (τ : State C Γ') : Prop :=
  ∃ o : Out C σ.H Γ', s.run σ = .ok o ∧ o.st = τ

theorem TRuns.nil (σ : State C Γ) : TRuns σ (.nil : Prog C Γ Γ) σ := ⟨_, rfl, rfl⟩

theorem TRuns.cons {Γ₁ Γ₂ : Ctx} {σ : State C Γ} {s : Stmt C Γ Γ₁} {P : Prog C Γ₁ Γ₂}
    {τ : State C Γ₁} {υ : State C Γ₂} (hs : SRuns σ s τ) (hP : TRuns τ P υ) :
    TRuns σ (.cons s P) υ := by
  obtain ⟨o, ho, rfl⟩ := hs
  obtain ⟨o', ho', rfl⟩ := hP
  exact ⟨_, by rw [Prog.run_cons_ok ho, ho']; rfl, rfl⟩

theorem TRuns.cons_inv {Γ₁ Γ₂ : Ctx} {σ : State C Γ} {s : Stmt C Γ Γ₁} {P : Prog C Γ₁ Γ₂}
    {υ : State C Γ₂} (h : TRuns σ (.cons s P) υ) : ∃ τ, SRuns σ s τ ∧ TRuns τ P υ := by
  obtain ⟨o, ho, rfl⟩ := h
  cases hs : s.run σ with
  | error e =>
    have he : Prog.run σ (.cons s P) = .error e := by
      show TRun.seq s.runR P.runR σ = _
      simp only [TRun.seq, Stmt.run] at hs ⊢
      rw [hs]
    rw [he] at ho
    cases ho
  | ok o₁ =>
    rw [Prog.run_cons_ok hs] at ho
    cases hp : Prog.run o₁.st P with
    | error e => rw [hp] at ho; cases ho
    | ok o₂ =>
      rw [hp] at ho
      cases ho
      exact ⟨o₁.st, ⟨o₁, hs, rfl⟩, ⟨o₂, hp, rfl⟩⟩

theorem TRuns.append : {Γ Δ Ε : Ctx} → {σ : State C Γ} → {P : Prog C Γ Δ} →
    {Q : Prog C Δ Ε} → {τ : State C Δ} → {υ : State C Ε} → TRuns σ P τ → TRuns τ Q υ →
    TRuns σ (P.append Q) υ
  | _, _, _, _, .nil, _, _, _, hP, hQ => by
    obtain ⟨o, ho, rfl⟩ := hP
    cases ho
    exact hQ
  | _, _, _, _, .cons _ _, _, _, _, hP, hQ =>
    let ⟨_, hs, hP'⟩ := hP.cons_inv
    TRuns.cons hs (TRuns.append hP' hQ)

theorem TRuns.single {Γ' : Ctx} {σ : State C Γ} {s : Stmt C Γ Γ'} {τ : State C Γ'}
    (h : SRuns σ s τ) : TRuns σ (.cons s .nil) τ :=
  TRuns.cons h (TRuns.nil _)

/-! ### Paths the builder resolves -/

theorem resolveT_alias {σ : State C Γ} {R : RefTy} {a : Idx Γ (.alias R)} {ref : SRef C (.ref R)}
    (h : TEnv.get a σ.env = some ref) : (SPath.alias a).resolveT σ = .ok ref := by
  show (match (TEnv.get a σ.env : Option (SRef C _)) with
    | some r => .ok r
    | none => .error .revert : TRes _) = _
  rw [h]

theorem resolveT_field {σ : State C Γ} {s f : Name} {T : Ty} {a : Idx Γ (.alias (.struct s))}
    {ref : SRef C (.ref (.struct s))} (hf : C.fieldType s f = some T)
    (h : TEnv.get a σ.env = some ref) :
    (Loc.field (C := C) (.alias a) f hf).resolveT σ = .ok (ref.field hf) := by
  show (do let r ← (SPath.alias a).resolveT σ; pure (r.field hf) : TRes _) = _
  rw [resolveT_alias h]
  rfl

theorem litOf_evalT (σ : State C Γ) : (p : PrimTy) → (v : p.Denote) →
    (litOf (C := C) (Γ := Γ) p v).evalT σ = v
  | .bool, _ | .uint, _ | .int, _ => rfl

/-- An index the storage takes, at a literal. -/
theorem resolveT_index_lit {σ : State C Γ} {R : RefTy} {E : Ty} (ak : ArrTy R E)
    {a : Idx Γ (.alias R)} {ref : SRef C (.ref R)} {j : Nat} (hb : j < 2 ^ 256)
    (h : TEnv.get a σ.env = some ref)
    (hck : σ.storage.checkIndex ref (.arr ak) (idxU j hb) = some ()) :
    (Loc.index (C := C) (.arr ak) (.alias a) (.simple (numLit .uint rfl (j : Int)))).resolveT σ =
      .ok (ref.index (.arr ak) (idxU j hb)) := by
  rw [numLit_eq (inRange_of_lt hb)]
  show (do
    let r ← (SPath.alias a).resolveT σ
    let k ← (Val.simple (Simple.lit (C := C) (Γ := Γ) (p := .uint) (j : Int) _)).evalT σ
    TRes.ofOpt (σ.storage.checkIndex r (.arr ak) k)
    pure (r.index (.arr ak) k) : TRes _) = _
  rw [resolveT_alias h]
  simp only [bind, Except.bind, Val.evalT, Simple.evalT]
  rw [show PrimTy.ofLit .uint (j : Int) (inRange_of_lt hb) = idxU j hb from rfl, hck]
  rfl

theorem resolveT_index_map {σ : State C Γ} {k : PrimTy} {V : Ty} {key : k.Denote}
    {a : Idx Γ (.alias (.mapping k V))}
    {ref : SRef C (.ref (.mapping k V))} (h : TEnv.get a σ.env = some ref)
    (hfind : ∃ v, σ.storage.find ref = some v) :
    (Loc.index (C := C) (V := V) .map (.alias a) (.simple (litOf k key))).resolveT σ =
      .ok (ref.index .map key) := by
  obtain ⟨v, hv⟩ := hfind
  have hck : σ.storage.checkIndex ref (.map (V := V)) key = some () := by
    simp only [Storage.checkIndex, hv, Option.bind_eq_bind, Option.bind_some]
    rfl
  show (do
    let r ← (SPath.alias a).resolveT σ
    let x ← (Val.simple (litOf (C := C) (Γ := Γ) k key)).evalT σ
    TRes.ofOpt (σ.storage.checkIndex r .map x)
    pure (r.index .map x) : TRes _) = _
  rw [resolveT_alias h]
  simp only [bind, Except.bind, Val.evalT]
  rw [litOf_evalT σ, hck]
  rfl

/-! ### One statement at a time

Each step of the builder, from a state whose storage is `st₀` with `X`
written at a reference, leaves the state with only its storage replaced, by
`st₀` with what the step makes of `X` written there. -/

/-- A save lands where a value is found. -/
theorem Wrote.save_exists {st₀ st : Storage C} {U : Ty} {r : SRef C U} {X : SVal U}
    (h : Wrote st₀ st r X) (Y : SVal U) : ∃ st', st.save r Y = some st' := by
  have hf : (st.get r.hroot).findM r.path = some X := by rw [← SVal.find_eq_findM]; exact h.find
  obtain ⟨v, hv⟩ := SVal.saveM_of_findM _ _ hf Y
  exact ⟨_, by rw [Storage.save_eq, hv]; rfl⟩

/-- `l = v;` for a word `v`. -/
theorem run_assign {σ : State C Γ} {p : PrimTy} {l : Loc C Γ (.prim p)} {ref : SRef C (.prim p)}
    (hl : l.resolveT σ = .ok ref) {st₀ : Storage C} {X : SVal (.prim p)}
    (hW : Wrote st₀ σ.storage ref X) (v : p.Denote) :
    ∃ st', SRuns σ (.assign l (.val (.simple (litOf p v)))) (σ.withStorage st') ∧
      Wrote st₀ st' ref (.prim v) := by
  obtain ⟨st', hs⟩ := hW.save_exists (.prim v)
  refine ⟨st', ⟨⟨σ.withStorage st', List.prefix_refl _⟩, ?_, rfl⟩, hW.trans hs⟩
  show TRun.assign l (.val (.simple (litOf p v))) σ = _
  simp only [TRun.assign, Src.valueT, Val.evalT, litOf_evalT, bind, Except.bind, pure, Except.pure]
  rw [hl]
  simp only [Storage.write, SVal.isPrim, Ty.isPrimitive, ↓reduceIte, hs, TRes.ofOpt]

/-- The literal array of `L` and `S`. -/
def arrOf {E : Ty} (L S : List (SVal E)) (h : L.length < 2 ^ 256) : SVal (.ref (.array E)) :=
  .array (SVec.ofList L) (SList.ofList S) h

theorem arrOf_congr {E : Ty} {L L' S : List (SVal E)} {h : L.length < 2 ^ 256}
    {h' : L'.length < 2 ^ 256} (hL : L = L') : arrOf L S h = arrOf L' S h' := by
  subst hL; rfl

theorem Wrote.arr_congr {st₀ st : Storage C} {E : Ty} {r : SRef C (.ref (.array E))}
    {L L' S : List (SVal E)} {h : L.length < 2 ^ 256} {h' : L'.length < 2 ^ 256}
    (hW : Wrote st₀ st r (arrOf L S h)) (e : L = L') : Wrote st₀ st r (arrOf L' S h') := by
  subst e; exact hW

theorem len_snoc {α : Type} {L : List α} {x : α} (hb : L.length + 1 < 2 ^ 256) :
    (L ++ [x]).length < 2 ^ 256 := by
  rw [List.length_append, List.length_singleton]; exact hb

/-- `a.push();` on an array with nothing past its end, below the bound. -/
theorem run_push {σ : State C Γ} {E : Ty} {a : Idx Γ (.alias (.array E))}
    {ref : SRef C (.ref (.array E))} (hd : (none.isSome || E.defaultOkS) = true)
    (ha : TEnv.get a σ.env = some ref) {st₀ : Storage C} {L : List (SVal E)}
    {hL : L.length < 2 ^ 256} (hW : Wrote st₀ σ.storage ref (arrOf L [] hL))
    (hb : L.length + 1 < 2 ^ 256) :
    ∃ st', SRuns σ (.push (C := C) (.alias a : SPath C Γ (.array E)) none hd)
        (σ.withStorage st') ∧
      Wrote st₀ st' ref (arrOf (L ++ [SVal.dflt E]) [] (len_snoc hb)) := by
  have hf := hW.find
  have hb' : L.length + 1 < 2 ^ 256 := hb
  have hfull : σ.storage.full ref = false := by
    simp only [Storage.full, hf, arrOf, SVal.view_array, hb', decide_true, Bool.not_true]
  obtain ⟨st', hs⟩ := hW.save_exists (arrOf (L ++ [SVal.dflt E]) [] (len_snoc hb))
  refine ⟨st', ⟨⟨σ.withStorage st', List.prefix_refl _⟩, ?_, rfl⟩, hW.trans hs⟩
  show TRun.push (.alias a) none σ = _
  simp only [TRun.push, bind, Except.bind, pure, Except.pure]
  rw [resolveT_alias ha]
  simp only [hfull, Bool.false_eq_true, ↓reduceIte, Storage.push, hf, arrOf, SVal.view_array,
    Option.bind_eq_bind, Option.bind_some, Option.getD_none]
  rw [dif_pos hb']
  have hX : ∀ pf, SVal.array (SVec.ofList ((SVec.ofList L).toList ++
      [(pushSlot E (SList.ofList ([] : List (SVal E))).toList).fst]))
      (SList.ofList (pushSlot E (SList.ofList ([] : List (SVal E))).toList).snd) pf =
      arrOf (L ++ [SVal.dflt E]) [] (len_snoc hb) := fun _ =>
    SVal.array_ext _ _ _ _ _ _ (by simp only [SVec.toList_ofList, SList.toList_ofList, pushSlot])
      (by simp only [SList.toList_ofList, pushSlot])
  rw [hX, hs]
  rfl

/-- `a.pop();` on an array whose live elements end in `last`. -/
theorem run_pop {σ : State C Γ} {E : Ty} {a : Idx Γ (.alias (.array E))}
    {ref : SRef C (.ref (.array E))} (ha : TEnv.get a σ.env = some ref) {st₀ : Storage C}
    {L S : List (SVal E)} {last : SVal E} {hL : (L ++ [last]).length < 2 ^ 256}
    (hW : Wrote st₀ σ.storage ref (arrOf (L ++ [last]) S hL)) :
    ∃ st', SRuns σ (.pop (C := C) (E := E) (.alias a)) (σ.withStorage st') ∧
      Wrote st₀ st' ref (arrOf L ((if E.isMapping then last else last.defaultOf) :: S)
        (Nat.lt_of_le_of_lt (by rw [List.length_append]; omega) hL)) := by
  have hf := hW.find
  obtain ⟨st', hs⟩ := hW.save_exists (arrOf L ((if E.isMapping then last else last.defaultOf) :: S)
    (Nat.lt_of_le_of_lt (by rw [List.length_append]; omega) hL))
  refine ⟨st', ⟨⟨σ.withStorage st', List.prefix_refl _⟩, ?_, rfl⟩, hW.trans hs⟩
  show TRun.pop (.alias a) σ = _
  simp only [TRun.pop, bind, Except.bind, pure, Except.pure]
  rw [resolveT_alias ha]
  simp only [Storage.pop, hf, arrOf, SVal.view_array, Option.bind_eq_bind, Option.bind_some,
    SVec.toList_ofList, List.reverse_append, List.reverse_cons, List.reverse_nil, List.nil_append,
    List.cons_append, SList.toList_ofList]
  have hX : ∀ pf, SVal.array (SVec.ofList (SVec.ofList (L ++ [last])).toList.dropLast)
      (SList.ofList ((if E.isMapping then last else last.defaultOf) :: S)) pf =
      arrOf L ((if E.isMapping then last else last.defaultOf) :: S)
        (Nat.lt_of_le_of_lt (by rw [List.length_append]; omega) hL) := fun _ =>
    SVal.array_ext _ _ _ _ _ _ (by simp only [SVec.toList_ofList, List.dropLast_concat]) rfl
  rw [hX, hs]
  rfl

/-- `delete l;`. -/
theorem run_delete {σ : State C Γ} {T : Ty} {l : Loc C Γ T} {ref : SRef C T}
    (hl : l.resolveT σ = .ok ref) {cur : SVal T} (hf : σ.storage.find ref = some cur)
    {st' : Storage C} (hs : σ.storage.save ref cur.defaultOf = some st') :
    SRuns σ (.delete l) (σ.withStorage st') := by
  refine ⟨⟨σ.withStorage st', List.prefix_refl _⟩, ?_, rfl⟩
  show TRun.delete l σ = _
  simp only [TRun.delete, bind, Except.bind]
  rw [hl]
  simp only [Storage.delete, hf, Option.bind_eq_bind, Option.bind_some, hs, TRes.ofOpt]
  rfl

/-- The alias a `bound` block declares, bound to `q`. -/
theorem run_decl {d : Nat} {R : RefTy} {σ : State C Γ} {q : SPath C Γ (.ref R)}
    {ref : SRef C (.ref R)} (hq : q.resolveT σ = .ok ref) :
    SRuns σ (.declStorage R (slot d) (some (.path q))) (σ.push (t := .alias R) (some ref)) := by
  refine ⟨⟨σ.push (t := .alias R) (some ref), List.prefix_refl _⟩, ?_, rfl⟩
  show TRun.declStorage R (some (.path q)) σ = _
  simp only [TRun.declStorage, ARhs.evalT, bind, Except.bind, pure, Except.pure]
  rw [hq]
  rfl

theorem run_block {Γ₁ : Ctx} (σ : State C Γ) (P : Prog C Γ Γ₁) :
    Stmt.run σ (.block P) = (Prog.run σ P).map fun o => ⟨o.st.drop P.ext, o.ext⟩ := rfl

/-- A block that binds an alias to `q` and runs `body` through it, changing
only the storage. -/
theorem run_bound {d : Nat} {R : RefTy} {σ : State C Γ} {q : SPath C Γ (.ref R)}
    {ref : SRef C (.ref R)} (hq : q.resolveT σ = .ok ref)
    {body : Prog C (.alias R :: Γ) (.alias R :: Γ)} {st' : Storage C}
    (hb : TRuns (σ.push (t := .alias R) (some ref)) body
      ((σ.push (t := .alias R) (some ref)).withStorage st')) :
    TRuns σ (bound d R q body) (σ.withStorage st') := by
  obtain ⟨o, ho, he⟩ := TRuns.cons (run_decl (d := d) hq) hb
  have h : TRuns σ (bound d R q body) (o.st.drop (.push .refl)) := by
    refine TRuns.single ⟨⟨o.st.drop (.push .refl), o.ext⟩, ?_, rfl⟩
    rw [run_block, ho, Ext.eq_of_depth (Prog.ext _) (.push .refl)]
    rfl
  rw [he] at h
  exact h

/-- `run_bound` at a location. -/
theorem run_boundL {d : Nat} {R : RefTy} {σ : State C Γ} {l : Loc C Γ (.ref R)}
    {ref : SRef C (.ref R)} (hq : l.resolveT σ = .ok ref)
    {body : Prog C (.alias R :: Γ) (.alias R :: Γ)} {st' : Storage C}
    (hb : TRuns (σ.push (t := .alias R) (some ref)) body
      ((σ.push (t := .alias R) (some ref)).withStorage st')) :
    TRuns σ (bound d R (.loc l) body) (σ.withStorage st') :=
  run_bound (q := .loc l) hq hb

end Steps

/-! ## The builder writes what it is given -/

section Fills

/-! ### Saves at one slot -/

theorem arrOf_saveM_live {E : Ty} {L S : List (SVal E)} (h : L.length < 2 ^ 256) {i : Nat}
    (hi : i < L.length) (x : SVal E) :
    (arrOf L S h).saveM (.at (idxU i (Nat.lt_trans hi h)) .nil) x =
      some (arrOf (L.set i x) S (by rw [List.length_set]; exact h)) := by
  have hl : i < (L ++ S).length := by rw [List.length_append]; omega
  simp only [arrOf, SVal.saveM, idxU, Int.natCast_nonneg, ↓reduceIte, SVec.toList_ofList,
    SList.toList_ofList, Int.toNat_natCast, List.getElem?_eq_getElem hl, SVal.saveM_nil,
    Option.bind_eq_bind, Option.bind_some]
  congr 1
  apply SVal.array_ext
  · simp only [SVec.toList_ofList]
    rw [List.set_append_left _ _ hi, List.take_left' (List.length_set ..)]
  · simp only [SList.toList_ofList]
    rw [List.set_append_left _ _ hi, List.drop_left' (List.length_set ..)]

theorem arrOf_saveM_shadow {E : Ty} {L S : List (SVal E)} (h : L.length < 2 ^ 256) {i : Nat}
    (hi : L.length ≤ i) (hi' : i < L.length + S.length) (hb : i < 2 ^ 256) (x : SVal E) :
    (arrOf L S h).saveM (.at (idxU i hb) .nil) x = some (arrOf L (S.set (i - L.length) x) h) := by
  have hl : i < (L ++ S).length := by rw [List.length_append]; omega
  simp only [arrOf, SVal.saveM, idxU, Int.natCast_nonneg, ↓reduceIte, SVec.toList_ofList,
    SList.toList_ofList, Int.toNat_natCast, List.getElem?_eq_getElem hl, SVal.saveM_nil,
    Option.bind_eq_bind, Option.bind_some]
  congr 1
  apply SVal.array_ext
  · simp only [SVec.toList_ofList]
    rw [List.set_append_right _ _ hi, List.take_left' rfl]
  · simp only [SList.toList_ofList]
    rw [List.set_append_right _ _ hi, List.drop_left' rfl]

theorem fixed_saveM {E : Ty} {n : Nat} (e : SVec E n) {i : Nat} (hi : i < n) (hb : i < 2 ^ 256)
    (x : SVal E) : (SVal.fixed e).saveM (.atF (idxU i hb) .nil) x = some (.fixed (e.set i x)) := by
  have hl : i < e.toList.length := by rw [SVec.length_toList]; exact hi
  simp only [SVal.saveM, idxU, Int.natCast_nonneg, ↓reduceIte, Int.toNat_natCast,
    List.getElem?_eq_getElem hl, SVal.saveM_nil, Option.bind_eq_bind, Option.bind_some]

theorem map_saveM {K : PrimTy} {V : Ty} (m : SMap K V) (d : SVal V) (k : K.Denote) (x : SVal V) :
    (SVal.map (K := K) m d).saveM (.key k .nil) x = some (.map (.ofList (setBy k x m.toList)) d) := by
  simp only [SVal.saveM]
  split <;> simp only [Option.bind_eq_bind, Option.bind_some]

/-! ### A child filled -/

/-- What `fill` does for one value `v`: from a path where saving the default
changes nothing, in any context, it leaves `v` there, changing nothing but
the storage. -/
def FillOK (C : Contract) {T : Ty} (v : SVal T) : Prop :=
  ∀ (d : Nat) (Γ : Ctx) (q : SPath C Γ T) (σ : State C Γ) (ref : SRef C T),
    v.Canon → v.Tight → v.Fits → q.resolveT σ = .ok ref →
    σ.storage.save ref (SVal.dflt T) = some σ.storage →
    ∃ st', TRuns σ (fill d q v) (σ.withStorage st') ∧ σ.storage.save ref v = some st'

variable {Γ : Ctx}

/-- A child filled below the node written at `ref`: the node, `N`, becomes
`N'`. -/
theorem child_step {d : Nat} {T W : Ty} {q : SPath C Γ W} {σ : State C Γ} {st₀ : Storage C}
    {ref : SRef C T} {N N' : SVal T} {p : Path T W} {w : SVal W}
    (hw : FillOK C w) (hc : w.Canon) (ht : w.Tight) (hf : w.Fits)
    (hq : q.resolveT σ = .ok (ref.append p)) (hW : Wrote st₀ σ.storage ref N)
    (hnoop : N.saveM p (SVal.dflt W) = some N) (hs : N.saveM p w = some N') :
    ∃ st', TRuns σ (fill (d + 1) q w) (σ.withStorage st') ∧ Wrote st₀ st' ref N' := by
  obtain ⟨st', hrun, hsave⟩ := hw (d + 1) Γ q σ (ref.append p) hc ht hf hq (hW.childNoop hnoop)
  obtain ⟨N'', hN'', hW'⟩ := hW.child hsave
  rw [hs] at hN''
  cases hN''
  exact ⟨st', hrun, hW'⟩

/-- `child_step` at a location. -/
theorem child_stepL {d : Nat} {T W : Ty} {l : Loc C Γ W} {σ : State C Γ} {st₀ : Storage C}
    {ref : SRef C T} {N N' : SVal T} {p : Path T W} {w : SVal W}
    (hw : FillOK C w) (hc : w.Canon) (ht : w.Tight) (hf : w.Fits)
    (hq : l.resolveT σ = .ok (ref.append p)) (hW : Wrote st₀ σ.storage ref N)
    (hnoop : N.saveM p (SVal.dflt W) = some N) (hs : N.saveM p w = some N') :
    ∃ st', TRuns σ (fill (d + 1) (.loc l) w) (σ.withStorage st') ∧ Wrote st₀ st' ref N' :=
  child_step hw hc ht hf hq hW hnoop hs

/-- `a.push();` `k` times on an array with nothing past its end, below the
bound. -/
theorem pushes_run {E : Ty} {a : Idx Γ (.alias (.array E))} {ref : SRef C (.ref (.array E))}
    (hd : (none.isSome || E.defaultOkS) = true) {st₀ : Storage C} :
    ∀ (k : Nat) (L : List (SVal E)) (σ : State C Γ) (hL : L.length < 2 ^ 256),
      TEnv.get a σ.env = some ref → Wrote st₀ σ.storage ref (arrOf L [] hL) →
      (hk : L.length + k < 2 ^ 256) →
      ∃ st', TRuns σ (Prog.rep k (Stmt.push (C := C) (.alias a : SPath C Γ (.array E)) none hd))
        (σ.withStorage st') ∧
        Wrote st₀ st' ref (arrOf (L ++ List.replicate k (SVal.dflt E)) []
          (by rw [List.length_append, List.length_replicate]; exact hk))
  | 0, L, σ, hL, _, hW, _ => ⟨σ.storage, TRuns.nil σ, by simpa only [List.replicate_zero,
      List.append_nil] using hW⟩
  | k + 1, L, σ, hL, ha, hW, hk => by
    obtain ⟨st₁, hs₁, hW₁⟩ := run_push hd ha hW (by omega)
    obtain ⟨st', hrun, hW'⟩ := pushes_run hd k (L ++ [SVal.dflt E]) (σ.withStorage st₁) _ ha hW₁
      (by rw [List.length_append, List.length_singleton]; omega)
    refine ⟨st', TRuns.cons hs₁ hrun, ?_⟩
    simpa only [List.append_assoc, List.replicate_succ, List.singleton_append] using hW'

/-! ### Structs, member by member -/

/-- What `fillFields` does for the members `x` (a suffix of the struct's):
from a node `N` holding the default at each member still to fill and the
target `tgt` at every other, it leaves the target there. -/
def FieldsOK (C : Contract) {fs : List (Name × Ty)} (x : SFields fs) : Prop :=
  ∀ (s : Name) (d : Nat) (Γ : Ctx) (a : Idx Γ (.alias (.struct s)))
    (hsub : ∀ f T, (f, T) ∈ fs → lookupBy f (structDef s) = some T) (σ : State C Γ)
    (ref : SRef C (.ref (.struct s))) (st₀ : Storage C) (N tgt : SFields (structDef s)),
    TEnv.get a σ.env = some ref → Wrote st₀ σ.storage ref (.struct N) →
    (∀ g U (hg : lookupBy g (structDef s) = some U), (∃ V, (g, V) ∈ fs) → N.get hg = SVal.dflt U) →
    (∀ g U (hg : lookupBy g (structDef s) = some U), (¬∃ V, (g, V) ∈ fs) → N.get hg = tgt.get hg) →
    (∀ g U (h' : lookupBy g fs = some U) (hg : lookupBy g (structDef s) = some U),
      x.get h' = tgt.get hg) →
    x.All canonH → x.All tightH → x.All fitsH → nodupKeysB fs = true →
    ∃ st', TRuns σ (fillFields d a hsub x) (σ.withStorage st') ∧ Wrote st₀ st' ref (.struct tgt)

theorem fields_nil : FieldsOK C SFields.nil := by
  intro s d Γ a hsub σ ref st₀ N tgt _ hW _ h2 _ _ _ _ _
  have hN : N = tgt := SFields.ext_get (structDef_nodup s) N tgt fun g U hg =>
    h2 g U hg fun ⟨_, hm⟩ => nomatch hm
  subst hN
  exact ⟨σ.storage, TRuns.nil σ, hW⟩

theorem fields_cons {f : Name} {T : Ty} {fs : List (Name × Ty)} {v : SVal T} {rest : SFields fs}
    (hv : FillOK C v) (hrest : FieldsOK C rest) :
    FieldsOK C (SFields.cons (f := f) v rest) := by
  intro s d Γ a hsub σ ref st₀ N tgt ha hW h1 h2 hag hc ht hf hnd
  simp only [SFields.All] at hc ht hf
  simp only [nodupKeysB, Bool.and_eq_true, Option.isNone_iff_eq_none] at hnd
  have hfT : lookupBy f (structDef s) = some T := hsub f T List.mem_cons_self
  have hN : N.get hfT = SVal.dflt T := h1 f T hfT ⟨T, List.mem_cons_self⟩
  have hhead : v = tgt.get hfT := by
    have h0 : lookupBy f ((f, T) :: fs) = some T := by simp only [lookupBy, ↓reduceIte]
    have := hag f T h0 hfT
    simp only [SFields.get_cons, dite_true] at this
    exact this
  have hnoop : (SVal.struct N).saveM (.field hfT .nil) (SVal.dflt T) = some (.struct N) := by
    simp only [SVal.saveM, SVal.saveM_nil, Option.bind_eq_bind, Option.bind_some]
    rw [← hN, SFields.set_get_self]
  have hs : (SVal.struct N).saveM (.field hfT .nil) v = some (.struct (N.set hfT v)) := by
    simp only [SVal.saveM, SVal.saveM_nil, Option.bind_eq_bind, Option.bind_some]
  obtain ⟨st₁, hrun₁, hW₁⟩ := child_stepL (d := d) (p := .field hfT .nil) hv hc.1 ht.1 hf.1 (resolveT_field hfT ha) hW hnoop hs
  have hne : ∀ g, (∃ V, (g, V) ∈ fs) → g ≠ f := fun g ⟨V, hm⟩ he => by
    have := lookupBy_isSome_of_mem' hm
    rw [he, hnd.1] at this
    exact nomatch this
  obtain ⟨st', hrun₂, hW'⟩ := hrest s d Γ a (fun g U hm => hsub g U (List.mem_cons_of_mem _ hm))
    (σ.withStorage st₁) ref st₀ (N.set hfT v) tgt ha hW₁
    (fun g U hg hm => by
      rw [SFields.get_set_ne N hfT hg (hne g hm).symm]
      exact h1 g U hg (let ⟨V, hV⟩ := hm; ⟨V, List.mem_cons_of_mem _ hV⟩))
    (fun g U hg hm => by
      by_cases hgf : g = f
      · subst hgf
        have hU : U = T := Option.some.inj (hg.symm.trans hfT)
        subst hU
        rw [SFields.get_set_same, hhead]
      · rw [SFields.get_set_ne N hfT hg (Ne.symm hgf)]
        refine h2 g U hg fun ⟨V, hV⟩ => ?_
        rcases List.mem_cons.mp hV with hV | hV
        · exact hgf (congrArg Prod.fst hV)
        · exact hm ⟨V, hV⟩)
    (fun g U h' hg => by
      have hgf : g ≠ f := hne g ⟨U, lookupBy_eq_some_mem h'⟩
      have h0 : lookupBy g ((f, T) :: fs) = some U := by
        simp only [lookupBy, hgf, ↓reduceIte]; exact h'
      have := hag g U h0 hg
      simp only [SFields.get_cons, hgf, dite_false] at this
      exact this)
    hc.2 ht.2 hf.2 hnd.2
  exact ⟨st', TRuns.append hrun₁ hrun₂, hW'⟩

/-- A struct filled member by member through an alias bound to it. -/
theorem fill_struct {s : Name} {fs : SFields (structDef s)} (hfs : FieldsOK C fs) :
    FillOK C (SVal.struct fs) := by
  intro d Γ q σ ref hc ht hf hq h0
  simp only [SVal.All] at hc ht hf
  rw [SVal.dflt_struct] at h0
  obtain ⟨st', hrun, hW⟩ := hfs s d _ .here
    (fun _ _ hm => lookupBy_of_nodup (structDef_nodup _) hm)
    (σ.push (t := .alias (.struct s)) (some ref)) ref σ.storage (SFields.dflt (structDef s)) fs
    rfl h0 (fun g U hg _ => SFields.dflt_get hg)
    (fun g U hg hm => absurd ⟨U, lookupBy_eq_some_mem hg⟩ hm) (fun _ _ _ _ => rfl) hc ht hf
    (structDef_nodup s)
  exact ⟨st', run_bound hq hrun, hW⟩

/-! ### Arrays, element by element -/

theorem checkIndex_dyn {st : Storage C} {E : Ty} {ref : SRef C (.ref (.array E))}
    {L S : List (SVal E)} {hL : L.length < 2 ^ 256} (hf : st.find ref = some (arrOf L S hL))
    {j : Nat} (hj : j < L.length) (hb : j < 2 ^ 256) :
    st.checkIndex ref (.arr .dyn) (idxU j hb) = some () := by
  simp only [Storage.checkIndex, hf, Option.bind_eq_bind, Option.bind_some]
  show (if (j : Int).toNat < L.length then some () else none) = some ()
  rw [if_pos (by rw [Int.toNat_natCast]; exact hj)]

theorem checkIndex_fixed {st : Storage C} {E : Ty} {n : Nat} {ref : SRef C (.ref (.fixed E n))}
    {e : SVec E n} (hf : st.find ref = some (.fixed e)) {j : Nat} (hj : j < n) (hb : j < 2 ^ 256) :
    st.checkIndex ref (.arr .fixed) (idxU j hb) = some () := by
  simp only [Storage.checkIndex, hf, Option.bind_eq_bind, Option.bind_some]
  show (if (j : Int).toNat < n then some () else none) = some ()
  rw [if_pos (by rw [Int.toNat_natCast]; exact hj)]

/-- What `fillElems` does for the live elements `x` of a dynamic array, from
index `pre.length`. -/
def ElemsOK (C : Contract) {E : Ty} {n : Nat} (x : SVec E n) : Prop :=
  ∀ (d : Nat) (Γ : Ctx) (a : Idx Γ (.alias (.array E))) (σ : State C Γ)
    (ref : SRef C (.ref (.array E))) (st₀ : Storage C) (pre S : List (SVal E))
    (hL : (pre ++ List.replicate n (SVal.dflt E)).length < 2 ^ 256),
    TEnv.get a σ.env = some ref →
    Wrote st₀ σ.storage ref (arrOf (pre ++ List.replicate n (SVal.dflt E)) S hL) →
    x.All canonH → x.All tightH → x.All fitsH →
    ∃ st' hL', TRuns σ (fillElems d (ArrTy.dyn (E := E)) a pre.length x) (σ.withStorage st') ∧
      Wrote st₀ st' ref (arrOf (pre ++ x.toList) S hL')

theorem elems_nil {E : Ty} : ElemsOK C (SVec.nil (E := E)) := by
  intro d Γ a σ ref st₀ pre S hL _ hW _ _ _
  refine ⟨σ.storage, by simpa only [SVec.toList_nil, List.append_nil, List.replicate_zero]
    using hL, TRuns.nil σ, ?_⟩
  simpa only [SVec.toList_nil, List.replicate_zero] using hW

theorem elems_cons {E : Ty} {n : Nat} {v : SVal E} {rest : SVec E n}
    (hv : FillOK C v) (hrest : ElemsOK C rest) : ElemsOK C (SVec.cons v rest) := by
  intro d Γ a σ ref st₀ pre S hL ha hW hc ht hf
  simp only [SVec.All] at hc ht hf
  have hlen : (pre ++ List.replicate (n + 1) (SVal.dflt E)).length = pre.length + n + 1 := by
    simp only [List.length_append, List.length_replicate]; omega
  have hj : pre.length < (pre ++ List.replicate (n + 1) (SVal.dflt E)).length := by omega
  have hq := resolveT_index_lit (C := C) (ArrTy.dyn (E := E)) (by omega) ha
    (checkIndex_dyn hW.find hj (by omega))
  rw [show ∀ hb, ref.index (.arr .dyn) (idxU pre.length hb) = ref.append (.at (idxU pre.length hb) .nil)
    from fun _ => by simp only [SRef.index, Path.index_dyn]] at hq
  have hset : ∀ x : SVal E, (pre ++ List.replicate (n + 1) (SVal.dflt E)).set pre.length x =
      (pre ++ [x]) ++ List.replicate n (SVal.dflt E) := by
    intro x
    rw [List.set_append_right _ _ (Nat.le_refl _), Nat.sub_self, List.replicate_succ,
      List.set_cons_zero, List.append_assoc, List.singleton_append]
  have hnoop : (arrOf (pre ++ List.replicate (n + 1) (SVal.dflt E)) S hL).saveM
      (.at (idxU pre.length (by omega)) .nil) (SVal.dflt E) =
      some (arrOf (pre ++ List.replicate (n + 1) (SVal.dflt E)) S hL) := by
    rw [arrOf_saveM_live hL hj]
    exact congrArg some (arrOf_congr (by rw [hset, List.append_assoc, List.singleton_append,
      ← List.replicate_succ]))
  have hs : (arrOf (pre ++ List.replicate (n + 1) (SVal.dflt E)) S hL).saveM
      (.at (idxU pre.length (by omega)) .nil) v =
      some (arrOf ((pre ++ [v]) ++ List.replicate n (SVal.dflt E)) S (by
        simp only [List.length_append, List.length_singleton, List.length_replicate]; omega)) := by
    rw [arrOf_saveM_live hL hj]
    exact congrArg some (arrOf_congr (hset v))
  obtain ⟨st₁, hrun₁, hW₁⟩ := child_stepL (d := d) hv hc.1 ht.1 hf.1 hq hW hnoop hs
  obtain ⟨st', hL', hrun₂, hW'⟩ := hrest d Γ a (σ.withStorage st₁) ref st₀ (pre ++ [v]) S _ ha hW₁
    hc.2 ht.2 hf.2
  refine ⟨st', by simpa only [SVec.toList_cons, List.append_assoc, List.singleton_append]
      using hL', TRuns.append hrun₁ ?_, ?_⟩
  · simpa only [List.length_append, List.length_singleton] using hrun₂
  · simpa only [SVec.toList_cons, List.append_assoc, List.singleton_append] using hW'

/-- What `fillElems` does for the elements `x` of a fixed-size array, from
index `pre.length`. -/
def FixedOK (C : Contract) {E : Ty} {m : Nat} (x : SVec E m) : Prop :=
  ∀ (d : Nat) (Γ : Ctx) {N : Nat} (a : Idx Γ (.alias (.fixed E N))) (σ : State C Γ)
    (ref : SRef C (.ref (.fixed E N))) (st₀ : Storage C) (pre : List (SVal E)) (cur : SVec E N),
    N ≤ 2 ^ 256 → cur.toList = pre ++ List.replicate m (SVal.dflt E) →
    TEnv.get a σ.env = some ref → Wrote st₀ σ.storage ref (.fixed cur) →
    x.All canonH → x.All tightH → x.All fitsH →
    ∃ (st' : Storage C) (cur' : SVec E N), cur'.toList = pre ++ x.toList ∧
      TRuns σ (fillElems d (ArrTy.fixed (E := E) (n := N)) a pre.length x) (σ.withStorage st') ∧
      Wrote st₀ st' ref (.fixed cur')

theorem fixedElems_nil {E : Ty} : FixedOK C (SVec.nil (E := E)) := by
  intro d Γ N a σ ref st₀ pre cur _ hcur _ hW _ _ _
  exact ⟨σ.storage, cur, by simpa only [SVec.toList_nil, List.append_nil,
    List.replicate_zero] using hcur, TRuns.nil σ, hW⟩

theorem fixedElems_cons {E : Ty} {m : Nat} {v : SVal E} {rest : SVec E m}
    (hv : FillOK C v) (hrest : FixedOK C rest) : FixedOK C (SVec.cons v rest) := by
  intro d Γ N a σ ref st₀ pre cur hN hcur ha hW hc ht hf
  simp only [SVec.All] at hc ht hf
  have hj : pre.length < N := by
    have := congrArg List.length hcur
    simp only [SVec.length_toList, List.length_append, List.length_replicate] at this
    omega
  have hq := resolveT_index_lit (C := C) (ArrTy.fixed (E := E) (n := N)) (by omega) ha
    (checkIndex_fixed hW.find hj (by omega))
  rw [show ∀ hb, ref.index (.arr .fixed) (idxU pre.length hb) =
    ref.append (.atF (idxU pre.length hb) .nil) from fun hb => by
      simp only [SRef.index, Path.index_fixed]] at hq
  have hset : ∀ x : SVal E, (cur.set pre.length x).toList =
      (pre ++ [x]) ++ List.replicate m (SVal.dflt E) := by
    intro x
    rw [SVec.toList_set, hcur, List.set_append_right _ _ (Nat.le_refl _), Nat.sub_self,
      List.replicate_succ, List.set_cons_zero, List.append_assoc, List.singleton_append]
  have hnoop : (SVal.fixed cur).saveM (.atF (idxU pre.length (by omega)) .nil) (SVal.dflt E) =
      some (.fixed cur) := by
    rw [fixed_saveM cur hj (by omega)]
    congr 2
    apply SVec.eq_of_toList_eq
    rw [hset, hcur, List.append_assoc, List.singleton_append, ← List.replicate_succ]
  obtain ⟨st₁, hrun₁, hW₁⟩ := child_stepL (d := d) hv hc.1 ht.1 hf.1 hq hW hnoop
    (fixed_saveM cur hj (by omega) v)
  obtain ⟨st', cur', hcur', hrun₂, hW'⟩ := hrest d Γ a (σ.withStorage st₁) ref st₀ (pre ++ [v])
    (cur.set pre.length v) hN (hset v) ha hW₁ hc.2 ht.2 hf.2
  refine ⟨st', cur', by simpa only [SVec.toList_cons, List.append_assoc, List.singleton_append]
      using hcur', TRuns.append hrun₁ ?_, hW'⟩
  simpa only [List.length_append, List.length_singleton] using hrun₂

/-! ### Slots past the end -/

/-- What `fillShadow` does for the slots `x` past the end, from slot `i`:
pushed as defaults, it leaves `i` live defaults and `x` past them. -/
def ShadowOK (C : Contract) {E : Ty} (x : SList E) : Prop :=
  ∀ (d : Nat) (Γ : Ctx) (a : Idx Γ (.alias (.array E))) (i : Nat) (σ : State C Γ)
    (ref : SRef C (.ref (.array E))) (st₀ : Storage C) (SH : List (SVal E))
    (hL : (List.replicate (i + x.length) (SVal.dflt E)).length < 2 ^ 256),
    TEnv.get a σ.env = some ref →
    Wrote st₀ σ.storage ref (arrOf (List.replicate (i + x.length) (SVal.dflt E)) SH hL) →
    x.All canonH → x.All tightH → x.All fitsH →
    (E.isPrimitive = true → ∀ w ∈ x.toList, w = SVal.dflt E) →
    ∃ st' hL', TRuns σ (fillShadow d a i x) (σ.withStorage st') ∧
      Wrote st₀ st' ref (arrOf (List.replicate i (SVal.dflt E)) (x.toList ++ SH) hL')

theorem shadow_nil {E : Ty} : ShadowOK C (SList.nil (E := E)) := by
  intro d Γ a i σ ref st₀ SH hL _ hW _ _ _ _
  refine ⟨σ.storage, by simpa only [SList.length_nil, Nat.add_zero] using hL, TRuns.nil σ, ?_⟩
  simpa only [SList.length_nil, Nat.add_zero, SList.toList_nil, List.nil_append] using hW

theorem SList.length_cons {E : Ty} (v : SVal E) (rest : SList E) :
    (SList.cons v rest).length = rest.length + 1 := by
  simp only [SList.length, SList.toList_cons, List.length_cons]

theorem shadow_cons {E : Ty} {v : SVal E} {rest : SList E}
    (hv : FillOK C v) (hrest : ShadowOK C rest) : ShadowOK C (SList.cons v rest) := by
  intro d Γ a i σ ref st₀ SH hL ha hW hc ht hf hprim
  simp only [SList.All] at hc ht hf
  have hlen : i + (SList.cons v rest).length = (i + 1) + rest.length := by
    rw [SList.length_cons]; omega
  obtain ⟨st₁, hL₁, hrun₁, hW₁⟩ := hrest d Γ a (i + 1) σ ref st₀ SH (by rw [← hlen]; exact hL) ha
    (hW.arr_congr (by rw [hlen])) hc.2 ht.2 hf.2
    (fun hp w hw => hprim hp w (by rw [SList.toList_cons]; exact List.mem_cons_of_mem _ hw))
  have hrep : List.replicate (i + 1) (SVal.dflt E) = List.replicate i (SVal.dflt E) ++
      [SVal.dflt E] := List.replicate_succ' ..
  have hW₁' : Wrote st₀ st₁ ref (arrOf (List.replicate i (SVal.dflt E) ++ [SVal.dflt E])
      (rest.toList ++ SH) (by rw [← hrep]; exact hL₁)) := hW₁.arr_congr hrep
  have hy : (if E.isMapping then SVal.dflt E else (SVal.dflt E).defaultOf) = SVal.dflt E := by
    split
    · rfl
    · exact SVal.defaultOf_dflt E
  have hres : (SList.cons v rest).toList ++ SH = v :: (rest.toList ++ SH) := by
    rw [SList.toList_cons, List.cons_append]
  have hi : i < 2 ^ 256 := by
    simp only [List.length_replicate] at hL; omega
  cases E with
  | prim p =>
    have hv' : v = SVal.dflt (.prim p) :=
      hprim rfl v (by rw [SList.toList_cons]; exact List.mem_cons_self)
    obtain ⟨st₂, hs₂, hW₂⟩ := run_pop (C := C) (σ := σ.withStorage st₁) ha hW₁'
    refine ⟨st₂, by simpa only [List.length_replicate] using hi,
      TRuns.append hrun₁ (TRuns.single hs₂), ?_⟩
    rw [hy] at hW₂
    rw [hres, hv']
    exact hW₂
  | ref R =>
    have hck : (σ.withStorage st₁).storage.checkIndex ref (.arr .dyn) (idxU i hi) = some () :=
      checkIndex_dyn hW₁.find (by rw [List.length_replicate]; omega) hi
    have hq := resolveT_index_lit (C := C) (σ := σ.withStorage st₁) (ArrTy.dyn (E := .ref R)) hi
      ha hck
    obtain ⟨st₂, hs₂, hW₂⟩ := run_pop (C := C)
      (σ := (σ.withStorage st₁).push (t := .alias R) (some (ref.index (.arr .dyn) (idxU i hi))))
      (a := a.there) ha hW₁'
    rw [hy] at hW₂
    have hsh : ∀ x : SVal (.ref R), (arrOf (List.replicate i (SVal.dflt (.ref R)))
        (SVal.dflt (.ref R) :: (rest.toList ++ SH)) (by simpa only [List.length_replicate]
          using hi)).saveM (.at (idxU i hi) .nil) x =
        some (arrOf (List.replicate i (SVal.dflt (.ref R))) (x :: (rest.toList ++ SH))
          (by simpa only [List.length_replicate] using hi)) := by
      intro x
      rw [arrOf_saveM_shadow _ (by simp only [List.length_replicate, Nat.le_refl]) (by
        rw [List.length_replicate, List.length_cons]; omega) hi]
      simp only [List.length_replicate, Nat.sub_self, List.set_cons_zero]
    have hal : (SPath.alias (C := C) (Idx.here (Γ := Γ) (t := .alias R))).resolveT
        (((σ.withStorage st₁).push (t := .alias R)
          (some (ref.index (.arr .dyn) (idxU i hi)))).withStorage st₂) =
        .ok (ref.append (.at (idxU i hi) .nil)) := by
      rw [resolveT_alias rfl]
      simp only [SRef.index, Path.index_dyn]
    obtain ⟨st₃, hrun₃, hW₃⟩ := child_step (d := d) hv hc.1 ht.1 hf.1 hal hW₂ (hsh _) (hsh v)
    refine ⟨st₃, by simpa only [List.length_replicate] using hi,
      TRuns.append hrun₁ (run_boundL hq (TRuns.cons hs₂ hrun₃)), ?_⟩
    rw [hres]
    exact hW₃

/-! ### Mappings, entry by entry -/

theorem Storage.find_append {st : Storage C} {U W : Ty} (r : SRef C U) (q : Path U W) :
    st.find (r.append q) = (st.find r).bind (·.findM q) := by
  show (st.get r.hroot).find (r.path.append q) = ((st.get r.hroot).find r.path).bind _
  rw [SVal.find_eq_findM, SVal.find_eq_findM, SVal.findM_append]

theorem Storage.save_exists_of_find {st : Storage C} {U : Ty} {r : SRef C U} {y : SVal U}
    (h : st.find r = some y) (X : SVal U) : ∃ st', st.save r X = some st' := by
  have hf : (st.get r.hroot).findM r.path = some y := by rw [← SVal.find_eq_findM]; exact h
  obtain ⟨v, hv⟩ := SVal.saveM_of_findM _ _ hf X
  exact ⟨_, by rw [Storage.save_eq, hv]; rfl⟩

/-- What `fillEntries` does for the entries `x`, after the entries `done`. -/
def EntriesOK (C : Contract) {K : PrimTy} {V : Ty} (x : SMap K V) : Prop :=
  ∀ (d : Nat) (Γ : Ctx) (a : Idx Γ (.alias (.mapping K V)))
    (σ : State C Γ) (ref : SRef C (.ref (.mapping K V))) (st₀ : Storage C)
    (done : List (K.Denote × SVal V)),
    TEnv.get a σ.env = some ref →
    Wrote st₀ σ.storage ref (.map (SMap.ofList done) (SVal.dflt V)) →
    x.All canonH → x.All tightH → x.All fitsH →
    nodupKeysB (done ++ x.toList) = true →
    ∃ st', TRuns σ (fillEntries d K a x) (σ.withStorage st') ∧
      Wrote st₀ st' ref (.map (SMap.ofList (done ++ x.toList)) (SVal.dflt V))

theorem entries_nil {K : PrimTy} {V : Ty} : EntriesOK C (SMap.nil (K := K) (V := V)) := by
  intro d Γ a σ ref st₀ done _ hW _ _ _ _
  exact ⟨σ.storage, TRuns.nil σ, by simpa only [SMap.toList_nil, List.append_nil] using hW⟩

theorem entries_cons {K : PrimTy} {V : Ty} {key : K.Denote} {w : SVal V} {rest : SMap K V}
    (hv : FillOK C w) (hrest : EntriesOK C rest) : EntriesOK C (SMap.cons key w rest) := by
  intro d Γ a σ ref st₀ done ha hW hc ht hf hnd
  simp only [SMap.All] at hc ht hf
  rw [SMap.toList_cons] at hnd
  have hkey : lookupBy key done = none := nodupKeysB_mid hnd
  have hpath : ref.index .map key = ref.append (.key key .nil) := by
    simp only [SRef.index, Path.index_map]
  have hq := resolveT_index_map (C := C) (V := V) (key := key) ha ⟨_, hW.find⟩
  rw [hpath] at hq
  have hcur : σ.storage.find (ref.append (.key key .nil)) = some (SVal.dflt V) := by
    rw [Storage.find_append, hW.find]
    simp only [Option.bind_some, SVal.findM, SMap.toList_ofList, hkey, SVal.findM_nil']
  obtain ⟨st₁, hs₁⟩ := Storage.save_exists_of_find hcur (SVal.dflt V)
  have hdel := run_delete hq hcur (by rw [SVal.defaultOf_dflt]; exact hs₁)
  obtain ⟨N₁, hN₁, hW₁⟩ := hW.child hs₁
  rw [map_saveM, SMap.toList_ofList,
    show setBy key (SVal.dflt V) done = done ++ [(key, SVal.dflt V)] by
      rw [← List.append_nil done, setBy_append_none _ hkey, List.append_nil]; rfl] at hN₁
  cases hN₁
  have hkey' : lookupBy key (done ++ [(key, SVal.dflt V)]) = some (SVal.dflt V) := by
    rw [lookupBy_append_none _ hkey]; simp only [lookupBy, ↓reduceIte]
  have hq₁ := resolveT_index_map (C := C) (σ := σ.withStorage st₁) (V := V) (key := key) ha
    ⟨_, hW₁.find⟩
  rw [hpath] at hq₁
  have hset : ∀ x : SVal V, setBy key x (done ++ [(key, SVal.dflt V)]) = done ++ [(key, x)] := by
    intro x
    rw [setBy_append_none _ hkey]
    simp only [setBy, ↓reduceIte]
  have hnoop : (SVal.map (K := K) (SMap.ofList (done ++ [(key, SVal.dflt V)])) (SVal.dflt V)).saveM
      (.key key .nil) (SVal.dflt V) =
      some (.map (SMap.ofList (done ++ [(key, SVal.dflt V)])) (SVal.dflt V)) := by
    rw [map_saveM, SMap.toList_ofList, hset]
  have hs : (SVal.map (K := K) (SMap.ofList (done ++ [(key, SVal.dflt V)])) (SVal.dflt V)).saveM
      (.key key .nil) w = some (.map (SMap.ofList (done ++ [(key, w)])) (SVal.dflt V)) := by
    rw [map_saveM, SMap.toList_ofList, hset]
  obtain ⟨st₂, hrun₂, hW₂⟩ := child_stepL (d := d) hv hc.1 ht.1 hf.1 hq₁ hW₁ hnoop hs
  obtain ⟨st₃, hrun₃, hW₃⟩ := hrest d Γ a (σ.withStorage st₂) ref st₀ (done ++ [(key, w)]) ha hW₂
    hc.2 ht.2 hf.2
    (by simpa only [List.append_assoc, List.singleton_append] using hnd)
  refine ⟨st₃, TRuns.cons hdel (TRuns.append hrun₂ hrun₃), ?_⟩
  rw [SMap.toList_cons]
  simpa only [List.append_assoc, List.singleton_append] using hW₃

/-! ### Every value -/

theorem fill_prim {p : PrimTy} {x : p.Denote} : FillOK C (SVal.prim x) := by
  intro d Γ q σ ref _ _ _ hq h0
  cases q with
  | loc l =>
    obtain ⟨st', hs, hW⟩ := run_assign hq h0 x
    exact ⟨st', TRuns.single hs, hW⟩

theorem fill_array {E : Ty} {n : Nat} {e : SVec E n} {sh : SList E} {hn : n < 2 ^ 256}
    (he : ElemsOK C e) (hsh : ShadowOK C sh) : FillOK C (SVal.array e sh hn) := by
  intro d Γ q σ ref hc ht hf hq h0
  simp only [SVal.All] at hc ht hf
  rw [SVal.dflt_array] at h0
  have h0' : Wrote σ.storage σ.storage ref (arrOf [] [] SVal.zero_lt_bound) := h0
  have hval : ∀ (hL : ([] ++ e.toList).length < 2 ^ 256),
      arrOf ([] ++ e.toList) (sh.toList ++ []) hL = SVal.array e sh hn := fun _ =>
    SVal.array_ext _ _ _ _ _ _ (by simp only [SVec.toList_ofList, List.nil_append])
      (by simp only [SList.toList_ofList, List.append_nil])
  by_cases hE : E.defaultOkS = true
  · have hb : n + sh.length < 2 ^ 256 := hf.1
    have hd : ((none : Option (Src C (.alias (.array E) :: Γ) E)).isSome || E.defaultOkS) = true := by
      simp only [Option.isSome_none, hE, Bool.or_true]
    obtain ⟨st₁, hrun₁, hW₁⟩ := pushes_run (a := Idx.here) hd (n + sh.length) []
      (σ.push (t := .alias (.array E)) (some ref)) SVal.zero_lt_bound rfl h0'
      (by simp only [List.length_nil, Nat.zero_add]; exact hb)
    obtain ⟨st₂, hL₂, hrun₂, hW₂⟩ := hsh d _ .here n
      ((σ.push (t := .alias (.array E)) (some ref)).withStorage st₁) ref σ.storage []
      (by simp only [List.length_replicate]; exact hb) rfl
      (hW₁.arr_congr (by rw [List.nil_append])) hc.2.2 ht.2.2 hf.2.2
      (fun hp w hw => ht.1.2 hp w hw)
    obtain ⟨st₃, hL₃, hrun₃, hW₃⟩ := he d _ .here
      ((σ.push (t := .alias (.array E)) (some ref)).withStorage st₂) ref σ.storage []
      (sh.toList ++ []) (by simpa only [List.nil_append] using hL₂) rfl
      (hW₂.arr_congr (by rw [List.nil_append])) hc.2.1 ht.2.1 hf.2.1
    refine ⟨st₃, ?_, by rw [← hval hL₃]; exact hW₃⟩
    show TRuns σ (bound d _ q (if hE : E.defaultOkS = true then _ else .nil)) _
    rw [dif_pos hE]
    exact run_bound hq (TRuns.append hrun₁ (TRuns.append hrun₂ hrun₃))
  · obtain ⟨hn0, hsh0⟩ := ht.1.1 (by simpa only [Bool.not_eq_true] using hE)
    subst hn0 hsh0
    cases e
    refine ⟨σ.storage, ?_, h0⟩
    show TRuns σ (bound d _ q (if hE : E.defaultOkS = true then _ else .nil)) _
    rw [dif_neg hE]
    exact run_bound hq (TRuns.nil _)

theorem fill_fixed {E : Ty} {n : Nat} {e : SVec E n} (he : FixedOK C e) :
    FillOK C (SVal.fixed e) := by
  intro d Γ q σ ref hc ht hf hq h0
  simp only [SVal.All] at hc ht hf
  rw [SVal.dflt_fixed] at h0
  obtain ⟨st', cur', hcur', hrun, hW⟩ := he d _ (N := n) .here
    (σ.push (t := .alias (.fixed E n)) (some ref)) ref σ.storage [] (SVec.replicate (SVal.dflt E) n)
    hf.1 (by rw [SVec.toList_replicate, List.nil_append]) rfl h0 hc.2 ht.2 hf.2
  have hce : cur' = e := SVec.eq_of_toList_eq _ _ (by rw [hcur', List.nil_append])
  subst hce
  exact ⟨st', run_bound hq hrun, hW⟩

theorem fill_map {K : PrimTy} {V : Ty} {m : SMap K V} {dv : SVal V} (hm : EntriesOK C m) :
    FillOK C (SVal.map (K := K) m dv) := by
  intro d Γ q σ ref hc ht hf hq h0
  simp only [SVal.All] at hc ht hf
  obtain ⟨⟨hnd, hdv⟩, hcm, -⟩ := hc
  subst hdv
  rw [SVal.dflt_map] at h0
  obtain ⟨st', hrun, hW⟩ := hm d _ .here (σ.push (t := .alias (.mapping K V)) (some ref))
    ref σ.storage [] rfl h0 hcm ht.2.1 hf.2.1
    (by simpa only [List.nil_append] using hnd)
  refine ⟨st', run_bound hq hrun, ?_⟩
  rw [List.nil_append, SMap.ofList_toList] at hW
  exact hW

mutual

/-- **The builder writes what it is given**: from the default at a typed
path, `fill` leaves any canonical, tight value that fits there. -/
theorem fill_ok : {T : Ty} → (v : SVal T) → FillOK C v
  | _, .prim _ => fill_prim
  | _, .struct fs => fill_struct (fillFields_ok fs)
  | _, .array e sh _ => fill_array (fillElems_ok e) (fillShadow_ok sh)
  | _, .fixed e => fill_fixed (fillFixed_ok e)
  | _, .map m _ => fill_map (fillEntries_ok m)

theorem fillFields_ok : {fs : List (Name × Ty)} → (x : SFields fs) → FieldsOK C x
  | _, .nil => fields_nil
  | _, .cons v rest => fields_cons (fill_ok v) (fillFields_ok rest)

theorem fillShadow_ok : {E : Ty} → (x : SList E) → ShadowOK C x
  | _, .nil => shadow_nil
  | _, .cons v rest => shadow_cons (fill_ok v) (fillShadow_ok rest)

theorem fillElems_ok : {E : Ty} → {n : Nat} → (x : SVec E n) → ElemsOK C x
  | _, _, .nil => elems_nil
  | _, _, .cons v rest => elems_cons (fill_ok v) (fillElems_ok rest)

theorem fillFixed_ok : {E : Ty} → {n : Nat} → (x : SVec E n) → FixedOK C x
  | _, _, .nil => fixedElems_nil
  | _, _, .cons v rest => fixedElems_cons (fill_ok v) (fillFixed_ok rest)

theorem fillEntries_ok : {K : PrimTy} → {V : Ty} → (x : SMap K V) → EntriesOK C x
  | _, _, .nil => entries_nil
  | _, _, .cons _ v rest => entries_cons (fill_ok v) (fillEntries_ok rest)

end

end Fills

/-! ### Every root -/

/-- The whole program: every root filled with its value in `st`. -/
def rootsProg (st : Storage C) :
    (vs : List (Name × Ty)) → (∀ r T, (r, T) ∈ vs → C.rootType r = some T) → Prog C [] []
  | [], _ => .nil
  | (r, T) :: vs, h =>
    (fill 0 (.loc (.root r (h r T List.mem_cons_self))) (st.get (h r T List.mem_cons_self))).append
      (rootsProg st vs fun r' T' hm => h r' T' (List.mem_cons_of_mem _ hm))

theorem rootsProg_run (st : Storage C) (hnd : nodupKeysB C.vars = true) :
    ∀ (vs : List (Name × Ty)) (h : ∀ r T, (r, T) ∈ vs → C.rootType r = some T)
      (σ : State C []),
      (∀ r T (hr : C.rootType r = some T), (∃ U, (r, U) ∈ vs) → σ.storage.get hr = SVal.dflt T) →
      (∀ r T (hr : C.rootType r = some T), (¬∃ U, (r, U) ∈ vs) → σ.storage.get hr = st.get hr) →
      st.Canon → st.Tight → st.Fits → nodupKeysB vs = true →
      TRuns σ (rootsProg st vs h) (σ.withStorage st)
  | [], _, σ, _, h2, _, _, _, _ => by
    have hst : σ.storage = st := SFields.ext_get hnd _ _ fun r T hr =>
      h2 r T hr fun ⟨_, hm⟩ => nomatch hm
    have hσ : σ.withStorage st = σ := by rw [← hst]; rfl
    rw [hσ]
    exact TRuns.nil σ
  | (r, T) :: vs, h, σ, h1, h2, hc, ht, hf, hnv => by
    simp only [nodupKeysB, Bool.and_eq_true, Option.isNone_iff_eq_none] at hnv
    have hr : C.rootType r = some T := h r T List.mem_cons_self
    have hd : σ.storage.get hr = SVal.dflt T := h1 r T hr ⟨T, List.mem_cons_self⟩
    have hsave : ∀ X : SVal T, σ.storage.save (SRef.ofRoot r hr) X =
        some (σ.storage.set hr X) := by
      intro X
      rw [Storage.save_eq]
      show ((σ.storage.get hr).saveM .nil X).map (σ.storage.set hr) = _
      rw [SVal.saveM_nil]
      rfl
    have h0 : σ.storage.save (SRef.ofRoot r hr) (SVal.dflt T) = some σ.storage := by
      rw [hsave, ← hd, SFields.set_get_self]
    obtain ⟨st₁, hrun₁, hs₁⟩ := fill_ok (st.get hr) 0 [] (.loc (.root r hr)) σ (SRef.ofRoot r hr)
      (SFields.all_get hr hc) (SFields.all_get hr ht) (SFields.all_get hr hf) rfl h0
    rw [hsave] at hs₁
    cases hs₁
    have hne : ∀ g, (∃ U, (g, U) ∈ vs) → g ≠ r := fun g ⟨U, hm⟩ he => by
      have := lookupBy_isSome_of_mem' hm
      rw [he, hnv.1] at this
      exact nomatch this
    have hrest := rootsProg_run st hnd vs (fun r' T' hm => h r' T' (List.mem_cons_of_mem _ hm))
      (σ.withStorage (σ.storage.set hr (st.get hr)))
      (fun g U hg hm => by
        show (σ.storage.set hr (st.get hr)).get hg = _
        rw [SFields.get_set_ne _ hr hg (hne g hm).symm]
        exact h1 g U hg (let ⟨V, hV⟩ := hm; ⟨V, List.mem_cons_of_mem _ hV⟩))
      (fun g U hg hm => by
        show (σ.storage.set hr (st.get hr)).get hg = _
        by_cases hgr : g = r
        · subst hgr
          have hU : U = T := Option.some.inj (hg.symm.trans hr)
          subst hU
          rw [SFields.get_set_same]
        · rw [SFields.get_set_ne _ hr hg (Ne.symm hgr)]
          refine h2 g U hg fun ⟨V, hV⟩ => ?_
          rcases List.mem_cons.mp hV with hV | hV
          · exact hgr (congrArg Prod.fst hV)
          · exact hm ⟨V, hV⟩)
      hc ht hf hnv.2
    exact TRuns.append hrun₁ hrest

end Build

/-! ## The characterisation -/

open Build

/-- **Canonical and tight ⇒ reachable, by one program**: `Build.rootsProg`,
run by the typed run from `C`'s initial state, leaves exactly `st`, for keys
and slots in range. -/
theorem storage_reachable (hnd : nodupKeysB C.vars = true) {st : Storage C} (hc : st.Canon)
    (ht : st.Tight) (hf : st.Fits) :
    TRuns (State.init C) (rootsProg st C.vars fun _ _ hm => lookupBy_of_nodup hnd hm)
      ((State.init C).withStorage st) :=
  rootsProg_run st hnd C.vars _ (State.init C) (fun _ _ hr _ => SFields.dflt_get hr)
    (fun _ T hr hm => absurd ⟨T, lookupBy_eq_some_mem hr⟩ hm) hc ht hf hnd

/-- **Canonical and tight ⇒ reachable**, for keys and slots in range. -/
theorem canon_reachable (hnd : nodupKeysB C.vars = true) {st : Storage C} (hc : st.Canon)
    (ht : st.Tight) (hf : st.Fits) : Reachable C st := by
  obtain ⟨o, ho, he⟩ := storage_reachable hnd hc ht hf
  exact ⟨[], _, o, ho, by rw [he]; rfl⟩

/-- **Nothing inferable is missing**: a property of storage that holds
initially and that every program keeps, by the typed run from any typed
state whose storage is canonical, holds of every canonical, tight storage
whose keys and slots fit.  The typed state is well-typed by construction,
so the step asks only the storage's canonicity. -/
theorem no_hidden_invariant (hnd : nodupKeysB C.vars = true) (P : Storage C → Prop)
    (hinit : P (Storage.init C))
    (hstep : ∀ (Γ' : Ctx) (σ : State C []) (o : Out C σ.H Γ') (prog : Prog C [] Γ'),
      σ.storage.Canon → prog.run σ = .ok o → P σ.storage → P o.st.storage)
    (st : Storage C) (hc : st.Canon) (ht : st.Tight) (hf : st.Fits) : P st := by
  obtain ⟨o, ho, he⟩ := storage_reachable hnd hc ht hf
  have := hstep _ _ o _ Storage.init_canon ho hinit
  rw [he] at this
  exact this

theorem deepOk_of_all (h : C.vars.all (·.2.okDeep) = true) : DeepOk C :=
  fun _ _ hr => List.all_eq_true.mp h _ (lookupBy_eq_some_mem hr)

/-- **Reachable ⇒ canonical and tight**, for a contract whose types have
well-formed defaults all the way down. -/
theorem reachable_shape (hdeep : C.vars.all (·.2.okDeep) = true) {st : Storage C}
    (h : Reachable C st) : st.Canon ∧ st.Tight :=
  ⟨reachable_canon h, reachable_tight (deepOk_of_all hdeep) h⟩

/-- **The reachable storages, exactly**: for a contract whose types have
well-formed defaults all the way down, a storage whose keys and slots are in
range (`SVal.Fits`, what a literal can write) is reachable by a program iff
it is canonical and tight. -/
theorem reachable_iff (hnd : nodupKeysB C.vars = true) (hdeep : C.vars.all (·.2.okDeep) = true)
    {st : Storage C} (hf : st.Fits) : Reachable C st ↔ st.Canon ∧ st.Tight :=
  ⟨reachable_shape hdeep, fun ⟨hc, ht⟩ => canon_reachable hnd hc ht hf⟩

/-- **The reachable storages, exactly, with no premise on the storage**: for
a contract whose types have well-formed defaults all the way down and whose
fixed sizes fit, a storage is reachable iff it is canonical, tight and fits. -/
theorem reachable_iff_fits (hnd : nodupKeysB C.vars = true)
    (hdeep : C.vars.all (·.2.okDeep) = true) (hf : FixedFits C) {st : Storage C} :
    Reachable C st ↔ st.Canon ∧ st.Tight ∧ st.Fits :=
  ⟨fun h => ⟨(reachable_shape hdeep h).1, (reachable_shape hdeep h).2, reachable_fits hf h⟩,
    fun ⟨hc, ht, hfs⟩ => canon_reachable hnd hc ht hfs⟩

/-! ## What is reachable and what is not -/

section Witnesses

/-- One `uint[]` root. -/
def Words : Contract := contract!{ uint[] xs; }

/-- One `bool`-keyed mapping root. -/
def BoolKeyed : Contract := contract!{ mapping(bool => uint) flags; }

/-- One `Token[]` root. -/
def Tokens : Contract := contract!{ Token[] tokens; }

/-- `xs` empty, with a `5` past its end. -/
def Words.dirty : Storage Words :=
  .cons (.array .nil (.cons (.prim (PrimTy.ofLit .uint 5 rfl)) .nil) SVal.zero_lt_bound) .nil

/-- A word past the end of a `uint[]` that is not cleared: canonical, not
reachable, since `pop`, `delete` and a shorter copy clear the words they
leave behind and nothing writes past the end of an array of words. -/
theorem dirty_word_not_reachable : Words.dirty.Canon ∧ ¬ Reachable Words Words.dirty := by
  refine ⟨?_, fun h => ?_⟩
  · simp only [Words.dirty, SFields.All, SVal.All, SVec.All, SList.All, canonH,
      and_self]
  · have ht := reachable_tight (deepOk_of_all (by decide)) h
    simp only [Words.dirty, SFields.All, SVal.All, tightH] at ht
    have h5 := ht.1.1.2 rfl _ (by rw [SList.toList_cons]; exact List.mem_cons_self)
    rw [SVal.dflt_prim] at h5
    cases h5

/-- One `uint[2^256 + 1]` root: more slots than a `uint` index reaches
(solc refuses a storage type that large). -/
def Huge : Contract := { vars := [("big", .ref (.fixed .uint (2 ^ 256 + 1)))] }

/-- **Reachable does not imply `Fits`** (decision 77): `Huge`'s initial
storage is reached by the empty program, and its root has `2^256 + 1`
elements, past what `Fits` allows a fixed-size array (the builder writes
each element at a literal index).  So `reachable_iff` keeps its `Fits`
premise.  Under solc's bound on fixed sizes (`FixedFits`, which `Huge`
fails) every reachable storage fits, and `reachable_iff_fits` drops the
premise (`Typing/Fits.lean`). -/
theorem huge_reachable_not_fits :
    Reachable Huge (Storage.init Huge) ∧ ¬ (Storage.init Huge).Fits := by
  refine ⟨⟨[], .nil, ⟨State.init Huge, List.prefix_refl _⟩, Prog.run_nil _, rfl⟩, fun hf => ?_⟩
  have hr : lookupBy "big" Huge.vars = some (.ref (.fixed .uint (2 ^ 256 + 1))) := rfl
  have h := SFields.all_get hr hf
  rw [Storage.init, SFields.dflt_get, SVal.dflt_fixed] at h
  simp only [SVal.All] at h
  exact Nat.not_succ_le_self _ h.1

/-- `Huge`'s one root is past solc's bound, so it is no counterexample to
`reachable_fits`. -/
theorem huge_not_fixedFits : ¬ FixedFits Huge := by
  intro hf
  have h := hf ("big", _) List.mem_cons_self .uint (2 ^ 256 + 1) .nil
  omega

/-- `flags[true] = 3`. -/
def BoolKeyed.flag : Storage BoolKeyed :=
  .cons (.map (.cons (true : Bool) (.prim (PrimTy.ofLit .uint 3 rfl)) .nil)
    (.prim (PrimTy.dflt .uint))) .nil

/-- An entry in a `bool`-keyed mapping, at the key `1` that `true` hashes
to (decisions 10 and 14): reachable, by the builder (`flags[true] = 3;`). -/
theorem bool_key_reachable : Reachable BoolKeyed BoolKeyed.flag := by
  refine canon_reachable (by decide) ?_ ?_ ?_
  · simp only [BoolKeyed.flag, SFields.All, SVal.All, SMap.All, canonH, and_true]
    refine ⟨?_, rfl⟩
    simp only [SMap.toList]
    decide
  · simp only [BoolKeyed.flag, SFields.All, SVal.All, SMap.All, tightH, and_true]
  · simp only [BoolKeyed.flag, SFields.All, SVal.All, SMap.All, fitsH, and_true]
    intro e he
    simp only [SMap.toList, List.mem_cons, List.not_mem_nil, or_false] at he
    subst he
    exact PrimTy.keyFits_key (p := .bool) true

/-- A `Token` past the end of `tokens`. -/
def Tokens.dangling : Storage Tokens :=
  .cons (.array .nil (.cons (.struct (.cons (.prim (PrimTy.ofLit .uint 7 rfl)) .nil)) .nil)
    SVal.zero_lt_bound) .nil

/-- A `Token` past the end of `tokens`, written through a reference taken
before its `pop`: reachable, by the builder. -/
theorem dangling_slot_reachable : Reachable Tokens Tokens.dangling := by
  refine canon_reachable (by decide) ?_ ?_ ?_
  · simp only [Tokens.dangling, SFields.All, SVal.All, SVec.All, SList.All, canonH,
      and_self]
  · simp only [Tokens.dangling, SFields.All, SVal.All, SVec.All, SList.All, tightH,
      and_true]
    refine ⟨fun h => absurd h (by decide), fun h => absurd h (by decide)⟩
  · simp only [Tokens.dangling, SFields.All, SVal.All, SVec.All, SList.All, fitsH,
      and_true]
    show 0 + SList.length _ < 2 ^ 256
    simp only [SList.length, SList.toList_cons, SList.toList_nil, List.length_cons,
      List.length_nil]
    decide

end Witnesses

end Solidity
