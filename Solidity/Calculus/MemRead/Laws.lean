import Solidity.Calculus.MemRead.Spine

/-!
# Memory reads: copies and the laws of a read

A copy's objects, their views, and the laws of a read.

A piece of `Calculus/MemRead.lean`, whose docstring describes the whole.
-/

namespace Solidity

namespace Decide

open Semantics (lookupBy structDef)

variable {C : Contract}

section CopyObj

variable {g : State C []} {ν : AEnv}

/-- How deep a read walks down a memory, and a returning check down a term. -/
def memFuel : Nat := 256

/-- At a binary symbol: `sfind(st, q)` taken to `sfind(st, q.f)`. -/
def _root_.Solidity.Op2.sfindFieldStep {s f : Name} {T : Ty} (hf : C.fieldType s f = some T)
    {a b : Srt} (o : Op2 C a b (.sv (.ref (.struct s)))) (x : LTm C a) (y : LTm C b) :
    Option (LTm C (.sv T)) :=
  match o, x, y with
  | .sfind, st, q => some (.app2 .sfind st (.app1 (.field hf) q))
  | _, _, _ => none

/-- `sfind(st, q)` taken to `sfind(st, q.f)`. -/
def LTm.sfindField {s f : Name} {T : Ty} (S : LTm C (.sv (.ref (.struct s))))
    (hf : C.fieldType s f = some T) : Option (LTm C (.sv T)) :=
  match S with
  | .app2 o x y => o.sfindFieldStep hf x y
  | _ => none

theorem LTm.sfindField_eval {s f : Name} {T : Ty} {S : LTm C (.sv (.ref (.struct s)))}
    {hf : C.fieldType s f = some T} {S' : LTm C (.sv T)} (h : S.sfindField hf = some S')
    {v : SVal (.ref (.struct s))} (hv : (S.eval g ν : Option (SVal _)) = some v) :
    (S'.eval g ν : Option (SVal T)) = some ((SVal.view v : SFields _).get hf) := by
  cases S with
  | app2 o x y =>
    cases o <;> simp only [LTm.sfindField, Op2.sfindFieldStep, reduceCtorEq, Option.some.injEq] at h
    subst h
    rw [LTm.eval_app2] at hv ⊢
    rw [LTm.eval_app1]
    cases hx : (x.eval g ν : Option (Storage C)) with
    | none => rw [hx, Op2.eval_none_left] at hv; cases hv
    | some st =>
      cases hy : (y.eval g ν : Option (SRef C _)) with
      | none => rw [hx, hy, Op2.eval_none_right g _ rfl] at hv; cases hv
      | some r =>
        rw [hx, hy] at hv
        change st.find r = some v at hv
        change st.find (r.field hf) = _
        rw [SRef.field, Storage.find_append, hv]
        cases v with
        | struct fs => rfl
  | _ => simp only [LTm.sfindField, reduceCtorEq] at h

/-- At a binary symbol: `sfind(st, q)` taken to the word `find(st, q.f)`. -/
def _root_.Solidity.Op2.findFieldStep {s f : Name} {P : PrimTy} (hf : C.fieldType s f = some (.prim P))
    {a b : Srt} (o : Op2 C a b (.sv (.ref (.struct s)))) (x : LTm C a) (y : LTm C b) :
    Option (LTm C (.val P)) :=
  match o, x, y with
  | .sfind, st, q => some (.app2 .find st (.app1 (.field hf) q))
  | _, _, _ => none

/-- `sfind(st, q)` taken to the word `find(st, q.f)`. -/
def LTm.findField {s f : Name} {P : PrimTy} (S : LTm C (.sv (.ref (.struct s))))
    (hf : C.fieldType s f = some (.prim P)) : Option (LTm C (.val P)) :=
  match S with
  | .app2 o x y => o.findFieldStep hf x y
  | _ => none

theorem LTm.findField_eval {s f : Name} {P : PrimTy} {S : LTm C (.sv (.ref (.struct s)))}
    {hf : C.fieldType s f = some (.prim P)} {y : LTm C (.val P)} (h : S.findField hf = some y)
    {v : SVal (.ref (.struct s))} (hv : (S.eval g ν : Option (SVal _)) = some v) :
    (y.eval g ν : Option P.Denote) = some ((SVal.view v : SFields _).get hf).view := by
  cases S with
  | app2 o x z =>
    cases o <;> simp only [LTm.findField, Op2.findFieldStep, reduceCtorEq, Option.some.injEq] at h
    subst h
    rw [LTm.eval_app2] at hv ⊢
    rw [LTm.eval_app1]
    cases hx : (x.eval g ν : Option (Storage C)) with
    | none => rw [hx, Op2.eval_none_left] at hv; cases hv
    | some st =>
      cases hz : (z.eval g ν : Option (SRef C _)) with
      | none => rw [hx, hz, Op2.eval_none_right g _ rfl] at hv; cases hv
      | some r =>
        rw [hx, hz] at hv
        change st.find r = some v at hv
        change (st.find (r.field hf)).bind (fun w => some w.view) = _
        rw [SRef.field, Storage.find_append, hv]
        cases v with
        | struct fs => rfl
  | _ => simp only [LTm.findField, reduceCtorEq] at h

/-- At a binary symbol: `sfind(st, q)` of an array taken to the word at
`i`, within the stored length. -/
def _root_.Solidity.Op2.findIndexStep {P : PrimTy} (i : LTm C (.val .uint))
    {a b : Srt} (o : Op2 C a b (.sv (.ref (.array (.prim P))))) (x : LTm C a) (y : LTm C b) :
    Option (LTm C (.val P)) :=
  match o, x, y with
  | .sfind, st, q =>
    some (.app3 .ite (.app2 (.binop .lt rfl) i (.app2 .len st q))
      (.app2 .find st (.index (.arr .dyn) q i)) .err)
  | _, _, _ => none

/-- `sfind(st, q)` of an array taken to `if (i < len(st, q)) then
find(st, q[i]) else err`. -/
def LTm.findIndex {P : PrimTy} (S : LTm C (.sv (.ref (.array (.prim P)))))
    (i : LTm C (.val .uint)) : Option (LTm C (.val P)) :=
  match S with
  | .app2 o x y => o.findIndexStep i x y
  | _ => none

theorem LTm.findIndex_eval {P : PrimTy} {S : LTm C (.sv (.ref (.array (.prim P))))}
    {i : LTm C (.val .uint)} {y : LTm C (.val P)} (h : S.findIndex i = some y)
    {n : Nat} {e : SVec (.prim P) n} {sh : SList (.prim P)} {hn : n < 2 ^ 256}
    (hv : (S.eval g ν : Option (SVal _)) = some (.array e sh hn)) :
    (y.eval g ν : Option P.Denote) =
      (i.eval g ν : Option PrimTy.uint.Denote).bind fun k =>
        (e.toList[k.1.toNat]?).map fun x => x.view := by
  cases S with
  | app2 o x z =>
    cases o <;> simp only [LTm.findIndex, Op2.findIndexStep, reduceCtorEq, Option.some.injEq] at h
    subst h
    rw [LTm.eval_app2] at hv
    cases hx : (x.eval g ν : Option (Storage C)) with
    | none => rw [hx, Op2.eval_none_left] at hv; cases hv
    | some st =>
      cases hz : (z.eval g ν : Option (SRef C _)) with
      | none => rw [hx, hz, Op2.eval_none_right g _ rfl] at hv; cases hv
      | some r =>
        rw [hx, hz] at hv
        change st.find r = some (.array e sh hn) at hv
        cases hi : (i.eval g ν : Option PrimTy.uint.Denote) with
        | none =>
          simp only [LTm.eval_app3, LTm.eval_app2, hi]
          rw [Op2.eval_none_left]
          rfl
        | some k =>
          simp only [LTm.eval_app3, LTm.eval_app2, LTm.eval_index, hi, hx, hz]
          have hlen : Op2.eval g Op2.len (some st) (some r) = some (lenU n hn) := by
            show (st.len r) = _
            unfold Storage.len; rw [hv]; rfl
          have hf : Op2.eval g Op2.find (some st) (some (SRef.index r (IndexTy.arr ArrTy.dyn) k)) =
              ((e.toList ++ sh.toList)[k.1.toNat]?).map fun x => x.view := by
            rw [show SRef.index r (IndexTy.arr ArrTy.dyn) k = r.append (.at k .nil) by rw [SRef.index, Path.index_dyn]]
            change (st.find (r.append (.at k .nil))).bind (fun w => some w.view) = _
            rw [Storage.find_append, hv, Option.bind_some]
            try rw [SVal.find_eq_findM]
            simp only [SVal.findM]
            cases (e.toList ++ sh.toList)[k.1.toNat]? <;> rfl
          simp only [Option.bind_some]
          rw [hlen, hf]
          change (bif decide (k.1 < (n : Int)) then _ else none) = _
          have hk := k.2
          simp only [PrimTy.inRange, decide_eq_true_eq] at hk
          by_cases hkn : k.1.toNat < n
          · have hlt : k.1 < (n : Int) := by omega
            have hl : k.1.toNat < e.toList.length := by rw [SVec.length_toList]; exact hkn
            simp only [hlt, decide_true, cond_true, List.getElem?_append_left hl]
          · have hlt : ¬ k.1 < (n : Int) := by omega
            have hl : e.toList.length ≤ k.1.toNat := by rw [SVec.length_toList]; omega
            simp only [hlt, decide_false, cond_false, List.getElem?_eq_none hl, Option.map_none]
  | _ => simp only [LTm.findIndex, reduceCtorEq] at h

/-- `copyObjN`'s step at an identity member: `o.f`, `o` holding
`sfind(st, q)`, holds `sfind(st, q.f)`. -/
def _root_.Solidity.Op1.objField
    (ih : {R : RefTy} → LTm C (.ident R) → Option (LTm C (.sv (.ref R))))
    {a : Srt} {R : RefTy} (o : Op1 C a (.addr (.ref R))) (x : LTm C a) :
    Option (LTm C (.sv (.ref R))) :=
  match o, x with
  | .mfield hf, x => (ih x).bind fun S₁ => S₁.sfindField hf

/-- `copyObjN`'s step at a binary symbol: the copy's root, or an identity
member read at the copy. -/
def _root_.Solidity.Op2.objStep (X m : LTm C .mem) {U : Ty} (S : LTm C (.sv U))
    (ih : {R : RefTy} → LTm C (.ident R) → Option (LTm C (.sv (.ref R))))
    {a b : Srt} {R : RefTy} (o : Op2 C a b (.ident R)) (x : LTm C a) (y : LTm C b) :
    Option (LTm C (.sv (.ref R))) :=
  match o, x, y with
  | .copy _, m', S' => if (m'.beqR m || m'.beqR m.stripW) && S'.beqR S then some S' else none
  | .iread, X', b =>
    if X'.beqR X then
      match b with
      | .app1 o' x' => o'.objField ih x'
      | _ => none
    else none

/-- **What an object of a copy of storage holds, read at the copy**
`X = copySt(m, S)` (`readFromCopyToStorageIdentity`, KeY's
`idC(idp, fxs)`): the root holds `S`; an identity member read at `X` of an
object holding `sfind(st, q)` holds `sfind(st, q.f)`.  By the recursor on
the depth. -/
def copyObjN (X m : LTm C .mem) {U : Ty} (S : LTm C (.sv U)) (n : Nat) :
    {R : RefTy} → LTm C (.ident R) → Option (LTm C (.sv (.ref R))) :=
  Nat.rec (motive := fun _ => {R : RefTy} → LTm C (.ident R) → Option (LTm C (.sv (.ref R))))
    (fun _ => none)
    (fun _ ih {_} o =>
      match o with
      | .app2 op x y => op.objStep X m S ih x y
      | _ => none) n

/-- The copy `copySt(m, S)` read: `m` grown by the copy of `S`. -/
theorem LTm.copySt_eval {m : LTm C .mem} {U : Ty} {hU : U.mapFree = true} {S : LTm C (.sv U)}
    {μ : Grown g.H (fun _ => Unit)} (hm : m.eval g ν = some μ) {v : SVal U}
    (hS : (S.eval g ν : Option (SVal U)) = some v) :
    (LTm.app2 (.copySt hU) m S).eval g ν = some (μ.then (v.copyStToM μ.heap hU)) := by
  rw [LTm.eval_app2, hm, hS]; rfl

theorem copyObjN_eval {m : LTm C .mem} {U : Ty} {hU : U.mapFree = true} {S : LTm C (.sv U)}
    {μ : Grown g.H (fun _ => Unit)} (hm : m.eval g ν = some μ) {v : SVal U}
    (hS : (S.eval g ν : Option (SVal U)) = some v) (n : Nat) :
    ∀ {R : RefTy} (o : LTm C (.ident R)) (S' : LTm C (.sv (.ref R))),
      copyObjN (.app2 (.copySt hU) m S) m S n o = some S' →
      ∃ (r : HRef (v.copyStToM μ.heap hU).H' R) (v' : SVal (.ref R)),
        (o.eval g ν : Option Nat) = some r.id ∧ (S'.eval g ν : Option (SVal (.ref R))) = some v' ∧
        v'.Mirrors (v.copyStToM μ.heap hU).heap μ.H'.length r := by
  induction n with
  | zero => intro R o S' h; cases h
  | succ n ih =>
    intro R o S' h
    cases o with
    | app2 op x y =>
      cases op
      case copy hR =>
        change (if (x.beqR m || x.beqR m.stripW) && y.beqR S then some y else none) = some S' at h
        split at h
        case isFalse => cases h
        case isTrue hc =>
          cases h
          simp only [Bool.and_eq_true, Bool.or_eq_true] at hc
          obtain ⟨hx, hy⟩ := hc
          obtain ⟨hUU, hyS⟩ := Sigma.mk.inj (LTm.sigma_eq_of_beqR hy)
          cases hUU
          cases eq_of_heq hyS
          have hxm : (LTm.app2 (.copy hR) x S').eval g ν = (LTm.app2 (.copy hR) m S').eval g ν := by
            rcases hx with hx | hx
            · rw [LTm.eq_of_beqR hx]
            · rw [LTm.eq_of_beqR hx]; exact LTm.copy_stripW_eval hm hR S'
          refine ⟨(v.copyStToM μ.heap hU).val, v, ?_, hS, SVal.mirrors_copyStToM μ.heap v hU⟩
          rw [hxm, LTm.eval_app2, hm, hS]; rfl
      case iread =>
        change (if x.beqR (LTm.app2 (.copySt hU) m S) then
          (match y with
            | .app1 o' x' => o'.objField (copyObjN (.app2 (.copySt hU) m S) m S n) x'
            | _ => none) else none) = some S' at h
        split at h
        case isFalse => cases h
        case isTrue hx =>
          cases LTm.eq_of_beqR hx
          cases y with
          | app1 o' x' =>
            cases o'
            case mfield s f hf =>
              change ((copyObjN (.app2 (.copySt hU) m S) m S n x').bind
                fun S₁ => S₁.sfindField hf) = some S' at h
              obtain ⟨S₁, h₁, h₂⟩ := Option.bind_eq_some_iff.1 h
              obtain ⟨r₁, v₁, hx', hS₁, hM⟩ := ih x' S₁ h₁
              cases v₁ with
              | struct fs =>
                simp only [SVal.Mirrors] at hM
                refine ⟨(v.copyStToM μ.heap hU).heap.field r₁ hf, fs.get hf, ?_,
                  LTm.sfindField_eval h₂ hS₁, SFields.Mirrors.get fs _ hM.2 hf⟩
                simp only [LTm.iread_evalT, LTm.copySt_eval hm hS, Option.bind_some, LTm.eval_app1,
                  hx', Op1.eval_eq_evalM, Op1.evalM, Option.map_some, MAddrT.resolve_eq_resolveM,
                  MAddrT.resolveM]
                change ((((HRef.ofId? (SVal.copyStToM μ.heap v hU).H' (.struct s) r₁.id).map
                  (fun x => MAddr.field x hf)).bind
                    fun rb => (SVal.copyStToM μ.heap v hU).heap.readAddr rb).bind
                      fun r => some (r : HRef _ R).id) = _
                rw [HRef.ofId?_self (r := r₁)]
                rfl
          | _ => cases h
    | _ => cases h

/-- `copyPathRd?` at a member: the word the member of the object holds. -/
def _root_.Solidity.Op1.copyFieldRd
    (obj : {R : RefTy} → LTm C (.ident R) → Option (LTm C (.sv (.ref R))))
    {a : Srt} {P : PrimTy} (o : Op1 C a (.addr (.prim P))) (x : LTm C a) :
    Option (LTm C (.val P)) :=
  match o, x with
  | .mfield (f := f) hf, x => if f != "length" then (obj x).bind fun S₁ => S₁.findField hf else none

/-- `copyPathRd?` at an element: the word the array holds there, within its
length. -/
def _root_.Solidity.Op2.copyElemRd
    (obj : {R : RefTy} → LTm C (.ident R) → Option (LTm C (.sv (.ref R))))
    {a b : Srt} {P : PrimTy} (o : Op2 C a b (.addr (.prim P))) (x : LTm C a) (y : LTm C b) :
    Option (LTm C (.val P)) :=
  match o, x, y with
  | .mat .dyn, x, i => (obj x).bind fun S₁ => S₁.findIndex i
  | _, _, _ => none

/-- **A word of an object of a copy of storage, read at the copy**
(`readFromCopyToStorage` at `idC(idp, fxs)`, any `fxs`; an element Lean
only): what the storage it copied holds there (`copyObjN`). -/
def copyPathRd? (X m : LTm C .mem) {U : Ty} (S : LTm C (.sv U)) {P : PrimTy}
    (b : LTm C (.addr (.prim P))) : Option (LTm C (.val P)) :=
  match b with
  | .app1 o x => o.copyFieldRd (copyObjN X m S memFuel) x
  | .app2 o x y => o.copyElemRd (copyObjN X m S memFuel) x y
  | _ => none

theorem copyPathRd?_eval {m : LTm C .mem} {U : Ty} {hU : U.mapFree = true} {S : LTm C (.sv U)}
    {P : PrimTy} {b : LTm C (.addr (.prim P))} {y : LTm C (.val P)}
    (h : copyPathRd? (.app2 (.copySt hU) m S) m S b = some y) :
    ((LTm.app2 .read (.app2 (.copySt hU) m S) b).eval g ν : Option P.Denote) =
      (LTm.seq (.app2 (.copySt hU) m S) y).eval g ν := by
  cases hm : (m.eval g ν : Option (Grown g.H (fun _ => Unit))) with
  | none =>
    rw [LTm.eval_app2_none _ _ _ (LTm.eval_app2_none _ _ _ hm), LTm.eval_seq,
      LTm.eval_app2_none _ _ _ hm]; rfl
  | some μ =>
  cases hS : (S.eval g ν : Option (SVal U)) with
  | none =>
    have hX : (LTm.app2 (.copySt hU) m S).eval g ν = none := by
      rw [LTm.eval_app2, hm, hS, Op2.eval_none_right g _ rfl]
    rw [LTm.eval_app2_none _ _ _ hX, LTm.eval_seq, hX]; rfl
  | some v =>
  rw [LTm.eval_seq, LTm.copySt_eval hm hS, Option.bind_some, LTm.read_evalT,
    LTm.copySt_eval hm hS, Option.bind_some]
  cases b with
  | app1 o x =>
    cases o
    case mfield s f hf =>
      change (if f != "length" then (copyObjN _ m S memFuel x).bind fun S₁ => S₁.findField hf
        else none) = some y at h
      split at h
      case isFalse => cases h
      case isTrue =>
        obtain ⟨S₁, h₁, h₂⟩ := Option.bind_eq_some_iff.1 h
        obtain ⟨r, v₁, hx, hS₁, hM⟩ := copyObjN_eval hm hS memFuel x S₁ h₁
        cases v₁ with
        | struct fs =>
          simp only [SVal.Mirrors] at hM
          rw [LTm.findField_eval h₂ hS₁, LTm.eval_app1, hx]
          change ((((HRef.ofId? (SVal.copyStToM μ.heap v hU).H' (.struct s) r.id).map
            (fun x => MAddr.field x hf)).bind
              fun rb => (SVal.copyStToM μ.heap v hU).heap.readAddr rb)) = _
          rw [HRef.ofId?_self (r := r)]
          change some (MFields.get _ ((v.copyStToM μ.heap hU).heap.get r) hf) = _
          rw [SVal.Mirrors.prim _ _ (SFields.Mirrors.get fs _ hM.2 hf)]
          rfl
  | app2 o x i =>
    cases o
    case mat ak =>
      cases ak
      case dyn =>
        change ((copyObjN _ m S memFuel x).bind fun S₁ => S₁.findIndex i) = some y at h
        obtain ⟨S₁, h₁, h₂⟩ := Option.bind_eq_some_iff.1 h
        obtain ⟨r, v₁, hx, hS₁, hM⟩ := copyObjN_eval hm hS memFuel x S₁ h₁
        cases v₁ with
        | array e sh hn =>
          simp only [SVal.Mirrors] at hM
          rw [LTm.findIndex_eval h₂ hS₁, LTm.eval_app2, hx]
          cases hi : (i.eval g ν : Option PrimTy.uint.Denote) with
          | none => rfl
          | some k =>
            change ((((HRef.ofId? (SVal.copyStToM μ.heap v hU).H' (.array (.prim P)) r.id).map
              (fun x => MAddr.index x .dyn k)).bind
                fun rb => (SVal.copyStToM μ.heap v hU).heap.readAddr rb)) = _
            rw [HRef.ofId?_self (r := r)]
            change (MObj.elems .dyn ((v.copyStToM μ.heap hU).heap.get r))[k.1.toNat]? = _
            rcases SVec.Mirrors.getElem e _ hM.2 k.1.toNat with ⟨h1, h2⟩ | ⟨x₀, w, h1, h2, h3⟩
            · rw [h2, Option.bind_some, h1]; rfl
            · rw [h2, Option.bind_some, h1, SVal.Mirrors.prim _ _ h3]; rfl
      all_goals cases h
    all_goals cases h
  | _ => cases h

/-- `LTm.copyFresh?` at a binary symbol. -/
def _root_.Solidity.Op2.copyFreshStep {a b : Srt} {R : RefTy} (o : Op2 C a b (.ident R))
    (x : LTm C a) (y : LTm C b) (t : LTm C (.ident R)) : Option (LTm C .mem) :=
  match o, x, y with
  | .iread, X, _ =>
    match X.memView with
    | .copySt m _ S => if (copyObjN X m S memFuel t).isSome then some m else none
    | _ => none
  | _, _, _ => none

/-- **An object a copy made, read at the copy**, is fresh over the memory
the copy grows (`Grown.alloc_fresh`, as the copy's root). -/
def LTm.copyFresh? {R : RefTy} (t : LTm C (.ident R)) : Option (LTm C .mem) :=
  match t with
  | .app2 o x y => o.copyFreshStep x y t
  | _ => none

theorem LTm.copyFresh?_eval {R : RefTy} {t : LTm C (.ident R)} {m : LTm C .mem}
    (h : t.copyFresh? = some m) {id : Nat} (ht : (t.eval g ν : Option Nat) = some id) :
    ∃ μ : Grown g.H (fun _ => Unit), m.eval g ν = some μ ∧ μ.H'.length ≤ id := by
  cases t with
  | app2 o X b =>
    cases o
    case iread =>
      change (match X.memView with
        | .copySt m _ S => if (copyObjN X m S memFuel (.app2 .iread X b)).isSome then some m
          else none
        | _ => none) = some _ at h
      split at h
      case h_1 m' U hU S hX =>
        obtain rfl := LTm.memView_copySt hX
        split at h
        case isFalse => cases h
        case isTrue hc =>
          cases h
          obtain ⟨S', hS'⟩ := Option.isSome_iff_exists.1 hc
          cases hm : (m.eval g ν : Option (Grown g.H (fun _ => Unit))) with
          | none =>
            rw [LTm.eval_app2_none _ _ _ (LTm.eval_app2_none _ _ _ hm)] at ht; cases ht
          | some μ =>
            cases hS : (S.eval g ν : Option (SVal U)) with
            | none =>
              have hX : (LTm.app2 (.copySt hU) m S).eval g ν = none := by
                rw [LTm.eval_app2, hm, hS, Op2.eval_none_right g _ rfl]
              rw [LTm.eval_app2_none _ _ _ hX] at ht; cases ht
            | some v =>
              obtain ⟨r, v', hr, -, hM⟩ := copyObjN_eval hm hS memFuel _ S' hS'
              rw [hr] at ht
              cases ht
              exact ⟨μ, rfl, SVal.Mirrors.id_ge v' r hM⟩
      all_goals cases h
    all_goals cases h
  | _ => cases h

/-- **The memory an identity is fresh over**: an allocation's, a copy's,
an object's of a copy (`LTm.copyFresh?`). -/
def LTm.freshOverC? {R : RefTy} (t : LTm C (.ident R)) : Option (LTm C .mem) :=
  match t.freshOver? with
  | some m => some m
  | none => t.copyFresh?

theorem LTm.freshOverC?_eval {R : RefTy} {t : LTm C (.ident R)} {m : LTm C .mem}
    (h : t.freshOverC? = some m) {id : Nat} (ht : (t.eval g ν : Option Nat) = some id) :
    ∃ μ : Grown g.H (fun _ => Unit), m.eval g ν = some μ ∧ μ.H'.length ≤ id := by
  unfold LTm.freshOverC? at h
  split at h
  · rename_i m' hm
    cases h
    exact LTm.freshOver?_eval hm ht
  · exact LTm.copyFresh?_eval h ht

end CopyObj

section Views

variable {g : State C []} {ν : AEnv}

/-- **Two identities that differ** (`Grown.alloc_fresh`, the freshness behind `newFromAdd`): one fresh over a
memory the other is older than (`LTm.freshOverC?`). -/
def LTm.identApart? {R R' : RefTy} (t : LTm C (.ident R)) (t' : LTm C (.ident R')) : Bool :=
  (match t'.freshOverC? with
    | some m => t.boundedIn m
    | none => false) ||
  (match t.freshOverC? with
    | some m => t'.boundedIn m
    | none => false)

theorem LTm.identApart?_ne {R R' : RefTy} {t : LTm C (.ident R)} {t' : LTm C (.ident R')}
    (h : t.identApart? t' = true) {id id' : Nat} (ht : (t.eval g ν : Option Nat) = some id)
    (ht' : (t'.eval g ν : Option Nat) = some id') : id ≠ id' := by
  unfold LTm.identApart? at h
  rcases Bool.or_eq_true_iff.1 h with h | h
  · split at h
    · rename_i m hm
      obtain ⟨μ, hμ, hle⟩ := LTm.freshOverC?_eval hm ht'
      have : id < μ.H'.length := LTm.boundedIn_eval hμ t h id ht
      omega
    · cases h
  · split at h
    · rename_i m hm
      obtain ⟨μ, hμ, hle⟩ := LTm.freshOverC?_eval hm ht
      have : id' < μ.H'.length := LTm.boundedIn_eval hμ t' h id' ht'
      omega
    · cases h

/-- An address term's shape. -/
inductive AddrShapeL (C : Contract) where
  | field (f : Name) (o : (R : RefTy) × LTm C (.ident R))
  | index (i : (R : RefTy) × LTm C (.ident R)) (k : Option PrimTy.uint.Denote)

/-- At a unary symbol. -/
def _root_.Solidity.Op1.addrStepL {a u : Srt} : Op1 C a u → LTm C a → Option (AddrShapeL C)
  | .mfield (f := f) _, x => some (.field f ⟨_, x⟩)
  | _, _ => none

/-- At a binary symbol. -/
def _root_.Solidity.Op2.addrStepL {a b u : Srt} : Op2 C a b u → LTm C a → LTm C b →
    Option (AddrShapeL C)
  | .mat _, x, y => some (.index ⟨_, x⟩ y.uintLit?)
  | _, _, _ => none

/-- An address term's shape.  Generic in the sort. -/
def LTm.addrShape? {u : Srt} : LTm C u → Option (AddrShapeL C)
  | .app1 o x => o.addrStepL x
  | .app2 o x y => o.addrStepL x y
  | _ => none

/-- **Two address terms that never meet** (`readOnWriteFrame`'s side
condition, decided on the terms): two members, a member and an element, or
two elements of one identity at two literal indices; each address with its
object's guards out (`LTm.hoistA`). -/
def LTm.apart? {T U : Ty} (a : LTm C (.addr T)) (b : LTm C (.addr U)) : Bool :=
  match a.hoistA.2.addrShape?, b.hoistA.2.addrShape? with
  | some (.field f o), some (.field g o') => f != g || LTm.identApart? o.2 o'.2
  | some (.field _ _), some (.index _ _) => true
  | some (.index _ _), some (.field _ _) => true
  | some (.index i k), some (.index j k') =>
    (i.2.beqR j.2 && match k, k' with
      | some k, some k' => k != k'
      | _, _ => false) || LTm.identApart? i.2 j.2
  | _, _ => false

/-- What an address term's shape says of the address it reads. -/
def AddrShapeL.Reads (g : State C []) (ν : AEnv) {T : Ty} : AddrShapeL C → MAddrT T → Prop
  | .field f o, ad => ∃ (s : Name) (id : Nat) (h : lookupBy f (structDef s) = some T),
      ad = MAddrT.field id h ∧ (o.2.eval g ν : Option Nat) = some id
  | .index ⟨R, i⟩ k, ad => ∃ (id : Nat) (a : ArrTy R T) (j : PrimTy.uint.Denote),
      (i.eval g ν : Option Nat) = some id ∧ ad = MAddrT.index id a j ∧ ∀ k', k = some k' → j = k'

theorem LTm.addrShape?_eval {T : Ty} {a : LTm C (.addr T)} {sh : AddrShapeL C}
    (h : a.addrShape? = some sh) {ad : MAddrT T} (ha : (a.eval g ν : Option (MAddrT T)) = some ad) :
    sh.Reads g ν ad := by
  cases a with
  | app1 o x =>
    cases o <;> simp only [LTm.addrShape?, Op1.addrStepL, reduceCtorEq, Option.some.injEq] at h
    subst h
    rename_i s f hf
    have ha : ((x.eval g ν : Option Nat).map (fun id => MAddrT.field id hf)) = some ad := ha
    obtain ⟨id, hid, rfl⟩ := Option.map_eq_some_iff.1 ha
    exact ⟨s, id, hf, rfl, hid⟩
  | app2 o x y =>
    cases o <;> simp only [LTm.addrShape?, Op2.addrStepL, reduceCtorEq, Option.some.injEq] at h
    subst h
    rename_i R arr
    have ha : (((x.eval g ν : Option Nat)).bind fun id =>
        (y.eval g ν : Option PrimTy.uint.Denote).bind fun k => some (MAddrT.index id arr k)) =
      some ad := ha
    simp only [Option.bind_eq_some_iff, Option.some.injEq] at ha
    obtain ⟨id, hi, w, hw, rfl⟩ := ha
    refine ⟨id, arr, w, hi, rfl, fun k' hk => ?_⟩
    have hw' := LTm.uintLit?_eval (g := g) (ν := ν) hk
    rw [hw] at hw'
    exact Option.some.inj hw'
  | _ => simp only [LTm.addrShape?, reduceCtorEq] at h

/-- Two apart address terms resolve, in one heap typing, to apart
addresses. -/
theorem LTm.apart?_resolve {T U : Ty} {a : LTm C (.addr T)} {b : LTm C (.addr U)}
    (h : a.apart? b = true) {ad : MAddrT T} {bd : MAddrT U}
    (ha : (a.eval g ν : Option (MAddrT T)) = some ad)
    (hb : (b.eval g ν : Option (MAddrT U)) = some bd) : ad.Apart bd := by
  have ha := LTm.hoistA_some ha
  have hb := LTm.hoistA_some hb
  unfold LTm.apart? at h
  split at h
  · rename_i f o f' o' hfa hfb
    obtain ⟨s, id, hf, rfl, hid⟩ := LTm.addrShape?_eval hfa ha
    obtain ⟨s', id', hg, rfl, hid'⟩ := LTm.addrShape?_eval hfb hb
    rcases Bool.or_eq_true_iff.1 h with h | h
    · exact .inr (by simpa only [bne_iff_ne, ne_eq] using h)
    · exact .inl (LTm.identApart?_ne h hid hid')
  · rename_i f o i k hfa hfb
    obtain ⟨s, id, hf, rfl, -⟩ := LTm.addrShape?_eval hfa ha
    obtain ⟨id', arr, j, -, rfl, -⟩ := LTm.addrShape?_eval hfb hb
    trivial
  · rename_i i k f o hfa hfb
    obtain ⟨id', arr, j, -, rfl, -⟩ := LTm.addrShape?_eval hfa ha
    obtain ⟨s, id, hf, rfl, -⟩ := LTm.addrShape?_eval hfb hb
    trivial
  · rename_i i k j k' hfa hfb
    obtain ⟨R, i⟩ := i
    obtain ⟨R', j⟩ := j
    obtain ⟨id, arr, n, hi, rfl, hn⟩ := LTm.addrShape?_eval hfa ha
    obtain ⟨id', arr', n', hi', rfl, hn'⟩ := LTm.addrShape?_eval hfb hb
    rcases Bool.or_eq_true_iff.1 h with h | h
    · simp only [Bool.and_eq_true] at h
      obtain ⟨hij, hk⟩ := h
      cases LTm.sigma_eq_of_beqR hij
      rw [hi] at hi'
      cases hi'
      refine .inr ?_
      split at hk
      · rename_i k₁ k₂
        have hk' : k₁ ≠ k₂ := by simpa only [bne_iff_ne, ne_eq] using hk
        exact fun e => hk' ((hn k₁ rfl).symm.trans (e.trans (hn' k₂ rfl)))
      · cases hk
    · exact .inl (LTm.identApart?_ne h hi hi')
  · nomatch h

end Views

/-! ## The laws of a read -/

section Laws

variable {g : State C []} {ν : AEnv}

/-- A read of a word, as `readId` reads it. -/
theorem LTm.read_eval_readId {P : PrimTy} (X : LTm C .mem) (b : LTm C (.addr (.prim P))) :
    ((LTm.app2 .read X b).eval g ν : Option P.Denote) =
      ((X.eval g ν : Option (Grown g.H (fun _ => Unit))).bind fun μ =>
        (b.eval g ν : Option (MAddrT (.prim P))).bind fun bd => μ.readId bd) := by
  rw [LTm.read_evalT]
  cases (X.eval g ν : Option (Grown g.H (fun _ => Unit))) with
  | none => rfl
  | some μ =>
    cases (b.eval g ν : Option (MAddrT (.prim P))) with
    | none => rfl
    | some bd =>
      simp only [Option.bind_some, Grown.readId, Grown.readT, Option.bind_eq_bind]
      cases (bd.resolve μ.H').bind μ.heap.readAddr <;> rfl

/-- A read of an identity, as `readId` reads it. -/
theorem LTm.iread_eval_readId {R : RefTy} (X : LTm C .mem) (b : LTm C (.addr (.ref R))) :
    ((LTm.app2 .iread X b).eval g ν : Option Nat) =
      ((X.eval g ν : Option (Grown g.H (fun _ => Unit))).bind fun μ =>
        (b.eval g ν : Option (MAddrT (.ref R))).bind fun bd => μ.readId bd) := by
  rw [LTm.iread_evalT]
  cases (X.eval g ν : Option (Grown g.H (fun _ => Unit))) with
  | none => rfl
  | some μ =>
    cases (b.eval g ν : Option (MAddrT (.ref R))) with
    | none => rfl
    | some bd =>
      simp only [Option.bind_some, Grown.readId, Grown.readT, Option.bind_eq_bind]
      cases (bd.resolve μ.H').bind μ.heap.readAddr <;> rfl

/-- A write that returns: its memory, address and value, and the memory it
leaves. -/
theorem LTm.write_some {T : Ty} {m : LTm C .mem} {a : LTm C (.addr T)} {v : LTm C (.mv T)}
    {μ' : Grown g.H (fun _ => Unit)}
    (h : ((LTm.app3 .write m a v).eval g ν : Option (Grown g.H (fun _ => Unit))) = some μ') :
    ∃ μ ad w, (m.eval g ν : Option (Grown g.H (fun _ => Unit))) = some μ ∧
      (a.eval g ν : Option (MAddrT T)) = some ad ∧ (v.eval g ν : Option (MvT T)) = some w ∧
      μ.writeT ad w = some μ' := by
  rw [LTm.eval_app3, Op3.eval_eq_evalM] at h
  simp only [Op3.evalM, Option.bind_eq_bind, Option.bind_eq_some_iff] at h
  obtain ⟨μ, hm, ad, ha, w, hv, hw⟩ := h
  exact ⟨μ, ad, w, hm, ha, hv, hw⟩

/-- **readOnWrite**: the address written reads the word written, where the
write returns. -/
theorem LTm.read_write_same {P : PrimTy} (m : LTm C .mem) (a : LTm C (.addr (.prim P)))
    (x : LTm C (.val P)) :
    ((LTm.app2 .read (.app3 .write m a (.app1 .mval x)) a).eval g ν : Option P.Denote) =
      (LTm.seq (.app3 .write m a (.app1 .mval x)) x).eval g ν := by
  rw [LTm.read_eval_readId, LTm.eval_seq]
  cases hW : ((LTm.app3 .write m a (.app1 .mval x)).eval g ν :
      Option (Grown g.H (fun _ => Unit))) with
  | none => rfl
  | some μ' =>
    obtain ⟨μ, ad, w, hm, ha, hv, hw⟩ := LTm.write_some hW
    rw [Option.bind_some, ha, Option.bind_some, (Grown.writeT_facts hw).1]
    have hx : (x.eval g ν : Option P.Denote) = some w := hv
    rw [Option.bind_some, hx]

/-- **readOnWrite** of an identity. -/
theorem LTm.iread_write_same {R : RefTy} (m : LTm C .mem) (a : LTm C (.addr (.ref R)))
    (t : LTm C (.ident R)) :
    ((LTm.app2 .iread (.app3 .write m a (.app1 .ref t)) a).eval g ν : Option Nat) =
      (LTm.seq (.app3 .write m a (.app1 .ref t)) t).eval g ν := by
  rw [LTm.iread_eval_readId, LTm.eval_seq]
  cases hW : ((LTm.app3 .write m a (.app1 .ref t)).eval g ν :
      Option (Grown g.H (fun _ => Unit))) with
  | none => rfl
  | some μ' =>
    obtain ⟨μ, ad, w, hm, ha, hv, hw⟩ := LTm.write_some hW
    rw [Option.bind_some, ha, Option.bind_some, (Grown.writeT_facts hw).1]
    have hx : (t.eval g ν : Option Nat) = some w := hv
    rw [Option.bind_some, hx]

/-- **readOnWrite** at the address written, its object's guards out
(`LTm.hoistA`): where the write returns, the guards hold. -/
theorem LTm.read_write_hoist {P : PrimTy} (m : LTm C .mem) (a : LTm C (.addr (.prim P)))
    (x : LTm C (.val P)) :
    ((LTm.app2 .read (.app3 .write m a (.app1 .mval x)) a.hoistA.2).eval g ν : Option P.Denote) =
      (LTm.seq (.app3 .write m a (.app1 .mval x)) x).eval g ν := by
  rw [LTm.read_eval_readId, LTm.eval_seq]
  cases hW : ((LTm.app3 .write m a (.app1 .mval x)).eval g ν :
      Option (Grown g.H (fun _ => Unit))) with
  | none => rfl
  | some μ' =>
    obtain ⟨μ, ad, w, hm, ha, hv, hw⟩ := LTm.write_some hW
    rw [Option.bind_some, LTm.hoistA_some ha, Option.bind_some, (Grown.writeT_facts hw).1]
    have hx : (x.eval g ν : Option P.Denote) = some w := hv
    rw [Option.bind_some, hx]

/-- **readOnWrite** of an identity, its object's guards out. -/
theorem LTm.iread_write_hoist {R : RefTy} (m : LTm C .mem) (a : LTm C (.addr (.ref R)))
    (t : LTm C (.ident R)) :
    ((LTm.app2 .iread (.app3 .write m a (.app1 .ref t)) a.hoistA.2).eval g ν : Option Nat) =
      (LTm.seq (.app3 .write m a (.app1 .ref t)) t).eval g ν := by
  rw [LTm.iread_eval_readId, LTm.eval_seq]
  cases hW : ((LTm.app3 .write m a (.app1 .ref t)).eval g ν :
      Option (Grown g.H (fun _ => Unit))) with
  | none => rfl
  | some μ' =>
    obtain ⟨μ, ad, w, hm, ha, hv, hw⟩ := LTm.write_some hW
    rw [Option.bind_some, LTm.hoistA_some ha, Option.bind_some, (Grown.writeT_facts hw).1]
    have hx : (t.eval g ν : Option Nat) = some w := hv
    rw [Option.bind_some, hx]

/-- **readOnWriteFrame**: an address apart from the one written reads
below the write, where it returns. -/
theorem LTm.read_write_apart {T U : Ty} (m : LTm C .mem) (a : LTm C (.addr T)) (v : LTm C (.mv T))
    (b : LTm C (.addr U)) (h : a.apart? b = true) :
    ((LTm.app3 .write m a v).eval g ν : Option (Grown g.H (fun _ => Unit))).bind
        (fun μ => (b.eval g ν : Option (MAddrT U)).bind fun bd => μ.readId bd) =
      ((LTm.app3 .write m a v).eval g ν : Option (Grown g.H (fun _ => Unit))).bind
        (fun _ => (m.eval g ν : Option (Grown g.H (fun _ => Unit))).bind fun μ =>
          (b.eval g ν : Option (MAddrT U)).bind fun bd => μ.readId bd) := by
  cases hW : ((LTm.app3 .write m a v).eval g ν : Option (Grown g.H (fun _ => Unit))) with
  | none => rfl
  | some μ' =>
    obtain ⟨μ, ad, w, hm, ha, hv, hw⟩ := LTm.write_some hW
    rw [Option.bind_some, Option.bind_some, hm, Option.bind_some]
    cases hb : (b.eval g ν : Option (MAddrT U)) with
    | none => rfl
    | some bd =>
      simp only [Option.bind_some]
      exact (Grown.writeT_facts hw).2 bd (LTm.apart?_resolve h ha hb)

theorem LTm.read_write_apart' {P : PrimTy} {T : Ty} (m : LTm C .mem) (a : LTm C (.addr T))
    (v : LTm C (.mv T)) (b : LTm C (.addr (.prim P))) (h : a.apart? b = true) :
    ((LTm.app2 .read (.app3 .write m a v) b).eval g ν : Option P.Denote) =
      (LTm.seq (.app3 .write m a v) (.app2 .read m b)).eval g ν := by
  rw [LTm.read_eval_readId, LTm.eval_seq, LTm.read_write_apart m a v b h]
  congr 1
  funext _
  rw [LTm.read_eval_readId]

theorem LTm.iread_write_apart' {R : RefTy} {T : Ty} (m : LTm C .mem) (a : LTm C (.addr T))
    (v : LTm C (.mv T)) (b : LTm C (.addr (.ref R))) (h : a.apart? b = true) :
    ((LTm.app2 .iread (.app3 .write m a v) b).eval g ν : Option Nat) =
      (LTm.seq (.app3 .write m a v) (.app2 .iread m b)).eval g ν := by
  rw [LTm.iread_eval_readId, LTm.eval_seq, LTm.read_write_apart m a v b h]
  congr 1
  funext _
  rw [LTm.iread_eval_readId]

/-- **readOnAddMFrame**: below an allocation, an address whose object is
older reads below it. -/
theorem LTm.read_addM_old {P : PrimTy} (m : LTm C .mem) (R : RefTy)
    (hR : (Ty.ref R).mapFree = true) (b : LTm C (.addr (.prim P))) (h : b.boundedIn m = true) :
    ((LTm.app2 .read (.app1 (.addM R hR) m) b).eval g ν : Option P.Denote) =
      (LTm.app2 .read m b).eval g ν := by
  rw [LTm.read_evalT, LTm.read_evalT, LTm.eval_app1, Op1.eval_eq_evalM]
  cases hm : (m.eval g ν : Option (Grown g.H (fun _ => Unit))) with
  | none => rfl
  | some μ₀ =>
    simp only [Op1.evalM, Option.map_some, Option.bind_some]
    cases hb : (b.eval g ν : Option (MAddrT (.prim P))) with
    | none => rfl
    | some bd =>
      simp only [Option.bind_some]
      rw [Grown.read_then_old μ₀ (μ₀.heap.allocDefault R hR) (SVal.keeps_copyStToM _ hR μ₀.heap) bd
        (LTm.boundedIn_eval hm b h bd hb)]
      exact MVal.map_wk_prim _ _

theorem LTm.iread_addM_old {R' : RefTy} (m : LTm C .mem) (R : RefTy)
    (hR : (Ty.ref R).mapFree = true) (b : LTm C (.addr (.ref R'))) (h : b.boundedIn m = true) :
    ((LTm.app2 .iread (.app1 (.addM R hR) m) b).eval g ν : Option Nat) =
      (LTm.app2 .iread m b).eval g ν := by
  rw [LTm.iread_evalT, LTm.iread_evalT, LTm.eval_app1, Op1.eval_eq_evalM]
  cases hm : (m.eval g ν : Option (Grown g.H (fun _ => Unit))) with
  | none => rfl
  | some μ₀ =>
    simp only [Op1.evalM, Option.map_some, Option.bind_some]
    cases hb : (b.eval g ν : Option (MAddrT (.ref R'))) with
    | none => rfl
    | some bd =>
      simp only [Option.bind_some]
      rw [Grown.read_then_old μ₀ (μ₀.heap.allocDefault R hR) (SVal.keeps_copyStToM _ hR μ₀.heap) bd
        (LTm.boundedIn_eval hm b h bd hb)]
      exact MVal.bind_id_map_wk _ _

/-- **readOnAddMFrame** below a copy into memory. -/
theorem LTm.read_copySt_old {P : PrimTy} {U : Ty} (m : LTm C .mem) (hU : U.mapFree = true)
    (S : LTm C (.sv U)) (b : LTm C (.addr (.prim P))) (h : b.boundedIn m = true) :
    ((LTm.app2 .read (.app2 (.copySt hU) m S) b).eval g ν : Option P.Denote) =
      (LTm.seq S (.app2 .read m b)).eval g ν := by
  rw [LTm.read_evalT, LTm.eval_seq, LTm.read_evalT, LTm.eval_app2, Op2.eval_eq_evalM]
  cases hm : (m.eval g ν : Option (Grown g.H (fun _ => Unit))) with
  | none => cases (S.eval g ν : Option (SVal U)) <;> rfl
  | some μ₀ =>
    cases hS : (S.eval g ν : Option (SVal U)) with
    | none => rfl
    | some v =>
      simp only [Op2.evalM, Option.bind_eq_bind, Option.bind_some]
      cases hb : (b.eval g ν : Option (MAddrT (.prim P))) with
      | none => rfl
      | some bd =>
        simp only [Option.bind_some]
        rw [Grown.read_then_old μ₀ _ (SVal.keeps_copyStToM v hU μ₀.heap) bd
          (LTm.boundedIn_eval hm b h bd hb)]
        exact MVal.map_wk_prim _ _

theorem LTm.iread_copySt_old {R' : RefTy} {U : Ty} (m : LTm C .mem) (hU : U.mapFree = true)
    (S : LTm C (.sv U)) (b : LTm C (.addr (.ref R'))) (h : b.boundedIn m = true) :
    ((LTm.app2 .iread (.app2 (.copySt hU) m S) b).eval g ν : Option Nat) =
      (LTm.seq S (.app2 .iread m b)).eval g ν := by
  rw [LTm.iread_evalT, LTm.eval_seq, LTm.iread_evalT, LTm.eval_app2, Op2.eval_eq_evalM]
  cases hm : (m.eval g ν : Option (Grown g.H (fun _ => Unit))) with
  | none => cases (S.eval g ν : Option (SVal U)) <;> rfl
  | some μ₀ =>
    cases hS : (S.eval g ν : Option (SVal U)) with
    | none => rfl
    | some v =>
      simp only [Op2.evalM, Option.bind_eq_bind, Option.bind_some]
      cases hb : (b.eval g ν : Option (MAddrT (.ref R'))) with
      | none => rfl
      | some bd =>
        simp only [Option.bind_some]
        rw [Grown.read_then_old μ₀ _ (SVal.keeps_copyStToM v hU μ₀.heap) bd
          (LTm.boundedIn_eval hm b h bd hb)]
        exact MVal.bind_id_map_wk _ _

/-- **readOnAddM**, **initMember**, **defaultValueInt**: below an
allocation, an address at a member path of the fresh root, of a primitive
type, reads its default, where the memory below returns. -/
theorem LTm.read_addM_fresh {P : PrimTy} (m : LTm C .mem) (R : RefTy)
    (hR : (Ty.ref R).mapFree = true) (b : LTm C (.addr (.prim P)))
    (h : (LTm.freshPath? m R b).bind (Ty.ref R).memberTy = some (.prim P)) :
    ((LTm.app2 .read (.app1 (.addM R hR) m) b).eval g ν : Option P.Denote) =
      (LTm.seq m (.lit (PrimTy.dflt P))).eval g ν := by
  rw [LTm.eval_seq]
  cases hm : (m.eval g ν : Option (Grown g.H (fun _ => Unit))) with
  | none =>
    rw [LTm.read_evalT, LTm.eval_app1, hm, Op1.eval_none]; rfl
  | some μ₀ =>
    obtain ⟨p, hp, hT⟩ := Option.bind_eq_some_iff.1 h
    have hX : ((LTm.app1 (.addM R hR) m).eval g ν : Option (Grown g.H (fun _ => Unit))) =
        some (μ₀.then (μ₀.heap.allocDefault R hR)) := by
      rw [LTm.eval_app1, Op1.eval_eq_evalM]
      simp only [Op1.evalM, hm, Option.map_some]
    rw [LTm.read_evalT, hX, Option.bind_some]
    exact Srt.FreshRead.read_prim (LTm.freshPath_eval (hR := hR) hm b hp) hT

/-- A member address term, viewed: its object and member. -/
structure FieldV (C : Contract) where
  {s f : Name}
  {T : Ty}
  hf : C.fieldType s f = some T
  t : LTm C (.ident (.struct s))

def _root_.Solidity.Op1.fieldV {a u : Srt} (o : Op1 C a u) (x : LTm C a) : Option (FieldV C) :=
  match o, x with
  | .mfield hf, x => some ⟨hf, x⟩
  | _, _ => none

/-- A member address term's object and member. -/
def LTm.fieldV? {u : Srt} (b : LTm C u) : Option (FieldV C) :=
  match b with
  | .app1 o x => o.fieldV x
  | _ => none

/-- A storage value term read out of storage, viewed: `sfind(st, q)`. -/
structure SFindV (C : Contract) where
  {T : Ty}
  st : LTm C .st
  q : LTm C (.path T)

def _root_.Solidity.Op2.sfindV {a b u : Srt} (o : Op2 C a b u) (x : LTm C a) (y : LTm C b) :
    Option (SFindV C) :=
  match o, x, y with
  | .sfind, x, y => some ⟨x, y⟩
  | _, _, _ => none

/-- A storage value term's storage and path, where it is read out of one. -/
def LTm.sfindV? {u : Srt} (S : LTm C u) : Option (SFindV C) :=
  match S with
  | .app2 o x y => o.sfindV x y
  | _ => none

/-- An identity minted over `m` without its writes, minted over `m` itself
(`LTm.stripW`): how a copy's root reads at the node that copies it. -/
def _root_.Solidity.Op2.unstripId (m : LTm C .mem) {a b s : Srt} (o : Op2 C a b s) (x : LTm C a)
    (y : LTm C b) : LTm C s :=
  match o, x with
  | .copy h, x => if x.beqR m.stripW then .app2 (.copy h) m y else .app2 (.copy h) x y
  | o, x => .app2 o x y

/-- `Op2.unstripId` on a term. -/
def LTm.unstripId {s : Srt} (t : LTm C s) (m : LTm C .mem) : LTm C s :=
  match t with
  | .app2 o x y => o.unstripId m x y
  | t => t

/-- An address with its object's identity read at `m` (`LTm.unstripId`). -/
def _root_.Solidity.Op1.unstripA (m : LTm C .mem) {a s : Srt} (o : Op1 C a s) (x : LTm C a) :
    LTm C s :=
  match o with
  | .mfield h => .app1 (.mfield h) (x.unstripId m)
  | o => .app1 o x

/-- At a binary symbol. -/
def _root_.Solidity.Op2.unstripA (m : LTm C .mem) {a b s : Srt} (o : Op2 C a b s) (x : LTm C a)
    (y : LTm C b) : LTm C s :=
  match o with
  | .mat ak => .app2 (.mat ak) (x.unstripId m) y
  | o => .app2 o x y

/-- **An address read at the copy that minted its object**: its identity
over `m` in place of `m` without its writes, so that the copy's laws
(`copyFieldRd?`, `copyNewArrayRd?`) see the root they copy. -/
def LTm.unstripAddr {s : Srt} (b : LTm C s) (m : LTm C .mem) : LTm C s :=
  match b with
  | .app1 o x => o.unstripA m x
  | .app2 o x y => o.unstripA m x y
  | b => b

theorem LTm.unstripId_eval {m : LTm C .mem} {μ : Grown g.H (fun _ => Unit)}
    (hm : m.eval g ν = some μ) {s : Srt} (t : LTm C s) :
    (t.unstripId m).eval g ν = t.eval g ν := by
  cases t with
  | app2 o x y =>
    cases o
    case copy =>
      show (if x.beqR m.stripW then _ else _ : LTm C _).eval g ν = _
      split
      · rename_i hx
        obtain rfl := LTm.eq_of_beqR hx
        exact (LTm.copy_stripW_eval hm _ y).symm
      · rfl
    all_goals rfl
  | _ => rfl

theorem LTm.unstripAddr_eval {m : LTm C .mem} {μ : Grown g.H (fun _ => Unit)}
    (hm : m.eval g ν = some μ) {s : Srt} (b : LTm C s) :
    (b.unstripAddr m).eval g ν = b.eval g ν := by
  cases b with
  | app1 o x =>
    cases o
    case mfield =>
      show (LTm.app1 _ (x.unstripId m)).eval g ν = _
      rw [LTm.eval_app1, LTm.eval_app1, LTm.unstripId_eval hm]
    all_goals rfl
  | app2 o x y =>
    cases o
    case mat =>
      show (LTm.app2 _ (x.unstripId m) y).eval g ν = _
      rw [LTm.eval_app2, LTm.eval_app2, LTm.unstripId_eval hm]
    all_goals rfl
  | _ => rfl

/-- A read at the node `copySt(m, S)`, its address read there
(`LTm.unstripAddr`). -/
theorem LTm.read_unstrip {P : PrimTy} {U : Ty} (m : LTm C .mem) (hU : U.mapFree = true)
    (S : LTm C (.sv U)) (b : LTm C (.addr (.prim P))) :
    (LTm.app2 .read (.app2 (.copySt hU) m S) (b.unstripAddr m)).eval g ν =
      (LTm.app2 .read (.app2 (.copySt hU) m S) b).eval g ν := by
  cases hm : (m.eval g ν : Option (Grown g.H (fun _ => Unit))) with
  | none =>
    rw [LTm.eval_app2_none _ _ _ (LTm.eval_app2_none _ _ _ hm),
      LTm.eval_app2_none _ _ _ (LTm.eval_app2_none _ _ _ hm)]
  | some μ => simp only [LTm.eval_app2, LTm.unstripAddr_eval hm]

/-- **A member of a copy of storage, read** (`readFromCopyToStorage`): the
word at the member of the copy's root, as the storage it copied holds it
there. -/
def copyFieldRd? (m : LTm C .mem) {U : Ty} (S : LTm C (.sv U)) {P : PrimTy}
    (b : LTm C (.addr (.prim P))) : Option (LTm C (.val P)) :=
  match b.fieldV? with
  | some fv =>
    match fv.t.identView with
    | .copy m' _ S' =>
      if m'.beqR m && S'.beqR S && fv.f != "length" then
        match S.sfindV? with
        | some ⟨st, q⟩ =>
          (q.castTo? (s' := .path (.ref (.struct fv.s)))).bind fun q' =>
            ((LTm.app1 (.field fv.hf) q').castTo? (s' := .path (.prim P))).map fun q'' =>
              .app2 .find st q''
        | none => none
      else none
    | _ => none
  | none => none

theorem copyFieldRd?_eval {m : LTm C .mem} {U : Ty} {hU : U.mapFree = true} {S : LTm C (.sv U)}
    {P : PrimTy} {b : LTm C (.addr (.prim P))} {y : LTm C (.val P)} (h : copyFieldRd? m S b = some y) :
    ((LTm.app2 .read (.app2 (.copySt hU) m S) b).eval g ν : Option P.Denote) =
      (LTm.seq (.app2 (.copySt hU) m S) y).eval g ν := by
  unfold copyFieldRd? at h
  split at h
  · rename_i fv hfv
    split at h
    · rename_i m' U' hU' S' ht
      split at h
      · rename_i hc
        simp only [Bool.and_eq_true, bne_iff_ne, ne_eq] at hc
        obtain ⟨⟨hm, hS⟩, hl⟩ := hc
        split at h
        · rename_i T' st q hsf
          obtain ⟨q', hq', h⟩ := Option.bind_eq_some_iff.1 h
          obtain ⟨q'', hq'', rfl⟩ := Option.map_eq_some_iff.1 h
          cases b with
          | app1 o x =>
            cases o <;> simp only [LTm.fieldV?, Op1.fieldV, reduceCtorEq, Option.some.injEq] at hfv
            subst hfv
            rename_i s f hf
            obtain ⟨-, hq2⟩ := Sigma.mk.inj (LTm.castTo?_eq hq'')
            cases eq_of_heq hq2
            obtain ⟨hT, hq1⟩ := Sigma.mk.inj (LTm.castTo?_eq hq')
            cases hT
            cases eq_of_heq hq1
            cases LTm.sigma_eq_of_beqR hm
            obtain ⟨hUU, hSS⟩ := Sigma.mk.inj (LTm.sigma_eq_of_beqR hS)
            cases hUU
            cases eq_of_heq hSS
            cases x with
            | app2 o xm xS =>
              cases o <;> simp only [LTm.identView, Op2.identV, reduceCtorEq, IdentV.copy.injEq] at ht
              obtain ⟨rfl, hR, hxS⟩ := ht
              cases hR
              cases eq_of_heq hxS
              cases xS with
              | app2 o st' q0 =>
                cases o <;> simp only [LTm.sfindV?, Op2.sfindV, reduceCtorEq, Option.some.injEq,
                  SFindV.mk.injEq] at hsf
                obtain ⟨-, hst', hq0⟩ := hsf
                subst st
                cases eq_of_heq hq0
                have ev : ((LTm.app2 .sfind st' q0).eval g ν : Option (SVal _)) =
                    (st'.eval g ν : Option (Storage C)).bind fun st₀ =>
                      (q0.eval g ν : Option (SRef C _)).bind fun r₀ => st₀.find r₀ := by
                  rw [LTm.eval_app2]
                  cases (st'.eval g ν : Option (Storage C)) <;>
                    cases (q0.eval g ν : Option (SRef C _)) <;> rfl
                rw [LTm.read_evalT, LTm.eval_seq, LTm.eval_app2 g ν (Op2.copySt hU), Op2.eval_eq_evalM]
                cases hxm : (xm.eval g ν : Option (Grown g.H (fun _ => Unit))) with
                | none => rfl
                | some μ₀ =>
                  cases hv : ((LTm.app2 .sfind st' q0).eval g ν : Option (SVal _)) with
                  | none => rfl
                  | some v =>
                    rw [ev] at hv
                    simp only [Option.bind_eq_some_iff] at hv
                    obtain ⟨st₀, hst, r₀, hr₀, hfv⟩ := hv
                    rename_i hcp
                    have hv2 : ((LTm.app2 .sfind st' q0).eval g ν : Option (SVal _)) = some v := by
                      rw [ev, hst, Option.bind_some, hr₀, Option.bind_some, hfv]
                    have hb : ((LTm.app1 (Op1.mfield f) (LTm.app2 (Op2.copy hcp) xm
                        (LTm.app2 Op2.sfind st' q0))).eval g ν : Option (MAddrT _)) =
                        some (MAddrT.field (v.copyStToM μ₀.heap hcp).val.id f) := by
                      rw [LTm.eval_app1, LTm.eval_app2, hxm, hv2]; rfl
                    rw [show Op2.evalM g (Op2.copySt hU) (some μ₀) (some v) =
                      some (μ₀.then (v.copyStToM μ₀.heap hU)) from rfl, Option.bind_some,
                      Option.bind_some, hb, Option.bind_some]
                    show ((MAddrT.field (SVal.copyStToM μ₀.heap v hU).val.id f).resolve
                      (SVal.copyStToM μ₀.heap v hU).H').bind
                      (fun rb => (SVal.copyStToM μ₀.heap v hU).heap.readAddr rb) = _
                    rw [MAddrT.resolve_eq_resolveM]
                    simp only [MAddrT.resolveM]
                    rw [HRef.ofId?_self (r := ((SVal.copyStToM μ₀.heap v hU).val : HRef _ _))]
                    simp only [Option.map_some, Option.bind_some]
                    show some ((SVal.copyStToM μ₀.heap v hU).heap.field
                      (SVal.copyStToM μ₀.heap v hU).val f) = _
                    rw [SVal.copyStToM_field μ₀.heap v hU f, LTm.eval_app2, hst, LTm.eval_app1, hr₀]
                    show _ = (st₀.find (r₀.field f)).bind fun w => some w.view
                    rw [SRef.field, Storage.find_append, hfv]
                    cases v with
                    | struct fs => rfl
              | _ => simp only [LTm.sfindV?, reduceCtorEq] at hsf
            | app1 o xm => cases o <;> simp only [LTm.identView, Op1.identV, reduceCtorEq] at ht
            | _ => simp only [LTm.identView, reduceCtorEq] at ht
          | _ => simp only [LTm.fieldV?, reduceCtorEq] at hfv
        · cases h
      · cases h
    · cases h
  · cases h

end Laws

end Decide

end Solidity
